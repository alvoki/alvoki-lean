import Alvoki.Experiments.L0.TableWriterSchedule
import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder

namespace ExperimentalL0.NativeTableWriter
open System ImmutableSSTable Unified
open NativeScope (W Post)

private def Safe (a : Observed α) (w : W) (ok : α → W → Prop) (bad : IO.Error → W → Prop)
    (P : W → Prop) : Prop := Post a.run w ok bad ∧ ∀ l t, a.visits w l t → P t

private theorem Safe.bind (first : Safe a w mid bad P)
    (rest : ∀ x t, mid x t → Safe (next x) t ok bad P) : Safe (a >>= next) w ok bad P := by
  refine ⟨NativeScope.Post.bind _ _ (first.1.weaken (fun x t h => (rest x t h).1) (fun _ _ => id)),?_⟩
  rintro l u (visited | ⟨x,t,ran,visit⟩)
  · exact first.2 _ _ visited
  · have facts := first.1
    rw [Post,ran] at facts
    exact (rest x t facts).2 _ _ visit

private theorem Safe.caught (first : Safe a w ok mid P)
    (rest : ∀ e t, mid e t → Safe (next e) t ok bad P) : Safe (tryCatchThe IO.Error a next) w ok bad P := by
  have facts := first.1
  refine ⟨?_,?_⟩
  · change Post (tryCatchThe IO.Error a.run (fun e => (next e).run)) w ok bad
    unfold Post at facts ⊢
    cases ran : a.run w with
    | ok x t => simpa [tryCatchThe,MonadExceptOf.tryCatch,instMonadExceptOfEIO._aux_3,EST.tryCatch,ran] using (show ok x t by simpa [ran] using facts)
    | error e t =>
      rw [ran] at facts
      simpa [Post,tryCatchThe,MonadExceptOf.tryCatch,instMonadExceptOfEIO._aux_3,EST.tryCatch,ran] using (rest e t facts).1
  · rintro l u (visited | ⟨e,t,ran,visit⟩)
    · exact first.2 _ _ visited
    · rw [Post,ran] at facts
      exact (rest e t facts).2 _ _ visit

private theorem Safe.pure (h : ok x w) : Safe (pure x) w ok bad P := ⟨h,fun _ _ => False.elim⟩
private theorem Safe.fail (h : bad e w) : Safe (throw e) w ok bad P := ⟨h,fun _ _ => False.elim⟩

private theorem Safe.leaf (leaf : Leaf) {ok : leaf.Result → W → Prop} (entry : P w) (h : Post leaf.action w ok bad) : Safe (issue leaf) w ok bad P :=
  ⟨h,fun _ _ v => v.2 ▸ entry⟩

private theorem Safe.weaken (h : Safe a w ok bad P)
    (onOk : ∀ x t, ok x t → ok' x t) (onError : ∀ e t, bad e t → bad' e t) : Safe a w ok' bad' P :=
  ⟨h.1.weaken onOk onError,h.2⟩

/-- Current observations of the newly created inode and its private stdio
buffer. A successful flush copies the accepted bytes to the live inode. -/
structure Output (ns : TableNamespace W) where
  inodeOf : W → IO.FS.Handle → Option ns.inode
  buffered : W → IO.FS.Handle → ByteArray
  cursor : W → IO.Ref Rows → Rows → Prop

def Output.Bound (out : Output ns) (id : UInt64) (fd : IO.FS.Handle) (identity : ns.inode) (w : W) : Prop :=
  ns.names w (tablePath ns.directory id) = some identity ∧ out.inodeOf w fd = some identity

def Output.Held (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows)
    (fd : IO.FS.Handle) (identity : ns.inode) (rs : Rows) (bytes : ByteArray) (flushed : Bool) (w : W) : Prop :=
  P w ∧ out.Bound id fd identity w ∧ out.cursor w ref rs ∧ out.buffered w fd = bytes ∧
    (flushed = true → ns.contents w identity = some bytes)

def Output.Owns (out : Output ns) (P : W → Prop) (id : UInt64) (fd : IO.FS.Handle) (inode : ns.inode) (w : W) : Prop :=
  P w ∧ out.Bound id fd inode w

/-- The cursor and exclusive descriptor came from this invocation. The
identity is the new inode named at the successful acquisition. -/
def Output.Acquired (out : Output ns) (id : UInt64) (rows : Rows) (start : W)
    (ref : IO.Ref Rows) (fd : IO.FS.Handle) (inode : ns.inode) : Prop :=
  ∃ allocated created, (Leaf.allocate rows).action start = .ok ref allocated ∧
    IO.FS.Handle.mk (tablePath ns.directory id) .writeNew allocated = .ok fd created ∧ out.Bound id fd inode created

private theorem returnedAt (p : Post a w ok bad) :
    Post a w (fun x t => a w = .ok x t ∧ ok x t) bad := by
  unfold Post at *
  cases run : a w <;> rw [run] at p
  · exact ⟨rfl,p⟩
  · exact p

/-- OS reports on the acquired output and its private cursor. On failure
the still-owned name is available to the native unlink handler. A failed
exclusive acquisition never enters that handler. -/
structure Primitives (ns : TableNamespace W) (durable : W → ns.inode → Option ByteArray)
    (P : W → Prop) (id : UInt64) (rows : Rows) (start : W) where
  out : Output ns
  allocate : P start →
    Post (Leaf.allocate rows).action start (fun ref t => P t ∧ out.cursor t ref rows) (fun _ => P)
  openFile : ∀ ref w, (Leaf.allocate rows).action start = .ok ref w → P w → out.cursor w ref rows →
    Post (IO.FS.Handle.mk (tablePath ns.directory id) .writeNew) w
      (fun fd t => ∃ inode, out.Held P id ref fd inode rows .empty false t) (fun _ => P)
  read : ∀ ref fd inode rs bytes w, out.Acquired id rows start ref fd inode → out.Held P id ref fd inode rs bytes false w →
    Post (Leaf.readRows ref).action w (fun got t => got = rs ∧ out.Held P id ref fd inode rs bytes false t)
      (fun _ => out.Owns P id fd inode)
  advance : ∀ ref fd inode row rs bytes w, out.Acquired id rows start ref fd inode → out.Held P id ref fd inode (row :: rs) bytes false w →
    Post (Leaf.advance ref rs).action w (fun _ => out.Held P id ref fd inode rs bytes false)
      (fun _ => out.Owns P id fd inode)
  write : ∀ ref fd inode rs bytes w, out.Acquired id rows start ref fd inode → out.Held P id ref fd inode rs bytes false w → ∀ packet,
    Post (fd.write packet) w (fun _ => out.Held P id ref fd inode rs (bytes ++ packet) false)
      (fun _ => out.Owns P id fd inode)
  flush : ∀ ref fd inode rs bytes w, out.Acquired id rows start ref fd inode → out.Held P id ref fd inode rs bytes false w →
    Post fd.flush w (fun _ => out.Held P id ref fd inode rs bytes true) (fun _ => out.Owns P id fd inode)
  sync : ∀ ref fd inode rs bytes w, out.Acquired id rows start ref fd inode → out.Held P id ref fd inode rs bytes true w →
    Post (syncFileHandle fd) w (fun _ t => P t ∧ out.Bound id fd inode t ∧
      ns.contents t inode = some bytes ∧ durable t inode = some bytes) (fun _ => out.Owns P id fd inode)
  remove : ∀ ref fd inode w, out.Acquired id rows start ref fd inode → out.Owns P id fd inode w →
    Post (IO.FS.removeFile (tablePath ns.directory id)) w (fun _ => P) (fun _ => P)

private def Matches (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows)
    (fd : IO.FS.Handle) (inode : ns.inode) (stage : Bool) (w : W) (file : ModelFile) : Prop :=
  ∃ rs, file.rows = rs.map (Entry.encode keyCodec mutationCodec) ∧ out.Held P id ref fd inode rs file.bytes stage w

private def Sim (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows) (fd : IO.FS.Handle)
    (inode : ns.inode) (p q : Bool) (a : Observed α) (model : ModelM α) : Prop :=
  ∀ w file, Matches out P id ref fd inode p w file → Safe a w
    (fun x t => ∃ after, model.run file = .ok (x,after) ∧ Matches out P id ref fd inode q t after)
    (fun _ => out.Owns P id fd inode) P

private def rules (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows) (fd : IO.FS.Handle)
    (inode : ns.inode) : BuilderRelation.Rules Observed ModelM IO.userError _root_.id where
  rel := Sim out P id ref fd inode
  ret _ _ file initial := .pure ⟨file,rfl,initial⟩
  seq first later w file initial := (first w file initial).bind fun x t ⟨mid,ran,held⟩ =>
    (later x t mid held).weaken (fun y u ⟨last,done,kept⟩ => ⟨last,by
      unfold StateT.run at ran; change (Except.bind _ _) = _; rw [ran]; exact done,kept⟩) (fun _ _ => _root_.id)
  raise _ _ _ initial := by
    obtain ⟨_,_,h⟩ := initial
    exact .fail ⟨h.1,h.2.1⟩
  abort _ _ _ w file initial := by
    obtain ⟨_,_,h⟩ := initial
    apply Safe.bind (mid := fun _ _ => False) (Safe.fail ⟨h.1,h.2.1⟩)
    exact fun _ _ => False.elim

variable {id : UInt64}

private theorem rows_sim (io : Primitives ns durable P id rows start) (ref : IO.Ref Rows) (fd : IO.FS.Handle) (inode : ns.inode)
    (acquired : io.out.Acquired id rows start ref fd inode) :
    Sim io.out P id ref fd inode false false (supply ref) modelNext := by
  intro w file ⟨rs,eq,held⟩
  unfold supply nextTableRow
  apply (Safe.leaf _ held.1 (io.read ref fd inode rs file.bytes w acquired held)).bind
  rintro obtained t ⟨rfl, read⟩
  cases obtained with
  | nil =>
    exact .pure ⟨file, by simp [StateT.run,modelNext,eq], [],eq,read⟩
  | cons row tail =>
    apply (Safe.leaf _ read.1 (io.advance ref fd inode row tail file.bytes t acquired read)).bind
    intro _ _ current
    exact .pure ⟨{file with rows := tail.map (Entry.encode keyCodec mutationCodec)},by simp [StateT.run,modelNext,eq],tail,rfl,current⟩

private theorem sinkAgreement (io : Primitives ns durable P id rows start) (ref : IO.Ref Rows) (fd : IO.FS.Handle) (inode : ns.inode)
    (acquired : io.out.Acquired id rows start ref fd inode) :
    BuilderRelation.SinkAgreement (rules io.out P id ref fd inode) (ops.sink fd) modelSink := by
  constructor
  · rintro bytes w file ⟨rs,eq,held⟩
    apply (Safe.leaf (.write fd bytes) held.1 (io.write ref fd inode rs file.bytes w acquired held bytes)).weaken
    · intro _ _ current; exact ⟨_,rfl,rs,eq,current⟩
    · exact fun _ _ => _root_.id
  · rintro w file ⟨rs,eq,held⟩
    apply (Safe.leaf (.flush fd) held.1 (io.flush ref fd inode rs file.bytes w acquired held)).weaken
    · intro _ _ current; exact ⟨file,rfl,rs,eq,current⟩
    · exact fun _ _ => _root_.id

private theorem stream (io : Primitives ns durable P id rows start) (ref : IO.Ref Rows) (fd : IO.FS.Handle) (inode : ns.inode)
    (acquired : io.out.Acquired id rows start ref fd inode) :
    Sim io.out P id ref fd inode false true
      (buildStream Alvoki.CRC32C.extend (tableLayout id) (ops.sink fd) (supply ref) IO.userError {})
      (buildStream Alvoki.CRC32C.extend (tableLayout id) modelSink modelNext _root_.id {}) := by
  apply BuilderRelation.stream (law := rules io.out P id ref fd inode)
  · exact sinkAgreement io ref fd inode acquired
  · exact rows_sim io ref fd inode acquired

private theorem writer (io : Primitives ns durable P id rows start) (ref : IO.Ref Rows) (fd : IO.FS.Handle) (inode : ns.inode)
    (acquired : io.out.Acquired id rows start ref fd inode) (held : io.out.Held P id ref fd inode rows .empty false w) :
    Safe (do
        let count ← buildStream Alvoki.CRC32C.extend (tableLayout id) (ops.sink fd) (supply ref) IO.userError {}
        ops.sync fd
        return count) w
      (fun n t => n = rows.length ∧ P t ∧ Prepared ns durable id rows t)
      (fun _ => io.out.Owns P id fd inode) P := by
  let input : ModelFile := ⟨rows.map (Entry.encode keyCodec mutationCodec),.empty⟩
  apply (stream io ref fd inode acquired w input ⟨rows,rfl,held⟩).bind
  rintro n t ⟨file,ran,rs,_,flushed⟩
  have model : modelBuild Alvoki.CRC32C.extend (tableLayout id) input.rows {} = .ok (n,file.bytes) := by
    unfold modelBuild
    change ((buildStream _ _ modelSink modelNext _root_.id {}).run input).bind _ = _
    rw [ran]
    rfl
  obtain ⟨count,image⟩ := modelBuild_ok model
  apply (Safe.leaf (.sync fd) flushed.1 (io.sync ref fd inode rs file.bytes t acquired flushed)).bind
  rintro _ u ⟨final,bound,live,durable⟩
  exact .pure ⟨by simpa [input] using count,final,inode,file.bytes,bound.1,live,durable,image⟩

/-- Exclusive creation, bounded row iteration, output flush, and inode fsync.
Success returns a physically prepared image; every returned failure or
actually reached primitive site retains the caller's protected resources. -/
theorem build (io : Primitives ns durable P id rows start) (entry : P start) :
    Post (Native.buildSynced (tablePath ns.directory id) id rows) start
      (fun _ t => P t ∧ Prepared ns durable id rows t) (fun _ => P) ∧
    ∀ leaf t, Visits (tablePath ns.directory id) id rows start leaf t → P t := by
  rw [← erase]
  change Safe (schedule (tablePath ns.directory id) id rows) start _ _ P
  unfold schedule
  apply (Safe.leaf _ entry (returnedAt (io.allocate entry))).bind
  rintro ref w ⟨issued,before,cursor⟩
  apply Safe.bind (mid := fun _ t => P t ∧ Prepared ns durable id rows t) _ (fun _ _ h => .pure h)
  unfold buildFileWith withFreshOutputWith
  apply (Safe.leaf (.openFile _ .writeNew) before (returnedAt (io.openFile ref w issued before cursor))).bind
  rintro fd u ⟨created,inode,held⟩
  have acquired : io.out.Acquired id rows start ref fd inode := ⟨w,u,issued,created,held.2.1⟩
  apply Safe.caught
  · exact (writer io ref fd inode acquired held).weaken (fun _ _ h => h.2) (fun _ _ => _root_.id)
  · intro e t failed
    apply Safe.bind (mid := fun _ t => P t) _ (fun _ _ h => .fail h)
    apply Safe.caught (Safe.leaf (.remove _) failed.1 (io.remove ref fd inode t acquired failed))
    exact fun _ _ h => .pure h


/-- Successful local reports from the primitives this invocation actually
visits. No return condition is placed on a whole build or on a future site. -/
def Reports (a : Observed α) (w : W) : Prop :=
  ∀ leaf t, a.visits w leaf t → ∃ x u, leaf.action t = .ok x u

abbrev Healthy (path : FilePath) (id : UInt64) (rows : Rows) (w : W) :=
  Reports (schedule path id rows) w

private theorem Reports.first (h : Reports (a >>= f) w) : Reports a w :=
  fun l t v => h l t (.inl v)

private theorem Reports.next (h : Reports (a >>= f) w) (ran : a.run w = .ok x u) : Reports (f x) u :=
  fun l t v => h l t (.inr ⟨x,u,ran,v⟩)

private theorem Reports.body (h : Reports (tryCatchThe IO.Error a f) w) : Reports a w :=
  fun l t v => h l t (.inl v)

private theorem Reports.leaf {leaf : Leaf} (h : Reports (issue leaf) w) : ∃ x u, leaf.action w = .ok x u :=
  h _ _ ⟨rfl,rfl⟩

private def Progress (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows) (fd : IO.FS.Handle)
    (inode : ns.inode) (p q : Bool) (a : Observed α) (b : ModelM α) : Prop :=
  ∀ w file, Matches out P id ref fd inode p w file → Reports a w →
    ∀ x result, b.run file = .ok (x,result) → ∃ t, a.run w = .ok x t ∧ Matches out P id ref fd inode q t result

private def progressRules (out : Output ns) (P : W → Prop) (id : UInt64) (ref : IO.Ref Rows) (fd : IO.FS.Handle)
    (inode : ns.inode) : BuilderRelation.Rules Observed ModelM IO.userError _root_.id where
  rel := Progress out P id ref fd inode
  ret _ w file init _ x result model := by cases model; exact ⟨w,rfl,init⟩
  seq := by
    intro α β p q r a b f g first next w file init reports x result model
    change (b.run file).bind _ = _ at model
    cases observed : b.run file with
    | error => simp [observed,Except.bind] at model
    | ok pair =>
      obtain ⟨y,mid⟩ := pair
      rw [observed] at model
      obtain ⟨v,ran,atMid⟩ := first w file init reports.first y mid observed
      obtain ⟨t,done,last⟩ := next y v mid atMid (reports.next ran) x result model
      exact ⟨t, by simpa only [Bind.bind,instMonadObserved,instMonadEIO._aux_13,EST.bind,ran] using done,last⟩
  raise _ _ _ _ _ _ _ model := by cases model
  abort _ _ _ _ _ _ _ _ _ model := by cases model

private theorem fromSuccess (safe : Sim out P id ref fd inode p q a b)
    (returns : ∀ w, Reports a w → ∃ x t, a.run w = .ok x t) :
    Progress out P id ref fd inode p q a b := by
  intro w file init healthy x after model
  obtain ⟨y,t,ran⟩ := returns w healthy
  have kept := (safe w file init).1
  rw [Post,ran] at kept
  obtain ⟨seen,agreement,held⟩ := kept
  rw [model] at agreement
  cases agreement
  exact ⟨_,ran,held⟩

private theorem boundOk {a : Observed α} {f : α → Observed β}
    (first : a.run w = .ok x t) (next : (f x).run t = .ok y u) : (a >>= f).run w = .ok y u := by
  simpa only [Bind.bind,instMonadObserved,instMonadEIO._aux_13,EST.bind,first] using next

private theorem supplyReturns (ref : IO.Ref Rows) (w : W) (reports : Reports (supply ref) w) :
    ∃ x t, (supply ref).run w = .ok x t := by
  unfold supply nextTableRow at reports ⊢
  obtain ⟨rs,t,read⟩ := reports.first.leaf
  have readAt : (issue (.readRows ref)).run w = .ok rs t := read
  have later := reports.next readAt
  cases rs with
  | nil => exact ⟨_,t,boundOk readAt rfl⟩
  | cons row xs =>
    obtain ⟨v,u,advance⟩ := later.first.leaf
    have ran : (issue (.advance ref xs)).run t = .ok v u := advance
    exact ⟨_,u,boundOk readAt (boundOk ran rfl)⟩

private theorem streamProgress (io : Primitives ns durable P id rows start) (ref : IO.Ref Rows) (fd : IO.FS.Handle)
    (inode : ns.inode) (acquired : io.out.Acquired id rows start ref fd inode) :
    Progress io.out P id ref fd inode false true
      (buildStream Alvoki.CRC32C.extend (tableLayout id) (ops.sink fd) (supply ref) IO.userError {})
      (buildStream Alvoki.CRC32C.extend (tableLayout id) modelSink modelNext _root_.id {}) := by
  have sink := sinkAgreement io ref fd inode acquired
  apply BuilderRelation.stream (law := progressRules io.out P id ref fd inode)
  · exact ⟨fun bytes => fromSuccess (sink.append bytes) (fun _ h => Reports.leaf (leaf := .write fd bytes) h),
      fromSuccess sink.flush (fun _ h => Reports.leaf (leaf := .flush fd) h)⟩
  · exact fromSuccess (rows_sim io ref fd inode acquired) (supplyReturns ref)

private theorem caughtOk {a : Observed α} {f : IO.Error → Observed α} (ran : a.run w = .ok x t) :
    (tryCatchThe IO.Error a f).run w = .ok x t := by
  change (tryCatchThe IO.Error a.run (fun e => (f e).run)) w = _
  simp only [tryCatchThe,MonadExceptOf.tryCatch,instMonadExceptOfEIO._aux_3,EST.tryCatch,ran]

/-- On any bounded input accepted by the pure format, positive reports from
the actual leaves force the native writer to succeed on its original fd. -/
theorem healthy (io : Primitives ns durable P id rows start) (entry : P start)
    (valid : modelBuild Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) {} = .ok (count,bytes))
    (reports : Healthy (tablePath ns.directory id) id rows start) :
    ∃ t, Native.buildSynced (tablePath ns.directory id) id rows start = .ok () t ∧ P t ∧ Prepared ns durable id rows t := by
  let path := tablePath ns.directory id
  change Reports (schedule path id rows) start at reports
  unfold schedule at reports
  obtain ⟨ref,w,allocated⟩ := reports.first.leaf
  have alloc : (issue (.allocate rows)).run start = .ok ref w := allocated
  have active := io.allocate entry
  rw [Post,allocated] at active
  have building := (reports.next alloc).first
  unfold buildFileWith withFreshOutputWith at building
  obtain ⟨fd,u,opened⟩ := building.first.leaf
  have created : (issue (.openFile path .writeNew)).run w = .ok fd u := opened
  have fresh := io.openFile ref w allocated active.1 active.2
  change IO.FS.Handle.mk path .writeNew w = .ok fd u at opened
  rw [Post,opened] at fresh
  obtain ⟨inode,held⟩ := fresh
  have acquired : io.out.Acquired id rows start ref fd inode := ⟨w,u,allocated,opened,held.2.1⟩
  have body := (building.next created).body
  let input : ModelFile := ⟨rows.map (Entry.encode keyCodec mutationCodec),.empty⟩
  let model := buildStream Alvoki.CRC32C.extend (tableLayout id) modelSink modelNext _root_.id {}
  change (model.run input).bind _ = _ at valid
  cases run : model.run input with
  | error e => simp [run,Except.bind] at valid
  | ok result =>
    obtain ⟨n,file⟩ := result
    obtain ⟨v,built,_⟩ := streamProgress io ref fd inode acquired u input ⟨rows,rfl,held⟩ body.first n file run
    have synching := body.next built
    obtain ⟨value,t,synced⟩ := synching.first.leaf
    have sync : (issue (.sync fd)).run v = .ok value t := synced
    have actual : (schedule path id rows).run start = .ok () t := by
      unfold schedule buildFileWith withFreshOutputWith
      exact boundOk alloc (boundOk (boundOk created (caughtOk (boundOk built (boundOk sync rfl)))) rfl)
    rw [erase] at actual
    have safe := (build io entry).1
    rw [Post,actual] at safe
    exact ⟨_,actual,safe⟩

end ExperimentalL0.NativeTableWriter
