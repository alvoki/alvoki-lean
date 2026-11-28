import Alvoki.Experiments.L0.NativeTableCheck

namespace ExperimentalL0.NativeRead
open ImmutableSSTable Unified

private abbrev RefM := EStateM String Unit
private def bounded (bytes : ByteArray) : Source RefM :=
  ⟨pure bytes.size, fun o n => if n ≤ maxRowSize ∧ o + n ≤ bytes.size then pure (bytes.extract o (o+n))
    else throw "outside checked table extent"⟩

private def Progress (P : W → Prop) (a : EIO String α) (b : RefM β) (rel : α → β → Prop) : Prop :=
  ∀ y, b () = .ok y () → ∀ w, P w → ∃ x t, a w = .ok x t ∧ P t ∧ rel x y

private def progressRules (P : W → Prop) : ReaderRelation.Rules where
  Rel := Progress P
  bind := by
    intro α β γ δ a b f g rel out first next y done w held
    cases ran : b () with
    | error e t => simp [Bind.bind,EStateM.bind,ran] at done
    | ok x t =>
      cases t
      simp only [Bind.bind,EStateM.bind,ran] at done
      obtain ⟨z,u,h,kept,same⟩ := first _ ran _ held
      obtain ⟨v,t,h',kept',same'⟩ := next _ _ same _ done _ kept
      exact ⟨v,t,by simp [Bind.bind,instMonadEIO._aux_13,EST.bind,h,h'],kept',same'⟩
  pure := by
    intro α β rel x y related z done w held
    cases done
    exact ⟨x,w,rfl,held,related⟩
  throw := by
    intro α β rel e y impossible
    contradiction

private theorem HealthyChecks.lookupSource {ns : TableNamespace W} {life : Lifetime} {P : W → Prop}
    {prim : Primitives ns life P} {bytes : ByteArray} {id : UInt64} (ok : HealthyChecks prim ids)
    (built : Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (h inode) (key : UInt64) (w) (held : P w ∧ life.privateBorrow h w ∧ prim.inodeOf h w = some inode ∧
      ns.contents w inode = some bytes) :
    ∃ t, withTableSource (handleSource h) id (·.lookup key) w = .ok (lookupRows rows key) t ∧ P t := by
  let Q := fun t => P t ∧ life.privateBorrow h t ∧ prim.inodeOf h t = some inode ∧ ns.contents t inode = some bytes
  have available := ok.available built.extent h inode
  have steps : ReaderRelation.SourceSteps (progressRules Q) (handleSource h) (bounded bytes) := by
    constructor
    · intro y eq t current
      cases eq
      obtain ⟨u,ran,next⟩ := available.size t current
      exact ⟨_,u,ran,next,rfl⟩
    · intro o n y eq t current
      change (if _ then _ else _ : RefM ByteArray) () = _ at eq
      split at eq
      next fits =>
        cases eq
        obtain ⟨u,ran,next⟩ := available.read o n fits.1 fits.2 t current
        exact ⟨_,u,ran,next,rfl⟩
      next => contradiction
  have served : (bounded bytes).Serves bytes :=
    ⟨rfl,fun o n fits within => by simp [bounded, fits, within]⟩
  obtain ⟨table, rep, opened⟩ := withTableSource_built built served
  have reference : withTableSource (bounded bytes) id (·.lookup key) = pure (lookupRows rows key) := by
    rw [opened, typed_lookup_spec rep]
  have relation := ReaderRelation.typedLookup (crc := Alvoki.CRC32C.extend) (tableId := id)
    (progressRules Q) steps keyCodec mutationCodec key
  letI := lawfulEIO
  simp only [withTableSource,openTableChecked,bind_assoc,pure_bind] at reference ⊢
  obtain ⟨x,t,ran,frame,rfl⟩ := relation (lookupRows rows key) (congrFun reference ()) w held
  exact ⟨t,ran,frame.1⟩

theorem HealthyChecks.lookup {ns : TableNamespace W} {life : Lifetime} {P : W → Prop}
    {prim : Primitives ns life P} (ok : HealthyChecks prim ids) (id : UInt64) (member : id ∈ ids)
    (catalog : ∀ t, P t → ns.Bound t id rows) (key : UInt64) (w) (held : P w) :
    ∃ t, (nativeTableAt ns.directory id (·.lookup key)).run w = .ok (.ok (lookupRows rows key)) t ∧ P t := by
  obtain ⟨md,t,stat,regular⟩ := ok.stat id member w held
  have afterStat := prim.stat (tablePath ns.directory id) w held
  rw [stat] at afterStat
  obtain ⟨inode,bytes,named,stored,built⟩ := catalog t afterStat.1
  obtain ⟨h,u,opened⟩ := ok.acquire id member t afterStat.1
  have borrowed := prim.openRead _ _ _ _ afterStat.1 named stored
  rw [opened] at borrowed
  obtain ⟨v,looked,frame⟩ := ok.lookupSource built h inode key u borrowed
  refine ⟨v,?_,frame⟩
  rw [nativeTableAt_acquired stat regular opened]
  change (BaseIO.toEIO (withTableSource (handleSource h) id (·.lookup key)).toBaseIO) u = _
  simp [EIO.toBaseIO, BaseIO.toEIO, looked]

end ExperimentalL0.NativeRead
