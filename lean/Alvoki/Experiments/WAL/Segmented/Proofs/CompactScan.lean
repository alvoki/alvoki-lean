import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.WAL.Proofs.BoundedRead
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented.Native

/-- The disk, ready state and owned resources can all be included in `σ`.
Only a successful scan contributes a history observation to the client trace. -/
def ReadOutcome (healthy : Prop) (before : σ) (value : α) : EStateM.Result ε σ α → Prop
  | .ok seen after => seen = value ∧ after = before
  | .error _ after => after = before ∧ ¬healthy

private theorem ReadOutcome.bind
    {a : EStateM ε σ α} {k : α → EStateM ε σ β} {before : σ} {value : α} {expected : β}
    (source : ReadOutcome healthy before value (a before))
    (rest : ReadOutcome healthy before expected (k value before)) :
    ReadOutcome healthy before expected ((a >>= k) before) := by
  cases ran : a before with
  | error error after =>
    simpa [Bind.bind, EStateM.bind, ran, ReadOutcome] using source
  | ok seen after =>
    have same : seen = value ∧ after = before := by simpa [ran, ReadOutcome] using source
    obtain ⟨rfl, rfl⟩ := same
    simpa [Bind.bind, EStateM.bind, ran] using rest

theorem foldSealedWith_read
    (read : Nat → α → EStateM ε σ α) (expected : Nat → α → α)
    (before : σ) (healthy : Prop) (first count : Nat) (seed : α)
    (reads : ∀ id, first ≤ id → id < first + count → ∀ acc,
      ReadOutcome healthy before (expected id acc) (read id acc before)) :
    ReadOutcome healthy before (foldSealedWith (m := Id) expected first count seed)
      (foldSealedWith read first count seed before) := by
  induction count generalizing first seed with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    exact ReadOutcome.bind (reads first (by omega) (by omega) seed)
      (ih (first + 1) (expected first seed) (fun id lo hi acc => reads id (by omega) (by omega) acc))

/-- Composition for the shared scan schedule. Its primitive premises account
for scoped acquisition/close and exact bytes. Healthy progress is conditional
on the reads at this installed snapshot, independently of error framing. -/
theorem scanReadyWith_read
    (session : CompactSession) (seed : α) (readSealed : Nat → α → EStateM ε σ α)
    (readActive : α → EStateM ε σ α) (sealed : Nat → α → α) (active : α → α)
    (before : σ) (healthy : Prop)
    (sealedReads : ∀ id, session.control.firstNeeded ≤ id → id < session.control.active → ∀ acc,
      ReadOutcome healthy before (sealed id acc) (readSealed id acc before))
    (activeRead : ∀ acc, ReadOutcome healthy before (active acc) (readActive acc before)) :
    ReadOutcome healthy before (scanReadyWith (m := Id) session seed sealed active)
      (scanReadyWith session seed readSealed readActive before) := by
  have first := Nat.min_le_left session.control.active (session.control.discarded / session.control.capacity)
  have span : session.control.firstNeeded + (session.control.active - session.control.firstNeeded) =
      session.control.active := by unfold Control.firstNeeded; omega
  apply ReadOutcome.bind (foldSealedWith_read readSealed sealed before healthy _ _ _
    (fun id lo hi acc => sealedReads id lo (by rwa [span] at hi) acc))
  exact ReadOutcome.bind (activeRead _) ⟨rfl, rfl⟩

theorem ReadOutcome.healthy
    {result : EStateM.Result ε σ α} (h : ReadOutcome available before expected result)
    (progress : available) : result = .ok expected before := by
  cases result with
  | error _ _ => exact False.elim (h.2 progress)
  | ok _ _ => obtain ⟨rfl, rfl⟩ := h; rfl

open SingleFile (foldBatchesFrom foldBatches)

private theorem fold_append (step : α → Nat → Bytes → α) (base : Nat) (seed : α)
    (left right : List Bytes) :
    foldBatchesFrom step base seed (left ++ right) =
      foldBatchesFrom step (base + left.length) (foldBatchesFrom step base seed left) right := by
  induction left generalizing base seed with
  | nil => simp [foldBatchesFrom]
  | cons batch rest ih =>
    simp only [List.cons_append, foldBatchesFrom, List.length_cons, ih]
    congr 1
    omega

private theorem fold_offset (step : α → Nat → Bytes → α) (offset base : Nat)
    (seed : α) (batches : List Bytes) :
    foldBatchesFrom (fun acc pos batch => step acc (offset + pos) batch) base seed batches =
      foldBatchesFrom step (offset + base) seed batches := by
  induction batches generalizing base seed with
  | nil => rfl
  | cons batch rest ih => rw [foldBatchesFrom, foldBatchesFrom, ih, Nat.add_assoc]

private def after (cut : Nat) (step : α → Nat → Bytes → α) (acc : α)
    (position : Nat) (batch : Bytes) : α :=
  if cut < position then step acc position batch else acc

def foldChild (c : Control) (history : List Bytes) (step : α → Nat → Bytes → α)
    (id : Nat) (seed : α) : α :=
  foldBatches (segmentHistory c.capacity id history) seed (retainedStep c id step)

private theorem foldChild_eq (c : Control) (history : List Bytes)
    (step : α → Nat → Bytes → α) (id : Nat) (seed : α) :
    foldChild c history step id seed = foldBatchesFrom (after c.discarded step)
      (id * c.capacity) seed (segmentHistory c.capacity id history) := by
  have stepEq : retainedStep c id step = fun acc pos batch =>
      after c.discarded step acc (id * c.capacity + pos) batch := by
    funext acc pos batch
    rfl
  rw [foldChild, foldBatches, stepEq, fold_offset, Nat.add_zero]

private theorem fold_window (c : Control) (history : List Bytes)
    (step : α → Nat → Bytes → α) (first count : Nat) (seed : α)
    (full : (first + count) * c.capacity ≤ history.length) :
    foldSealedWith (m := Id) (foldChild c history step) first count seed =
      foldBatchesFrom (after c.discarded step) (first * c.capacity) seed
        (segmentWindow c.capacity first count history) := by
  induction count generalizing first seed with
  | zero => rfl
  | succ n ih =>
    have enough : (first + 1) * c.capacity ≤ history.length :=
      Nat.le_trans (Nat.mul_le_mul_right c.capacity (by omega)) full
    have rest : (first + 1 + n) * c.capacity ≤ history.length := by
      rwa [show first + 1 + n = first + (n + 1) by omega]
    change foldSealedWith (m := Id) (foldChild c history step) (first + 1) n
      (foldChild c history step first seed) = _
    rw [ih _ _ rest, segmentWindow, fold_append, segmentHistory_full enough,
      foldChild_eq, Nat.add_mul, Nat.one_mul]

private theorem fold_drop (cut base : Nat) (step : α → Nat → Bytes → α)
    (seed : α) (batches : List Bytes) :
    foldBatchesFrom (after cut step) base seed batches =
      foldBatchesFrom step (max cut base) seed (batches.drop (cut - base)) := by
  induction batches generalizing base seed with
  | nil => simp [foldBatchesFrom]
  | cons batch rest ih =>
    rw [foldBatchesFrom, ih]
    by_cases includeBatch : cut < base + 1
    · have leBase : cut ≤ base := by omega
      simp [after, includeBatch, Nat.max_eq_right leBase, Nat.sub_eq_zero_of_le leBase,
        Nat.max_eq_right (by omega : cut ≤ base + 1), Nat.sub_eq_zero_of_le (by omega : cut ≤ base + 1),
        foldBatchesFrom]
    · have advance : cut - base = (cut - (base + 1)) + 1 := by omega
      simp [after, includeBatch, advance, Nat.max_eq_left (by omega : base ≤ cut),
        Nat.max_eq_left (by omega : base + 1 ≤ cut)]

/-- Compose the native schedule's pure result over the exact selected child
histories. The consumer sees precisely the retained suffix with absolute IDs. -/
theorem scanReadyWith_selected (session : CompactSession) (history : List Bytes)
    (seed : α) (step : α → Nat → Bytes → α)
    (lower : session.control.active * session.control.capacity ≤ history.length)
    (upper : history.length ≤ (session.control.active + 1) * session.control.capacity) :
    scanReadyWith (m := Id) session seed (foldChild session.control history step)
      (foldChild session.control history step session.control.active) =
        (session.bounds, foldBatchesFrom step session.control.discarded seed
          (history.drop session.control.discarded)) := by
  let c := session.control
  change c.active * c.capacity ≤ history.length at lower
  change history.length ≤ (c.active + 1) * c.capacity at upper
  have first : c.firstNeeded ≤ c.active := Nat.min_le_left ..
  have exactSpan : c.firstNeeded + (c.active - c.firstNeeded) = c.active := by omega
  have fullSpan : (c.firstNeeded + (c.active - c.firstNeeded)) * c.capacity ≤ history.length := by
    rwa [exactSpan]
  have width : (segmentWindow c.capacity c.firstNeeded (c.active - c.firstNeeded) history).length =
      (c.active - c.firstNeeded) * c.capacity := by
    rw [segmentWindow_eq, List.length_take, List.length_drop, Nat.min_eq_left]
    have sum : c.firstNeeded * c.capacity + (c.active - c.firstNeeded) * c.capacity =
        c.active * c.capacity := by rw [← Nat.add_mul, exactSpan]
    omega
  have join : c.firstNeeded * c.capacity + (c.active - c.firstNeeded) * c.capacity =
      c.active * c.capacity := by rw [← Nat.add_mul, exactSpan]
  have retained : c.firstNeeded * c.capacity ≤ c.discarded :=
    Nat.le_trans (Nat.mul_le_mul_right c.capacity (Nat.min_le_right ..)) (Nat.div_mul_le_self ..)
  change (session.bounds, foldChild c history step c.active
      (foldSealedWith (m := Id) (foldChild c history step) c.firstNeeded
        (c.active - c.firstNeeded) seed)) = _
  rw [fold_window _ _ _ _ _ _ fullSpan, foldChild_eq]
  rw [← join, ← width, ← fold_append, fold_drop,
    Nat.max_eq_left retained, selectedHistory_eq c history upper]

theorem compactBounds_eq {session : Session} {disk : Model.Disk}
    (ready : Installed session disk) :
    (⟨session.control, session.activeCount⟩ : CompactSession).bounds =
      ⟨session.view.base, session.view.tail⟩ := by
  obtain ⟨history, shape, ready, _, _⟩ := ready
  have lower := ready.layout.lower
  have covered := ready.layout.discardedFits
  have count := segmentHistory_active_length (active := session.control.active) ready.layout.upper
  rw [shape]
  simp only [CompactSession.bounds, sessionOf]
  rw [historyView_tail covered, count]
  simp only [historyView]
  congr 1
  omega

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open SingleFile Persistence

/-- The descriptor read is local to the installed cursor. Decode and the
cursor check are derived by executing the native active-scan worker. -/
theorem activeScanWith_read (read : Nat → EStateM String σ Bytes)
    (before : σ) (healthy : Prop) (batches : List Bytes)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255)
    (seed : α) (step : α → Nat → Bytes → α)
    (data : ReadOutcome healthy before (encodeFrames 1 batches)
      (read (historyCursor batches).endPos before)) :
    ReadOutcome healthy before (foldBatches batches seed step)
      (activeScanWith read (historyCursor batches) seed step before) := by
  unfold activeScanWith
  apply ReadOutcome.bind data
  have decoded := scan_encodeFrames .boundary bounded fits
  simp [historyCursor, decoded, fromDecode, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    ReadOutcome]

private theorem scanMarker_read (read : OpenTarget → EStateM String σ Bytes)
    (before : σ) (healthy : Prop) (policy : Policy) (image : Image) (marker : Marker)
    (selected : policy = .boundary →
      selectMarker image.slot0.live image.slot1.live = .ok marker)
    (zero : ReadOutcome healthy before (image.slot0.live.take (markerSize + 1)) (read .marker0 before))
    (one : ReadOutcome healthy before (image.slot1.live.take (markerSize + 1)) (read .marker1 before)) :
    ReadOutcome healthy before (if policy == .boundary then some marker else none)
      (scanMarkerWith read policy before) := by
  cases policy with
  | logOnly => exact ⟨rfl, rfl⟩
  | boundary =>
    simp only [scanMarkerWith, show (Policy.boundary == .boundary) = true by rfl, ↓reduceIte]
    apply ReadOutcome.bind zero
    apply ReadOutcome.bind one
    have picked : selectMarker (image.slot0.live.take (markerSize + 1))
        (image.slot1.live.take (markerSize + 1)) = .ok marker := by
      simpa only [selectMarker, boundedMarker_decode] using selected rfl
    simp [picked, fromDecode, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ReadOutcome]

/-- The child result follows from three scoped file observations and the
settled image. This boundary does not assume a whole-child read result. -/
theorem sealedScanWith_reads (read : OpenTarget → EStateM String σ Bytes)
    (before : σ) (healthy : Prop) (policy : Policy) (image : Image) (batches : List Bytes)
    (settled : Child.Settled policy image batches)
    (bounded : ∀ b ∈ batches, b.length ≤ 32) (fits : batches.length ≤ 255)
    (seed : α) (step : α → Nat → Bytes → α)
    (zero : ReadOutcome healthy before (image.slot0.live.take (markerSize + 1)) (read .marker0 before))
    (one : ReadOutcome healthy before (image.slot1.live.take (markerSize + 1)) (read .marker1 before))
    (data : ReadOutcome healthy before (image.data.live.take 65536) (read .reader before)) :
    ReadOutcome healthy before (foldBatches batches seed step)
      (sealedScanWith read policy batches.length seed step before) := by
  have canonical := congrArg FileImage.live settled.ready.1.1
  have size := encoded_history_size batches 1 bounded
  have dataFits : (encodeFrames 1 batches).length ≤ 65536 := by omega
  rw [canonical, List.take_of_length_le dataFits] at data
  let marker : Marker := ⟨(encodeFrames 1 batches).length, batches.length⟩
  have selected (boundary : policy = .boundary) :
      selectMarker image.slot0.live image.slot1.live = .ok marker := by
    have slot0 := congrArg (fun i : Image => i.slot0.live) settled.clean
    have slot1 := congrArg (fun i : Image => i.slot1.live) settled.clean
    change image.slot0.durable = image.slot0.live at slot0
    change image.slot1.durable = image.slot1.live at slot1
    rw [← slot0, ← slot1]
    exact (settled.ready.2 boundary).selectDurable bounded fits
  unfold sealedScanWith
  apply ReadOutcome.bind (scanMarker_read read before healthy policy image marker selected zero one)
  apply ReadOutcome.bind data
  have decoded := scan_encodeFrames .boundary bounded fits
  have logOnly : (Policy.logOnly == .boundary) = false := rfl
  have boundary : (Policy.boundary == .boundary) = true := rfl
  cases policy <;>
    simp [logOnly, boundary, marker, decoded, fromDecode, Bind.bind, EStateM.bind, Pure.pure,
      EStateM.pure, ReadOutcome, Nat.add_comm]

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open SingleFile Persistence

/-- From a ready snapshot, local marker, data, and positional read reports
suffice for an exact retained observation. A scope report accounts for
acquisition and release of only its named descriptor. -/
theorem scanReadyWith_fileReads
    (session : CompactSession) (history : List Bytes) (disk : Model.Disk)
    (installed : ReadyLayout session.control history disk)
    (before : σ) (healthy : Prop) (seed : α) (step : α → Nat → Bytes → α)
    (sealed : Nat → OpenTarget → EStateM String σ Bytes)
    (active : Nat → EStateM String σ Bytes)
    (zero : ∀ id, session.control.selects id → id < session.control.active →
      ReadOutcome healthy before ((disk.segment id).slot0.live.take (markerSize + 1))
        (sealed id .marker0 before))
    (one : ∀ id, session.control.selects id → id < session.control.active →
      ReadOutcome healthy before ((disk.segment id).slot1.live.take (markerSize + 1))
        (sealed id .marker1 before))
    (data : ∀ id, session.control.selects id → id < session.control.active →
      ReadOutcome healthy before ((disk.segment id).data.live.take 65536)
        (sealed id .reader before))
    (positioned : ReadOutcome healthy before
      ((disk.segment session.control.active).data.live)
      (active (disk.cursor session.control.active).endPos before)) :
    ReadOutcome healthy before (session.bounds, foldBatchesFrom step session.control.discarded seed
      (history.drop session.control.discarded))
      (scanReadyWith session seed
        (fun id acc => sealedScanWith (sealed id) session.control.policy session.control.capacity acc
          (retainedStep session.control id step))
        (fun acc => activeScanWith active (disk.cursor session.control.active) acc
          (retainedStep session.control session.control.active step)) before) := by
  let c := session.control
  rw [← scanReadyWith_selected session history seed step installed.layout.lower installed.layout.upper]
  apply scanReadyWith_read
  · intro id lo hi acc
    have chosen : c.selects id := ⟨lo, Nat.le_of_lt hi⟩
    have full : (segmentHistory c.capacity id history).length = c.capacity :=
      segmentHistory_full (Nat.le_trans (Nat.mul_le_mul_right c.capacity (by omega)) installed.layout.lower)
    have fits : (segmentHistory c.capacity id history).length ≤ 255 := by
      rw [full]
      exact installed.layout.capacityFits
    have leaf := sealedScanWith_reads (sealed id) before healthy c.policy (disk.segment id)
      (segmentHistory c.capacity id history) (installed.layout.sealed id chosen hi)
      (segmentHistory_bounded installed.layout id) fits acc (retainedStep c id step)
      (zero id chosen hi) (one id chosen hi) (data id chosen hi)
    rw [full] at leaf
    simpa only [foldChild] using leaf
  · intro acc
    have same := congrArg FileImage.live installed.active.ready.1.1
    rw [installed.active.position, same] at positioned
    rw [installed.active.position]
    exact activeScanWith_read active before healthy _ (segmentHistory_bounded installed.layout c.active)
      (Nat.le_trans (segmentHistory_fits c.capacity c.active history) installed.layout.capacityFits)
      acc (retainedStep c c.active step) positioned

end WalRecoverySlice.Segmented.Native
