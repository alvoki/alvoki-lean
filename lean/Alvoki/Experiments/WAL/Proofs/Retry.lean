import Alvoki.Experiments.WAL.Proofs.Persistence
import Alvoki.Experiments.WAL.Proofs.ScanRepair

namespace WalRecoverySlice.Persistence

def ReopenSelection (policy : Policy) (b : Image) (marker : Option Marker) (d : Decoded) : Prop :=
  match policy, marker with
  | .logOnly, none => scan b.data.live b.data.live.length .logOnly = .ok d
  | .boundary, some m =>
    selectMarker b.slot0.live b.slot1.live = .ok m ∧
    scan b.data.live m.endPos .boundary = .ok d ∧ d.cursor.nextSeq = m.lastSeq + 1
  | _, _ => False

private def Image.settleSlot (b : Image) (slot : Nat) : Image :=
  b.withMarker slot ⟨(b.marker slot).live, (b.marker slot).live⟩

def Image.selectedSync (b : Image) : Option Marker → Image
  | none => b
  | some m => b.settleSlot (m.lastSeq % 2)

def Image.bothSynced (b : Image) : Option Marker → Image
  | none => b
  | some m => (b.selectedSync (some m)).settleSlot (1 - m.lastSeq % 2)

def Image.trimmed (b : Image) (d : Decoded) : Image :=
  { b with data.live := b.data.live.take d.cursor.endPos }

def Image.dataSettled (b : Image) : Image :=
  { b with data.durable := b.data.live }

private def stopped (a : Abort) (b : Image) : Result Decoded :=
  match a with
  | .error => .ok (.error "primitive I/O error") b
  | .interrupted => .error () b

private def barrier (effect : Primitive) (b : Image) (slot : Nat) (next : Image → Result Decoded) :
    Result Decoded :=
  match effect with
  | .before a => stopped a b
  | .after (some a) => stopped a (b.settleSlot slot)
  | .after none => next (b.settleSlot slot)

private def finish (effects : Effects) (d : Decoded) (trim : Bool) : M Decoded := do
  if trim then (ops effects).truncate d.cursor.endPos
  (ops effects).syncData
  return d

private def Allowed (S : Image → Prop) (d : Decoded) (final : Image) (out : Result Decoded) :=
  S (reached out) ∧ ∀ returned, acknowledged out = some returned → returned = d ∧ reached out = final

private theorem stopped_allowed {S : Image → Prop} {b : Image} (hb : S b)
    (d : Decoded) (final : Image) (a : Abort) : Allowed S d final (stopped a b) := by
  cases a <;> exact ⟨hb, by simp [stopped, acknowledged]⟩

private theorem read_error_allowed {S : Image → Prop} {b : Image} (hb : S b)
    (d : Decoded) (final : Image) (e : String) : Allowed S d final (.ok (.error e) b) :=
  ⟨hb, by simp [acknowledged]⟩

private theorem barrier_allowed {S : Image → Prop} {b : Image} {slot : Nat}
    {d : Decoded} {final : Image} {next : Image → Result Decoded}
    (eff : Primitive) (old : S b) (new : S (b.settleSlot slot))
    (cont : Allowed S d final (next (b.settleSlot slot))) :
    Allowed S d final (barrier eff b slot next) := by
  cases eff with
  | before a => exact stopped_allowed old _ _ _
  | after abort => cases abort with
    | none => exact cont
    | some a => exact stopped_allowed new _ _ _

private theorem primitive_cases (p : Primitive) :
    p = .before .error ∨ p = .before .interrupted ∨ p = .after (some .error) ∨
    p = .after (some .interrupted) ∨ p = .after none := by
  cases p with
  | before a => cases a <;> simp
  | after a => cases a with
    | none => simp
    | some a => cases a <;> simp

private theorem finish_allowed (effects : Effects) (d : Decoded) (b : Image)
    {S : Image → Prop} (orig : S b) (trunc : S (b.trimmed d)) (done : S (b.trimmed d).dataSettled) :
    Allowed S d (b.trimmed d).dataSettled
      ((finish effects d (decide (d.cursor.endPos < b.data.live.length))).run b) := by
  by_cases trim : d.cursor.endPos < b.data.live.length
  · rcases primitive_cases effects.truncate with t | t | t | t | t <;>
      rcases primitive_cases effects.dataSync with s | s | s | s | s <;>
      simp [finish, ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, Primitive.syncResult, Abort.result,
        Allowed, reached, acknowledged, trim, t, s, Image.trimmed, Image.dataSettled] at *
    all_goals assumption
  · have same : b.trimmed d = b := by
      simp [Image.trimmed, List.take_of_length_le (Nat.le_of_not_gt trim)]
    rw [same] at done ⊢
    rcases primitive_cases effects.dataSync with s | s | s | s | s <;>
      simp [finish, ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
        EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, Primitive.syncResult, Abort.result,
        Allowed, reached, acknowledged, trim, s, Image.dataSettled] at *
    all_goals assumption

private theorem reopen_log (fx : Effects) (b : Image) :
    (reopen (ops fx) .logOnly).run b =
      if fx.readDataError then .ok (.error "data read error") b
      else match scan b.data.live b.data.live.length .logOnly with
      | .error e => .ok (.error e) b
      | .ok d => (finish fx d (decide (d.cursor.endPos < b.data.live.length))).run b := by
  have branch : (Policy.logOnly == .boundary) = false := rfl
  cases r : fx.readDataError <;> cases sc : scan b.data.live b.data.live.length .logOnly <;>
    simp [reopen, finish, ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, r, branch, sc] <;> rfl

private theorem reopen_marked (fx : Effects) (b : Image) :
    (reopen (ops fx) .boundary).run b =
      if fx.readMarkerError == some 0 || fx.readMarkerError == some 1 then
        .ok (.error "marker read error") b
      else match selectMarker b.slot0.live b.slot1.live with
      | .error e => .ok (.error e) b
      | .ok m =>
        if fx.readDataError then .ok (.error "data read error") b
        else match scan b.data.live m.endPos .boundary with
        | .error e => .ok (.error e) b
        | .ok d =>
          if d.cursor.nextSeq != m.lastSeq + 1 then .ok (.error "marker sequence mismatch") b
          else
            let slot := m.lastSeq % 2
            barrier (fx.markerSync slot) b slot fun selected =>
              barrier (fx.markerSync (1 - slot)) selected (1 - slot) fun synced =>
                (finish fx d (decide (d.cursor.endPos < b.data.live.length))).run synced := by
  have branch : (Policy.boundary == .boundary) = true := rfl
  unfold reopen
  by_cases m0 : fx.readMarkerError = some 0 <;>
    simp [ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, branch, m0] <;> try rfl
  by_cases m1 : fx.readMarkerError = some 1 <;> simp [m1, EStateM.pure] <;> try rfl
  cases picked : selectMarker b.slot0.live b.slot1.live with
  | error e => rfl
  | ok m =>
    cases read : fx.readDataError <;> simp [ExceptT.bindCont, EStateM.bind, EStateM.pure] <;> try rfl
    cases scanned : scan b.data.live m.endPos .boundary with
    | error e => rfl
    | ok d =>
      by_cases ord : d.cursor.nextSeq = m.lastSeq + 1 <;>
        simp [ord, ExceptT.bindCont, EStateM.bind, EStateM.pure] <;> try rfl
      rcases primitive_cases (fx.markerSync (m.lastSeq % 2)) with t | t | t | t | t <;>
        simp [t, barrier, stopped, Image.settleSlot, Primitive.syncResult, Abort.result] <;> try rfl
      rcases primitive_cases (fx.markerSync (1 - m.lastSeq % 2)) with u | u | u | u | u <;>
        simp [u, Primitive.syncResult, Abort.result, finish, ops, Bind.bind,
          ExceptT.bind, ExceptT.bindCont, EStateM.bind, ExceptT.mk, Pure.pure,
          ExceptT.pure, EStateM.pure] <;> rfl

private theorem data_after_markers (b : Image) (m : Option Marker) :
    (b.bothSynced m).data = b.data := by
  cases m <;> simp [Image.bothSynced, Image.selectedSync, Image.settleSlot, Image.data_updatedMarker]

/-- The only images reached by the actual recovery program, including errors
after a barrier took effect and interruptions before an API response. -/
theorem reopen_cuts (effects : Effects) {policy : Policy} {b : Image} {marker : Option Marker} {d : Decoded}
    (selected : ReopenSelection policy b marker d) :
    let b1 := b.selectedSync marker
    let b2 := b.bothSynced marker
    let b3 := b2.trimmed d
    let b4 := b3.dataSettled
    let out := (reopen (ops effects) policy).run b
    (reached out = b ∨ reached out = b1 ∨ reached out = b2 ∨ reached out = b3 ∨ reached out = b4) ∧
      ∀ returned, acknowledged out = some returned → returned = d ∧ reached out = b4 := by
  intro b1 b2 b3 b4 out
  let S := fun (x : Image) => x = b ∨ x = b1 ∨ x = b2 ∨ x = b3 ∨ x = b4
  change Allowed S d b4 out
  have at0 : S b := .inl rfl
  have at1 : S b1 := .inr (.inl rfl)
  have at2 : S b2 := .inr (.inr (.inl rfl))
  have at3 : S b3 := .inr (.inr (.inr (.inl rfl)))
  have at4 : S b4 := .inr (.inr (.inr (.inr rfl)))
  have tail := finish_allowed effects d b2 at2 at3 at4
  dsimp only [out]
  cases policy <;> cases marker <;> try contradiction
  case logOnly.none =>
    rw [reopen_log]
    change scan _ _ _ = _ at selected
    rw [selected]
    cases effects.readDataError
    · exact tail
    · exact read_error_allowed at0 _ _ _
  case boundary.some m =>
    obtain ⟨picked, scanned, ord⟩ := selected
    rw [reopen_marked]
    simp [picked, scanned, ord]
    split <;> try exact read_error_allowed at0 _ _ _
    split <;> try exact read_error_allowed at0 _ _ _
    apply barrier_allowed _ at0 at1
    apply barrier_allowed _ at1 at2
    have same : (b.bothSynced (some m)).data = b.data := data_after_markers _ _
    rw [← same]
    exact tail

private theorem finish_success (b : Image) (d : Decoded) :
    (finish healthyReopen d (decide (d.cursor.endPos < b.data.live.length))).run b =
      .ok (.ok d) (b.trimmed d).dataSettled := by
  by_cases trim : d.cursor.endPos < b.data.live.length
  · simp [trim, finish, Image.trimmed, Image.dataSettled, healthyReopen, ops, Bind.bind,
      ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind, Pure.pure, ExceptT.pure,
      EStateM.pure, Primitive.syncResult]
  · simp [trim, finish, Image.trimmed, Image.dataSettled, List.take_of_length_le (Nat.le_of_not_gt trim),
      healthyReopen, ops, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
      EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, Primitive.syncResult]

theorem reopen_selected_healthy {policy : Policy} {b : Image} {marker : Option Marker} {d : Decoded}
    (selected : ReopenSelection policy b marker d) :
    (reopen (ops healthyReopen) policy).run b = .ok (.ok d) ((b.bothSynced marker).trimmed d).dataSettled := by
  cases policy <;> cases marker <;> try contradiction
  case logOnly.none =>
    rw [reopen_log]
    change scan _ _ _ = _ at selected
    rw [selected]
    exact finish_success _ _
  case boundary.some m =>
    obtain ⟨picked, scanned, ord⟩ := selected
    rw [reopen_marked]
    simp [picked, scanned, ord, healthyReopen, barrier]
    change (finish healthyReopen d _).run (b.bothSynced (some m)) = _
    rw [← data_after_markers b (some m)]
    exact finish_success _ _

theorem healthy_reopen_selection {policy : Policy} {b : Image} {d : Decoded} {after : Image}
    (healthy : (reopen (ops healthyReopen) policy).run b = .ok (.ok d) after) :
    ∃ marker, ReopenSelection policy b marker d ∧ after = ((b.bothSynced marker).trimmed d).dataSettled := by
  cases policy with
  | logOnly =>
    rw [reopen_log] at healthy
    cases sc : scan b.data.live b.data.live.length .logOnly with
    | error e => simp [healthyReopen, sc] at healthy
    | ok found =>
      have sel : ReopenSelection .logOnly b none found := sc
      have actual := reopen_selected_healthy sel
      rw [reopen_log] at actual
      cases healthy.symm.trans actual
      exact ⟨none, sel, rfl⟩
  | boundary =>
    rw [reopen_marked] at healthy
    cases picked : selectMarker b.slot0.live b.slot1.live with
    | error e => simp [healthyReopen, picked] at healthy
    | ok m =>
      cases sc : scan b.data.live m.endPos .boundary with
      | error e => simp [healthyReopen, picked, sc] at healthy
      | ok found =>
        by_cases ord : found.cursor.nextSeq = m.lastSeq + 1
        · have sel : ReopenSelection .boundary b (some m) found := ⟨picked, sc, ord⟩
          have actual := reopen_selected_healthy sel
          rw [reopen_marked] at actual
          cases healthy.symm.trans actual
          exact ⟨some m, sel, rfl⟩
        · simp [healthyReopen, picked, sc, ord] at healthy

private theorem selected_boot (image : Image) (marker : Option Marker) :
    image.powerLoss.selectedSync marker = image.powerLoss := by
  cases marker with
  | none => rfl
  | some m =>
    by_cases zero : m.lastSeq % 2 = 0 <;>
      simp [Image.selectedSync, Image.settleSlot, Image.withMarker, Image.marker,
        Image.powerLoss, FileImage.powerLoss, zero]

theorem both_boot (image : Image) (marker : Option Marker) :
    image.powerLoss.bothSynced marker = image.powerLoss := by
  cases marker with
  | none => rfl
  | some m =>
    simp only [Image.bothSynced, selected_boot]
    by_cases zero : 1 - m.lastSeq % 2 = 0 <;>
      simp [Image.settleSlot, Image.withMarker, Image.marker, Image.powerLoss, FileImage.powerLoss, zero]

/-- A failed repair can leave its original durable image or settle its entire
repair before the response is lost. A successful attempt returns exactly the
healthy result at its identical repaired image. -/
theorem reopen_retry (effects : Effects) (policy : Policy) (image : Image)
    {decoded : Decoded} {after : Image}
    (healthy : (reopen (ops healthyReopen) policy).run image.powerLoss = .ok (.ok decoded) after) :
    let out := (reopen (ops effects) policy).run image.powerLoss
    ((reached out).powerLoss = image.powerLoss ∨ (reached out).powerLoss = after) ∧
      ∀ returned, acknowledged out = some returned → returned = decoded ∧ reached out = after := by
  obtain ⟨marker, sel, rfl⟩ := healthy_reopen_selection healthy
  obtain ⟨cuts, ack⟩ := reopen_cuts effects sel
  simp only [selected_boot, both_boot] at cuts ack ⊢
  refine ⟨?_, ack⟩
  rcases cuts with h | h | h | h | h <;> rw [h] <;> first | exact .inl rfl | exact .inr rfl

private theorem scanned_length {bs : Bytes} {n : Nat} {p : Policy} {d : Decoded}
    (ok : scan bs n p = .ok d) : n ≤ bs.length := by
  simp only [scan] at ok
  split at ok
  · contradiction
  · rename_i h
    simp [List.length_take] at h
    omega

/-- Rescanning a live image after a failed attempt uses the same observed
marker bytes and sees either the original data or exactly the decoded prefix. -/
private theorem selected_again {p : Policy} {before later : Image} {marker : Option Marker} {d : Decoded}
    (sel : ReopenSelection p before marker d)
    (m0 : later.slot0.live = before.slot0.live) (m1 : later.slot1.live = before.slot1.live)
    (data : later.data.live = before.data.live ∨
      later.data.live = before.data.live.take d.cursor.endPos) :
    ReopenSelection p later marker d := by
  cases p <;> cases marker <;> try contradiction
  case logOnly.none =>
    change scan _ _ _ = _ at sel ⊢
    rcases data with h | h
    · simpa only [h] using sel
    · have stable := scan_repair_stable sel
      have lengthOk := scanned_length stable
      rw [h]
      have len : (before.data.live.take d.cursor.endPos).length = d.cursor.endPos := by
        simp only [List.length_take] at lengthOk ⊢
        omega
      rwa [len]
  case boundary.some m =>
    obtain ⟨picked, sc, ord⟩ := sel
    refine ⟨by rwa [m0, m1], ?_, ord⟩
    rcases data with h | h
    · rwa [h]
    · rw [h, ← scan_boundary_end sc]
      exact scan_repair_stable sc

private theorem both_some (b : Image) (m : Marker) :
    b.bothSynced (some m) =
      {b with slot0.durable := b.slot0.live, slot1.durable := b.slot1.live} := by
  have which : m.lastSeq % 2 = 0 ∨ m.lastSeq % 2 = 1 := by omega
  rcases which with h | h <;>
    simp [Image.bothSynced, Image.selectedSync, Image.settleSlot, Image.withMarker, Image.marker, h]

/-- A retry without power loss observes the same cursor and settles the same
image, even when the preceding call already truncated live data or synced just
one marker. -/
theorem reopen_live_retry (effects : Effects) (policy : Policy) (before : Image)
    {d : Decoded} {after : Image}
    (healthy : (reopen (ops healthyReopen) policy).run before = .ok (.ok d) after) :
    let out := (reopen (ops effects) policy).run before
    (reopen (ops healthyReopen) policy).run (reached out) = .ok (.ok d) after := by
  obtain ⟨marker, sel, rfl⟩ := healthy_reopen_selection healthy
  obtain ⟨cuts, _⟩ := reopen_cuts effects sel
  let later := reached ((reopen (ops effects) policy).run before)
  change (reopen (ops healthyReopen) policy).run later = _
  have facts :
      later.slot0.live = before.slot0.live ∧ later.slot1.live = before.slot1.live ∧
      (later.data.live = before.data.live ∨ later.data.live = before.data.live.take d.cursor.endPos) ∧
      (later.bothSynced marker).slot0 = (before.bothSynced marker).slot0 ∧
      (later.bothSynced marker).slot1 = (before.bothSynced marker).slot1 := by
    dsimp only [later]
    rcases cuts with h | h | h | h | h <;> rw [h]
    all_goals cases marker with
      | none => simp [Image.bothSynced, Image.selectedSync, Image.dataSettled, Image.trimmed]
      | some m =>
        have which : m.lastSeq % 2 = 0 ∨ m.lastSeq % 2 = 1 := by omega
        rcases which with which | which <;>
          simp [both_some, Image.selectedSync, Image.settleSlot, Image.withMarker, Image.marker,
            Image.dataSettled, Image.trimmed, which]
  obtain ⟨m0, m1, dat, s0, s1⟩ := facts
  rw [reopen_selected_healthy (selected_again sel m0 m1 dat)]
  have keep : later.data.live.take d.cursor.endPos = before.data.live.take d.cursor.endPos := by
    rcases dat with h | h <;> simp [h, List.take_take]
  simp only [Image.dataSettled, Image.trimmed, data_after_markers, s0, s1, keep]

end WalRecoverySlice.Persistence
