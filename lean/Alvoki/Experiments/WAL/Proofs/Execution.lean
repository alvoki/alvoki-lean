import Alvoki.Experiments.WAL.Contract
import Alvoki.Experiments.WAL.Proofs.Client
import Alvoki.Experiments.WAL.Proofs.DirtyAppend

namespace WalRecoverySlice.Persistence
open Contract (Batch History Event Allows Permitted)

inductive Session where
  | online (image : Image) (cursor : Cursor) (cached : History)
  | offline (image : Image)

/-- Process exit preserves the page cache. Power loss loads the durable bytes. -/
inductive Restart where
  | processExit
  | powerLoss

def Restart.image (mode : Restart) (before : Image) : Image :=
  match mode with
  | .processExit => before
  | .powerLoss => before.powerLoss

/-- Operational traces use actual append/reopen results. No constructor asks
the caller to supply a proof of the client contract. -/
inductive Run (policy : Policy) : List Event → Session → Prop where
  | fresh : Run policy [] (.online freshImage {} [])
  | ack (prior : Run policy events (.online image cursor cached)) (effects : Effects)
      (returned : (appendBatch (ops effects) policy cursor p).run image = .ok (.ok next) after) :
      Run policy (events ++ [.ack p]) (.online after next (cached ++ [p]))
  /-- The caller saw no ACK, including a reply lost after the final sync. -/
  | uncertain (prior : Run policy events (.online image cursor cached)) (effects : Effects) :
      Run policy (events ++ [.uncertain p])
        (.offline (reached ((appendBatch (ops effects) policy cursor p).run image)))
  | stop (mode : Restart) (prior : Run policy events (.online image cursor cached)) :
      Run policy (events ++ [.stop]) (.offline (mode.image image))
  | stoppedAgain (mode : Restart) (prior : Run policy events (.offline image)) :
      Run policy (events ++ [.stop]) (.offline (mode.image image))
  | failed (prior : Run policy events (.offline image)) (effects : Effects)
      (returned : (reopen (ops effects) policy).run image = .ok (.error error) after) :
      Run policy (events ++ [.openFailed]) (.offline after)
  /-- The caller lost the open attempt before observing a response. -/
  | abandonOpen (prior : Run policy events (.offline image)) (effects : Effects) :
      Run policy (events ++ [.stop]) (.offline (reached ((reopen (ops effects) policy).run image)))
  | opened (prior : Run policy events (.offline image)) (effects : Effects)
      (returned : (reopen (ops effects) policy).run image = .ok (.ok d) after) :
      Run policy (events ++ [.opened d.batches]) (.online after d.cursor d.batches)
  | scan (prior : Run policy events (.online image cursor cached)) :
      Run policy (events ++ [.scan cached]) (.online image cursor cached)

private def Sized (h : History) := (∀ b ∈ h, b.length ≤ 32) ∧ h.length ≤ 255

private theorem sized_append {h : History} {p : Bytes} (old : Sized h) (sized : p.length ≤ 32)
    (room : h.length < 255) : Sized (h ++ [p]) := by
  refine ⟨?_, by simp; omega⟩
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact old.1 b hb
  · simpa [List.mem_singleton.mp hb] using sized

private inductive Represents (policy : Policy) : Session → Contract.View → Prop where
  | online (ready : Ready policy image cached) (sized : Sized cached) (clean : image.powerLoss = image) :
      Represents policy (.online image (historyCursor cached) cached) (.online cached)
  | offline (dirty : Dirty policy known actual image) (markers : policy = .logOnly → image.MarkersSettled)
      (permitted : ∀ h, Permitted known actual h → Permitted known pending h) :
      Represents policy (.offline image) (.offline known pending)

private theorem restart_represents {policy known pending image} (dirty : Dirty policy known pending image)
    (markers : policy = .logOnly → image.MarkersSettled) {advertised : Option Batch}
    (permit : ∀ h, Permitted known pending h → Permitted known advertised h) (mode : Restart) :
    Represents policy (.offline (mode.image image)) (.offline known advertised) := by
  cases mode with
  | processExit => exact .offline dirty markers permit
  | powerLoss => exact .offline dirty.powerLoss (fun _ => ⟨rfl, rfl⟩) permit

private theorem sound {policy events session} (run : Run policy events session) :
    ∃ view, Allows events view ∧ Represents policy session view := by
  induction run with
  | fresh => exact ⟨_, .fresh, .online (fresh_ready _) ⟨by simp, by decide⟩ rfl⟩
  | @ack events image cursor cached p next after prior effects returned ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | online entry old clean =>
      by_cases valid : p.length ≤ 32 ∧ (historyCursor cached).nextSeq ≤ 255
      · have fits : cached.length < 255 := by have := valid.2; simp [historyCursor] at this; omega
        obtain ⟨rfl, next⟩ := ready_after_ack entry p effects returned old.1 fits valid.1
        have ack : acknowledged ((appendBatch (ops effects) policy (historyCursor cached) p).run image) =
            some (historyCursor (cached ++ [p])) := by rw [returned]; rfl
        have settled := appendBatch_ack_clean policy effects image cached p entry clean old.1 fits valid.1 ack
        rw [returned] at settled
        exact ⟨_, .next allowed .ack, .online next (sized_append old valid.1 fits) settled⟩
      · have rejected := append_rejected policy effects (historyCursor cached) p image (by omega)
        rw [returned] at rejected
        cases rejected
  | @uncertain events image cursor cached p prior effects ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | online entry old clean =>
      refine ⟨_, .next allowed .uncertain, ?_⟩
      by_cases valid : p.length ≤ 32 ∧ (historyCursor cached).nextSeq ≤ 255
      · have fits : cached.length < 255 := by have := valid.2; simp [historyCursor] at this; omega
        refine .offline (appendBatch_dirty policy effects image cached p entry clean old.1 fits valid.1) ?_ (fun _ h => h)
        intro log
        subst policy
        exact appendBatch_logOnly_markers effects image cached p entry clean old.1 fits valid.1
      · rw [append_rejected policy effects (historyCursor cached) p image (by omega)]
        refine .offline (ready_dirty policy image cached entry clean old.1 old.2)
          (fun _ => by change image.MarkersSettled; rw [← clean]; exact ⟨rfl, rfl⟩) ?_
        intro h allowedHistory
        simp [Contract.Permitted] at allowedHistory
        exact .inl allowedHistory
  | stop mode prior ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | online entry sized clean =>
      exact ⟨_, .next allowed .stop, restart_represents (ready_dirty policy _ _ entry clean sized.1 sized.2)
        (fun _ => by rw [← clean]; exact ⟨rfl, rfl⟩) (fun _ h => h) mode⟩
  | stoppedAgain mode prior ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | offline dirty markers permit =>
      exact ⟨_, .next allowed .stoppedAgain, restart_represents dirty markers permit mode⟩
  | failed prior effects returned ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | offline dirty markers permit =>
      obtain ⟨next, keep, _⟩ := dirty.reopen effects
      rw [returned] at next keep
      exact ⟨_, .next allowed .failed, .offline next (fun log => keep (markers log)) permit⟩
  | abandonOpen prior effects ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | offline dirty markers permit =>
      obtain ⟨next, keep, _⟩ := dirty.reopen effects
      exact ⟨_, .next allowed .stoppedAgain, .offline next (fun log => keep (markers log)) permit⟩
  | opened prior effects returned ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | offline dirty markers permit =>
      obtain ⟨_, _, success⟩ := dirty.reopen effects
      rw [returned] at success
      obtain ⟨permitted, cursor, ready, bounded, fits, clean⟩ := success _ rfl
      have settled := clean (by
        by_cases isLog : policy = .logOnly
        · exact .inr (markers isLog)
        · exact .inl (by cases policy <;> simp_all))
      exact ⟨_, .next allowed (.opened (permit _ permitted)), cursor ▸ Represents.online ready ⟨bounded, fits⟩ settled⟩
  | scan prior ih =>
    obtain ⟨_, allowed, rep⟩ := ih
    cases rep with
    | online entry sized clean => exact ⟨_, .next allowed .scan, .online entry sized clean⟩

/-- The only client histories observable on any finite source execution are
those admitted by the batch-level contract. -/
theorem Run.refines {policy events session} (run : Run policy events session) :
    ∃ view, Allows events view := by
  obtain ⟨view, valid, _⟩ := sound run
  exact ⟨view, valid⟩

/-- Once the filesystem operations succeed, every reachable offline state can
actually be opened. The refinement theorem constrains its result. -/
theorem Run.healthy_open {policy events image} (run : Run policy events (.offline image)) :
    ∃ d after, (reopen (ops healthyReopen) policy).run image = .ok (.ok d) after := by
  obtain ⟨_, _, rep⟩ := sound run
  cases rep with
  | offline dirty _ _ => exact dirty.healthy_reopen

end WalRecoverySlice.Persistence
