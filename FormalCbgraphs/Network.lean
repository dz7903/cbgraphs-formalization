import Mathlib.Tactic
import FormalCbgraphs.Graph

/-- A network (instance) is a graph with initial routes and transfer functions. -/
structure Network (R : Type) extends Graph where
  init : V → R
  transfer : toGraph.E → R → R

variable {R : Type} {N : Network R}

/-- A schedule of a network `N` includes activation function and flow function. -/
structure Schedule (N : Network R) where
  nodeActivate : N.V → Nat → Bool
  flow : N.E → Nat → Nat
  /-- Flow function must satisfy causality. -/
  flow_lt : ∀ (e t), flow e (t + 1) < (t + 1)

namespace Schedule

variable (S : Schedule N) {e : N.E}

/-- A node is said non-failed if it is activated infinitely often. -/
def NodeNonFailed (v : N.V) : Prop :=
  ∀ T, ∃ t ≥ T, S.nodeActivate v t

/-- An edge is said non-failed if one message can not be sent infinite times. -/
def EdgeNonFailed (e : N.E) : Prop :=
  ∀ T, ∃ T' ≥ T, ∀ t ≥ T', S.flow e t ≥ T

/-- A schedule is fair if all nodes and edges are non-failed. -/
def Fair : Prop :=
  (∀ v, S.NodeNonFailed v) ∧ ∀ e, S.EdgeNonFailed e

/-- A schedule is fair with at most `k` failure if all nodes are non-failed, and all edges except
at most `k` are non-failed. -/
def FairWithFailure (k : ℕ) : Prop :=
  (∀ v, S.NodeNonFailed v) ∧ ∃ (F : Finset N.E), F.card ≤ k ∧ ∀ e ∉ F, S.EdgeNonFailed e

theorem fairWithFailure_zero_iff : S.FairWithFailure 0 ↔ S.Fair := by
  simp [FairWithFailure, Fair]

variable [SemilatticeInf R] [OrderTop R]

/-- The semantics of a network. This requires the existence of selection function
(`SemilatticeInf R`) and the invalid route (`OrderTop R`). We do not require a linear order on `R`,
though that is the usual case (we do require that in completeness). -/
def sem : N.V → Nat → R
| v, 0 => N.init v
| v, t + 1 =>
  if S.nodeActivate v (t + 1) then
    N.init v ⊓ (N.neighbors v).attach.inf λ ⟨u, huv⟩ =>
      let e := ⟨u, v, huv⟩
      let t' := S.flow e (t + 1)
      have : t' ≤ t := by simpa using S.flow_lt e t
      N.transfer e (sem u t')
  else
    sem v t

end Schedule

variable (N) in
/-- Apply each transfer functions along a path in the network. -/
def Network.applyPath : ∀ {v}, N.Path v → R
| _, .nil (u := u) => N.init u
| _, .cons p h => N.transfer ⟨_, _, h⟩ (applyPath p)

def Network.syncSchedule : Schedule N where
  nodeActivate v t := True
  flow e t := t - 1
  flow_lt := by grind

theorem Network.fair_syncSchedule : N.syncSchedule.Fair := by
  constructor
  · intro v
    simp only [syncSchedule, Schedule.NodeNonFailed, ge_iff_le, decide_true, and_true]
    intro T
    exists T
  · intro e
    simp only [syncSchedule,Schedule.EdgeNonFailed, ge_iff_le]
    intro T
    exists T + 1
    grind

variable (N) in
/-- There exists a fair schedule, which is the synchronous schedule. -/
lemma Network.exists_fair_schedule : ∃ (S : Schedule N), S.Fair :=
  ⟨N.syncSchedule, N.fair_syncSchedule⟩
