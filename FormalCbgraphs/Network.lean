import Mathlib.Tactic
import FormalCbgraphs.Graph

structure Network (R : Type) extends Graph where
  init : V → R
  transfer : toGraph.E → R → R

variable {R : Type} {N : Network R}

structure Schedule (N : Network R) where
  nodeActivate : N.V → Nat → Bool
  flow : N.E → Nat → Nat
  flow_lt : ∀ (e t), flow e (t + 1) < (t + 1)

namespace Schedule

variable (S : Schedule N)

/-- A node is said eventually activated if it is activated infinitely often. -/
def NodeEventuallyActivated (v : N.V) : Prop :=
  ∀ T, ∃ t ≥ T, S.nodeActivate v t

/-- An edge is said eventually delivering if messages are guaranteed to be delivered infinitely often. This is superseded by `edgeEventualFlush`. -/
def EdgeEventuallyDelivering (e : N.E) : Prop :=
  ∀ T, ∃ t ≥ T, S.flow e t ≥ T

/-- An edge is said eventually flushed if one message will not be sent infinitely times. -/
def EdgeEventuallyFlushed (e : N.E) : Prop :=
  ∀ T, ∃ T' ≥ T, ∀ t ≥ T', S.flow e t ≥ T

theorem eventuallyFlushed_implies_eventuallyDelivering :
    S.EdgeEventuallyFlushed e → S.EdgeEventuallyDelivering e := by
  intro h T
  rcases h T with ⟨t, ht, ht'⟩
  exact ⟨t, ht, ht' t le_rfl⟩

/-- An edge is said ordered if it deliver messages in the same order as it was sent. Our theorems do not require `edgeOrdered` and only require a weaker property `edgeEventualFlush`. -/
def EdgeOrdered (e : N.E) : Prop :=
  ∀ t₁ t₂, t₁ ≤ t₂ → S.flow e t₁ ≤ S.flow e t₂

theorem ordered_and_eventuallyDelivering_implies_eventuallyFlushed :
    S.EdgeOrdered e → S.EdgeEventuallyDelivering e → S.EdgeEventuallyFlushed e := by
  intro h₁ h₂ T
  rcases h₂ T with ⟨t₁, ht₁, ht₁'⟩
  refine ⟨t₁, ht₁, ?_⟩
  intro t₂ ht₂
  exact ht₁'.trans (h₁ _ _ ht₂)

/-- A schedule is fair if all nodes are eventually activated and all edges are eventually flushed. -/
def Fair : Prop :=
  (∀ v, S.NodeEventuallyActivated v) ∧ ∀ e, S.EdgeEventuallyFlushed e

/-- A schedule is fair with at most `k` failure if all nodes are eventually activated, and all edges except at most `k` failed edges are eventually flushed. -/
def FairWithFailure (k : ℕ) : Prop :=
  (∀ v, S.NodeEventuallyActivated v) ∧ ∃ (F : Finset N.E), F.card ≤ k ∧ ∀ e ∉ F, S.EdgeEventuallyFlushed e

theorem fairWithFailure_zero_iff : S.FairWithFailure 0 ↔ S.Fair := by
  simp [FairWithFailure, Fair]

variable [SemilatticeInf R] [OrderTop R]

/-- The semantics of a network. -/
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
