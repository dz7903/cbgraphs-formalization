import FormalCbgraphs.Network

lemma Finset.inf_induction' {ι α : Type*} [SemilatticeInf α] [OrderTop α]
    {p : α → Prop} {s : Finset ι} {f : ι → α} {a : α}
    (ht : p a) (hp : ∀ x, ∀ y ∈ s, p x → p (x ⊓ f y)) :
    p (a ⊓ s.inf f) := by
  classical
  induction s using Finset.induction with
  | empty => simpa
  | insert x s _ ih =>
    rw [inf_insert, ← inf_assoc, inf_right_comm]
    apply hp
    · simp
    · apply ih
      intros; apply hp
      · simp; right; assumption
      · assumption

variable {R : Type} [SemilatticeInf R] [OrderTop R]

structure VC (N : Network R) where
  I : N.V → R → Prop
  Q : N.V → R → Prop
  Y : N.V → R → Prop
  CBRoots : Set N.V
  CBEdges : Set N.E
  init : ∀ v, I v (N.init v)
  property : ∀ v sv, Q v sv → Y v sv
  inv : ∀ (e : N.E) su sv, I e.u su → I e.v sv → I e.v (sv ⊓ N.transfer e su)
  root₁ : ∀ v ∈ CBRoots, Q v (N.init v)
  root₂ : ∀ (e : N.E) su sv, e.v ∈ CBRoots → I e.u su → Q e.v sv → Q e.v (sv ⊓ N.transfer e su)
  edge : ∀ e ∈ CBEdges, ∀ su sv, Q e.u su → I e.v sv → Q e.v (sv ⊓ N.transfer e su)
  connected : ∀ v, Graph.Connected CBRoots CBEdges v

namespace VC

variable {N : Network R} {S : Schedule N} (vc : VC N)

/-- The invariance interface `vc.I` holds at any time on any schedules. -/
lemma invariance : ∀ v t, vc.I v (S.sem v t) := by
  intro v t
  induction t using Nat.strong_induction_on generalizing v with | _ t ih
  cases t with
  | zero => simp [Schedule.sem]; exact vc.init v
  | succ t =>
    simp [Schedule.sem]
    split_ifs with h
    · apply Finset.inf_induction'
      · exact vc.init v
      · simp
        intro sv u huv hsv
        apply vc.inv ⟨u, v, huv⟩
        · apply ih
          exact S.flow_lt _ _
        · exact hsv
    · exact ih t (Nat.lt_succ_self t) _

/-- A node `v` abstractly converge at `τ` if its semantics satisfies `vc.Q` since `τ`. -/
def AbstractlyConverge (S : Schedule N) (v : N.V) (τ : ℕ) : Prop :=
  ∀ t ≥ τ, vc.Q v (S.sem v t)

/-- CB-roots abstractly converge at time `0`. -/
lemma cbroot : ∀ v ∈ vc.CBRoots, vc.AbstractlyConverge S v 0 := by
  rintro v hv t -
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => simp [Schedule.sem]; exact vc.root₁ v hv
  | succ t =>
    simp [Schedule.sem]
    split_ifs with h
    · apply Finset.inf_induction'
      · exact vc.root₁ v hv
      · simp
        intro sv u huv hsv
        apply vc.root₂ ⟨u, v, huv⟩ _ _ hv
        · exact vc.invariance _ _
        · exact hsv
    · exact ih t (Nat.lt_succ_self t)

/-- With fairness assumption, a CB-edge gives an order of abstract convergence. -/
lemma cbedge (e) (he : e ∈ vc.CBEdges) (he₁ : S.NodeEventuallyActivated e.v) (he₂ : S.EdgeEventuallyFlushed e) :
    vc.AbstractlyConverge S e.u τ → ∃ τ' > τ, vc.AbstractlyConverge S e.v τ' := by
  classical
  intro hu
  rcases he₂ τ with ⟨τ₁, hτ₁, hτ₁'⟩
  rcases he₁ (τ₁ + 1) with ⟨τ₂, hτ₂, hτ₂'⟩
  refine ⟨τ₂, hτ₂.trans' (Nat.succ_le_succ hτ₁), ?_⟩
  intro t ht
  cases τ₂ with simp at hτ₂ | succ τ₂
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with simp at ht | succ t
  simp [Schedule.sem]
  split_ifs with h
  · rw [← Finset.insert_erase (Finset.mem_attach _ _ : ⟨e.u, e.isEdge⟩ ∈ (N.neighbors e.v).attach),
      Finset.inf_insert, inf_left_comm, inf_comm]
    apply vc.edge _ he
    · apply hu
      apply hτ₁'
      exact Nat.le_succ_of_le (ht.trans' hτ₂)
    · apply Finset.inf_induction'
      · exact vc.init e.v
      · simp
        intro sv u huv _ hsv
        apply vc.inv ⟨u, e.v, huv⟩
        · exact vc.invariance _ _
        · exact hsv
  · apply ih t (Nat.lt_succ_self t)
    by_contra ht'
    rw [← eq_of_le_of_not_lt ht ht'] at h
    contradiction

/-- A connected CB-graph gives abstract convergence on all fair schedules (note `VC` already assumes the connectedness). -/
theorem connected_cbgraph (h : S.Fair) : ∀ v, ∃ τ, ∀ t ≥ τ, vc.Q v (S.sem v t) := by
  intro v
  induction vc.connected v with
  | base v hv =>
    exists 0
    simpa [AbstractlyConverge] using vc.cbroot v hv
  | step e _ he ih =>
    rcases ih with ⟨τ₁, hτ₁⟩
    rcases vc.cbedge e he (h.1 e.v) (h.2 e) hτ₁ with ⟨τ₂, _, hτ₂⟩
    exact ⟨τ₂, hτ₂⟩

/-- A CB-graph with `k` connectivity on node `v` gives abstract convergence at `v` on all schedules with at most `k` failures. -/
theorem connected_cbgraph_with_failure (h₁ : S.FairWithFailure k)
    (h₂ : Graph.ConnectedWithFailure vc.CBRoots vc.CBEdges v k) :
    ∃ τ, ∀ t ≥ τ, vc.Q v (S.sem v t) := by
  rcases h₁ with ⟨h₁, F, hF, h₁'⟩
  specialize h₂ F hF
  induction h₂ with
  | base v hv =>
    exists 0
    simpa [AbstractlyConverge] using vc.cbroot v hv
  | step e _ he ih =>
    simp at he
    rcases ih with ⟨τ₁, hτ₁⟩
    rcases vc.cbedge e he.1 (h₁ e.v) (h₁' e he.2) hτ₁ with ⟨τ₂, _, hτ₂⟩
    exact ⟨τ₂, hτ₂⟩

theorem correctness (h : S.Fair) : ∀ v, ∃ τ, ∀ t ≥ τ, vc.Y v (S.sem v t) := by
  intro v
  rcases vc.connected_cbgraph h v with ⟨τ, hτ⟩
  exists τ
  intro t ht
  exact vc.property v _ (hτ t ht)

theorem correctness_with_failure (h₁ : S.FairWithFailure k)
    (h₂ : ∀ v, Graph.ConnectedWithFailure vc.CBRoots vc.CBEdges v k) :
    ∀ v, ∃ τ, ∀ t ≥ τ, vc.Y v (S.sem v t) := by
  intro v
  rcases vc.connected_cbgraph_with_failure h₁ (h₂ v) with ⟨τ, hτ⟩
  exists τ
  intro t ht
  exact vc.property v _ (hτ t ht)
