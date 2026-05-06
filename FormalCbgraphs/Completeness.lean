import FormalCbgraphs.Soundness
import Mathlib.Order.ConditionallyCompleteLattice.Defs

-- def Distributive {R} [SemilatticeInf R] (f : R → R) :=
--   ∀ x y, f x ⊓ f y = f (x ⊓ y)

-- theorem distributive_iff_monotone {R} [LinearOrder R] {f : R → R} : Distributive f ↔ Monotone f := by
--   constructor
--   · intro hf x y h
--     rw [← inf_eq_right] at h ⊢
--     rw [hf, h]
--   · intro hf x y
--     rw [hf.map_min]

-- def Network.IsDistributive {R} [SemilatticeInf R] (N : Network R) :=
--   ∀ e, Distributive (N.transfer e)

def Network.IsStrictMono {R} [Preorder R] (N : Network R) :=
  ∀ e, StrictMono (N.transfer e)

/-- The condition that `Y` holds eventually stably on any fair schedule of `N`. -/
def Network.IsEventualStable {R} [SemilatticeInf R] [OrderTop R] (N : Network R)
    (Y : N.V → R → Prop) :=
  ∀ (S : Schedule N), S.Fair → ∀ v, ∃ t, ∀ t' ≥ t, Y v (S.sem v t')

variable {R} [LinearOrder R] [OrderTop R] [WellFoundedLT R] {N : Network R} {u v : N.V}
  {Y : N.V → R → Prop} (hN : N.IsStrictMono) (hY : N.IsEventualStable Y)

noncomputable def bestRoute (v : N.V) : R :=
  wellFounded_lt.min {N.applyPath p | (p : N.Path v)} ⟨_, .nil, rfl⟩

omit [OrderTop R] in
lemma bestRoute_le_applyPath (p : N.Path v) : bestRoute v ≤ N.applyPath p :=
  WellFounded.min_le _ (by exists p)

omit [OrderTop R] in
theorem exists_applyPath_eq_bestRoute (v : N.V) :
    ∃ p : N.Path v, N.applyPath p = bestRoute v :=
  wellFounded_lt.min_mem {N.applyPath p | (p : N.Path v)} _

include hN in
omit [OrderTop R] in
theorem applyPath_eq_bestRoute_of_cons {p : N.Path u} {huv : u ∈ N.neighbors v} :
    N.applyPath (p.cons huv) = bestRoute v → N.applyPath p = bestRoute u := by
  intro h
  apply (bestRoute_le_applyPath _).antisymm'
  by_contra! h'
  apply h.not_gt
  rw [Network.applyPath]
  apply (hN ⟨u, v, huv⟩ h').trans_le'
  rcases exists_applyPath_eq_bestRoute u with ⟨p, hp⟩
  rw [← hp, ← Network.applyPath]
  exact bestRoute_le_applyPath _

include hN hY in
/-- Soundness theorem: if `Y` holds eventually stably for any fair schedule of `N`, and all
transfer functions are strict monotone, then there exists some annotations and a CB-graph that
satisfies all verification conditions and the connectedness. -/
theorem completeness : Nonempty (VC N Y) := by
  let vc' : VC N (fun v s => s = bestRoute v) := {
    I v s := ∃ p, N.applyPath p = s
    Q v s := s = bestRoute v
    CBRoots := {v | N.applyPath (.nil (u := v)) = bestRoute v}
    CBEdges := {e | ∃ (p : N.Path e.u), N.applyPath (p.cons e.isEdge) = bestRoute e.v}
    init v := ⟨.nil, by rw [Network.applyPath]⟩
    property := by simp
    inv e su sv := by
      intro ⟨p, hp⟩ ⟨q, hq⟩
      rcases le_or_gt sv (N.transfer e su) with h | h
      · exists q
        rw [hq, min_eq_left h]
      · exists p.cons e.isEdge
        rw [Network.applyPath, hp, min_eq_right h.le]
    root₁ v := by simp [Network.applyPath]
    root₂ e su sv := by
      intro hv ⟨p, hp⟩ hv'
      simp only [Set.mem_setOf_eq, Network.applyPath] at hv
      rw [hv', min_eq_left_iff, ← hp, ← Network.applyPath]
      exact bestRoute_le_applyPath _
    edge e := by
      intro ⟨p, hp⟩ su sv hu ⟨q, hq⟩
      have hp' := applyPath_eq_bestRoute_of_cons hN hp
      rw [hu, ← hq, ← hp', ← Network.applyPath, hp, min_eq_right_iff]
      exact bestRoute_le_applyPath _
    connected v := by
      rcases exists_applyPath_eq_bestRoute v with ⟨p, hp⟩
      induction p with
      | nil =>
        apply Graph.Connected.base
        simpa
      | @cons u v p huv ih =>
        specialize ih (applyPath_eq_bestRoute_of_cons hN hp)
        apply Graph.Connected.step ⟨u, v, huv⟩ ih
        exists p
  }
  refine ⟨vc'.I, vc'.Q, vc'.CBRoots, vc'.CBEdges, vc'.init, ?_, vc'.inv, vc'.root₁, vc'.root₂, vc'.edge, vc'.connected⟩
  intro v sv hv
  rcases N.exists_fair_schedule with ⟨S, hS⟩
  rcases vc'.correctness hS v with ⟨T₁, hT₁⟩
  rcases hY S hS v with ⟨T₂, hT₂⟩
  grind [hT₁ (max T₁ T₂), hT₂ (max T₁ T₂)]
