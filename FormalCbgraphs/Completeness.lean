import FormalCbgraphs.Soundness

def Network.IsStrictMono {R} [Preorder R] (N : Network R) :=
  ∀ e, StrictMono (N.transfer e)

/-- The condition that `Y` holds eventually stably on any fair schedule of `N`. -/
def Network.IsEventualStable {R} [SemilatticeInf R] [OrderTop R] (N : Network R)
    (Y : N.V → R → Prop) :=
  ∀ (S : Schedule N), S.Fair → ∀ v, ∃ t, ∀ t' ≥ t, Y v (S.sem v t')

variable {R} [CompleteLinearOrder R] [WellFoundedLT R] {N : Network R} {u v : N.V}
  {Y : N.V → R → Prop} (hN : N.IsStrictMono) (hY : N.IsEventualStable Y)

def bestRoute (v : N.V) : R :=
  ⨅ (p : N.Path v), N.applyPath p

theorem exists_applyPath_eq_bestRoute (u : N.V) :
    ∃ p : N.Path u, N.applyPath p = bestRoute u := by
  rcases Finset.exists_inf_eq_iInf (N.applyPath (v := u)) with ⟨s, hs⟩
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · rw [eq_comm, Finset.inf_empty, iInf_eq_top] at hs
    exists .nil
    simp [bestRoute, hs]
  · rcases s.exists_mem_eq_inf hs' N.applyPath with ⟨p, -, hp⟩
    exists p
    rw [bestRoute, ← hs, hp]

include hN in
theorem applyPath_eq_bestRoute_of_cons {p : N.Path u} {huv : u ∈ N.neighbors v} :
    N.applyPath (p.cons huv) = bestRoute v → N.applyPath p = bestRoute u := by
  intro h
  apply (iInf_le _ _).antisymm'
  by_contra! h'
  apply h.not_gt
  rw [Network.applyPath]
  apply (hN ⟨u, v, huv⟩ h').trans_le'
  rcases exists_applyPath_eq_bestRoute u with ⟨p, hp⟩
  rw [← bestRoute, ← hp, ← Network.applyPath]
  exact iInf_le _ _

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
      exact iInf_le _ _
    edge e := by
      intro ⟨p, hp⟩ su sv hu ⟨q, hq⟩
      have hp' := applyPath_eq_bestRoute_of_cons hN hp
      rw [hu, ← hq, ← hp', ← Network.applyPath, hp, min_eq_right_iff]
      exact iInf_le _ _
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
