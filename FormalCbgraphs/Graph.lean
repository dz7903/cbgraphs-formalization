import Mathlib.Data.Finset.Card

structure Graph where
  V : Type
  neighbors : V → Finset V

namespace Graph

structure E (G : Graph) where
  u : G.V
  v : G.V
  isEdge : u ∈ G.neighbors v

/-- `Connected Roots Edges v` means a node `v` is connected to a node in `Nodes` via `Edges`. -/
inductive Connected {G : Graph} (Roots : Set G.V) (Edges : Set G.E) : G.V → Prop where
| base (v : G.V) : v ∈ Roots → Connected Roots Edges v
| step (e : G.E) : Connected Roots Edges e.u → e ∈ Edges → Connected Roots Edges e.v

/-- `ConnectedWithFailure Roots Edges v k` means a node `v` is connected to a node in `Nodes` via
`Edges` when excluding at most `k` edges arbitrarily. -/
def ConnectedWithFailure {G : Graph} (Roots : Set G.V) (Edges : Set G.E) (v : G.V) (k : ℕ) :=
  ∀ (F : Finset G.E), F.card ≤ k → Connected Roots (Edges \ F) v

theorem connectedWithFailure_zero_iff : ConnectedWithFailure Roots Edges v 0 ↔ Connected Roots Edges v := by
  simp [ConnectedWithFailure]

end Graph
