import Mathlib.Data.Finset.Card

structure Graph where
  V : Type
  neighbors : V → Finset V

namespace Graph

variable {G : Graph} {v : G.V}

structure E (G : Graph) where
  u : G.V
  v : G.V
  isEdge : u ∈ G.neighbors v

/-- `Connected Roots Edges v` means a node `v` is connected to a node in `Roots` via `Edges`. -/
inductive Connected (Roots : Set G.V) (Edges : Set G.E) : G.V → Prop where
| base (v : G.V) : v ∈ Roots → Connected Roots Edges v
| step (e : G.E) : Connected Roots Edges e.u → e ∈ Edges → Connected Roots Edges e.v

/-- `ConnectedWithFailure Roots Edges v k` means a node `v` is connected to a node in `Roots` via
`Edges` when excluding at most `k` edges arbitrarily. -/
def ConnectedWithFailure (Roots : Set G.V) (Edges : Set G.E) (v : G.V) (k : ℕ) :=
  ∀ (F : Finset G.E), F.card ≤ k → Connected Roots (Edges \ F) v

theorem connectedWithFailure_zero_iff {Roots Edges} :
    ConnectedWithFailure Roots Edges v 0 ↔ Connected Roots Edges v := by
  simp [ConnectedWithFailure]

inductive Path : G.V → Type where
| nil {u} : Path u
| cons {u v} : Path u → u ∈ G.neighbors v → Path v

end Graph
