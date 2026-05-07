import FormalCbgraphs.Completeness
import Mathlib.Tactic.DeriveFintype

@[simp]
theorem Finset.attach_singleton {α} [DecidableEq α] (a : α) :
    attach {a} = {⟨a, mem_singleton_self a⟩} := rfl

lemma Graph.Connected.root_or_exists_edge {G : Graph} {Roots Edges v} :
    G.Connected Roots Edges v → v ∈ Roots ∨ ∃ e ∈ Edges, e.v = v := by
  intro h
  cases h with
  | base _ h => exact Or.inl h
  | step e _ he => exact Or.inr ⟨e, he, rfl⟩

namespace Counterexample

def R : Type :=
  WithTop (Fin 5)
deriving LinearOrder, OrderTop

abbrev R.r0 : R := WithTop.some (0 : Fin 5)
abbrev R.r1 : R := WithTop.some (1 : Fin 5)
abbrev R.r2 : R := WithTop.some (2 : Fin 5)
abbrev R.r3 : R := WithTop.some (3 : Fin 5)
abbrev R.r4 : R := WithTop.some (4 : Fin 5)
abbrev R.infty := (⊤ : WithTop (Fin 5))

def f1 : R → R
| WithTop.some x => if x < 4 then WithTop.some (x + 1) else ⊤
| none => ⊤

def f2 : R → R
| WithTop.some x => if x < 3 then WithTop.some (x + 3) else ⊤
| none => ⊤

def f3 : R → R
| WithTop.some 2 => ⊤
| r => f1 r

example : R.r0 < R.r2 := by decide
example : R.r4 < R.infty := by decide
example : f1 R.r4 = R.infty := rfl
example : f3 R.r0 = R.r1 := rfl

inductive V : Type
| a | b | c | d
deriving DecidableEq

def N : Network R where
  V := V
  neighbors
  | V.a => ∅
  | V.b => {V.a}
  | V.c => {V.a, V.b}
  | V.d => {V.c}
  init
  | V.a => R.r0
  | _ => R.infty
  transfer
  | ⟨V.a, V.b, _⟩
  | ⟨V.b, V.c, _⟩ => f1
  | ⟨V.a, V.c, _⟩ => f2
  | ⟨V.c, V.d, _⟩ => f3

variable {S : Schedule N} (hS : S.Fair)

theorem sem_a : ∀ t, S.sem V.a t = R.r0 := by
  intro t
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => simp [Schedule.sem, N]
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp [N]
    · apply ih
      simp

theorem sem_b : ∀ t, S.sem V.b t = R.infty ∨ S.sem V.b t = R.r1 := by
  intro t
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => simp [Schedule.sem, N]
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp [N, sem_a]
      decide
    · apply ih
      simp

theorem sem_c : ∀ t, S.sem V.c t = R.infty ∨ S.sem V.c t = R.r2 ∨ S.sem V.c t = R.r3 := by
  intro t
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => simp [Schedule.sem, N]
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp only [N, Finset.attach_insert, Finset.attach_singleton, Finset.image_singleton,
        Finset.inf_insert, sem_a, Finset.inf_singleton]
      generalize S.flow ⟨V.b, V.c, _⟩ _ = t'
      rcases sem_b (S := S) t' with h | h <;> simp +decide [h]
    · apply ih
      simp

theorem sem_d : ∀ t, S.sem V.d t = R.infty ∨ S.sem V.d t = R.r4 := by
  intro t
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => simp [Schedule.sem, N]
  | succ t =>
    simp [Schedule.sem]
    split_ifs
    · simp only [N, Finset.attach_singleton, Finset.inf_singleton]
      generalize S.flow ⟨V.c, V.d, _⟩ _ = t'
      rcases sem_c (S := S) t' with h | h | h <;> simp +decide [h]
    · apply ih
      simp

section

include hS

theorem sem_b_converge : ∃ T, ∀ t ≥ T, S.sem V.b t = R.r1 := by
  rcases hS.2 ⟨V.a, V.b, by simp [N]⟩ 0 with ⟨T₁, -, h₁⟩
  rcases hS.1 V.b (T₁ + 1) with ⟨T₂, hT₂, h₂⟩
  exists T₂
  intro t ht
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => grind
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp +decide [N, sem_a]
    · apply ih <;> grind

theorem sem_c_converge : ∃ T, ∀ t ≥ T, S.sem V.c t = R.r2 := by
  rcases sem_b_converge hS with ⟨T₁, h₁⟩
  rcases hS.2 ⟨V.b, V.c, by simp [N]⟩ T₁ with ⟨T₂, hT₂, h₂⟩
  rcases hS.1 V.c (T₂ + 1) with ⟨T₃, hT₃, h₃⟩
  exists T₃
  intro t ht
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => grind
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp only [N, Finset.attach_insert, Finset.attach_singleton, Finset.image_singleton,
        Finset.inf_insert, sem_a, Finset.inf_singleton]
      generalize ht' : S.flow ⟨V.b, V.c, _⟩ _ = t'
      simp +decide [h₁ t' (by rw [← ht']; apply h₂; grind)]
    · apply ih <;> grind

theorem sem_d_converge : ∃ T, ∀ t ≥ T, S.sem V.d t = R.infty := by
  rcases sem_c_converge hS with ⟨T₁, h₁⟩
  rcases hS.2 ⟨V.c, V.d, by simp [N]⟩ T₁ with ⟨T₂, hT₂, h₂⟩
  rcases hS.1 V.d (T₂ + 1) with ⟨T₃, hT₃, h₃⟩
  exists T₃
  intro t ht
  induction t using Nat.strong_induction_on with | _ t ih
  cases t with
  | zero => grind
  | succ t =>
    simp only [Schedule.sem]
    split_ifs
    · simp only [N, Finset.attach_singleton, Finset.inf_singleton]
      generalize ht' : S.flow ⟨V.c, V.d, _⟩ _ = t'
      simp +decide [h₁ t' (by rw [← ht']; apply h₂; grind)]
    · apply ih <;> grind

end

theorem incomplete : ∃ Y, N.IsEventualStable Y ∧ IsEmpty (VC N Y) := by
  let Y : N.V → R → Prop | V.d, s => s = R.infty | _, _ => True
  refine ⟨Y, ?_, ?_⟩
  · intro S hS v
    cases v with
    | a | b | c => simp [Y]
    | d => simp only [Y]; exact sem_d_converge hS
  · by_contra! ⟨vc⟩
    let S := N.syncSchedule
    have hS : S.Fair := N.fair_syncSchedule
    have hc : vc.Q V.c R.r2 := by
      rcases vc.connected_cbgraph hS V.c with ⟨T, h⟩
      rcases sem_c_converge hS with ⟨T', h'⟩
      grind [h (max T T'), h' (max T T')]
    have hd : vc.I V.d R.r4 := by
      convert vc.invariance (S := S) V.d 2
      decide +kernel
    have hd' : ¬ vc.Q V.d R.r4 := by
      intro h
      apply vc.property at h
      revert h
      decide
    rcases (vc.connected V.d).root_or_exists_edge with h | ⟨e, h, he⟩
    · apply hd'
      convert vc.cbroot (S := S) _ h 2 (by simp)
      decide +kernel
    · rcases e with ⟨u, _, hu⟩
      subst he
      simp only [N, Finset.mem_singleton] at hu
      subst hu
      exact hd' (vc.edge _ h _ _ hc hd)
