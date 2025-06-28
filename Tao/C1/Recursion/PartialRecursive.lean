import Tao.C1.Recursion.InitialSegment

open Peano IsInitialSegment

variable [Inhabited Peano]


/-!
## Partial Recursive Sequences

A partial recursive sequence is a function that satisfies the recursive definition
up to a given boundary point `N`. These sequences form the building blocks for
constructing the complete recursive function.
-/

class PartialRecursive {X : Sort*} (N : 𝑵) [IsInitialSegment N] (c : X) (f : 𝑵 → X → X) where
  ofSeq : 𝑵 → X
  zero_eq : ofSeq 0 = c
  recursive : ∀ {m}, m⁺⁺ ∈ A[N] → ofSeq m⁺⁺ = f m (ofSeq m)

notation "prf[" N ";" c ";" f "]" => PartialRecursive N c f

/-!
### Existence of Partial Recursive Sequences

This section shows the existence of partial recursive sequences for any natural number.
This is done in three steps:
1. Base case: Constructing a partial recursive sequence at zero
2. Inductive step: Extending an partial recursive sequence from n to n+1
3. General existence: Combining these to prove existence for all numbers
-/

namespace PartialRecursive

variable {X : Sort*} (N : 𝑵) (c : X) (seq : 𝑵 → X) (f : 𝑵 → X → X)
variable [IsInitialSegment N] [IsInitialSegment N⁺⁺]

/-- A partial recursive sequence for N = 0 -/
def partial_recursive_zero [IsInitialSegment 0] : prf[0;c;f] where
  ofSeq := fun _ ↦ c
  zero_eq := rfl
  recursive h := False.elim <| axiom_2_3 (initial_zero_eq ▸ h)

/-- The following definition allows us to extends a sequence from N to N + 1 -/
def extend [DecidableEq 𝑵] : 𝑵 → X := fun m ↦ if m = N⁺⁺ then f N (seq N) else seq m

/-- The extended sequence of a partial recursive sequence is also a partial recursive sequence -/
def partial_recursive_succ [DecidableEq 𝑵] (prev : prf[N;c;f]) : prf[N⁺⁺;c;f] where
  ofSeq := extend N prev.ofSeq f
  zero_eq := by rw [extend, if_neg axiom_2_3.symm, prev.zero_eq]
  recursive {n} h_mem := by
    rw [← mem_trans_succ] at h_mem
    simp_rw [extend, if_neg (mem_init_not_succ_boundary h_mem), succ_succ_eq_iff]
    split_ifs with h
    rw [h]
    exact prev.recursive (init_closed h_mem h)

/-  The main existence theorem for partial recursive sequences.
    Shows that for any boundary N, there exists a sequence satisfying
    the recursive definition up to that point. -/
theorem partial_recursive_exists (N : 𝑵) [∀ n, IsInitialSegment n] : Nonempty (prf[N;c;f]) := by
  classical
  induction N using Peano.induction with
  | zero => exact ⟨partial_recursive_zero c f⟩
  | succ N ih =>
    obtain ⟨seq⟩ := ih
    exact ⟨seq.partial_recursive_succ⟩

lemma partial_recursive_eq {n : 𝑵} {c : X} {f : 𝑵 → X → X}
  {seq₁ : prf[N⁺⁺;c;f]} {seq₂ : prf[N;c;f]} (h : n ∈ A[N]) : seq₁.ofSeq n = seq₂.ofSeq n := by
  induction n using Peano.induction with
  | zero => rw [zero_eq, zero_eq]
  | succ n ih =>
    rw [recursive <| mem_trans_succ.mp (pred_in_init h), recursive h, ih (pred_in_init h)]

end PartialRecursive
