import Tao.C1.Main

open Peano Set

/-!
# Initial Segments

An initial segment at `n` partitions the natural numbers into two sets:
* An initial set containing numbers up to `n`
* A tail set containing numbers after `n`

These segments provide precise control over succession, which is essential
for our recursive construction. The key properties ensure that:
* The initial set is closed under succession up to `n`
* The tail set is closed under succession
* The boundary point `n` belongs to the initial set but `n` belongs to the tail.
-/

/-!
## Definition of Initial Segments

An initial segment of natural numbers consists of two disjoint sets `A` and `B`,
where `A` contains all numbers up to `n` and `B` contains all numbers after `n`.
-/

variable [Inhabited Peano]


class IsInitialSegment (n : 𝑵) where
  A : Set 𝑵
  B : Set 𝑵
  disjoint : A ∩ B = ∅
  complete : A ∪ B = univ
  zero_mem_init : 0 ∈ A
  succ_boundry_mem_tail : n⁺⁺ ∈ B
  tail_closed {m : 𝑵} (h : m ∈ B) : m⁺⁺ ∈ B
  init_closed {m : 𝑵} (h_mem : m ∈ A) (h_neq : m ≠ n) : m⁺⁺ ∈ A

def SetA (n : 𝑵) [IsInitialSegment n] : Set 𝑵 := ‹IsInitialSegment n›.A
def SetB (n : 𝑵) [IsInitialSegment n] : Set 𝑵 := ‹IsInitialSegment n›.B

namespace IsInitialSegment

scoped notation "A["n"]" => SetA n
scoped notation "B["n"]" => SetB n

/-!
### Basic Properties of Initial Segments

This section establishes fundamental properties of initial segments:
* Closure properties for both the initial and tail sets
* Complementation relationships between the sets
* Behavior at and around the boundary point
* Uniqueness properties for segments with the same boundary
-/

section Properties

variable {N m : 𝑵} {Init : IsInitialSegment N}

/-- The complement of the initial segment is exactly the tail segment -/
lemma init_tail_compl : A[N]ᶜ = B[N] := compl_unique disjoint complete

/-- A number is in the initial segment if and only if it's not in the tail segment -/
lemma mem_init_iff_not_tail : m ∉ B[N] ↔ m ∈ A[N] := init_tail_compl ▸ not_mem_compl_iff

/-- A number is in the tail segment if and only if it's not in the initial segment -/
lemma mem_tail_iff_not_init : m ∉ A[N] ↔ m ∈ B[N] := not_iff_comm.mpr mem_init_iff_not_tail

/-- The successor of the boundary point is not in the initial segment -/
lemma boundary_succ_not_init : N⁺⁺ ∉ A[N] := mem_tail_iff_not_init.mpr succ_boundry_mem_tail

/-- The boundary point belongs to the initial segment -/
lemma boundary_mem_init : N ∈ A[N] := by
  /- If m is in A and m⁺⁺ is not, then m must be the boundary -/
  have boundary_character {m : 𝑵} (h_mem : m ∈ A[N]) (h_succ_not : m⁺⁺ ∉ A[N]) : m = N := by
    contrapose! h_succ_not
    exact init_closed h_mem h_succ_not

  /- There exists some point where we transition from A to B -/
  obtain ⟨i, h_mem, h_succ_not⟩ : ∃ w, w ∈ A[N] ∧ w⁺⁺ ∉ A[N] := by
    by_contra! h
    have all_in_A {i : 𝑵} : i ∈ A[N] := by
      induction i using Peano.induction with
      | zero => exact zero_mem_init
      | succ k ih => exact h k ih
    exact boundary_succ_not_init all_in_A

  exact boundary_character h_mem h_succ_not ▸ h_mem

/-- The boundary point is not in the tail segment -/
lemma boundary_not_mem_tail : N ∉ B[N] := mem_init_iff_not_tail.2 boundary_mem_init

/-- If a successor is in the initial segment, so is its predecessor -/
lemma pred_in_init {m : 𝑵} (h_succ : m⁺⁺ ∈ A[N]) : m ∈ A[N] := by
  contrapose h_succ
  rw [mem_tail_iff_not_init] at h_succ ⊢
  exact tail_closed h_succ

/-- No element in the initial segment equals the successor of the boundary -/
lemma mem_init_not_succ_boundary (h_mem : m ∈ A[N]) : m ≠ N⁺⁺ :=
  fun h_eq ↦ boundary_succ_not_init (h_eq ▸ h_mem)

/-- Characterization of when a successor belongs to the initial segment -/
lemma succ_mem_init_iff : m⁺⁺ ∈ A[N] ↔ m ∈ A[N] ∧ m ≠ N := by
  apply Iff.intro
  · exact fun h ↦ ⟨pred_in_init h, fun h' ↦ boundary_succ_not_init (h' ▸ h)⟩
  · exact fun ⟨h_mem, h_neq⟩ ↦ init_closed h_mem h_neq

/-- Characterization of membership in the initial segment -/
lemma mem_init_iff : m ∈ A[N] ↔ m⁺⁺ ∈ A[N] ∨ m = N := by
  rw [succ_mem_init_iff, and_or_right, or_iff_left_of_imp, and_iff_left_iff_imp.2]
  · exact fun a ↦ ne_or_eq m N
  · exact fun h ↦ h ▸ Init.boundary_mem_init

variable [Init₁ : IsInitialSegment N] (Init₂ : IsInitialSegment N)

local notation "A₁["n"]" => @SetA _ n Init₁
local notation "A₂["n"]" => @SetA _ n Init₂

/-- Initial segments with the same boundary have subset relationship -/
lemma init_subset_of_same_boundary : A₁[N] ⊆ A₂[N] := by
  intro m h_mem
  induction m using Peano.induction with
  | zero => exact Init₂.zero_mem_init
  | succ m ih =>
    rw [Init₁.succ_mem_init_iff] at h_mem
    exact Init₂.init_closed (ih h_mem.1) h_mem.2

/-- Initial segments with the same boundary are equal -/
lemma init_subset_of_same_boundary_unique : A₁[N] = A₂[N] :=
  le_antisymm (Init₁.init_subset_of_same_boundary _) (Init₂.init_subset_of_same_boundary _)

end Properties

/-!
### Existence of Initial Segments

This section establishes the existence of initial segments for natural numbers.

The construction proceeds in three steps:
1. Base case: Constructing the initial segment at zero
2. Inductive step: Extending an initial segment from n to n+1
3. General existence: Proving existence for all natural numbers
-/

section Existence

variable {N n : 𝑵}

/-- The initial segment at zero, partitioning 𝑵 into {0} and its complement.
This forms the base case for our construction. -/
def init_zero : IsInitialSegment 0 where
  A:= {0}
  B:= {0}ᶜ
  disjoint := inter_compl_self _
  complete := union_compl_self _
  zero_mem_init := rfl
  succ_boundry_mem_tail := notMem_singleton_iff.mp axiom_2_3
  tail_closed {_ _} := notMem_singleton_iff.mpr axiom_2_3
  init_closed {_ h₁ h₂} := (h₂ h₁).elim

/-- Given an initial segment at n, constructs an initial segment at n+1
by adding n+1 to the initial set. -/
def init_succ [IsInitialSegment N] : IsInitialSegment N⁺⁺ where
  A := A[N] ∪ {N⁺⁺}
  B := (A[N] ∪ {N⁺⁺})ᶜ
  disjoint := inter_compl_self _
  complete := union_compl_self _
  zero_mem_init := mem_union_left _ zero_mem_init
  succ_boundry_mem_tail := by
    rw [compl_union, init_tail_compl]
    exact ⟨tail_closed succ_boundry_mem_tail, mem_compl_singleton_iff.2 succ_succ_neq_nat⟩
  tail_closed {m} h := by
    rw [compl_union, init_tail_compl] at h ⊢
    apply mem_inter (tail_closed h.1) _
    rw [mem_compl_singleton_iff, succ_succ_neq_iff]
    exact fun h₂ ↦ boundary_not_mem_tail (h₂ ▸ h.1)
  init_closed {m} h₁ h₂ := by
    rw [mem_union, mem_singleton_iff, succ_succ_eq_iff, ← mem_init_iff]
    cases h₁ with
    | inl h => exact h
    | inr h => exact False.elim (h₂ h)

/-- Proves that every natural number admits an initial segment. -/
theorem initial_segments_exists : Nonempty (IsInitialSegment n) := by
  induction n using Peano.induction with
  | zero => exact ⟨init_zero⟩
  | succ m ih =>
    obtain ⟨init⟩ := ih
    exact ⟨init.init_succ⟩

end Existence

section Properties

variable {N : 𝑵} [IsInitialSegment N⁺⁺] [IsInitialSegment N]

/-- The canonical initial segment at zero is exactly {0}. -/
lemma initial_zero_eq [IsInitialSegment 0] : A[0] = {0} :=
  init_subset_of_same_boundary_unique init_zero

/-- The canonical initial segment at n+1 is obtained by adding n+1 to the initial segment at n. -/
lemma initial_succ_eq_iff : A[N⁺⁺] = A[N] ∪ {N⁺⁺} := init_subset_of_same_boundary_unique init_succ

/-- Membership in successive initial segments corresponds exactly:
m ∈ I[ n ] if and only if m⁺⁺ ∈ I[ n⁺⁺ ]. -/
lemma mem_trans_succ {m : 𝑵} : m ∈ A[N] ↔ m⁺⁺ ∈ A[N⁺⁺] := by
  rw [initial_succ_eq_iff, mem_init_iff, mem_union, mem_singleton_iff, succ_succ_eq_iff]

end Properties

end IsInitialSegment
