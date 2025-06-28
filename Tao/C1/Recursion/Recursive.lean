import Tao.C1.Recursion.PartialRecursive

open Peano Set

variable [Inhabited Peano]

/-!
# Recursion Theorem in Peano Arithmetic

This file proves the existence and uniqueness of recursively defined functions
on natural numbers, following Exercise 3.5.12 from Tao's Analysis I.

The main goal is to prove that for any type `X`, initial value `c : X`, and step
function `f : 𝑵 → X → X`, there exists a unique function `g : 𝑵 → X` satisfying:
* `g(0) = c`
* `g(n + 1) = f(n, g(n)) `for all `n ∈ 𝑵`

## Construction Strategy

The proof proceeds in three main stages:
1. *Initial Segments:* We develop a theory of initial segments that partition the natural numbers
   at any given point n, with precise control over the behavior of succession in each part.
2. *Partial Recursive Sequences:* Using initial segments, we show existence of sequences that satisfy
   the recursive definition up to any finite boundary.
3. *Full Recursive Function*: We combine these partial sequences to show existence of the complete
   recursive function and prove its uniqueness.

## Main Results

* `recursive_function_exists`: The existence and uniqueness of recursive functions
* `recursive_function_def`: The canonical construction of recursive functions
* `recursive_function_unique`: The uniqueness property of recursive functions
-/

/-!
## Existence of Recursion

This section combines the previous results to construct the complete
recursive function and establish its properties. This is the culmination
of our development.
-/

namespace Recursive

open PartialRecursive IsInitialSegment
variable {X : Sort*} (n : 𝑵)
variable {X : Sort*} (zero : X) (motive : 𝑵 → X → X)
variable [∀ n, IsInitialSegment n]
variable [SeqOfN : ∀ (n : 𝑵) (zero : X) (motive : 𝑵 → X → X), prf[n;zero;motive]]

/- The canonical recursive function construction. -/
def recursion : 𝑵 → X := fun n ↦ (SeqOfN n zero motive).ofSeq n

/-- Verifies that our construction satisfies the base case. -/
theorem rec_zero {zero : X} {motive : 𝑵 → X → X} : recursion zero motive 0 = zero := zero_eq

/-- Verifies that our construction satisfies the recursive equation. -/
theorem rec_succ {zero : X} {motive : 𝑵 → X → X} :
  recursion zero motive n⁺⁺ = motive n (recursion zero motive n) := by
  rw [recursion, recursive boundary_mem_init, partial_recursive_eq _  boundary_mem_init, recursion]

/-- The uniqueness property of recursive functions. -/
theorem rec_unique {zero : X} {motive : 𝑵 → X → X} {h : 𝑵 → X} (h₁ : h 0 = zero)
  (h₂ : ∀ n, h n⁺⁺ = motive n (h n)) : h = recursion zero motive := by
  ext n
  induction n using Peano.induction with
  | zero => rw [h₁, rec_zero]
  | succ n ih => rw [rec_succ, h₂, ih]

end Recursive

namespace Choice

open PartialRecursive Recursive IsInitialSegment

variable {X : Sort*} (zero : X) (motive : 𝑵 → X → X)

noncomputable scoped instance (n : 𝑵) : IsInitialSegment n := Classical.choice initial_segments_exists

noncomputable scoped instance (n : 𝑵) : prf[n;zero;motive] :=
  Classical.choice (partial_recursive_exists zero motive n)

end Choice
