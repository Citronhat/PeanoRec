import Tao.C1.Defs

/-!
# Natural Numbers: Properties and Theorems

This file proves the main results from Section 2.1 of Terence Tao's Analysis I,
along with additional useful properties of Peano natural numbers.

## Core Theorems
* `axiom_2_3` - Zero is not a successor
* `axiom_2_4` - Successor function is injective
* `axiom_2_5` - Principle of mathematical induction
* `prop_2_1_6` - Four is not zero
* `prop_2_1_8` - Six is not two
* `prop_2_1_11` - A more practical form of induction

## Additional Theorems
* `succ_succ_eq_iff` - Equivalence between equality of successors
* `succ_succ_neq_iff` - Equivalence between inequality of successors
* `succ_succ_neq_nat` - No number equals its own successor
-/

namespace Peano

variable [Inhabited Peano]

/-!
### Core Theorems from Tao's Analysis I

This section contains the main results as presented in the textbook,
following the same numbering scheme.
-/

section Core

/-- Zero is not the successor of any natural number -/
theorem axiom_2_3 {n : 𝑵} : n⁺⁺ ≠ 0 := zero_not_successor _ _
alias zero_not_succ := axiom_2_3

/-- The successor function is injective. -/
theorem axiom_2_4 {n m : 𝑵} (h : n⁺⁺ = m⁺⁺) : n = m := successor_injective _ h
alias succ_injective := axiom_2_4

/-- The principle of mathematical induction for Peano numbers. -/
theorem axiom_2_5 : ∀ {P : 𝑵 → Prop},
  P 0 → (∀ n : 𝑵, P n → P (n⁺⁺)) → (∀ m : 𝑵, P m) := principle_of_induction _

/-- Four is not equal to zero -/
theorem prop_2_1_6 : (4 : 𝑵) ≠ 0 := by
  change 3⁺⁺ ≠ 0
  exact axiom_2_3

/-- Six is not equal to two. -/
theorem prop_2_1_8 : (6 : 𝑵) ≠ 2 := by
  intro h
  have h₁ : (5 : 𝑵) = 1 := axiom_2_4 h
  have h₂ : (4 : 𝑵) = 0 := axiom_2_4 h₁
  exact axiom_2_3 h₂

/-- A more convenient form of the induction principle. -/
@[elab_as_elim]
theorem prop_2_1_11 {P : 𝑵 → Prop} (zero : P 0) (succ : ∀ n, P n → P n⁺⁺) (n : 𝑵) : P n :=
  axiom_2_5 zero succ n
alias induction := prop_2_1_11

end Core

/-!
### Additional Theorems

This section contains useful additional properties of Peano natural numbers
that complement the core theorems.
-/

section Additional

variable {n m : 𝑵}

/-- The successor function preserves equality in both directions. -/
@[simp] theorem succ_succ_eq_iff : n⁺⁺ = m⁺⁺ ↔ n = m :=
  ⟨fun h ↦ axiom_2_4 h, fun h ↦ h ▸ rfl⟩

/-- The successor function preserves inequality in both directions. -/
@[simp] theorem succ_succ_neq_iff : n⁺⁺ ≠ m⁺⁺ ↔ n ≠ m :=
  not_iff_not.mpr succ_succ_eq_iff

/-- No natural number equals its own successor. -/
theorem succ_succ_neq_nat : n⁺⁺ ≠ n := by
  induction n using Peano.induction with
  | zero => exact axiom_2_3
  | succ m ih => rwa [succ_succ_neq_iff]

end Additional

end Peano
