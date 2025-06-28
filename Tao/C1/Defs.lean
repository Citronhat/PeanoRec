import Mathlib.Tactic

/-!
# Natural Numbers: Basic Definitions and Axioms

This file formalizes the definitions of Section 2.1 of Terence Tao's Analysis I,
which introduces the natural numbers via Peano's axioms.

## Core Definitions
* `Peano` - A structure encapsulating the Peano axioms for natural numbers
* `def_2_1_3` - Natural numbers as Arabic numerals

## Additional Definitions
* `𝑵` - Notation for the type of Peano natural numbers
* `n⁺⁺` - Postfix notation for the successor function.
-/

/-- The Peano structure encapsulates Peano's axioms for natural numbers. -/
structure Peano where
  /-- The type of natural numbers -/
  natural : Type*

  /-- Axiom 2.1: There exists a natural number called zero -/
  zero : natural

  /-- Axiom 2.2: Every natural number has a successor -/
  successor : natural → natural

  /-- Axiom 2.3: Zero is not the successor of any natural number -/
  zero_not_successor : ∀ n : natural, successor n ≠ zero

  /-- Axiom 2.4: Different natural numbers must have different successors (injectivity) -/
  successor_injective : ∀ {n m : natural}, successor n = successor m → n = m

  /-- Axiom 2.5: The principle of mathematical induction -/
  principle_of_induction : ∀ {P : natural → Prop},
    P zero → (∀ n : natural, P n → P (successor n)) →
    ∀ n : natural, P n

namespace Peano

variable [Inhabited Peano]

/-- The type of Peano natural numbers. -/
notation "𝑵" => Peano.natural default

/--
Successor function for Peano natural numbers.
This is a convenience wrapper around the successor function from the Peano structure.
-/
def succ : 𝑵 → 𝑵 := successor _

/--
Postfix notation for the successor function.
This allows writing n⁺⁺ instead of succ n.
-/
postfix:max "⁺⁺" => succ

/--
Implementation of natural number literals for Peano numbers.
This allows writing numbers like 0, 1, 2 directly as Peano numbers.
-/

instance def_2_1_3 {n} : OfNat 𝑵 n where
  ofNat := Nat.recOn n (zero _) (fun _ ih ↦ ih⁺⁺)

end Peano
