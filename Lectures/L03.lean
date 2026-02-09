/-
Languages and Computation (COMP2012) 25-26
L03 : Operations on languages

-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Lectures.L02
set_option linter.unusedSectionVars false

section LangOps

variable {Sigma : Type}[Alphabet Sigma]

abbrev concat(L₁ L₂ : Lang Sigma)
:= { w ++ v | (w ∈ L₁)(v ∈ L₂)}

abbrev concat'(L₁ L₂ : Lang Sigma)
| x => ∃ w v , w ∈ L₁ ∧ v ∈ L₂ ∧ x = w ++ v

infix: 70 " ⋅ " => concat

def ε : Lang Sigma := { [] } -- \Ge = ε , \epsilon = ε

open Nat

-- def lpow : Lang Sigma → ℕ → Lang Sigma
-- | _ , zero => ε
-- | L , succ n => L ⋅ lpow L n

instance : HPow (Lang Sigma) ℕ (Lang Sigma) where
  hPow := lpow
where
  lpow : Lang Sigma → ℕ → Lang Sigma
  | _, 0     => ε
  | L, n+1   => L ⋅ lpow L n

def star (L : Lang Sigma) : Lang Sigma
:= { w | ∃ n : ℕ , w ∈ L ^ n}

postfix : 100 " * " => star


end LangOps


-- ·  ⋅
namespace LangOpsEx
variable (Sigma : Type)[Alphabet Sigma]

open Examples
open SigmaABC

abbrev L₁ : Lang SigmaABC
:= {[a],[a,a],[a,a,a]}
abbrev L₂ : Lang SigmaABC
:= {[a],[b,c]}

abbrev L₃ : Lang SigmaABC
:= L₁ ∪ L₂ -- \cup

example : L₃ = {[a],[a,a],[a,a,a],[b,c]} := by aesop

abbrev L₄ : Lang SigmaABC
:= L₁ ∩ L₂ -- \cap

abbrev L₅ := L₁ ⋅ L₂ -- concat L₁ L₂

example : L₅ =  { [a,a], [a,b,c], [a,a,a], [a,a,b,c],
                  [a,a,a,a], [a,a,a,b,c] } := by aesop

#check (∅ : Lang SigmaABC)

open Nat

def lpow : Lang Sigma → ℕ → Lang Sigma
| _ , zero => ε
| L , succ n => L ⋅ lpow L n

instance : HPow (Lang Sigma) ℕ (Lang Sigma) where
  hPow := lpow
where
  lpow : Lang Sigma → ℕ → Lang Sigma
  | _, 0     => ε
  | L, n+1   => L ⋅ lpow L n

def star (L : Lang Sigma) : Lang Sigma
:= { w | ∃ n : ℕ , w ∈ L ^ n}

postfix : 100 " * " => star

-- algebra
-- (L₁ ∪ L₂) ∪ L₃ = L₁ ∪ (L₂ ∪ L₃) -- associativity
-- L₁ ∪ L₂ = L₂ ∪ L₁-- commutativity
-- L₁ ∪ ∅ = L₁ -- ∅ is neutral
-- commutative monoid
-- L₁ ∪ L₁ = L₁ , idempotent

-- concat
-- (L₁ ⋅ L₂) ⋅ L₃ = L₁ ⋅ (L₂ ⋅ L₃)
-- L₁ ⋅ L₂ = L₂ ⋅ L₁ -- not true
-- L₁ ⋅ ε = L₁ = ε ⋅ L₁
-- monoid

-- L₁ ⋅ ∅ = ∅ = ∅ ⋅ L₁
-- L₁ ⋅ (L₂ ∪ L₃) = L₁ ⋅ L₂ ∪ L₁ ⋅ L₃
-- (L₁ ∪ L₂) ⋅ L₃ = L₁ ⋅ L₃ ∪ L₂ ⋅ L₃
-- semiring

-- + Law for star : Kleene algebra

#check (L₂ ^ 2 : Lang SigmaABC)

#check (L₂ * : Lang SigmaABC)

end LangOpsEx
