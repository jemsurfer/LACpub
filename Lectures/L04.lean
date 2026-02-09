/-
Languages and Computation (COMP2012) 25-26
L04 : DFAs

-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Proofs.Lang

namespace Dfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure DFA : Type 1 where
  Q : Type
  [alphQ : Alphabet Q]
  s : Q
  F : Finset Q
  δ : Q → Sigma → Q

variable {Sigma : Type}[Alphabet Sigma]

variable (A : DFA Sigma)

def δ_star : A.Q → Word Sigma → A.Q
| q , [] => q
| q , (x :: w) => δ_star (A.δ q x) w

abbrev L : Lang Sigma
:= { w | δ_star A A.s w ∈ A.F }

end Dfa

namespace DFAex

open Lang
open Lang.Examples
open Dfa
--open DFA
open SigmaABC

abbrev A₁ : DFA SigmaABC
:= {
  Q := Fin 2
  s := 0
  F := { 1 }
  δ := λ | 0 , a => 1
         | 0 , _ => 0
         | 1 , _ => 1
}

example : [a,b,a] ∈ L A₁ := by aesop
example : [b,b] ∉ L A₁ := by sorry

abbrev A₂ : DFA SigmaABC
:= {
  Q := Fin 3
  s := 0
  F := { 0 , 1 }
  δ := λ | 0 , a => 0
         | 0 , b => 1
         | 0 , c => 2
         | 1 , b => 1
         | 1 , _ => 2
         | 2 , _ => 2
}

example : [a,a,b,b] ∈ L A₂ := by aesop
example : [a,b,a] ∉ L A₂ := by sorry

-- exercise : Ldiv3 : Lang (Fin 2)
-- define an automaton for this.

end DFAex
