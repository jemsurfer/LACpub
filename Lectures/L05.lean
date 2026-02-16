/-
Languages and Computation (COMP2012) 25-26
L05 : NFAs

-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Powerset
import Proofs.Lang

namespace Dfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure DFA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  s : Q    -- initial state
  F : Finset Q -- set of final states
  δ : Q → Sigma → Q

variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)
attribute [instance] DFA.alphQ

def δ_star : A.Q → Word Sigma → A.Q
| q , [] => q
| q , (x :: w) => δ_star (A.δ q x) w

abbrev L : Lang Sigma
:= { w | δ_star A A.s w ∈ A.F} -- with A

end Dfa

namespace DfaEx
open Lang Lang.Examples SigmaABC Dfa

abbrev A₁ : DFA SigmaABC
:= {
  Q := Fin 2
  s := 0
  F := { 1 }
  δ := λ | 0 , a => 1
         | 0 , _ => 0
         | 1 , _ => 1
}

example : [a,b] ∈ L A₁ := by simp [δ_star]
example : [b,b] ∉ L A₁ := by simp [δ_star]

-- Simulate at: https://www.automataverse.com/simulator

end DfaEx

namespace Nfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure NFA : Type 1 where
  Q : Type
  [alphQ : Alphabet Q]
  S : Finset Q
  F : Finset Q
  δ : Q → Sigma → Finset Q

attribute [instance] NFA.alphQ

variable {Sigma : Type}[Alphabet Sigma]
variable (A : NFA Sigma)

macro "⟪" q:ident " | " P:term "⟫" : term =>
  `( (Finset.univ).filter (fun $q => $P) )
macro "⟪" q:ident " ∈ " xs:term " | " P:term "⟫" : term =>
  `( ($xs).filter (fun $q => $P) )

def δ_step (A : NFA Sigma) (S : Finset A.Q) (a : Sigma) : Finset A.Q :=
  ⟪ q | ∃ p ∈ S, q ∈ A.δ p a ⟫

def δ_star : Finset A.Q → Word Sigma → Finset A.Q
| S, []      => S
| S, x :: w  => δ_star (δ_step A S x) w

def L : Lang Sigma
:= { w : Word Sigma |
      ∃ q : A.Q ,
      q ∈ A.F ∩ δ_star A A.S w }

namespace NfaEx
open Nfa Lang Lang.Examples SigmaABC

def A_1x : NFA SigmaABC
:= { Q := Fin 3
     S := { 0 }
     F := { 2 }
     δ := λ | 0 , a => {0,1}
            | 0 , _ => {0}
            | 1,  _  => {2}
            | _ , _ => {}
}

example : [a, b] ∈ L A_1x := by simp [L,δ_star,δ_step]; decide
example : [a,b,b] ∉ L A_1x := by simp [L,δ_star,δ_step]; decide

end NfaEx
