 /-
COMP2012 (LAC) 2026

Exercise 2

This exercise consists of 2 parts. In part 1,
define a DFA accepting the language of binary
words representing numbers divisible by 3.
In part 2, formalise the NFA in the description
of this exercise on Moodle, and give an
equivalent DFA.

Don't change anything else in this file!
-/

import Proofs.Lang
import Proofs.Autom

open Lang Lang.Examples SigmaABC Dfa DFA

namespace ex_div3

-- 1) defining a DFA (50%)

/-
Define a DFA that recognizes all binary numbers
in little endian (most significant bit at the end)
that are divisible by 3:
-/
abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}

-- N mod 3 will always be 0, 1, or 2
inductive Q_div3 : Type
| q0 | q1 | q2
deriving Fintype, DecidableEq
open Q_div3

abbrev A_div3 : DFA SigmaBin :=
  {   Q := Q_div3
      s := q0  --start with rem=0
      F := {q0} -- Must finish with rem=0 to be divisible
      δ := λ | q0, 0 => q0
             | q0, 1 => q1
             | q1, 0 => q2
             | q1, 1 => q0
             | q2, 0 => q1
             | q2, 1 => q2
  }

-- You don't have to prove this
lemma div3_lem : div3 = L A_div3 := by sorry

-- test cases
example : [ 0 , 1, 1 ] ∈ L A_div3 := by simp [δ_star]
example : [ 1 , 0, 0, 1 ] ∈ L A_div3 := by simp [δ_star]
example : [ 1 ] ∉ L A_div3 := by simp [δ_star]
example : [ 0, 0 , 1 ] ∉ L A_div3 := by simp [δ_star]

end ex_div3

namespace ex3_6

open Nfa NFA

-- 2) translating an NFA to a DFA (50%)

/-
Formalise the NFA depicted in the exercise
description on Moodle:
-/
inductive Q3_6_nfa : Type
| q0 | q1 | q2 | q3 | q4
deriving Fintype, DecidableEq
open Q3_6_nfa

abbrev A3_6_nfa : NFA SigmaBin :=
  {   Q := Q3_6_nfa
      S := {q0}
      F := {q4}
      δ := λ | q0, 0 => {q2}
             | q0, 1 => {q1,q3}
             | q1, 0 => {}
             | q1, 1 => {q0}
             | q2, 0 => {q0}
             | q2, 1 => {}
             | q3, 0 => {q4}
             | q3, 1 => {}
             | q4, _ => {}
  }

-- test cases
example : [ 1 , 0 ] ∈ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
example : [ 1 , 1 , 0 , 0 , 1, 0 ] ∈ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
example : [] ∉ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
example : [ 1 , 1 , 0, 1] ∉ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]

/-
Now, using the subset construction, translate
this into a DFA recginzing the same language.
-/
-- {q0} => d0
-- {q2} => d1
-- {q1, q3} => d2
-- {q4} => d3
-- {} => d4
inductive Q3_6_dfa : Type
| d0 | d1 | d2 | d3 | d4
deriving Fintype, DecidableEq
open Q3_6_dfa

abbrev A3_6_dfa : DFA SigmaBin :=
  {   Q := Q3_6_dfa
      s := d0
      F := {d3}
      δ := λ | d0, 0 => d1
             | d0, 1 => d2
             | d1, 0 => d0
             | d1, 1 => d4
             | d2, 0 => d3
             | d2, 1 => d0
             | d3, _ => d4
             | d4, _ => d4
  }

-- test cases
example : [ 1 , 0 ] ∈ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
example : [ 1 , 1 , 0 , 0 , 1, 0 ] ∈ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
example : [] ∉ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
example : [ 1 , 1 , 0, 1] ∉ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]

-- specification
theorem A3_6_ok : L A3_6_nfa = L A3_6_dfa
:= sorry
-- you don't need to prove this.


#eval "<!autograder!> SUBMISSION: 2 7846919"
