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
in big endian (most significant bit at the end)
that are divisible by 3:
-/
abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}

inductive Q_div3 : Type
-- *Insert* your states here
-- e.g. | q0 | q1 | ...
deriving Fintype, DecidableEq
open Q_div3

abbrev A_div3 : DFA SigmaBin :=
  -- *Insert* your definition of the automaton here.
  {   Q := sorry
      s := sorry
      F := sorry
      δ := sorry
  }

-- You don't have to prove this
lemma div3_lem : div3 = L A_div3 := by sorry

-- test cases
-- example : [ 0 , 1, 1 ] ∈ L A_div3 := by simp [δ_star]
-- example : [ 1 , 0, 0, 1 ] ∈ L A_div3 := by simp [δ_star]
-- example : [ 1 ] ∉ L A_div3 := by simp [δ_star]
-- example : [ 0, 0 , 1 ] ∉ L A_div3 := by simp [δ_star]

end ex_div3

namespace ex3_6

open Nfa NFA

-- 2) translating an NFA to a DFA (50%)

/-
Formalise the NFA depicted in the exercise
description on Moodle:
-/
inductive Q3_6_nfa : Type
-- *Insert* your states here
-- e.g. | q0 | q1 | ...
deriving Fintype, DecidableEq
open Q3_6_nfa

abbrev A3_6_nfa : NFA SigmaBin :=
  -- *insert* your definition of the automaton here.
  {   Q := sorry
      S := sorry
      F := sorry
      δ := sorry
  }

-- test cases
-- example : [ 1 , 0 ] ∈ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
-- example : [ 1 , 1 , 0 , 0 , 1, 0 ] ∈ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
-- example : [] ∉ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]
-- example : [ 1 , 1 , 0, 1] ∉ L A3_6_nfa := by simp [Nfa.L,Nfa.δ_star,δ_step]

/-
Now, using the subset construction, translate
this into a DFA recginzing the same language.
-/
inductive Q3_6_dfa : Type
-- *Insert* your states here
-- e.g. | q0 | q1 | ...
deriving Fintype, DecidableEq
open Q3_6_dfa

abbrev A3_6_dfa : DFA SigmaBin :=
  -- *insert* your definition of the automaton here.
  {   Q := sorry
      s := sorry
      F := sorry
      δ := sorry
  }

-- test cases
-- example : [ 1 , 0 ] ∈ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
-- example : [ 1 , 1 , 0 , 0 , 1, 0 ] ∈ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
-- example : [] ∉ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]
-- example : [ 1 , 1 , 0, 1] ∉ L A3_6_dfa := by simp [Dfa.L,Dfa.δ_star]

-- specification
theorem A3_6_ok : L A3_6_nfa = L A3_6_dfa
:= sorry
-- you don't need to prove this.


#eval "<!autograder!> SUBMISSION: 2 7846919"
