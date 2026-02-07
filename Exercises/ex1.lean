 /-
COMP2012 (LAC) 2025

Exercise 1

Enumerate the finite languages below by
replacing the sorrys by a finite set.

Don't change anything else in this file!
-/


--import LACNotes.Lectures.L02
import Proofs.Lang

open Lang
open Lang.Examples

open SigmaABC

namespace ex1
def L1 : Lang SigmaABC
:= { [] , [b], [a,c] }
def L2 : Lang SigmaABC
:= { [a] , [b] , [c,a]}

/- Example -/
def E0 : Lang SigmaABC
:= L1 ∩ L2

def E0_enum : Finset (Word SigmaABC)
--:= sorry
:= { [b] }
-- answer the question by replacing
-- sorry by the finite set.

example : E0 = E0_enum
:= by
    dsimp [E0,E0_enum,L1,L2]
    aesop
-- you don't have to prove the exercise

-------------------------
-- Exercises start here!
-- For each Ei_enum, replace sorry by
-- the finite set that is the language
-- Ei. You don't need to prove that
-- Ei = Ei_enum, but it is a nice challenge.
-------------------------

def E1 : Lang SigmaABC
:= { w | w.length <= 2 ∧ a ∈ w }

def E1_enum : Finset (Word SigmaABC)
:= { [a], [a,a], [a,b], [a,c], [b,a], [c,a] }

example : E1 = E1_enum := by sorry
-- you don't need to prove.

def E2 : Lang SigmaABC
:= L1 ∪ L2

def E2_enum : Finset (Word SigmaABC)
:= {[], [a], [b], [a,c], [c,a]}

example : E2 = E2_enum := by sorry
-- you don't need to prove.

def E3 : Lang SigmaABC
:= (L1 ⋅ { [] }) ⋅ (L2 ∩ L1)

def E3_enum : Finset (Word SigmaABC)
:= {[b], [b,b], [a,c,b]}

example : E3 = E3_enum := by sorry
-- you don't need to prove.

def E4 : Lang SigmaABC
:= (E2 ⋅ {}) ⋅ E3
def E4_enum : Finset (Word SigmaABC)
:= {}

example : E4 = E4_enum := by sorry
-- you don't need to prove.

def E5 : Lang SigmaABC
:= { [], [a], [b], [b, c] } *
   ∩ { w | List.length w <= 3 }
def E5_enum : Finset (Word SigmaABC)
:= {[],[a],[b],[b,c],[a,a],[a,b],[b,a],[b,b],[a,b,c],[b,b,c],[b,c,a],[b,c,b],[a,a,a],[a,a,b],[a,b,a],[a,b,b],[b,a,a],[b,a,b],[b,b,a],[b,b,b]}

example : E5 = E5_enum := by sorry
-- you don't need to prove.

end ex1
