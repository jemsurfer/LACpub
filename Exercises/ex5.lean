/-
COMP2012 (LAC) 2026

Exercise 5

Construct a CFG and PDA for the language of bracket-matched
words.

Don't change anything else in this file!
-/
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype
import Proofs.PDA

namespace ex5

open Lang Sum Cfg CFG Pda PDA

/-
Let SigmaPar be the alphabet of left and right brackets
-/

inductive SigmaPar : Type
| lpar -- "⟨"
| rpar -- "⟩"
deriving Fintype, DecidableEq
open SigmaPar

/-
We consider the language L : Lang Σ of bracket-matched words, words
words in which every ⟨ is “closed” by a ⟩ occurring later in the word. For instance:
• [] ∈ L -- ϵ ∈ L
• [lpar,rpar] ∈ L -- ⟨⟩ ∈ L
• [lpar,lpar,rpar,lpar,rpar,rpar] ∈ L -- ⟨⟩⟨⟩ ∈ L
• [lpar,lpar,rpar] ∉ L   -- ⟨⟨⟩ ∉ L because it has more ⟨’s than ⟩’s,
• [lpar,rpar,rpar] ∉ L   -- ⟨⟩⟩ ∉ L because it has more ⟩’s than ⟨’s,
• [lpar,rpar,rpar,lpar] ∉ L -- ⟨⟩⟩⟨ ∉ L because the second ⟩ occurs before the corresponding ⟨.
-/

/- 1. Define a CFG for the language, you will also need to define an inductive type for the Non-terminals -/
inductive NTPar : Type
| S
deriving Fintype, DecidableEq
open NTPar

abbrev GPar : CFG SigmaPar
:= { NT := NTPar
     S := NTPar.S
     P := {
          (NTPar.S, []),
          (NTPar.S, [inr SigmaPar.lpar, inl NTPar.S, inr SigmaPar.rpar, inl NTPar.S])
     }
}

/- 2. Define a PDA for the language -/
-- You need to define inductive types for the states and the stack alphabet
inductive QPar : Type
| S | L | R
deriving Fintype, DecidableEq
open QPar

inductive ΓPar : Type
| lpar | rpar | ε
deriving Fintype, DecidableEq
open ΓPar

abbrev PPar : PDA SigmaPar
:= { Q := QPar
     Γ := ΓPar
     s := QPar.S
     Z₀ := ε
     δ q x z :=
            match q, x, z with
            | QPar.S, some SigmaPar.lpar, ΓPar.ε =>
                 { (QPar.S, [ΓPar.lpar, ΓPar.ε]) }
            | QPar.S, some SigmaPar.lpar, ΓPar.lpar =>
                 { (QPar.S, [ΓPar.lpar, ΓPar.lpar]) }
            | QPar.S, some SigmaPar.rpar, ΓPar.lpar =>
                 { (QPar.S, []) }
            | QPar.S, none, ΓPar.ε =>
                 { (QPar.R, []) }
            | _, _, _ => {}
     F := { QPar.R }
}

-- 3. Show that ⟨⟩⟨⟩ ∈ L PPar
-- you can either do this by spelling out the sequence of IDs in a comment or by proving
theorem e3 : [SigmaPar.lpar,SigmaPar.lpar, SigmaPar.rpar,SigmaPar.lpar,SigmaPar.rpar, SigmaPar.rpar] ∈ L PPar := by
     refine ⟨QPar.R, [], ?_, ?_⟩
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.read
     constructor
     apply Star.step
     apply Step.silent
     constructor
     apply Star.refl
     simp [PPar]
-- in Lean.

/-
⟨⟩⟨⟩ ∈ L PPar because:
(q0, lpar lpar rpar lpar rpar rpar, hash) ->
...
-/
end ex5
