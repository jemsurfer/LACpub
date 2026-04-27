/-
COMP2012 (LAC) 2026

Exercise 5


Don't change anything else in this file!
-/
import Proofs.TM
import Mathlib.Tactic.DeriveFintype
import Proofs.CFG

namespace ex6_1
open Sum Cfg CFG

/-
We are defining a grammar for regular expressions over

inductive Sigma : Type
| a | b | c

These are the expressions we have been using in ex4. E.g.
(a + b)* ⬝ c*
and so on.
-/

/- Here is the alphabet
epsilon = ε
empty = ∅
dot = ⬝
plus = +
star = *
lpar = (
rpar = )
-/
inductive Sigma_RE : Type
| a | b | c | epsilon | empty | dot | plus | star | lpar | rpar
deriving Fintype, DecidableEq
open Sigma_RE

-- We introduce the following grammar, st L(G₁) : Lang Sigma_RE
-- is the language of regular expressions.
namespace g₁

inductive NT₁ : Type
| E
deriving Fintype, DecidableEq
open NT₁

abbrev G₁ : CFG Sigma_RE :=
{ NT := NT₁
  S := E
  P := { (E, [inr a]),
         (E, [inr b]),
         (E, [inr c]),
         (E, [inr epsilon]),
         (E, [inr empty]),
         (E, [inl E, inr dot,inl E]),
         (E, [inl E, inr plus,inl E]),
         (E, [inl E, inr star]),
         (E, [inr lpar, inl E,inr rpar]) }
}

end g₁

namespace g₂
/-
Alas, G₁ is ambigious (why ?).
Define a grammar G₂ which is not ambigious and whose parsetrees
reflect the conventions on how to read regular expressions.
-/

inductive NT₂ : Type
-- Define your nonterminals here
deriving Fintype, DecidableEq
open NT₂

abbrev G₂ : CFG Sigma_RE :=
{ NT := sorry
  S := sorry
  P := sorry
}

end g₂
namespace g₃

/- Is the grammar you have defined in the previous step LL(1)?
If not define another grammar G₃ for the same language,
which is LL(1). If G₂ is already LL(1) the just copy this.
-/

inductive NT₃ : Type
-- Define your nonterminals here
deriving Fintype, DecidableEq
open NT₃

abbrev G₃ : CFG Sigma_RE :=
{ NT := sorry
  S := sorry
  P := sorry
}

end g₃

end ex6_1

namespace ex6_2
open Sum Lang Tm TM

inductive SigmaABX : Type
| a | b | X
deriving Fintype, DecidableEq, Repr
open SigmaABX
/-
Define a Turing Machine M deciding the language
-/
abbrev Lww : Lang SigmaABX
:= { wXw | ∃ w , X ∉ w ∧ wXw = w ++ [ X ] ++ w }
/-
ie the language of repeated words over a , b separated by X in the middle.
e.g.
[ a , b, X , a , b] ∈ Lww
-/

inductive Qww : Type
-- Define your TM states here
deriving Fintype, DecidableEq, Repr
open Qww

inductive Γww : Type
-- Define your stack alphabet here
deriving Fintype, DecidableEq, Repr
open Γww

abbrev Mww : TM SigmaABX
:= {
  Q := sorry
  Γ := sorry
  s := sorry
  B := sorry
  F := sorry
  δ := sorry
}

/-
you can check your machine with
#eval (L_n  Mww 1000 [X])
#eval (L_n  Mww 1000 [a,X,a])
#eval (L_n  Mww 1000 [b,X,b])
#eval (L_n  Mww 1000 [a,a,X,a,a])
#eval (L_n  Mww 1000 [a,b,X,a,b])
You can also check the state after a fixed number of steps:
#eval (stepn_f Mww 9 (init Mww [a,b,X,a,b]))
-/

end ex6_2
