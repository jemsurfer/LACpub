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

/- 4 precedence levels:
- atoms (expressions in parentheses)
- star
- concatenation
- plus
- and E (expression)
-/
inductive NT₂ : Type
| A | S | C | P | E
deriving Fintype, DecidableEq
open NT₂

abbrev G₂ : CFG Sigma_RE :=
{ NT := NT₂
  S := E
  P := {
    (NT₂.E, [inl NT₂.P]),

    (NT₂.P, [inl NT₂.P, inr Sigma_RE.plus, inl NT₂.C]),
    (NT₂.P, [inl NT₂.C]),

    (NT₂.C, [inl NT₂.C, inr Sigma_RE.dot, inl NT₂.S]),
    (NT₂.C, [inl NT₂.S]),

    (NT₂.S, [inl NT₂.S, inr Sigma_RE.star]),
    (NT₂.S, [inl NT₂.A]),

    (NT₂.A, [inr Sigma_RE.a]),
    (NT₂.A, [inr Sigma_RE.b]),
    (NT₂.A, [inr Sigma_RE.c]),
    (NT₂.A, [inr Sigma_RE.epsilon]),
    (NT₂.A, [inr Sigma_RE.empty]),
    (NT₂.A, [inr Sigma_RE.lpar, inl NT₂.E, inr Sigma_RE.rpar])
  }
}

end g₂
namespace g₃

/- Is the grammar you have defined in the previous step LL(1)?
If not define another grammar G₃ for the same language,
which is LL(1). If G₂ is already LL(1) the just copy this.
-/

inductive NT₃ : Type
| E | P | Pp | C | Cp | S | Sp | A
deriving Fintype, DecidableEq
open NT₃

abbrev G₃ : CFG Sigma_RE :=
{ NT := NT₃
  S := E
  P := {
    (NT₃.E, [inl NT₃.P]),

    (NT₃.P, [inl NT₃.C, inl NT₃.Pp]),

    (NT₃.Pp, [inr Sigma_RE.plus, inl NT₃.C, inl NT₃.Pp]),
    (NT₃.Pp, []),

    (NT₃.C, [inl NT₃.S, inl NT₃.Cp]),

    (NT₃.Cp, [inr Sigma_RE.dot, inl NT₃.S, inl NT₃.Cp]),
    (NT₃.Cp, []),

    (NT₃.S, [inl NT₃.A, inl NT₃.Sp]),

    (NT₃.Sp, [inr Sigma_RE.star, inl NT₃.Sp]),
    (NT₃.Sp, []),

    (NT₃.A, [inr Sigma_RE.a]),
    (NT₃.A, [inr Sigma_RE.b]),
    (NT₃.A, [inr Sigma_RE.c]),
    (NT₃.A, [inr Sigma_RE.epsilon]),
    (NT₃.A, [inr Sigma_RE.empty]),
    (NT₃.A, [inr Sigma_RE.lpar, inl NT₃.E, inr Sigma_RE.rpar])
  }
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
| scan | seekA | seekB | matchA | matchB | return | check | accept
deriving Fintype, DecidableEq, Repr
open Qww

inductive Γww : Type
| blank | markA | markB
deriving Fintype, DecidableEq, Repr
open Γww

abbrev Mww : TM SigmaABX
:= {
  Q := Qww
  Γ := Γww
  s := Qww.scan
  B := Γww.blank
  F := { Qww.accept }
  δ q x :=
    match q, x with
    | Qww.scan, inl Γww.blank => some (Qww.scan, inl Γww.blank, Tm.Dir.R)
    | Qww.scan, inl Γww.markA => some (Qww.scan, inl Γww.markA, Tm.Dir.R)
    | Qww.scan, inl Γww.markB => some (Qww.scan, inl Γww.markB, Tm.Dir.R)
    | Qww.scan, inr SigmaABX.a => some (Qww.seekA, inl Γww.markA, Tm.Dir.R)
    | Qww.scan, inr SigmaABX.b => some (Qww.seekB, inl Γww.markB, Tm.Dir.R)
    | Qww.scan, inr SigmaABX.X => some (Qww.check, inr SigmaABX.X, Tm.Dir.R)

    | Qww.seekA, inl Γww.blank => none
    | Qww.seekA, inl Γww.markA => some (Qww.seekA, inl Γww.markA, Tm.Dir.R)
    | Qww.seekA, inl Γww.markB => some (Qww.seekA, inl Γww.markB, Tm.Dir.R)
    | Qww.seekA, inr SigmaABX.a => some (Qww.seekA, inr SigmaABX.a, Tm.Dir.R)
    | Qww.seekA, inr SigmaABX.b => some (Qww.seekA, inr SigmaABX.b, Tm.Dir.R)
    | Qww.seekA, inr SigmaABX.X => some (Qww.matchA, inr SigmaABX.X, Tm.Dir.R)

    | Qww.seekB, inl Γww.blank => none
    | Qww.seekB, inl Γww.markA => some (Qww.seekB, inl Γww.markA, Tm.Dir.R)
    | Qww.seekB, inl Γww.markB => some (Qww.seekB, inl Γww.markB, Tm.Dir.R)
    | Qww.seekB, inr SigmaABX.a => some (Qww.seekB, inr SigmaABX.a, Tm.Dir.R)
    | Qww.seekB, inr SigmaABX.b => some (Qww.seekB, inr SigmaABX.b, Tm.Dir.R)
    | Qww.seekB, inr SigmaABX.X => some (Qww.matchB, inr SigmaABX.X, Tm.Dir.R)

    | Qww.matchA, inl Γww.markA => some (Qww.matchA, inl Γww.markA, Tm.Dir.R)
    | Qww.matchA, inl Γww.markB => some (Qww.matchA, inl Γww.markB, Tm.Dir.R)
    | Qww.matchA, inr SigmaABX.a => some (Qww.return, inl Γww.markA, Tm.Dir.L)
    | Qww.matchA, inr SigmaABX.b => none
    | Qww.matchA, inr SigmaABX.X => none
    | Qww.matchA, inl Γww.blank => none

    | Qww.matchB, inl Γww.markA => some (Qww.matchB, inl Γww.markA, Tm.Dir.R)
    | Qww.matchB, inl Γww.markB => some (Qww.matchB, inl Γww.markB, Tm.Dir.R)
    | Qww.matchB, inr SigmaABX.b => some (Qww.return, inl Γww.markB, Tm.Dir.L)
    | Qww.matchB, inr SigmaABX.a => none
    | Qww.matchB, inr SigmaABX.X => none
    | Qww.matchB, inl Γww.blank => none

    | Qww.return, inl Γww.blank => some (Qww.scan, inl Γww.blank, Tm.Dir.R)
    | Qww.return, _ => some (Qww.return, x, Tm.Dir.L)

    | Qww.check, inl Γww.markA => some (Qww.check, inl Γww.markA, Tm.Dir.R)
    | Qww.check, inl Γww.markB => some (Qww.check, inl Γww.markB, Tm.Dir.R)
    | Qww.check, inl Γww.blank => some (Qww.accept, inl Γww.blank, Tm.Dir.R)
    | Qww.check, inr SigmaABX.a => none
    | Qww.check, inr SigmaABX.b => none
    | Qww.check, inr SigmaABX.X => none

    | Qww.accept, _ => none
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
