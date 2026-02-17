import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene

-- Regular expressions
-- grep

open Kleene
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
open Lang

variable (Sigma : Type)[Alphabet Sigma]

inductive RE : Type
| sym : Sigma → RE
| append : RE → RE → RE
| plus : RE → RE → RE
| epsilon : RE
| empty : RE
| star : RE → RE

open Lang.Examples
open SigmaABC
open RE

abbrev e1 : RE SigmaABC
:= append (sym a) (sym b)
-- ab

abbrev e2 : RE SigmaABC
:= plus (sym a) (sym b)
-- a+b

abbrev e3 : RE SigmaABC
:= append (sym a) (plus (sym b) (sym c))
-- a(b+c)
-- ac ∈ L, c ∉ L

abbrev e4 : RE SigmaABC
:= plus (append (sym a) (sym b)) (sym c)
-- ab+c
-- ac ∉ L , c ∈ L

abbrev e5 : RE SigmaABC
:= star (append (sym a) (sym b))
-- (ab)*
-- ab , abab , ababab ...

abbrev e6 : RE SigmaABC :=
append (append (plus (sym b) epsilon) e5)
      (plus (sym a) epsilon)
-- ((b+ε)(ab)*)(a+ε)
-- bababa ab a b

abbrev any : RE SigmaABC
:= star (plus (sym a) (plus (sym b) (sym c)))

abbrev e7
:= append (append any (append (sym a) (sym b)))
          any
-- (a+b+c)*ab(a+b+c)*

-- challenge : all words where ab does not appear

variable {Sigma : Type}[Alphabet Sigma]

def L : RE Sigma → Lang Sigma
| empty => {}
| plus e1 e2 => (L e1) ∪ (L e2)
| epsilon => { [] }
| append e1 e2 => L e1 ⋅ L e2
| RE.star e => (L e) *
| sym x => { [x] }

open Nfa
open NFA

abbrev nfa_empty : NFA Sigma
:= { Q := Fin 0
     S := {}
     F := {}
     δ := λ q x => {}
}

def nfa_sym : Sigma → NFA Sigma
| x => {
      Q := Fin 2
      S := {0}
      F := {1}
      δ := λ | 0 , y => if x=y then {1} else {}
             | 1 , _ => {}
}


def re2nfa : RE Sigma → NFA Sigma
| empty => nfa_empty
| plus e1 e2 => sorry
| epsilon => sorry
| append e1 e2 => sorry
| RE.star e => sorry
| sym x => nfa_sym x

theorem re2nfa_ok : ∀(e : RE Sigma),
  L e = Nfa.L (re2nfa e) := sorry
