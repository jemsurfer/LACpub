import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene

open Kleene
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Re
open Lang
variable (Sigma : Type)[Alphabet Sigma]

inductive RE : Type
| sym : Sigma → RE
| empty : RE
| plus : RE → RE → RE
| epsilon : RE
| append : RE → RE → RE
| star : RE → RE

open RE

variable {Sigma : Type}[Alphabet Sigma]
def L : RE Sigma → Lang Sigma
| sym x => { [ x ]}
| empty => {}
| plus e1 e2 => L e1 ∪ L e2
| epsilon => { [] }
| append e1 e2 => L e1 ⋅ L e2
| RE.star e => (L e) *

instance : Zero (RE Sigma) := ⟨RE.empty⟩
instance : One  (RE Sigma) := ⟨RE.epsilon⟩
instance : Add  (RE Sigma) := ⟨RE.plus⟩
instance : Mul  (RE Sigma) := ⟨RE.append⟩
instance : Kleene.Star (RE Sigma) := ⟨RE.star⟩

end Re

namespace REex

open Re
open Lang.Examples

open SigmaABC
open RE

def r : RE SigmaABC := (sym a + sym b)★ ⋅ ε

def anbm : RE SigmaABC := (sym a)★ ⋅ (sym b)★

def any : RE SigmaABC := (sym a + sym b + sym c)★

def contains_ab : RE SigmaABC
   := any ⋅ (sym a ⋅ sym b) ⋅ any

def bc_only : RE SigmaABC
  := (sym b + sym c)★

def contains_no_ab : RE SigmaABC
  := (bc_only ⋅
     (ε + ((sym a) ⋅ (sym a) ★ ⋅ (sym c)))) ★
     ⋅ (sym a) ★

def contains_no_ab' : RE SigmaABC :=
  (((sym b) + (sym c)) +
   ((sym a) ⋅ (sym a)★ ⋅ (sym c)))★
   ⋅ (sym a)★

def hi : RE Char
  := sym 'h' ⋅ sym 'i'

end REex

namespace re_nfa
open Lang
variable {Sigma : Type}[Alphabet Sigma]
open Nfa
open NFA
open Re

abbrev nfa_sym (x : Sigma) : NFA Sigma
:= { Q := Fin 2
     S := {0}
     F := {1}
     δ := λ | 0 , y => if x=y then {1} else {}
            | 1 , _  => {}}

abbrev nfa_empty : NFA Sigma
:= { Q := Fin 0
     S := {}
     F := {}
     δ := λ | _ , _ => {}}

abbrev nfa_epsilon : NFA Sigma
:= { Q := Fin 2
     S := {0}
     F := {0}
     δ := λ | 0 , _ => {1}
            | 1 , _  => {}}

open Sum

def nfa_plus (A1 A2 : NFA Sigma) : NFA Sigma :=
  let Q := Sum A1.Q A2.Q ;
  { Q := Q,
    S := ({ inl q | q ∈ A1.S } : Finset Q)
       ∪ ({ inr q | q ∈ A2.S } : Finset Q),
    F := ({ inl q | q ∈ A1.F } : Finset Q)
       ∪ ({ inr q | q ∈ A2.F } : Finset Q),
    δ := λ q x ↦
      match q with
      | inl s1 => ({ inl q | q ∈ A1.δ s1 x } : Finset Q)
      | inr s2 => ({ inr q | q ∈ A2.δ s2 x } : Finset Q) }

abbrev nullable : Set (NFA Sigma) :=
  { A | ∃ q , q ∈ A.S ∩ A.F }

def nfa_append (A1 A2 : NFA Sigma) : NFA Sigma
:= let Q := Sum A1.Q A2.Q ;
    { Q := Q
      S := ({ inl q | q ∈ A1.S } : Finset Q)
         ∪ ({ x | ∃ q, x = inr q ∧ q ∈ A2.S ∧ A1 ∈ nullable} : Finset Q)
      F := { inr q | q ∈ A2.S }
      δ := λ q x ↦ match q with
          | inl q => ({ inl q' | q' ∈ A1.δ q x} : Finset Q)
           ∪ ({ y | ∃ q', y = inr q' ∧ q' ∈ A2.S
                   ∧ ∃ q'' , q'' ∈ A1.δ q x ∧ q'' ∈ A1.F } : Finset Q)
            -- ∪ { inr q' | q' ∈ A2.S ∧
            --     ∃ q'' , q'' ∈ A1.δ q x ∧ q'' ∈ A1.F }
          | inr q => { inr s | s ∈ A2.δ q x}}

def nfa_star (A : NFA Sigma) : NFA Sigma
:= let Q := Sum A.Q (Fin 1) ;
   { Q := Q
     S := ({ inr 0 } : Finset Q)  ∪
          ({ inl q | q ∈ A.S } : Finset Q)
     F := { inr 0 } ∪ ({ inl q | q ∈ A.F } : Finset Q)
     δ := λ q x ↦ match q with
          | inl q => ({ inl q' | q' ∈ A.δ q x} : Finset Q)
           ∪ ({ y | ∃ q', y = inl q' ∧ q' ∈ A.S
                   ∧ ∃ q'' , q'' ∈ A.δ q x ∧ q'' ∈ A.F } : Finset Q)
            -- ∪ { inr q' | q' ∈ A2.S ∧
            --     ∃ q'' , q'' ∈ A1.δ q x ∧ q'' ∈ A1.F }
          | inr _ => {}}

open RE
def re2nfa : RE Sigma → NFA Sigma
| sym x => nfa_sym x
| empty => nfa_empty
| epsilon => nfa_epsilon
| plus e1 e2 => nfa_plus (re2nfa e1) (re2nfa e2)
| append e1 e2 => nfa_append (re2nfa e1) (re2nfa e2)
| RE.star e => nfa_star (re2nfa e)

---
lemma nfa_empty_ok :
    Nfa.L nfa_empty = ({} : Lang Sigma)
    := by ext x
          simp
lemma nfa_epsilon_ok :
    Nfa.L nfa_epsilon = ({ [] } : Lang Sigma)
    := sorry

lemma nfa_sym_ok : ∀ x : Sigma ,
    Nfa.L (nfa_sym x) = { [x]} := by sorry

lemma nfa_plus_ok : ∀ A1 A2 : NFA Sigma,
    Nfa.L (nfa_plus A1 A2) =
     Nfa.L A1 ∪ Nfa.L A2
    := sorry

lemma nfa_append_ok : ∀ A1 A2 : NFA Sigma,
    Nfa.L (nfa_append A1 A2) =
     Nfa.L A1 ⋅ Nfa.L A2
    := sorry

lemma nfa_star_ok : ∀ A : NFA Sigma,
    Nfa.L (nfa_star A) =
     Nfa.L A *
    := sorry


theorem re2nfa_ok : ∀ e : RE Sigma,
  Nfa.L (re2nfa e) = Re.L e  := by
  intro e
  induction e with
  | sym x =>
      apply nfa_sym_ok
  | empty =>
      apply nfa_empty_ok
  | epsilon =>
      apply nfa_epsilon_ok
  | plus e1 e2 ih1 ih2 =>
      simp [Re.L]
      rw  [← ih1,← ih2]
      apply nfa_plus_ok
  | append e1 e2 ih1 ih2 =>
      simp [Re.L]
      rw  [← ih1,← ih2]
      apply nfa_append_ok
  | star e ih =>
      simp [Re.L]
      rw  [← ih]
      apply nfa_star_ok

end re_nfa
