import Proofs.Lang
import Proofs.Autom
import Proofs.Kleene
import Proofs.RE
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
open Lang

variable (Sigma : Type)[Alphabet Sigma]

open Lang.Examples
open SigmaABC
open Re
open RE
scoped[re] infixl:70 " ⋅ " => RE.append
scoped[re] infixl:65 " + " => RE.plus
scoped[re] postfix:max "★" => RE.star
scoped[re] notation "∅" => RE.empty
scoped[re] notation "ε" => RE.epsilon

open scoped re

instance {Sigma : Type} : CoeTC Sigma (RE Sigma) where
  coe := RE.sym


open scoped re

variable {Sigma : Type}[Alphabet Sigma]

def L : RE Sigma → Lang Sigma
| empty => {}
| epsilon => { [] }
| plus e1 e2 => (L e1) ∪ (L e2)
| append e1 e2 => L e1 ⋅ L e2
| RE.star e => (L e) *
| sym x => { [x] }

open Nfa
open NFA

abbrev nullable : Set (NFA Sigma) :=
  { A | ∃ q , q ∈ A.S ∩ A.F }

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

abbrev nfa_epsilon : NFA Sigma
:= { Q := Fin 1
     S := {0}
     F := {0}
     δ := λ | _ , _ => {}
}

open Sum

abbrev nfa_plus :
NFA Sigma → NFA Sigma → NFA Sigma
| A1 , A2 =>
let Q := Sum A1.Q A2.Q
{
   Q := Q
   S := ({inl q | q ∈ A1.S} : Finset Q)
      ∪ ({inr q | q ∈ A2.S} : Finset Q)
   F := ({inl q | q ∈ A1.F} : Finset Q)
      ∪ ({inr q | q ∈ A2.F} : Finset Q)
   δ := λ | inl q, x =>
            { inl p | p ∈ A1.δ q x }
          | inr q, x =>
            { inr p | p ∈ A2.δ q x }
}

def nfa_append (A1 A2 : NFA Sigma) : NFA Sigma
:= let Q := Sum A1.Q A2.Q ;
    { Q := Q
      S := ({x | (∃ q ∈ A1.S, x = inl q) ∨
                (∃ q ∈ A2.S, x = inr q ∧ A1 ∈ nullable)})
      F := { inr q | q ∈ A2.F }
      δ := λ q x ↦ match q with
        | inl q => ({ inl q' | q' ∈ A1.δ q x} : Finset Q)
          ∪ ({y | ∃ q ∈ A1.δ q x, q ∈ A1.F ∧ ∃ q' ∈ A2.S, y = inr q'} : Finset Q)
        | inr q => { inr s | s ∈ A2.δ q x }
    }

def nfa_star (A1 : NFA Sigma) : NFA Sigma := sorry

def re2nfa' : RE Sigma → NFA Sigma
| empty => nfa_empty
| sym x => nfa_sym x
| plus e1 e2 =>
      nfa_plus (re2nfa' e1) (re2nfa' e2)
| epsilon => nfa_epsilon
| append e1 e2 => nfa_append (re2nfa' e1) (re2nfa' e2)
| RE.star e => nfa_star (re2nfa' e)


theorem re2nfa_ok : ∀(e : RE Sigma),
  Nfa.L (re_nfa.re2nfa e) = Re.L e := by apply re_nfa.re2nfa_ok

----------------------------------------------------------------
open Dfa
/-
So far we've seen regular languages:
A language is regular if:
 - it can be represented by a regular expression
 - or by an NFA
 - or by a DFA

The pumping lemma states the following:
For any regular language L there exists some n such that
  For any accepted word w of length greater than n
    We can wrtie w = xyz such that:
      - |xy| ≤ n
      - |y| ≥ 1
      - ∀ m ∈ ℕ, xy^mz is also accepted

Consider the language { a^n b^n | n ∈ ℕ }.
Suppose this is regular, for a contradiction
Then there exists a pumping length p

Consider the word a^p · b^p
By the pumping lemma, we can write a^p · b^p as xyz such that
|xy| ≤ p
|y| ≥ 1
xy^mz is accepted for every m ∈ ℕ

Since |xy| ≤ p, we know that xy = a^q for some q ≤ p
Hence, y = a^r for some 1 ≤ r ≤ q
But then, xz = a^{p-r} b^p
xz is not accepted, hence the pumping lemma does not hold
and therefore, the language {a^nb^n | n ∈ ℕ } is not regular
-/
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

theorem pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    ) := by sorry

/-
Usually, but not always, you can pump down, i.e., remove y
For the following language you have to pump up:

Consider { a^{n^2} | n ∈ ℕ }
a, aaaa, aaaaaaaaa, etc.

If this language is regular, then there exists a pumping length p
Consider the word w = a^{p^2}. Clearly, this is in the language
and it is of length at least p.

Then, by the pumping lemma, it can be written as w = xyz, where
|xy| ≤ p
|y| ≥ 1
∀ m ∈ ℕ, xy^mz is in the language.
y = a^q, where 1 ≤ q ≤ p

Consider the word xz. This word is of length a^{p^2-q}.
(p-1)^2 = p^2-2p+1
p^2-(2p-1)

So if q = 2p-1, then the word xz is in the language.
Hence, if p were 1, then q ≤ p = 2p-1 and the word could be in the language
So we have to pump up.

Consider xyyz = a^{p^2+q}. The next square is (p+1)^2 = p^2+2p+1
So p^2+q is only square is q ≥ 2p+1. However, q ≤ p, so p^2+q is not square.
Hence, xyyz is not in the language, and the language does not satisfy the pumping lemma.
{a^(n^2) | n ∈ ℕ} is not regular.

In general, the structure of an irregularity proof goes as follows:

Suppose for a contradiction, L is regular. Then there exists a pumping length p.
Take a word w in L of length at least p.
Then, by the structure of our word w, we know something about xy and hence about y.
We use that something to show that ∃ m ∈ ℕ such that xy^mz is not in L.
This contradicts the pumping lemma, and hence L is not regular.
-/
