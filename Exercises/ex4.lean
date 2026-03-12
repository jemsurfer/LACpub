/-
COMP2012 (LAC) 2026

Exercise 4

We are asking you to provide informal proofs
(i.e. in English) that the languages L₁, L₂ are
not regular. We are using Lean to specify the setup,
but you should give your answer in a comment.

If you are very Lean savvy you can try to do at
least the outline in Lean and rely on some lemmas
which are evident but which you don't want to
prove.
-/
import Mathlib.Tactic.DeriveFintype
import Proofs.Lang
import Proofs.Autom
open Lang Dfa DFA Lang.Examples SigmaABC

-- Here are the two languages:
abbrev L₁ : Lang SigmaABC
:= { a^n ++ b^m ++ c^(m+n)| (m : ℕ)(n : ℕ)}

abbrev L₂ : Lang SigmaABC
:= { w | w.count a = 2*(w.count b)
       ∧ w.count b = 2*(w.count c) }

-- this is the pumping lemma in Lean
-- we add it as an axiom here but it is
-- provable from our definition of DFA.
variable (Sigma : Type)[Alphabet Sigma]
instance : HPow (Word Sigma) ℕ (Word Sigma)
where hPow := λ x n ↦ List.flatten (x^n)
variable {Sigma : Type}[Alphabet Sigma]

def REG : Set (Lang Sigma)
:= {lang | ∃ A : DFA Sigma, Dfa.L A = lang}

axiom pumping_lemma : ∀ L₁ : Lang Sigma,
  L₁ ∈ REG →
    (∃ n : ℕ,
    ∀ w : Word Sigma,
    w.length ≥ n ∧ w ∈ L₁ →
      ∃ x y z : Word Sigma,
      w = x ++ y ++ z ∧
      (x ++ y).length ≤ n ∧
      y.length ≥ 1 ∧
      ∀ m : ℕ, x ++ y^m ++ z ∈ L₁
    )

-- Exercises

theorem ex1 : ¬ ∃ A : DFA SigmaABC, L A = L₁
:= sorry
/-
Proof that L₁ is not regular (in English).
Assume L₁ is regular
so there must be a pumping length n
let w = aⁿ bⁿ c²ⁿ

let w = xyz where:
x = a^(p-q)
y = a^(q)
z = a^(n-p) ++ b^(n) ++ c^(2n)

consider w = x ++ y^(s) ++ z:
so w = a^(p-q) ++ a^(s*q) ++ a^(n-p) ++ b^n ++ c^2n
w = a^( (s-1)*q+n) ++ b^n ++ c^2n

assume s = 0

so we have
w = a^( n-q ) ++ b^n ++ c^2n
But our expression had that the exponent of c had to be the sum of the exponents of a and b!
This isn't the case in our expression - n-q+n ≠ 2n
So we have a contradiction and our expression isn't regular
-/

theorem ex2 : ¬ ∃ A : DFA SigmaABC, L A = L₂
:= sorry
/-
Proof that L₂ is not regular (in English).
Assume L₂ is regular
let w = a^4n ++ b^2n ++ c^n

Let w = xyz where
x = a^(p-q)
y = a^(q)
z = a^(4n-p) ++ b^2n ++ c^n

Consider w = x ++ y^s ++ z
so w = a^(p-q) ++ a^(s*q) ++ a^(4n-p) ++ b^2n ++ c^n
w = a^((s-1)*q+4n) ++ b^2n ++ c^n

Assume s = 0

So the exponent of a is 4n-q, b is 2n and c is n
But our expression had that w = a^α ++ b^β ++ c^γ
Where α = 2 * β
and β = 2 * γ
It's clear that 8n-2q ≠ 2n, giving us a contradiction

-/
