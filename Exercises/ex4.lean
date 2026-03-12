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
let w = aⁿ bⁿ c²ⁿ
let the pumping length be m

let w = xyz, p ≥ |x| + |y|, and q ≥ 1 where:
x = a^(p-q)
y = a^(q)
z = a^(m-p) ++ b^(m) ++ c^(2m)

consider w = x ++ y^(s) ++ z:
so w = a^(p-q) ++ a^(s*q) ++ a^(m-p) ++ b^m ++ c^2m
w = a^( (s-1)*q+m) ++ b^m ++ c^2m

assume s = 0

so we have
w = a^( m-q ) ++ b^m ++ c^2m
But our expression had that the exponent of c had to be the sum of the exponents of a and b!
So 2m-q = 2m would require q being 0, which contradicts our requirement for q ≥ 1
So we have a contradiction and our expression isn't regular
-/

theorem ex2 : ¬ ∃ A : DFA SigmaABC, L A = L₂
:= sorry
/-
Proof that L₂ is not regular (in English).
Assume L₂ is regular
let w = a^4n ++ b^2n ++ c^n

let the pumping length be m
and let w = xyz, p ≥ |x| + |y|, and q ≥ 1 where
x = a^(p-q)
y = a^(q)
z = a^(4m-p) ++ b^2m ++ c^m

Consider w = x ++ y^s ++ z
so w = a^(p-q) ++ a^(s*q) ++ a^(4m-p) ++ b^2m ++ c^m
w = a^((s-1)*q+4m) ++ b^2m ++ c^m

Assume s = 0

So the exponent of a is 4m-q, b is 2m and c is m
But our expression had that w = a^α ++ b^β ++ c^γ
Where α = 2 * β
and β = 2 * γ
So we need 4m-q = 4m, meaning q=0 which violates our definition of q ≥ 1

-/
