import Proofs.Lang
open Lang

variable (Sigma : Type)[Alphabet Sigma]

open Sum 

structure CFG : Type 1 where
  NT : Type
  [alphNT : Alphabet NT]
  S : NT 
  P : Finset (NT × Word (Sum NT Sigma))


variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma )

abbrev Sent : Type -- Sentence Form
:= Word (Sum G.NT Sigma)

abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) |
      ∃ w w' : Sent G, ∃ A : G.NT, ∃ γ : Sent G,
      α = w ++ [inl A] ++ w'
      ∧ β = w ++ γ ++ w'
      ∧ (A , γ) ∈ G.P
}

inductive DerivStar : Set (Sent G × Sent G) 
| refl : ∀ α , DerivStar (α,α)
| step : ∀ α β γ, 
        Deriv G (α , β) → DerivStar (β, γ) 
         → DerivStar (α , γ)

open Sum

abbrev emb : Word Sigma → Sent G
:= List.map inr 

abbrev L : Lang Sigma
:= { w | DerivStar G ([inl G.S],emb G w)}



-- A for Arithmetic

inductive SigmaA : Type
| a | plus | times | lpar | rpar
deriving Fintype, DecidableEq
-- a , + , * , ( , )

inductive NTA : Type 
| E | T | F 
deriving Fintype, DecidableEq

-- SigmaA.a
open SigmaA
open NTA 
open CFG

abbrev GA : CFG SigmaA
:= { NT := NTA,
     S := E, 
     P := { (E , [ inl T ]),
            (E , [ inl E , inr plus, inl T]),
            (T , [ inl F]),
            (T , [ inl T, inr times, inl F]),
            (F , [ inr a]),
            (F , [ inr lpar , inl E, inr rpar])
            }
}