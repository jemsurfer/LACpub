import Proofs.Lang

namespace Cfg
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure CFG : Type 1 where
  NT : Type
  [ alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma ))

open CFG
open Sum

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

abbrev Symbol : Type
  := G.NT ⊕ Sigma

scoped instance : Coe G.NT (Symbol G) :=
  ⟨Sum.inl⟩

scoped instance : Coe Sigma (Symbol G) :=
  ⟨Sum.inr⟩

abbrev Sent : Type
  := Word (Symbol G)

abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) | ∃ α₁ α₂ ,
      ∃ A , α = α₁ ++ [inl A] ++ α₂
      ∧ ∃ γ , (A , γ) ∈ G.P
      ∧ β = α₁ ++ γ ++ α₂ }

-- infixr:70 " ⟹ " => Deriv

inductive DerivStar : Sent G × Sent G → Prop
| refl : ∀ α , DerivStar (α , α)
| step : ∀ α β γ ,
    Deriv G (α , β) → DerivStar (β , γ)
    → DerivStar (α , γ)

abbrev emb : Word Sigma → Sent G
:= List.map inr

abbrev L : Lang Sigma
:= { w | DerivStar G ([inl G.S],emb G w)}


end Cfg



namespace CfgEx
open Lang
open Cfg
open Sum
open scoped Cfg.CFG

inductive SigmaA : Type
| lpar | rpar | a | plus | times
deriving Fintype, DecidableEq
open SigmaA

inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq
open NTA

abbrev E : NTA ⊕ SigmaA := inl (NTA.E)
abbrev T : NTA ⊕ SigmaA := inl (NTA.T)
abbrev F : NTA ⊕ SigmaA := inl (NTA.F)
abbrev lpar : NTA ⊕ SigmaA := inr SigmaA.lpar
abbrev rpar : NTA ⊕ SigmaA := inr SigmaA.rpar
abbrev a : NTA ⊕ SigmaA := inr SigmaA.a
abbrev plus : NTA ⊕ SigmaA := inr SigmaA.plus
abbrev times : NTA ⊕ SigmaA := inr SigmaA.times

abbrev GA : CFG SigmaA :=
{ NT := NTA
  S := NTA.E
  P := { (NTA.E, [T]),
         (NTA.E , [E,plus,T]),
         (NTA.T, [F]),
         (NTA.T , [E,times,T]),
         (NTA.F, [a]),
         (NTA.F, [lpar,E,rpar])}
   }

end CfgEx
