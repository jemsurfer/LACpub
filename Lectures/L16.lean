import Proofs.Lang
import Mathlib.Tactic.DeriveFintype
import Proofs.PDA

open Lang
open Pda
open Examples
open SigmaABC
open Sum

-- Turing machines , 0 , 1 in chomsky hierarchy

abbrev anbn : Lang SigmaABC
:= { a^n ++ b^n | n : ℕ }

abbrev anbncn : Lang SigmaABC
:= { a^n ++ b^n ++ c^n | n : ℕ }
-- aabbcc
abbrev anbmcn : Lang SigmaABC
:= { a^n ++ b^m ++ c^n | (m : ℕ)(n : ℕ) }
-- aabcc
abbrev anbncm : Lang SigmaABC
:= { a^n ++ b^n ++ c^m | (m : ℕ)(n : ℕ) }
-- anbmcn ∩ anbncm = anbncn

-- how can we recognize anbncn
-- chomsky 1 , recognized by turing machine

variable (Sigma : Type)[Alphabet Sigma]

inductive Dir : Type where
| L | R
deriving Fintype , DecidableEq
open Dir

structure TM : Type 1  where
   Q : Type -- states
   [ alphQ : Alphabet Q]
   Γ : Type -- tape alphabet
   [ alphΓ : Alphabet Γ]
   s : Q
   B : Γ
   F : Finset Q
   δ : Q → Γ ⊕ Sigma
       → Option (Q × (Γ ⊕ Sigma) × Dir)

inductive Γb : Type where
| blank | X | Y | Z
deriving Fintype, DecidableEq

open Γb

abbrev Manbncn : TM SigmaABC :=
{
   Q := Fin 7
   Γ := Γb
   s := 0
   B := blank
   F := { 6 }
   δ q z := match q , z with
            | 0 , inr a => some (1, inl X, R)
            | 1 , inr a => some (1, inr a, R)
            | 1 , inl Y => some (1,inl Y, R )
            | 1 , inr b => some (2,inl Y, R )
            | 2 , inr b => some (2,inr b, R )
            | 2 , inl Z => some (2,inl Z, R )
            | 2 , inr c => some (3,inl Z, R )
            | 3 , inr c => some (4,inr c, Dir.L)
            | 4 , inr a => some (4,inr a, Dir.L)
            | 4 , inr b => some (4,inr b, Dir.L)
            | 4 , inl Y => some (4,inl Y, Dir.L)
            | 4 , inl Z => some (4,inl Z, Dir.L)
            | 4 , inl X => some (0,inl X, Dir.R)
            | 3 , inl blank => some (5,inl blank, Dir.L)
            | 5 , inl Y => some (5,inl Y, Dir.L)
            | 5 , inl Z => some (5,inl Z, Dir.L)
            | 5 , inl X => some (6,inl X, R)
            | _ , _  => none
      }

variable {Sigma : Type}[Alphabet Sigma]

variable (M : TM Sigma)

abbrev Sym : Type := M.Γ ⊕ Sigma

abbrev ID : Type
:= List (Sym M) × M.Q × List (Sym M)

inductive Step : ID M × ID M → Prop where
-- To be completed

def word2tape : List Sigma → List (Sym M)
| w => List.map inr w

abbrev init : Word Sigma → ID M
| w => ([] , M.s, word2tape M w )

abbrev accept : ID M → Prop
| (_,q,_) => q ∈ M.F

abbrev L : Lang Sigma
:= { w | ∃ st , Pda.Star (Step M) (init M w,st)
      ∧ accept M st}
