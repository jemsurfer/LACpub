import Proofs.Lang
import Mathlib.Tactic.DeriveFintype

open Lang

namespace Tm
variable (Sigma : Type)[Alphabet Sigma]

inductive Dir : Type where
| L | R
deriving Fintype, DecidableEq, Repr
open Dir

structure TM : Type 1 where
  Q : Type -- states
  [ alphQ : Alphabet Q]
  Γ : Type -- Tape alphabet
  [ alphΓ : Alphabet Γ]
  s : Q    -- initial state
  B : Γ    -- blank
  F : Finset Q -- set of final states
  δ : Q → Γ ⊕ Sigma →
        Option (Q × (Γ ⊕ Sigma) × Dir)

-- Make it easy to use the alphabet instances carried by a machine
instance (M : TM Sigma) : Alphabet M.Q := M.alphQ
instance (M : TM Sigma) : Alphabet M.Γ := M.alphΓ

-- This lets `q ∈ M.F` be decidable (Finset membership needs `DecidableEq`).
instance (M : TM Sigma) : DecidableEq M.Q := M.alphQ.decEq
instance (M : TM Sigma) : DecidableEq M.Γ := M.alphΓ.decEq

variable {Sigma : Type}[Alphabet Sigma]

variable (M : TM Sigma)

-- a symbol is either a tape-symbol or an input

abbrev Sym : Type
:= M.Γ ⊕ Sigma

-- we represent a tape as 2 lists
-- the first one is the tape on the left read backwards
-- the 2nd one is the tape on the right starting with
-- the current symbol.
-- hence the ID (Instantanous description)
-- is the state and 2 lists
abbrev ID : Type :=
    List (Sym M) × M.Q ×  List (Sym M)

open Sum

inductive Step : (ID M × ID M) → Prop
| right : ∀ q x q' y γL γR, M.δ q x = some (q',y,R)
        → Step ((γL,q,x::γR) , (y::γL,q',γR))
| left : ∀ q x q' y z γL γR, M.δ q x = some (q',y,L)
        → Step ((z::γL,q,x::γR) , (γL,q',z::y::γR))
| right_rightEnd : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,R)
        → Step ((γL,q,[]) , (y::γL,q',[]))
| left_rightEnd : ∀ q q' y z γL, M.δ q (inl M.B) = some (q',y,L)
        → Step ((z::γL,q,[]) , (γL,q',[z,y]))
| left_empty : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,L)
        → Step (([],q,[]) , (γL,q',[inl M.B,y]))
| leftEnd : ∀ q q' x y γR, M.δ q x = some (q',y,L)
         → Step (([],q,x::γR) , ([],q',(inl M.B)::y::γR))

-- every word can be turned into a tape
abbrev word2tape : Word Sigma → List (Sym M)
| w => List.map inr w

-- we repeat the defn of the Star
-- (I need to refactor this)
private inductive StarRel {A : Type}(R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , StarRel R (a , a)
| step : ∀ a b c , R (a , b)
      → StarRel R (b , c) → StarRel R (a , c)
-- transitive, reflexive closure

-- the initial state given by a word
abbrev init : Word Sigma → ID M
| w => ([],M.s,word2tape M w)

-- an ID is accepting if the state is final.
-- We keep this as Bool because it is decidable.
abbrev accepts : ID M → Bool
| (_,q,_) => q ∈ M.F

-- the language of a TM
abbrev L : Lang Sigma
:= { w | ∃ st , accepts M st = true ∧
         StarRel (Step M) (init M w,st)}

abbrev step_f : ID M → Option (ID M)
| (γL,q,x :: γR) =>
    match M.δ q x with
    | some (q',y,Dir.R) => some (y::γL,q',γR)
    | some (q',y,Dir.L) =>
         match γL with
         | [] => some ([],q',(inl M.B)::y::γR)
         | z::γL' => some (γL',q',z::y::γR)
    | none => none
| (γL,q,[]) =>
    match M.δ q (inl M.B) with
    | some (q',y,Dir.R) => some (y::γL,q',[])
    | some (q',y,Dir.L) =>
      match γL with
         | [] => some ([],q',(inl M.B)::y::[])
         | z::γL' => some (γL',q',z::y::[])
    | none => none

open Nat

abbrev stepn_f : ℕ → ID M → Option (ID M)
| zero , st => some st
| succ n , st =>
    if accepts M st
    then some st
    else match step_f M st with
      | none => none
      | some st' => stepn_f n st'

-- the language after running n steps
abbrev L_n : ℕ → Word Sigma → Bool
| n , w => match stepn_f M n (init M w) with
         | none => false
         | some st => accepts M st


end Tm

namespace TMEx

open Tm
open Examples
open SigmaABC
open Sum
open Dir

inductive Γb : Type
| blank | X | Y | Z
deriving Fintype, DecidableEq, Repr
open Γb

abbrev Manbncn : TM SigmaABC
:= { Q := Fin 7
     Γ := Γb
     s := 0
     B := blank
     F := { 6 }
     δ q x := match q , x with
              | 0 , inr a => some (1,inl X, R )
              | 1 , inr a => some (1,inr a, R )
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



-- some examples

#eval (L_n  Manbncn 1000 [])
#eval (L_n  Manbncn 1000 [a,b,c])
#eval (L_n  Manbncn 1000 [a,a,b,b,c,c])
#eval (L_n  Manbncn 1000 [a,a,b,c,c])
#eval (L_n  Manbncn 1000 [a,a,b,b,b,c,c])
#eval (stepn_f Manbncn 7 (init Manbncn [a,b,c]))
#eval (stepn_f Manbncn 11 (init Manbncn [a,a,b,b,c,c]))
