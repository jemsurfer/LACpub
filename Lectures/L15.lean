import Proofs.Lang
import Mathlib.Tactic.DeriveFintype
import Proofs.CFG

/-
How to write a compiler?
How to write parser_



-/


open Lang

variable {Sigma : Type}[Alphabet Sigma]

open Cfg
open Sum

variable (G : CFG Sigma)

inductive SigmaA : Type
| lpar | rpar | a | plus | times
deriving Fintype, DecidableEq
open SigmaA

abbrev First (α : Sent G) : Set Sigma
:= { a | ∃ β ,  DerivStar G (α  , a :: β ) }

abbrev Follow (A : G.NT) : Set (Option Sigma)
:= { x | ∃ α β a , x = some a ∧ DerivStar G ([inl G.S] , α++[inl A, inr a]++β)}
  ∪ { none | ∃ α , DerivStar G ([inl G.S] , α++[inl A]) }

abbrev LA (A : G.NT)(α : Sent G) : Set (Option Sigma) :=
  {some x | x ∈ First G α } ∪ {x | x ∈ Follow G A ∧ α  = [] }

abbrev isLL1 :=
  ∀ A , ∀ α β , (A , α ) ∈ G.P ∧ (A , β ) ∈ G.P
              ∧ α ≠ β → LA G A α ∩ LA G A β = {}

/-
E → T E'
E' → ε | + T E'
T → F T'
T' → ε | * F T'
F → a | ( E )

LA E' ε = {* , ) , $}
LA E' +TE = { + }

LA F' ε = { ) , $ }
-/



namespace Ga
inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq
open NTA

abbrev GA : CFG SigmaA :=
{ NT := NTA
  S := E
  P := { (E, [inl T]),
         (E , [inl E,inr plus,inl T]),
         (T, [inl F]),
         (T , [inl T,inr times,inl F]),
         (F, [inr SigmaA.a]),
         (F, [inr lpar,inl E,inr rpar])}
   }

end Ga

namespace Ex
inductive SigmaAB : Type where
| a | b

open SigmaAB

-- abbrev GG : CFG SigmaAB :=
-- {
--   NT := Fin 1
--   S := 0
--   P := { (0 , [inr a, inl 0, inr a] ),
--          (0 , [inr b, inl 0, inr b] ),
--          (0 , [])}
-- }

-- end Ex
