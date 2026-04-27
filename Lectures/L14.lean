import Proofs.Lang
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype

namespace pda

macro "⟪" q:ident " | " P:term "⟫" : term =>
  `( (Finset.univ).filter (fun $q => $P) )
macro "⟪" q:ident " ∈ " xs:term " | " P:term "⟫" : term =>
  `( ($xs).filter (fun $q => $P) )

open Lang Lang.Examples SigmaABC Sum
variable (Sigma : Type)[Alphabet Sigma]

-- What have we seen so far?
/-
Chomsky Hierarchy
Level 3: Regular languages
 - DFA = NFA = RE
Level 2: Context-free languages
 - CFGs
 - [N]PDAs
 - DPDAs
We have CFG = PDA, but DPDA ≠ NPDA!
Level 1: Context-sensitive languages
 - Context-sensitive grammars
Level 0: Recursively enumberable languages
 - Turing Machines (TMs)
[Nondeterministic TM = deterministic TM]
-/
structure PDA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- Stack alphabet
  [alphΓ : Alphabet Γ]
  s : Q -- initial state
  Z₀ : Γ -- initial stack state
  F : Finset Q -- set of final states
  δ : Q → Option Sigma → Γ → Finset (Q × List Γ) -- transition function

open PDA
variable {Sigma : Type}[Alphabet Sigma]
variable (P : PDA Sigma)

abbrev P₁ : PDA SigmaABC
:= {
  Q := Fin 3
  Γ := Sum (Fin 1) SigmaABC
  s := 0
  Z₀ := inl 0
  F := { 2 }
  δ q x γ :=
    match q, x, γ with
    | 0, some x, z => {(0, [inr x,z])}
    | 0, none, z => {(1,[z])}
    | 1, some a, inr a => {(1,[])}
    | 1, some b, inr b => {(1,[])}
    | 1, some c, inr c => {(1,[])}
    | 1, none, inl 0 => {(2,[])}
    | _,_,_ => {}
}

abbrev ID : Type := P.Q × Word Sigma × List P.Γ
-- instantaneous description

/-
A word w is accepted iff there exists a sequence of IDs
produced by the transitions in the PDA that ends with
the word empty and the state in a final state.

E.g., abba ∈ L P₁:
(0, [a,b,b,a], [inl 0])
-> (0, [b,b,a], [inr a, inl 0])
-> (0, [b,a], [inr b,inr a,inl 0])
-> (1, [b,a], [inr b,inr a,inl 0])
-> (1, [a], [inr a,inl 0])
-> (1, [], [inl 0])
-> (2, [], [])
-/
abbrev isDet : Prop
:=  ∀ q x z ,
    Fintype.card (P.δ q (some x) z) + Fintype.card (P.δ q none z) ≤ 1
/-
For NFAs, we could create an equivalent DFA by remembering
all states the NFA could be in concurrently.
For PDAs, this doesn't work, as the "state" would have to
include the stack (which gives infinitely many possibilities.)
Some context-free languages are inherently non-deterministic,
palindromes is one of them.

So DPDA ≠ NPDA, how about CFG?
We can create a CFG for palindromes:
-/
structure CFG' : Type 1 where
  NT : Type
  [ alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma))

open Cfg CFG

abbrev CFG₁ : CFG SigmaABC
:= {
  NT := Fin 1
  S := 0
  P := {
    (0, [inr a, inl 0, inr a]),
    (0, [inr b, inl 0, inr b]),
    (0, [inr c, inl 0, inr c]),
    (0, [inr a]),
    (0, [inr b]),
    (0, [inr c]),
    (0, [])
  }
}
/-
This is commonly written in shorthand as
0 := a0a | b0b | c0c | a | b | c | ε

A CFG accepts words by means of the derivation tree.
We can simulate this process using a PDA!

All we need is 1 state, pushing the productions from the
CFG using an ε transition whenever the top of the stack
is a NT and reading terminals popping them from the stack.
-/

variable (G : CFG Sigma)
abbrev cfg2pda : PDA Sigma :=
{ Q := Fin 1
  Γ := G.NT ⊕ Sigma
  s := (0 : Fin 1)
  Z₀ := inl G.S
  δ := fun q x z =>
    match x, z with
    | none, inl A =>
        (⟪ p ∈ G.P | p.1 = A ⟫).biUnion
          (fun p => { ((0 : Fin 1), p.2) })
    | some x, inr y =>
        if h : x = y then
          { ((0 : Fin 1), ([] : List (G.NT ⊕ Sigma))) }
        else
          {}
    | _, _ => {}
  F := {}   -- acceptance by empty stack
}

end pda
