import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC nfaDfa
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

structure DFA : Type 1 where
  Q : Type -- state
  [alphQ : Alphabet Q]
  s : Q -- initial state
  F : Finset Q -- set of final states
  δ : Q → Sigma → Q

structure NFA : Type 1 where
  Q : Type -- states
  S : Finset Q -- a set of initial states
  F : Finset Q -- set of final states
  δ : Q → Sigma → Finset Q

inductive StateEqParity : Type
| EE | EO | OE | OO
deriving Fintype, DecidableEq
open StateEqParity

abbrev DFA_aeqbmod2 : DFA SigmaABC :=
{
  Q := StateEqParity
  s := EE
  F := {EE,OO}
  δ := λ | EE, a => EO
         | EE, b => OE
         | EE, c => EE
         | EO, a => EE
         | EO, b => OO
         | EO, c => EO
         | OE, a => OO
         | OE, b => EE
         | OE, c => OE
         | OO, a => EO
         | OO, b => OE
         | OO, c => OO
}

example : [a,b,c] ∈ L DFA_aeqbmod2 := by aesop

abbrev NFA_no010or01 : NFA SigmaBin :=
{
  Q := Fin 3
  S := {0,1}
  F := {1}
  δ := λ | 0,0 => ∅
         | 0,1 => {0,1}
         | 1,0 => {1,2}
         | 1,1 => {0}
         | 2,0 => ∅
         | 2,1 => {0,2}
}

example : [0,1,1] ∈  L NFA_no010or01 := by simp [Nfa.L,Nfa.δ_star,δ_step]

def dfa2nfa' (A : DFA Sigma) : NFA Sigma
:= {
  Q := A.Q
  S := {A.s}
  F := A.F
  δ := λ s w ↦ { A.δ s w }
}

abbrev NFA_aeqbmod2 : NFA SigmaABC :=
{
  Q := StateEqParity
  S := { EE }
  F := {EE,OO}
  δ := λ | EE, a => { EO }
         | EE, b => { OE }
         | EE, c => { EE }
         | EO, a => { EE }
         | EO, b => { OO }
         | EO, c => { EO }
         | OE, a => { OO }
         | OE, b => { EE }
         | OE, c => { OE }
         | OO, a => { EO }
         | OO, b => { OE }
         | OO, c => { OO }
}

#check (dfa2nfa DFA_aeqbmod2)
example : Dfa.L DFA_aeqbmod2 = Nfa.L (dfa2nfa DFA_aeqbmod2) := by apply dfa2nfa_ok

def nfa2dfa' (A : NFA Sigma) : DFA Sigma
:= {
  Q := Finset A.Q
  s := A.S
  F := ⟪ S ∈ nfaDfa.Pow A.Q |
    ∃ (q : A.Q) , q ∈ S ∧ q ∈ A.F
  ⟫
  δ := δ_step A
}

#check nfa2dfa NFA_no010or01
example : [0,1,1] ∈ L (nfa2dfa NFA_no010or01) := by simp [nfa2dfa,Dfa.δ_star,δ_step]

example : Nfa.L NFA_no010or01 = Dfa.L (nfa2dfa NFA_no010or01) := by apply nfa2dfa_ok

abbrev DFA_no010or01 : DFA SigmaBin :=
{
  Q := Finset (Fin 3) -- {},{0},{1},{2},{0,1},{0,2},{1,2},{0,1,2}
  s := {0,1}
  F := {{1},{0,1},{1,2},{0,1,2}}
  δ := δ_step NFA_no010or01
}
