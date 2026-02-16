import Proofs.Lang
import Proofs.Autom

open Lang Dfa DFA Nfa NFA Lang.Examples SigmaABC nfaDfa
variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

/-
Lecture structure:
 - Start off with DFA definition, 1 example
 - Next, NFA definition, 2 examples
 - Explain that NFAs can simulate DFAs; in fact, they're pretty much the same thing. Use first DFA example
 - Explain that DFAs can simulate NFAs; they just represent programs with limited memory
 - Take 2nd NFA example, and show intuitive translation from NFA to DFA
 - Show full definition dfa2nfa and nfa2dfa in Lean
 - Show that dfa2nfa A is an NFA and nfa2dfa A2 is a DFA, use #reduce to show the state sets (and
 the mess of everything else)
 - Show L A₁ = L (dfa2nfa A₁) and L A₃ = L (nfa2dfa A₃) by our auxiliary proofs
-/

structure DFA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  s : Q    -- initial state
  F : Finset Q -- set of final states
  δ : Q → Sigma → Q

inductive StateEqParity : Type
| EE | EO | OE | OO
deriving Fintype, DecidableEq
open StateEqParity

abbrev DFA_aeqbmod2 : DFA SigmaABC :=
  {
    Q := StateEqParity
    s := EE
    F := {EE , OO}
    δ := λ  | EE , a => OE
            | EE , b => EO
            | OE , a => EE
            | OE , b => OO
            | EO , a => OO
            | EO , b => EE
            | OO , a => EO
            | OO , b => OE
            | q  , c => q
 }

 example : [a,b,b,a] ∈ L DFA_aeqbmod2 := by aesop

 structure NFA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  S : Finset Q
  δ : Q → Sigma → Finset Q

abbrev NFA_no010or01 : NFA SigmaBin :=
  {
    Q := Fin 3
    S := { 0, 1 }
    F := { 1 }
    δ := λ | 0,0 => ∅
           | 0,1 => {0,1}
           | 1,0 => {1,2}
           | 1,1 => {0}
           | 2,0 => ∅
           | 2,1 => {2,0}
  }

example : [1,1,0] ∈ L NFA_no010or01 := by simp [Nfa.L,δ_step,Nfa.δ_star]; decide

abbrev NFA_00or001then1 : NFA SigmaBin :=
{
  Q := Fin 5
  S := { 0 }
  F := { 4 }
  δ := λ | 0, 0 => {1,2}
         | 0, 1 => {4}
         | 1, 0 => {0}
         | 1, 1 => ∅
         | 2, 0 => {3}
         | 2, 1 => ∅
         | 3, 0 => ∅
         | 3, 1 => {0}
         | 4, _ => ∅
}

example : [0,0,1,1] ∈ L NFA_00or001then1 := by simp [Nfa.L,δ_step,Nfa.δ_star]

def dfa2nfa' (A : DFA Sigma) : NFA Sigma
:= { Q := A.Q
     S := {A.s}
     F := A.F
     δ := λ s w ↦ { A.δ s w}}

abbrev NFA_aeqbmod2 : NFA SigmaABC :=
  {
    Q := StateEqParity
    S := { EE }
    F := {EE , OO}
    δ := λ  | EE , a => { OE }
            | EE , b => { EO }
            | OE , a => { EE }
            | OE , b => { OO }
            | EO , a => { OO }
            | EO , b => { EE }
            | OO , a => { EO }
            | OO , b => { OE }
            | q  , c => { q }
 }

#check (dfa2nfa DFA_aeqbmod2)
example : L DFA_aeqbmod2 = L (dfa2nfa DFA_aeqbmod2) := by apply dfa2nfa_ok

def nfa2dfa' (A : NFA Sigma) : DFA Sigma
:= {
  Q := Finset A.Q
  s := A.S
  F := ⟪ S ∈ nfaDfa.Pow A.Q |
    ∃ (q : A.Q) , q ∈ S ∧ q ∈ A.F ⟫
  δ := δ_step A
}

abbrev DFA_no010or01 : DFA SigmaBin :=
  {
    Q := Finset (Fin 3)
    s := { 0, 1 }
    F := { { 1 }, {0,1}, {1,2}, {0,1,2} }
    δ := δ_step NFA_no010or01
  }

#check (nfa2dfa NFA_no010or01)
example : L NFA_no010or01 = L (nfa2dfa NFA_no010or01) := by apply nfa2dfa_ok
