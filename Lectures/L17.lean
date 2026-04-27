import Proofs.Lang
import Proofs.Pda
import Proofs.Autom

open Lang Examples SigmaABC Sum
open Dfa hiding L
open Pda hiding L

/-
Where are we, what are we talking about?

We've moved up the Chomsky hierarchy, currently covering level 0 and 1

Level 3 was:
NFA/DFA (+RE)
In Level 2 we added memory:
PDA = NFA + stack
Now we're in level 0:
TM = DFA + tape

Example:
-/
abbrev anbncn : Lang SigmaABC
:= { a^n ++ b^n ++ c^n | n : ℕ }
-- on automataverse


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
   s : Q -- inital state
   B : Γ -- blank tape character
   F : Finset Q -- set of final states
   δ : Q → Γ ⊕ Sigma
       → Option (Q × (Γ ⊕ Sigma) × Dir) -- transition function

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

/-
So how do these machines recognise languages?

Intuitively, the machine will move along the tape
performing transformations until it reaches a
final state (or it cannot move)

Formally, we will need to define what a configuration
of the machine is and how to move between configurations
exactly as we move along the tape.

For NFAs, the configuration of the machine as it
reads a word is simple:
-/
abbrev ID_DFA (A : DFA Sigma) : Type
:= A.Q × Word Sigma
-- The initial configuration is given by the word and initial state
abbrev init_dfa (A : DFA Sigma) : Word Sigma → ID_DFA A
| w => (A.s, w)
-- And one can take transitions in A to transfer between configurations:
inductive Step_dfa (A : DFA Sigma) : (ID_DFA A × ID_DFA A) → Prop
| read => ∀ q q' x w,
        q' = A.δ q x →
          Step_dfa A ((q, x::w), (q', w))
-- Lean doesn't like this definition because it can't figure out
-- that it terminates, but it does.

-- Acceptance is then given by whether the reflexive transitive
-- closure of Step_dfa reaches an accepting state
abbrev accept_dfa (A : DFA Sigma) : ID_DFA A → Prop
| (q, []) => q ∈ A.F
| _ => False

inductive Star' {A : Type}(R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , Star' R (a , a)
| step : ∀ a b c , R (a , b)
      → Star' R (b , c) → Star' R (a , c)
-- transitive, reflexive closure

abbrev L_DFA (A : DFA Sigma) : Lang Sigma
:= { w | ∃ fid, Star' (Step_dfa A) (init_dfa A w, fid) ∧ accept_dfa A fid}

-- We have seen the same structure for PDAs, extending the ID
-- with the stack contents and adjusting the step function accordingly:
abbrev ID_PDA (P : PDA Sigma) : Type
:= P.Q × Word Sigma × List P.Γ
-- With initial configuration
abbrev init_pda (P : PDA Sigma) : Word Sigma → ID_PDA P
| w => (P.s,w,[P.Z₀])
-- and step function
inductive Step_pda (P : PDA Sigma) : (ID P × ID P ) → Prop
| read : ∀ q q' α x w z γ ,
    (q' , α ) ∈ P.δ q (some x) z →
       Step_pda P ((q , x :: w, z :: γ) , (q' , w , α ++ γ ) )
| silent : ∀ q q' α w z γ ,
    (q' , α ) ∈ P.δ q none z →
       Step_pda P ((q , w , z :: γ) , (q' , w , α ++ γ ))
-- And acceptance
abbrev accept_pda (P : PDA Sigma) : ID_PDA P → Prop
| (q', [], _) => q' ∈ P.F
| _ => False
-- The language
abbrev L_PDA (P : PDA Sigma) : Lang Sigma
:= { w | ∃ fid, Star' (Step_pda P) (init_pda P w, fid) ∧ accept_pda P fid}

/-
Now it's time to define this structure for TMs.
What is required to describe a TM fully at any configuration? As we go
through the operations of the TM, what do we need to know to completely
specify its computation?
 - The tape contents
 - The current state
 - The position of the head
However, the tape is infinite!
But the number of transitions is not, and each step we can only take
one step in any directions, so we only need to remember the part of the
tape that the machine has seen.
One way to remember the tape and the position of the head, is using
a massive array and index within the array. However, this is inefficient
whenever we go beyond our current bounds.
Smarter way to do it: two linked lists!
One for everthing from the head onwards, and one reading backwards
until the first unread character.
-/
abbrev Sym : Type := M.Γ ⊕ Sigma

abbrev ID : Type
:= List (Sym M) × M.Q × List (Sym M)

-- What's the initial configuration?
def word2tape : List Sigma → List (Sym M)
| w => List.map inr w

abbrev init : Word Sigma → ID M
| w => ([] , M.s, word2tape M w )

-- The step function needs some careful analysis, in particular
-- whenever we reach the ends of the part of the tape that we've
-- read so far.
inductive Step : ID M × ID M → Prop
-- Easy when we're in the middle of the tape
| right : ∀ q x q' y γL γR, M.δ q x = some (q',y,R)
        → Step ((γL,q,x::γR) , (y::γL,q',γR))
| left : ∀ q x q' y z γL γR, M.δ q x = some (q',y,L)
        → Step ((z::γL,q,x::γR) , (γL,q',z::y::γR))
-- Special cases when we're at the right end of the tape
| right_rightEnd : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,R)
        → Step ((γL,q,[]) , (y::γL,q',[]))
| left_rightEnd : ∀ q q' y z γL, M.δ q (inl M.B) = some (q',y,L)
        → Step ((z::γL,q,[]) , (γL,q',[z,y]))
-- Special cases when we're at the left end of the tape
| left_empty : ∀ q q' y γL, M.δ q (inl M.B) = some (q',y,L)
        → Step (([],q,[]) , (γL,q',[inl M.B,y]))
| leftEnd : ∀ q q' x y γR, M.δ q x = some (q',y,L)
         → Step (([],q,x::γR) , ([],q',(inl M.B)::y::γR))

-- Acceptance is easy
abbrev accept : ID M → Prop
| (_,q,_) => q ∈ M.F

abbrev L : Lang Sigma
:= { w | ∃ st , Star' (Step M) (init M w,st)
      ∧ accept M st}
