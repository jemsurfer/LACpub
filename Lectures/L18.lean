import Proofs.TM

namespace halt

open Tm Lang Lang.Examples Classical

inductive Star' {A : Type}(R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , Star' R (a , a)
| step : ∀ a b c , R (a , b)
      → Star' R (b , c) → Star' R (a , c)
-- transitive, reflexive closure


variable {Sigma : Type}
[Fintype Sigma][DecidableEq Sigma]

variable (M : TM Sigma)

/-
What have we seen so far? Chomsky hierarchy!
Draw all languages, level 0 (RE), level 1 (CSL), level 2 (CFL), level 3 (REG)
Leave space for decidable languages
How is each recognised? Using NFA/DFA/RE,CFG/PDA,bounded TM/noncontracting grammar,TM
But how? From the initial ID, if we can reach an accepting ID then the word is accepted:
-/
abbrev accepts : ID M → Bool
| (_,q,_) => q ∈ M.F

abbrev L : Lang Sigma
:= { w | ∃ st , accepts M st ∧
         Star' (Step M) (init M w,st)}
/-
For NFAs, each step takes into consideration the next character of the word
Hence, this process is guaranteed to terminate
For PDAs, we may have loops over ε arrows, but we can detect and remove these
For TMs, either we end up in some state for which there is no successor state
Or we end up in a loop.
We say that we're stuck if there's no successor state:
-/
abbrev stuck : ID M → Prop
| st => ¬ ∃ st' , Step M (st,st')
-- And all words that eventually hit a stuck state are clearly rejected:
abbrev L_no : Lang Sigma
:= { w | ∃ st , stuck M st ∧
         Star' (Step M) (init M w,st)}
-- The set of all words, all inputs, on which the TM either accepts or gets stuck
-- is the halting language of the TM
abbrev L_halts : Lang Sigma
:= {w | w ∈ L M ∨ w ∈ L_no M}
-- And a TM _decides_ its language if it can say yes or no to all words
abbrev decides : Prop
:= ∀ w, w ∈ L_halts M

----
/-
What is the halting problem?
It asks whether a given TM and input halts
So, it is a language! Remember, Set T == T → Prop
And if it is a language, then we may be able to create a machine recognising the language
We'll need to encode the TM and input to a single input
Firstly, combine two words injectively:
-/
abbrev SigmaBin : Type
:= Fin 2 -- 0 , 1

abbrev expand : Word SigmaBin → Word SigmaBin
| [] => []
| (x::w) => 0::x::(expand w)

def pair : Word SigmaBin × Word SigmaBin
→ Word SigmaBin
| (w,v) => expand w ++ [1] ++ expand v

axiom pair_injective : Function.Injective pair
/-
Once we've done that, we need to encode our TM and combine it with its input
to act as the word for our machine recognising the halting problem
-/
abbrev encodeTM : TM SigmaBin → Word SigmaBin
:= sorry

axiom encodeTM_injective : Function.Injective encodeTM

abbrev encode : TM SigmaBin × Word SigmaBin → Word SigmaBin
| (M, x) => pair (encodeTM M,x)

-- The halting problem is then the language of halting encodings of TMs and their inputs:
abbrev halting_encodings : Lang SigmaBin
:= { w | ∃ M v , w = encode (M,v) ∧ v ∈ L_halts M}

-- an interpreter for TM
/-
Turns out, TMs are powerful enough to simulate a given TM!
-/
abbrev U : TM SigmaBin -- universal TM
:= sorry

theorem U_ok : ∀ w M, encode (M, w) ∈ L u
                      ↔ w ∈ L M := sorry
-- Basic idea: draw on whiteboard. Show UTM picture, say it's too big to implement during the lecture

/-
So if we can simulate TMs, then we can also just accept whenever we reach a stuck state!
-/
abbrev H : TM SigmaBin
:= sorry

theorem H_ok : L H = halting_encodings := sorry
-- Hence, H accepts the halting problem! Halting Problem is in RE
-- But wait, isn't the halting problem undecidable?
-- Yes, so that must mean any TM recognising the Halting Problem does not decide.
-- There are inputs for which it runs forever.

-- Assume we have a TM that decides the halting problem
variable (DH : TM SigmaBin)
axiom L_DH : L DH = halting_encodings
axiom d_DH : decides DH

-- By simulating this TM, we can create a machine that runs forever on all inputs
-- that encode a halting TM with its own encoding as input
abbrev W : TM SigmaBin
:= sorry

lemma W_ok : ∀ w, w ∈ L_halts W ↔
      pair (w,w) ∉ L DH
:= sorry

-- The idea is that we feed it with its own encoding as input
lemma W1 : encodeTM W ∈ L_halts W ↔
            pair (encodeTM W, encodeTM W) ∉ L DH
:= by apply W_ok

-- But the language of DH is precisely the halting encodings!
lemma W2 (DH : TM SigmaBin) : encodeTM W ∈ L_halts W ↔
            pair (encodeTM W, encodeTM W) ∉ halting_encodings := by
            rw [←L_DH DH]
            apply W1

-- And by the definition of the halting encodings, that must mean that W does not halt on its own encoding - contradiction!
lemma W3 (DH : TM SigmaBin) : encodeTM W ∈ L_halts W ↔ encodeTM W ∉ L_halts W := by
  constructor
  · intro inhalts
    apply (W2 DH).1 at inhalts
    intro inhalts2
    apply inhalts
    exists W
    exists encodeTM W
  · intro ninhalts
    apply (W2 DH).2
    intro pair
    apply ninhalts
    cases pair with
    | intro TM form =>
      cases form with
      | intro pword form =>
        cases form with | intro encword winlang
        rw [encode] at encword
        have eq : (encodeTM W, encodeTM W) = (encodeTM TM, pword) := by
          apply pair_injective
          assumption
        have tmeqw : W = TM := by
          apply encodeTM_injective
          injection eq
        have pwordeqencw : encodeTM W = pword := by
          injection eq
        rw [pwordeqencw]
        rw [tmeqw]
        exact winlang

-- And from that contradiction we derive falsehood, we have proven False = True and pigs can fly!
lemma boom (DH : TM SigmaBin) : ⊥ := by
  have boom : encodeTM W ∈ L_halts W ↔ encodeTM W ∉ L_halts W := by apply W3; apply DH
  cases boom with
  | intro lr rl =>
    apply lr
    apply rl
    intro inhalts
    apply lr
    exact inhalts
    exact inhalts
    apply rl
    intro inhalts
    apply lr
    exact inhalts
    exact inhalts

end halt
