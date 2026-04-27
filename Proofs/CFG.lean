import Proofs.Lang

namespace Cfg
open Lang

variable (Sigma : Type)[Alphabet Sigma]

-- ANCHOR: CFG
structure CFG : Type 1 where
  NT : Type
  [ alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma ))
-- ANCHOR_END: CFG

instance {G : CFG Sigma} : Alphabet G.NT :=
  G.alphNT

open CFG
open Sum

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

-- ANCHOR: Symbol
abbrev Symbol : Type
  := G.NT ⊕ Sigma
-- ANCHOR_END: Symbol

scoped instance : Coe G.NT (Symbol G) :=
  ⟨Sum.inl⟩

scoped instance : Coe Sigma (Symbol G) :=
  ⟨Sum.inr⟩
-- ANCHOR: Sent
abbrev Sent : Type
  := Word (Symbol G)
-- ANCHOR_END: Sent

-- ANCHOR: Deriv
abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) | ∃ α₁ α₂ ,
      ∃ A , α = α₁ ++ [inl A] ++ α₂
      ∧ ∃ γ , (A , γ) ∈ G.P
      ∧ β = α₁ ++ γ ++ α₂ }
-- ANCHOR_END: Deriv
-- infixr:70 " ⟹ " => Deriv

variable {A : Type}
-- ANCHOR: Star
inductive Star (R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , Star R (a , a)
| step : ∀ a b c , R (a , b)
      → Star R (b , c) → Star R (a , c)
-- ANCHOR_END: Star

-- transitive, reflexive closure
-- inductive DerivStar : Sent G × Sent G → Prop
-- | refl : ∀ α , DerivStar (α , α)
-- | step : ∀ α β γ ,
--     Deriv G (α , β) → DerivStar (β , γ)
--     → DerivStar (α , γ)

-- ANCHOR: emb
abbrev emb : Word Sigma → Sent G
:= List.map inr
-- ANCHOR_END: emb

-- ANCHOR: CFG_L
abbrev L : Lang Sigma
:= { w | Star (Deriv G) ([inl G.S],emb G w)}
-- ANCHOR_END: CFG_L

end Cfg



namespace CfgEx
open Lang
open Cfg
open Sum
open scoped Cfg.CFG

-- ANCHOR: SigmaE
inductive SigmaE : Type
| lpar | rpar | a | plus | times
-- ANCHOR_END: SigmaE
deriving Fintype, DecidableEq
open SigmaE
/-
a + a
a + a * a
(a + a) * a
-/
#check ([a,plus,a] : Word SigmaE)
#check ([a,plus,a,times,a] : Word SigmaE)
#check ([lpar,a,plus,a,rpar,times,a] : Word SigmaE)


namespace Ge
-- ANCHOR: NTE
inductive NTE : Type
| E | T | F
-- ANCHOR_END: NTE
deriving Fintype, DecidableEq
open NTE

-- ANCHOR: GE
abbrev GE : CFG SigmaE
:= { NT := NTE,
     S := E,
     P := { (E , [ inl T ]),
            (E , [ inl E , inr plus, inl T]),
            (T , [ inl F]),
            (T , [ inl T, inr times, inl F]),
            (F , [ inr a]),
            (F , [ inr lpar , inl E, inr rpar])
            }
}
-- ANCHOR_END: GE

--( E ) * a ⇒ ( E + T ) * a`
example :
-- ANCHOR: DerivEx
([inr lpar,inl E,inr rpar,inr times,inr a],
[inr lpar,inl E,inr plus,inl T,inr rpar,inr times,inr a])
∈ Deriv GE
-- ANCHOR_END: DerivEx
:= by sorry

example :
-- ANCHOR: LEx
[lpar,a,plus,a,rpar,times,a] ∈ L GE
-- ANCHOR_END: LEx
:= by sorry

example :
-- ANCHOR: LExn
[a,plus,plus,a] ∉ L GE
-- ANCHOR_END: LExn
:= by sorry

end Ge

namespace Ge2

inductive NTAA : Type
| E
deriving Fintype, DecidableEq

open NTAA
open SigmaE
open Sum

-- ANCHOR: GAA
abbrev GAA : CFG SigmaE :=
{ NT := NTAA
  S := E
  P := { (E, [inl E,inr plus,inl E]),
         (E, [inl E,inr times,inl E]),
         (E, [inr a]),
         (E, [inr lpar,inl E,inr rpar])}
}
-- ANCHOR_END: GAA

end Ge2
end CfgEx

namespace CfgEx2
open Lang
open Cfg
open Sum
--open Examples
--open SigmaABC

inductive SigmaAB : Type
| a | b | c
deriving Fintype, DecidableEq
--deriving Fintype, DecidableEq, Repr
open SigmaAB

-- ANCHOR: Ganbn
abbrev Ganbn : CFG SigmaAB :=
{
  NT := Fin 1
  S := 0
  P := { (0 , [] ),
         (0 , [inr a, inl 0, inr b])}
}
-- ANCHOR_END: Ganbn


-- ANCHOR: anbn
abbrev anbn : Lang SigmaAB
:= { a^n ++ b^n | (n : ℕ)}
-- ANCHOR_END: anbn

example :
[a,a,b,b] ∈ L Ganbn
:= by sorry

example :
[a,b,b] ∉ L Ganbn
:= by sorry

example :
L Ganbn = anbn
:= by sorry

-- ANCHOR: Gpali
abbrev Gpali : CFG SigmaAB :=
{
  NT := Fin 1
  S := 0
  P := { (0 , [] ),
         (0 , [inr a, inl 0, inr a]),
         (0 , [inr b, inl 0, inr b]),
         (0, [inr a]),
         (0, [inr b])
         }
}
-- ANCHOR_END: Gpali

example :
[a,b,b,a] ∈ L Gpali
:= by sorry

example :
[a,b,b] ∉ L Gpali
:= by sorry

-- ANCHOR: pali
abbrev pali : Lang SigmaAB
:= { w | List.reverse w = w}
-- ANCHOR_END: pali

example :
L Gpali = pali
:= by sorry

end CfgEx2


namespace ParseTrees

open Lang
open Cfg

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

open Sum

-- ANCHOR: PT
mutual

  inductive PT : G.NT → Type where
  | node : ∀ {A} , ∀ {α} ,
            (A , α ) ∈ G.P
            → PTSent α → PT A

  inductive PTSent : Sent G → Type where
  | nil : PTSent []
  | NT : ∀ {A α }, PT A → PTSent α → PTSent (inl A :: α)
  | T : ∀ a {α} , PTSent α →  PTSent (inr a :: α)

end
-- ANCHOR_END: PT

-- ANCHOR: yield
mutual
  def yield {A : G.NT} : PT G A → Word Sigma
  | PT.node _ pα => yieldSent pα

  def yieldSent {α : Sent G} : PTSent G α → Word Sigma
  | PTSent.nil => []
  | PTSent.NT pA pα  => yield pA ++ yieldSent pα
  | PTSent.T a pα => a :: yieldSent pα

end
-- ANCHOR_END: yield

-- ANCHOR: L_tree
abbrev L_tree : Lang Sigma
:= { w | ∃ p : PT G G.S , w = yield G p }
-- ANCHOR_END: L_tree

theorem L_tree_ok : L_tree G = Cfg.L G := by sorry

-- ANCHOR: Amb
abbrev Amb : Prop :=
  ∃ (w : Word Sigma ) (A : G.NT) (t₁ t₂ : PT G A),
    yield G t₁ = w ∧
    yield G t₂ = w ∧
    t₁ ≠ t₂
-- ANCHOR_END: Amb

end ParseTrees

namespace ParseTreeEx

open CfgEx.Ge2
open ParseTrees
open CfgEx
open SigmaE
open Sum

abbrev p1 : PT GAA NTAA.E :=
by
  refine
    PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr plus, inl NTAA.E])
      (by simp [GAA])
      ?_
  -- RHS: E plus E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) plus ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr times, inl NTAA.E])
        (by simp [GAA])
        ?_)
      (PTSent.nil (G := GAA))
  -- RHS: E times E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) times ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))

-- ANCHOR: p1_yield
lemma p1_yield : yield GAA p1 = [a,plus,a,times,a]
-- ANCHOR_END: p1_yield
  := by rfl

abbrev p2 : PT GAA NTAA.E :=
by
  refine
    PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr times, inl NTAA.E])
      (by simp [GAA])
      ?_
  -- RHS: E times E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr plus, inl NTAA.E])
        (by simp [GAA])
        ?_)
      ?_
  -- left: E plus E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) plus ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))
  -- then `times` and the right `a`
  refine PTSent.T (G := GAA) times ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))

-- ANCHOR: p2_yield
lemma p2_yield : yield GAA p2 = [a,plus,a,times,a]
-- ANCHOR_END: p2_yield
  := by rfl

def rootOp : PT GAA NTAA.E → Option SigmaE
| PT.node (A := _) (α := α) _ _ =>
    match α with
    | [Sum.inl _, Sum.inr op, Sum.inl _] => some op
    | _ => none

-- ANCHOR: p1p2
lemma p1p2 : (p1 : PT GAA NTAA.E) ≠ (p2 : PT GAA NTAA.E)
-- ANCHOR_END: p1p2
  := by
  intro h
  have : rootOp p1 = rootOp p2 := by
    simp [h]
  simpa [p1, p2, rootOp, GAA] using this

-- ANCHOR: amb_gaa
theorem amb_gaa : Amb GAA
-- ANCHOR_END: amb_gaa
  := by
  refine ⟨[a,plus,a,times,a], NTAA.E, p1, p2, ?_, ?_, ?_⟩
  . rfl
  . rfl
  . apply p1p2

end ParseTreeEx

namespace CfgArith
open Lang Cfg Sum

-- ANCHOR: SigmaA
inductive SigmaA : Type
| a | plus | times | lpar | rpar
-- ANCHOR_END: SigmaA
deriving Fintype, DecidableEq
open SigmaA

-- ANCHOR: NTA_1
inductive NTA_1 : Type
| E | T | F
-- ANCHOR_END: NTA_1
deriving Fintype, DecidableEq

section
open NTA_1
-- ANCHOR: GA_1
abbrev GA_1 : CFG SigmaA :=
{ NT := NTA_1,
  S := E,
  P := { (E, [inl T]),
         (E, [inl E, inr plus, inl T]),
         (T, [inl F]),
         (T, [inl T, inr times, inl F]),
         (F, [inr a]),
         (F, [inr lpar, inl E, inr rpar]) }
}
-- ANCHOR_END: GA_1
end

-- ANCHOR: NTA_2
inductive NTA_2 : Type
| E
-- ANCHOR_END: NTA_2
deriving Fintype, DecidableEq

section
open NTA_2
-- ANCHOR: GA_2
abbrev GA_2 : CFG SigmaA :=
{ NT := NTA_2,
  S := E,
  P := { (E, [inl E, inr plus, inl E]),
         (E, [inl E, inr times, inl E]),
         (E, [inr a]),
         (E, [inr lpar, inl E, inr rpar]) }
}
-- ANCHOR_END: GA_2
end

end CfgArith
