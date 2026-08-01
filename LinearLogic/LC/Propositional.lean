module

public import Foundation.Logic.Entailment
public import LinearLogic.LogicSymbol

/-!
# "Constructive" classical logic without neutrals
-/

@[expose] public section

namespace LO

class HTilde (α : Type*) (β : outParam Type*) where
  hTilde : α → β

prefix:75 "∼" => HTilde.hTilde

class HWedge (α : Type*) (β : Type*) (γ : outParam Type*) where
  hWedge : α → β → γ

infixr:69 " ⋏ " => HWedge.hWedge

class HVee (α : Type*) (β : Type*) (γ : outParam Type*) where
  hVee : α → β → γ

infixr:68 " ⋎ " => HVee.hVee

attribute [match_pattern] HTilde.hTilde HWedge.hWedge HVee.hVee

end LO

namespace LO.Propositional.LC

mutual

inductive PositiveFormula where
  | atom : ℕ → PositiveFormula
  | andPP : PositiveFormula → PositiveFormula → PositiveFormula
  | andPN : PositiveFormula → NegativeFormula → PositiveFormula
  | andNP : NegativeFormula → PositiveFormula → PositiveFormula
  | orPP : PositiveFormula → PositiveFormula → PositiveFormula

inductive NegativeFormula where
  | natom : ℕ → NegativeFormula
  | andNN : NegativeFormula → NegativeFormula → NegativeFormula
  | orPN : PositiveFormula → NegativeFormula → NegativeFormula
  | orNP : NegativeFormula → PositiveFormula → NegativeFormula
  | orNN : NegativeFormula → NegativeFormula → NegativeFormula

end

instance : HWedge PositiveFormula PositiveFormula PositiveFormula where
  hWedge := PositiveFormula.andPP

instance : HWedge PositiveFormula NegativeFormula PositiveFormula where
  hWedge := PositiveFormula.andPN

instance : HWedge NegativeFormula PositiveFormula PositiveFormula where
  hWedge := PositiveFormula.andNP

instance : HVee PositiveFormula PositiveFormula PositiveFormula where
  hVee := PositiveFormula.orPP

instance : HWedge NegativeFormula NegativeFormula NegativeFormula where
  hWedge := NegativeFormula.andNN

instance : HVee PositiveFormula NegativeFormula NegativeFormula where
  hVee := NegativeFormula.orPN

instance : HVee NegativeFormula PositiveFormula NegativeFormula where
  hVee := NegativeFormula.orNP

instance : HVee NegativeFormula NegativeFormula NegativeFormula where
  hVee := NegativeFormula.orNN

mutual

def PositiveFormula.neg : PositiveFormula → NegativeFormula
  |  .atom a => NegativeFormula.natom a
  | .andPP P Q => NegativeFormula.orNN P.neg Q.neg
  | .andPN P N => NegativeFormula.orNP P.neg N.neg
  | .andNP N P => NegativeFormula.orPN N.neg P.neg
  | .orPP P Q => NegativeFormula.andNN P.neg Q.neg

def NegativeFormula.neg : NegativeFormula → PositiveFormula
  |  .natom a => PositiveFormula.atom a
  | .andNN N M => PositiveFormula.orPP N.neg M.neg
  | .orPN P N => PositiveFormula.andNP P.neg N.neg
  | .orNP N P => PositiveFormula.andPN N.neg P.neg
  | .orNN N M => PositiveFormula.andPP N.neg M.neg

end

instance : HTilde PositiveFormula NegativeFormula := ⟨PositiveFormula.neg⟩
instance : HTilde NegativeFormula PositiveFormula := ⟨NegativeFormula.neg⟩

namespace PositiveFormula

@[simp] lemma neg_atom (p : ℕ) : ∼atom p = NegativeFormula.natom p := rfl

variable {P Q : PositiveFormula} {N M : NegativeFormula}

@[simp] lemma neg_andPP : ∼(P ⋏ Q) = ∼P ⋎ ∼Q := rfl

@[simp] lemma neg_andPN : ∼(P ⋏ M) = ∼P ⋎ ∼M := rfl

@[simp] lemma neg_andNP : ∼(N ⋏ Q) = ∼N ⋎ ∼Q := rfl

@[simp] lemma neg_orPP : ∼(P ⋎ Q) = (∼P ⋏ ∼Q) := rfl

end PositiveFormula

namespace NegativeFormula

@[simp] lemma neg_natom (p : ℕ) : ∼natom p = PositiveFormula.atom p := rfl

variable {P Q : PositiveFormula} {N M : NegativeFormula}

@[simp] lemma neg_andNN : ∼(N ⋏ M) = ∼N ⋎ ∼M := rfl

@[simp] lemma neg_orPN : ∼(P ⋎ M) = ∼P ⋏ ∼M := rfl

@[simp] lemma neg_orNP : ∼(N ⋎ Q) = ∼N ⋏ ∼Q := rfl

@[simp] lemma neg_orNN : ∼(N ⋎ M) = ∼N ⋏ ∼M := rfl

end NegativeFormula

mutual

@[simp] lemma PositiveFormula.neg_neg (P : PositiveFormula) : ∼∼P = P := by
  match P with
  |  .atom a => rfl
  | (P : PositiveFormula) ⋏ (Q : PositiveFormula) => simp [PositiveFormula.neg_neg P, PositiveFormula.neg_neg Q]
  | (P : PositiveFormula) ⋏ (M : NegativeFormula) => simp [PositiveFormula.neg_neg P, NegativeFormula.neg_neg M]
  | (N : NegativeFormula) ⋏ (Q : PositiveFormula) => simp [NegativeFormula.neg_neg N, PositiveFormula.neg_neg Q]
  | (P : PositiveFormula) ⋎ (Q : PositiveFormula) => simp [PositiveFormula.neg_neg P, PositiveFormula.neg_neg Q]

@[simp] lemma NegativeFormula.neg_neg (N : NegativeFormula) : ∼∼N = N := by
  match N with
  |  .natom a => rfl
  | (N : NegativeFormula) ⋏ (M : NegativeFormula) => simp [NegativeFormula.neg_neg N, NegativeFormula.neg_neg M]
  | (P : PositiveFormula) ⋎ (M : NegativeFormula) => simp [PositiveFormula.neg_neg P, NegativeFormula.neg_neg M]
  | (N : NegativeFormula) ⋎ (Q : PositiveFormula) => simp [NegativeFormula.neg_neg N, PositiveFormula.neg_neg Q]
  | (N : NegativeFormula) ⋎ (M : NegativeFormula) => simp [NegativeFormula.neg_neg N, NegativeFormula.neg_neg M]

end

/--/
inductive Formula where
  | atom : ℕ → Formula
  | natom : ℕ → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula

namespace Formula

def neg : Formula → Formula
  |  atom a => natom a
  | natom a => atom a
  | and φ ψ => or φ.neg ψ.neg
  |  or φ ψ => and φ.neg ψ.neg

lemma neg_neg (φ : Formula) : φ.neg.neg = φ := by
  match φ with
  |  atom a => rfl
  | natom a => rfl
  | and φ ψ => simp [neg_neg φ, neg_neg ψ, neg]
  |  or φ ψ => simp [neg_neg φ, neg_neg ψ, neg]

instance : LogicalConnective Formula where
  wedge := and
  vee := or
  tilde := neg
  arrow φ ψ := or φ.neg ψ

instance : TildeInvolutive Formula where
  tilde_involutive := neg_neg

instance : LogicalConnective.DeMorgan Formula where
  and _ _ := rfl
  or _ _ := rfl
  imply _ _ := rfl

def polarity : Formula → Bool
  |  atom _ => true
  | natom _ => false
  |   φ ⋏ ψ => φ.polarity || ψ.polarity
  |   φ ⋎ ψ => φ.polarity && ψ.polarity

@[simp] lemma neg_polarity (φ : Formula) : (∼φ).polarity = !φ.polarity := by
  match φ with
  |  atom _ => rfl
  | natom _ => rfl
  |   φ ⋏ ψ => simp [neg_polarity φ, neg_polarity ψ, polarity]
  |   φ ⋎ ψ => simp [neg_polarity φ, neg_polarity ψ, polarity]

abbrev IsPositive (φ : Formula) : Prop := φ.polarity = true

abbrev IsNegative (φ : Formula) : Prop := φ.polarity = false

@[simp] lemma IsPositive.atom (p : ℕ) : (atom p).IsPositive := rfl

@[simp] lemma IsPositive.and (φ ψ : Formula) : (φ ⋏ ψ).IsPositive ↔ φ.IsPositive ∨ ψ.IsPositive := by
  simp [IsPositive, polarity]

@[simp] lemma IsPositive.or (φ ψ : Formula) : (φ ⋎ ψ).IsPositive ↔ φ.IsPositive ∧ ψ.IsPositive := by
  simp [IsPositive, polarity]

@[simp] lemma IsNegative.natom (p : ℕ) : (natom p).IsNegative := rfl

@[simp] lemma IsNegative.and (φ ψ : Formula) : (φ ⋏ ψ).IsNegative ↔ φ.IsNegative ∧ ψ.IsNegative := by
  simp [IsNegative, polarity]

@[simp] lemma IsNegative.or (φ ψ : Formula) : (φ ⋎ ψ).IsNegative ↔ φ.IsNegative ∨ ψ.IsNegative := by
  simp [IsNegative, polarity]; grind

end Formula

structure PositiveFormula where
  val : Formula
  isPositive : val.IsPositive

namespace PositiveFormula

attribute [coe] PositiveFormula.val

instance : Coe PositiveFormula Formula := ⟨PositiveFormula.val⟩

instance : Wedge PositiveFormula where
  wedge φ ψ := ⟨φ.val ⋏ ψ.val, by { simp [Formula.IsPositive, φ.isPositive, ψ.isPositive] }⟩

instance : Vee PositiveFormula where
  vee φ ψ := ⟨φ.val ⋎ ψ.val, by { simp [Formula.IsPositive, φ.isPositive, ψ.isPositive] }⟩

def atom (p : ℕ) : PositiveFormula := ⟨Formula.atom p, by simp [Formula.IsPositive]⟩

def andRight (φ : Formula) (ψ : PositiveFormula) : PositiveFormula := ⟨φ ⋏ ψ.val, by simp [Formula.IsPositive, ψ.isPositive]⟩

end PositiveFormula

structure NegativeFormula where
  val : Formula
  isNegative : val.IsNegative

namespace NegativeFormula

attribute [coe] NegativeFormula.val

instance : Coe NegativeFormula Formula := ⟨NegativeFormula.val⟩

instance : Wedge NegativeFormula where
  wedge φ ψ := ⟨φ.val ⋏ ψ.val, by { simp [Formula.IsNegative, φ.isNegative, ψ.isNegative] }⟩

instance : Vee NegativeFormula where
  vee φ ψ := ⟨φ.val ⋎ ψ.val, by { simp [Formula.IsNegative, φ.isNegative, ψ.isNegative] }⟩

end NegativeFormula

def PositiveFormula.andN (P : PositiveFormula) (N : NegativeFormula) : PositiveFormula := ⟨P.val ⋏ N.val, by simp [Formula.IsPositive, P.isPositive]⟩

def NegativeFormula.andP (N : NegativeFormula) (P : PositiveFormula) : PositiveFormula := ⟨N.val ⋏ P.val, by simp [Formula.IsPositive, P.isPositive]⟩

def PositiveFormula.orN (P : PositiveFormula) (N : NegativeFormula) : NegativeFormula := ⟨P.val ⋎ N.val, by simp [Formula.IsNegative, N.isNegative]⟩

def NegativeFormula.orP (N : NegativeFormula) (P : PositiveFormula) : NegativeFormula := ⟨N.val ⋎ P.val, by simp [Formula.IsNegative, N.isNegative]⟩

structure Sequent where
  body : List Formula
  stoup : Option PositiveFormula

scoped infixl:55 " ;; " => Sequent.mk

inductive Derivation : Sequent → Type _
  /-- axiom -/
  | protected ax (p : ℕ) : Derivation ([.natom p];; some (PositiveFormula.atom p))
  /-- cut rule -/
  | cut : Derivation (Γ ;; some P) → Derivation ((∼P :: Δ) ;; Ξ) → Derivation (Γ ++ Δ ;; Ξ)
  /-- structural rules -/
  | exchange : Derivation (Γ ;; Ξ) → Γ.Perm Δ → Derivation (Δ ;; Ξ)
  | weakening : Derivation (Γ ;; Ξ) → Derivation (A :: Γ ;; Ξ)
  | contraction : Derivation (A :: A :: Γ ;; Ξ) → Derivation (A :: Γ ;; Ξ)
  | dereliction : Derivation (Γ ;; some P) → Derivation (P :: Γ ;; none)
  /-- logical rules -/
  | and_pos_pos :
    Derivation (Δ ;; some P) → Derivation (Γ ;; some Q) → Derivation (Δ ++ Γ ;; some (P ⋏ Q))
  | and_pos_neg {P : PositiveFormula} {M : NegativeFormula} :
    Derivation (Δ ;; some P) → Derivation (M :: Γ ;; none) → Derivation (Δ ++ Γ ;; some (P.andN M))
  | and_neg_pos {N : NegativeFormula} :
    Derivation (N :: Δ ;; none) → Derivation (Γ ;; some Q) → Derivation (Δ ++ Γ ;; some (N.andP Q))
  | and_neg_neg :
    Derivation (N :: Δ ;; Ξ) → Derivation (M :: Γ ;; Ξ) → Derivation (N ⋏ M :: (Δ ++ Γ) ;; Ξ)
  | or_pos_pos_left :
    Derivation (Γ ;; some P) → Derivation (Γ ;; some (P ⋎ Q))
  | or_pos_pos_right :
    Derivation (Γ ;; some Q) → Derivation (Γ ;; some (P ⋎ Q))
  | or_pos_neg_left {P : PositiveFormula} {M : NegativeFormula} :
    Derivation (P :: M :: Γ ;; Ξ) → Derivation (P ⋎ M :: Γ ;; Ξ)
  | or_pos_neg_right {N : NegativeFormula} {Q : PositiveFormula} :
    Derivation (N :: Q :: Γ ;; Ξ) → Derivation (N ⋎ Q :: Γ ;; Ξ)
  | or_neg_neg {N M : NegativeFormula} :
    Derivation (N :: M :: Γ ;; Ξ) → Derivation (N ⋎ M :: Γ ;; Ξ)

end LO.Propositional.LC

end
