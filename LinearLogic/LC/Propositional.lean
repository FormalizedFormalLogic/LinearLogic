module

public import Foundation.Logic.Entailment
public import LinearLogic.Vorspiel.Multiset

/-!
# "Constructive" classical logic without neutrals

### References
- J.-Y. Girard, A new constructive logic: classical logic.
- O. Laurent, Polarized Proof-Nets: Proof-Nets for LC.
-/

@[expose] public section

namespace LO.Propositional.LC

namespace Formula

mutual

inductive Positive where
  |  atom : ℕ → Positive
  | andPosPos : Positive → Positive → Positive
  | andPosNeg : Positive → Negative → Positive
  | andNegPos : Negative → Positive → Positive
  |  orPosPos : Positive → Positive → Positive

inductive Negative where
  | natom : ℕ → Negative
  | andNegNeg : Negative → Negative → Negative
  |  orPosNeg : Positive → Negative → Negative
  |  orNegPos : Negative → Positive → Negative
  |  orNegNeg : Negative → Negative → Negative

end

instance : HWedge Positive Positive Positive := ⟨.andPosPos⟩
instance : HWedge Positive Negative Positive := ⟨.andPosNeg⟩
instance : HWedge Negative Positive Positive := ⟨.andNegPos⟩
instance :   HVee Positive Positive Positive := ⟨.orPosPos⟩
instance : HWedge Negative Negative Negative := ⟨.andNegNeg⟩
instance :   HVee Positive Negative Negative := ⟨.orPosNeg⟩
instance :   HVee Negative Positive Negative := ⟨.orNegPos⟩
instance :   HVee Negative Negative Negative := ⟨.orNegNeg⟩

mutual

def Positive.neg : Positive → Negative
  |  .atom a => Negative.natom a
  | (P : Positive) ⋏ (Q : Positive) => P.neg ⋎ Q.neg
  | (P : Positive) ⋏ (N : Negative) => P.neg ⋎ N.neg
  | (N : Negative) ⋏ (P : Positive) => N.neg ⋎ P.neg
  | (P : Positive) ⋎ (Q : Positive) => P.neg ⋏ Q.neg

def Negative.neg : Negative → Positive
  |  .natom a => Positive.atom a
  | (N : Negative) ⋏ (M : Negative) => N.neg ⋎ M.neg
  | (P : Positive) ⋎ (N : Negative) => P.neg ⋏ N.neg
  | (N : Negative) ⋎ (P : Positive) => N.neg ⋏ P.neg
  | (N : Negative) ⋎ (M : Negative) => N.neg ⋏ M.neg

end

instance : HTilde Positive Negative := ⟨Positive.neg⟩
instance : HTilde Negative Positive := ⟨Negative.neg⟩

section neg

variable {P Q : Positive} {N M : Negative}

@[simp] lemma  neg_atom (X : ℕ) : ∼Positive.atom X = Negative.natom X := rfl
@[simp] lemma neg_natom (X : ℕ) : ∼Negative.natom X = Positive.atom X := rfl
@[simp] lemma neg_andPosPos : ∼(P ⋏ Q) = ∼P ⋎ ∼Q := rfl
@[simp] lemma neg_andPosNeg : ∼(P ⋏ M) = ∼P ⋎ ∼M := rfl
@[simp] lemma neg_andNegPos : ∼(N ⋏ Q) = ∼N ⋎ ∼Q := rfl
@[simp] lemma neg_andNegNeg : ∼(N ⋏ M) = ∼N ⋎ ∼M := rfl
@[simp] lemma  neg_orPosPos : ∼(P ⋎ Q) = ∼P ⋏ ∼Q := rfl
@[simp] lemma  neg_orPosNeg : ∼(P ⋎ M) = ∼P ⋏ ∼M := rfl
@[simp] lemma  neg_orNegPos : ∼(N ⋎ Q) = ∼N ⋏ ∼Q := rfl
@[simp] lemma  neg_orNegNeg : ∼(N ⋎ M) = ∼N ⋏ ∼M := rfl

end neg

mutual

@[simp] lemma Positive.neg_neg (P : Positive) : ∼∼P = P := by
  match P with
  |  .atom a => rfl
  | (P : Positive) ⋏ (Q : Positive) => simp [P.neg_neg, Q.neg_neg]
  | (P : Positive) ⋏ (M : Negative) => simp [P.neg_neg, M.neg_neg]
  | (N : Negative) ⋏ (Q : Positive) => simp [N.neg_neg, Q.neg_neg]
  | (P : Positive) ⋎ (Q : Positive) => simp [P.neg_neg, Q.neg_neg]

@[simp] lemma Negative.neg_neg (N : Negative) : ∼∼N = N := by
  match N with
  |  .natom a => rfl
  | (N : Negative) ⋏ (M : Negative) => simp [N.neg_neg, M.neg_neg]
  | (P : Positive) ⋎ (M : Negative) => simp [P.neg_neg, M.neg_neg]
  | (N : Negative) ⋎ (Q : Positive) => simp [N.neg_neg, Q.neg_neg]
  | (N : Negative) ⋎ (M : Negative) => simp [N.neg_neg, M.neg_neg]

end

mutual

def Positive.complexity : Positive → ℕ
  |  .atom _ => 0
  | (P : Positive) ⋏ (Q : Positive) => max P.complexity Q.complexity + 1
  | (P : Positive) ⋏ (M : Negative) => max P.complexity M.complexity + 1
  | (N : Negative) ⋏ (Q : Positive) => max N.complexity Q.complexity + 1
  | (P : Positive) ⋎ (Q : Positive) => max P.complexity Q.complexity + 1

def Negative.complexity : Negative → ℕ
  |  .natom _ => 0
  | (N : Negative) ⋏ (M : Negative) => max N.complexity M.complexity + 1
  | (P : Positive) ⋎ (M : Negative) => max P.complexity M.complexity + 1
  | (N : Negative) ⋎ (Q : Positive) => max N.complexity Q.complexity + 1
  | (N : Negative) ⋎ (M : Negative) => max N.complexity M.complexity + 1

end

section complexity

variable {P Q : Positive} {N M : Negative}

@[simp] lemma  complexity_atom (X : ℕ) : (Positive.atom X).complexity = 0 := rfl
@[simp] lemma complexity_natom (X : ℕ) : (Negative.natom X).complexity = 0 := rfl
@[simp] lemma complexity_andPosPos : (P ⋏ Q).complexity = max P.complexity Q.complexity + 1 := rfl
@[simp] lemma complexity_andPosNeg : (P ⋏ M).complexity = max P.complexity M.complexity + 1 := rfl
@[simp] lemma complexity_andNegPos : (N ⋏ Q).complexity = max N.complexity Q.complexity + 1 := rfl
@[simp] lemma  complexity_orPosPos : (P ⋎ Q).complexity = max P.complexity Q.complexity + 1 := rfl
@[simp] lemma complexity_andNegNeg : (N ⋏ M).complexity = max N.complexity M.complexity + 1 := rfl
@[simp] lemma  complexity_orPosNeg : (P ⋎ M).complexity = max P.complexity M.complexity + 1 := rfl
@[simp] lemma  complexity_orNegPos : (N ⋎ Q).complexity = max N.complexity Q.complexity + 1 := rfl
@[simp] lemma  complexity_orNegNeg : (N ⋎ M).complexity = max N.complexity M.complexity + 1 := rfl

mutual

@[simp] lemma Positive.complexity_neg (P : Positive) : (∼P).complexity = P.complexity := by
  match P with
  |  .atom a => rfl
  | (P : Positive) ⋏ (Q : Positive) => simp [P.complexity_neg, Q.complexity_neg]
  | (P : Positive) ⋏ (M : Negative) => simp [P.complexity_neg, M.complexity_neg]
  | (N : Negative) ⋏ (Q : Positive) => simp [N.complexity_neg, Q.complexity_neg]
  | (P : Positive) ⋎ (Q : Positive) => simp [P.complexity_neg, Q.complexity_neg]

@[simp] lemma Negative.complexity_neg (N : Negative) : (∼N).complexity = N.complexity := by
  match N with
  |  .natom a => rfl
  | (N : Negative) ⋏ (M : Negative) => simp [N.complexity_neg, M.complexity_neg]
  | (P : Positive) ⋎ (M : Negative) => simp [P.complexity_neg, M.complexity_neg]
  | (N : Negative) ⋎ (Q : Positive) => simp [N.complexity_neg, Q.complexity_neg]
  | (N : Negative) ⋎ (M : Negative) => simp [N.complexity_neg, M.complexity_neg]

end

end complexity

mutual

def Positive.depth : Positive → ℕ
  |  .atom _ => 1
  | (P : Positive) ⋏ (Q : Positive) => max P.depth Q.depth
  | (P : Positive) ⋏ (M : Negative) => max P.depth M.depth + 1
  | (N : Negative) ⋏ (Q : Positive) => max N.depth Q.depth + 1
  | (P : Positive) ⋎ (Q : Positive) => max P.depth Q.depth

def Negative.depth : Negative → ℕ
  |  .natom _ => 1
  | (N : Negative) ⋏ (M : Negative) => max N.depth M.depth
  | (P : Positive) ⋎ (M : Negative) => max P.depth M.depth + 1
  | (N : Negative) ⋎ (Q : Positive) => max N.depth Q.depth + 1
  | (N : Negative) ⋎ (M : Negative) => max N.depth M.depth

end

section depth

variable {P Q : Positive} {N M : Negative}

@[simp] lemma  depth_atom (X : ℕ) : (Positive.atom X).depth = 1 := rfl
@[simp] lemma depth_natom (X : ℕ) : (Negative.natom X).depth = 1 := rfl
@[simp] lemma depth_andPosPos : (P ⋏ Q).depth = max P.depth Q.depth := rfl
@[simp] lemma depth_andPosNeg : (P ⋏ M).depth = max P.depth M.depth + 1 := rfl
@[simp] lemma depth_andNegPos : (N ⋏ Q).depth = max N.depth Q.depth + 1 := rfl
@[simp] lemma  depth_orPosPos : (P ⋎ Q).depth = max P.depth Q.depth := rfl
@[simp] lemma depth_andNegNeg : (N ⋏ M).depth = max N.depth M.depth := rfl
@[simp] lemma  depth_orPosNeg : (P ⋎ M).depth = max P.depth M.depth + 1 := rfl
@[simp] lemma  depth_orNegPos : (N ⋎ Q).depth = max N.depth Q.depth + 1 := rfl
@[simp] lemma  depth_orNegNeg : (N ⋎ M).depth = max N.depth M.depth := rfl

mutual

@[simp] lemma Positive.depth_neg (P : Positive) : (∼P).depth = P.depth := by
  match P with
  |  .atom _ => rfl
  | (P : Positive) ⋏ (Q : Positive) => simp [P.depth_neg, Q.depth_neg]
  | (P : Positive) ⋏ (M : Negative) => simp [P.depth_neg, M.depth_neg]
  | (N : Negative) ⋏ (Q : Positive) => simp [N.depth_neg, Q.depth_neg]
  | (P : Positive) ⋎ (Q : Positive) => simp [P.depth_neg, Q.depth_neg]

@[simp] lemma Negative.depth_neg (N : Negative) : (∼N).depth = N.depth := by
  match N with
  |  .natom _ => rfl
  | (N : Negative) ⋏ (M : Negative) => simp [N.depth_neg, M.depth_neg]
  | (P : Positive) ⋎ (M : Negative) => simp [P.depth_neg, M.depth_neg]
  | (N : Negative) ⋎ (Q : Positive) => simp [N.depth_neg, Q.depth_neg]
  | (N : Negative) ⋎ (M : Negative) => simp [N.depth_neg, M.depth_neg]

end

end depth

end Formula

inductive Formula where
  | pos : Formula.Positive → Formula
  | neg : Formula.Negative → Formula

namespace Formula

instance : Coe Positive Formula := ⟨Formula.pos⟩

instance : Coe Negative Formula := ⟨Formula.neg⟩

inductive IsPrenegative : Formula → Prop where
  | natom (X : ℕ) : IsPrenegative (Negative.natom X)
  | pos (P : Positive) : IsPrenegative P

abbrev IsPrenegativeMultiset (Γ : Multiset Formula) : Prop := ∀ A ∈ Γ, IsPrenegative A

end Formula

open Formula

structure Sequent where
  body : Multiset Formula
  stoup : Option Positive

scoped infixl:55 " ;; " => Sequent.mk

inductive Derivation : Sequent → Type _
  /-- axiom -/
  | ax (X : ℕ) : Derivation (⦃(Negative.natom X : Formula)⦄ ;; some (.atom X))
  /-- cut rules -/
  | cutPos {P : Positive} :
    Derivation (Γ ;; some P) → Derivation (Δ + ⦃((∼P : Negative) : Formula)⦄ ;; Ξ) → Derivation (Γ + Δ ;; Ξ)
  | cutNeg {N : Negative} :
    Derivation (Γ + ⦃(N : Formula)⦄ ;; none) → Derivation (Δ + ⦃((∼N : Positive) : Formula)⦄ ;; Ξ) → Derivation (Γ + Δ ;; Ξ)
  /-- structural rules -/
  | weakening : Derivation (Γ ;; Ξ) → Derivation (Γ + ⦃A⦄ ;; Ξ)
  | contraction : Derivation (Γ + ⦃A⦄ + ⦃A⦄ ;; Ξ) → Derivation (Γ + ⦃A⦄ ;; Ξ)
  | dereliction : Derivation (Γ ;; some P) → Derivation (Γ + ⦃(P : Formula)⦄ ;; none)
  /-- logical rules -/
  | andPosPos :
    Derivation (Γ ;; some P) → Derivation (Δ ;; some Q) → Derivation (Γ + Δ ;; some (P ⋏ Q))
  | andPosNeg {P : Positive} {M : Negative} :
    Derivation (Γ ;; some P) → Derivation (Δ + ⦃(M : Formula)⦄ ;; none) → Derivation (Γ + Δ ;; some (P ⋏ M))
  | andNegPos {N : Negative} :
    Derivation (Γ + ⦃(N : Formula)⦄ ;; none) → Derivation (Δ ;; some Q) → Derivation (Γ + Δ ;; some (N ⋏ Q))
  | andNegNeg {N M : Negative} :
    Derivation (Γ + ⦃(N : Formula)⦄ ;; Ξ) → Derivation (Γ + ⦃(M : Formula)⦄ ;; Ξ) →
      Derivation (Γ + ⦃((N ⋏ M : Negative) : Formula)⦄ ;; Ξ)
  | orPosPosLeft {P Q : Positive} :
    Derivation (Γ ;; some P) → Derivation (Γ ;; some (P ⋎ Q))
  | orPosPosRight {P Q : Positive} :
    Derivation (Γ ;; some Q) → Derivation (Γ ;; some (P ⋎ Q))
  | orPosNeg {P : Positive} {M : Negative} :
    Derivation (Γ + ⦃(P : Formula)⦄ + ⦃(M : Formula)⦄ ;; Ξ) →
      Derivation (Γ + ⦃((P ⋎ M : Negative) : Formula)⦄ ;; Ξ)
  | orNegPos {N : Negative} {Q : Positive} :
    Derivation (Γ + ⦃(N : Formula)⦄ + ⦃(Q : Formula)⦄ ;; Ξ) →
      Derivation (Γ + ⦃((N ⋎ Q : Negative) : Formula)⦄ ;; Ξ)
  | orNegNeg {N M : Negative} :
    Derivation (Γ + ⦃(N : Formula)⦄ + ⦃(M : Formula)⦄ ;; Ξ) →
      Derivation (Γ + ⦃((N ⋎ M : Negative) : Formula)⦄ ;; Ξ)

prefix:45 "⊢ᴸᶜ " => Derivation

inductive DerivationRev : Sequent → Type _
  /-- axiom -/
  | ax (X : ℕ) : DerivationRev (⦃(Negative.natom X : Formula)⦄ ;; some (.atom X))
  /-- cut rules -/
  | cutPos {P : Positive} :
    DerivationRev (Γ ;; some P) → DerivationRev (Δ + ⦃((∼P : Negative) : Formula)⦄ ;; Ξ) → DerivationRev (Γ + Δ ;; Ξ)
  | cutNeg {N : Negative} (hΔ : IsPrenegativeMultiset Δ) :
    DerivationRev (Γ + ⦃(N : Formula)⦄ ;; none) → DerivationRev (Δ + ⦃((∼N : Positive) : Formula)⦄ ;; Ξ) → DerivationRev (Γ + Δ ;; Ξ)
  /-- structural rules -/
  | weakening (hA : IsPrenegative A) : DerivationRev (Γ ;; Ξ) → DerivationRev (Γ + ⦃A⦄ ;; Ξ)
  | contraction (hA : IsPrenegative A) : DerivationRev (Γ + ⦃A⦄ + ⦃A⦄ ;; Ξ) → DerivationRev (Γ + ⦃A⦄ ;; Ξ)
  | dereliction : DerivationRev (Γ ;; some P) → DerivationRev (Γ + ⦃(P : Formula)⦄ ;; none)
  /-- logical rules -/
  | andPosPos :
    DerivationRev (Γ ;; some P) → DerivationRev (Δ ;; some Q) → DerivationRev (Γ + Δ ;; some (P ⋏ Q))
  | andPosNeg {P : Positive} {M : Negative} (hΔ : IsPrenegativeMultiset Δ) :
    DerivationRev (Γ ;; some P) → DerivationRev (Δ + ⦃(M : Formula)⦄ ;; none) → DerivationRev (Γ + Δ ;; some (P ⋏ M))
  | andNegPos {N : Negative} (hΓ : IsPrenegativeMultiset Γ) :
    DerivationRev (Γ + ⦃(N : Formula)⦄ ;; none) → DerivationRev (Δ ;; some Q) → DerivationRev (Γ + Δ ;; some (N ⋏ Q))
  | andNegNeg {N M : Negative} :
    DerivationRev (Γ + ⦃(N : Formula)⦄ ;; Ξ) → DerivationRev (Γ + ⦃(M : Formula)⦄ ;; Ξ) →
      DerivationRev (Γ + ⦃((N ⋏ M : Negative) : Formula)⦄ ;; Ξ)
  | orPosPosLeft {P Q : Positive} :
    DerivationRev (Γ ;; some P) → DerivationRev (Γ ;; some (P ⋎ Q))
  | orPosPosRight {P Q : Positive} :
    DerivationRev (Γ ;; some Q) → DerivationRev (Γ ;; some (P ⋎ Q))
  | orPosNeg {P : Positive} {M : Negative} :
    DerivationRev (Γ + ⦃(P : Formula)⦄ + ⦃(M : Formula)⦄ ;; Ξ) →
      DerivationRev (Γ + ⦃((P ⋎ M : Negative) : Formula)⦄ ;; Ξ)
  | orNegPos {N : Negative} {Q : Positive} :
    DerivationRev (Γ + ⦃(N : Formula)⦄ + ⦃(Q : Formula)⦄ ;; Ξ) →
      DerivationRev (Γ + ⦃((N ⋎ Q : Negative) : Formula)⦄ ;; Ξ)
  | orNegNeg {N M : Negative} :
    DerivationRev (Γ + ⦃(N : Formula)⦄ + ⦃(M : Formula)⦄ ;; Ξ) →
      DerivationRev (Γ + ⦃((N ⋎ M : Negative) : Formula)⦄ ;; Ξ)

prefix:45 "⊢ᴸᶜᵣ " => DerivationRev

end LO.Propositional.LC

end
