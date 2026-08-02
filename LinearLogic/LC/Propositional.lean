module

public import Foundation.Logic.Entailment

/-!
# "Constructive" classical logic without neutrals
-/

@[expose] public section

namespace LO.Propositional.LC

mutual

inductive PositiveFormula where
  |  atom : ℕ → PositiveFormula
  | andPP : PositiveFormula → PositiveFormula → PositiveFormula
  | andPN : PositiveFormula → NegativeFormula → PositiveFormula
  | andNP : NegativeFormula → PositiveFormula → PositiveFormula
  |  orPP : PositiveFormula → PositiveFormula → PositiveFormula

inductive NegativeFormula where
  | natom : ℕ → NegativeFormula
  | andNN : NegativeFormula → NegativeFormula → NegativeFormula
  |  orPN : PositiveFormula → NegativeFormula → NegativeFormula
  |  orNP : NegativeFormula → PositiveFormula → NegativeFormula
  |  orNN : NegativeFormula → NegativeFormula → NegativeFormula

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

def PositiveFormula.complexity : PositiveFormula → ℕ
  |  .atom _ => 0
  | (P : PositiveFormula) ⋏ (Q : PositiveFormula) => max P.complexity Q.complexity + 1
  | (P : PositiveFormula) ⋏ (M : NegativeFormula) => max P.complexity M.complexity + 1
  | (N : NegativeFormula) ⋏ (Q : PositiveFormula) => max N.complexity Q.complexity + 1
  | (P : PositiveFormula) ⋎ (Q : PositiveFormula) => max P.complexity Q.complexity + 1

def NegativeFormula.complexity : NegativeFormula → ℕ
  |  .natom _ => 0
  | (N : NegativeFormula) ⋏ (M : NegativeFormula) => max N.complexity M.complexity + 1
  | (P : PositiveFormula) ⋎ (M : NegativeFormula) => max P.complexity M.complexity + 1
  | (N : NegativeFormula) ⋎ (Q : PositiveFormula) => max N.complexity Q.complexity + 1
  | (N : NegativeFormula) ⋎ (M : NegativeFormula) => max N.complexity M.complexity + 1

end

section complexity

variable {P Q : PositiveFormula} {N M : NegativeFormula}

@[simp] lemma  complexity_atom (p : ℕ) : (PositiveFormula.atom p).complexity = 0 := rfl
@[simp] lemma complexity_natom (p : ℕ) : (NegativeFormula.natom p).complexity = 0 := rfl
@[simp] lemma complexity_andPP : (P ⋏ Q).complexity = max P.complexity Q.complexity + 1 := rfl
@[simp] lemma complexity_andPN : (P ⋏ M).complexity = max P.complexity M.complexity + 1 := rfl
@[simp] lemma complexity_andNP : (N ⋏ Q).complexity = max N.complexity Q.complexity + 1 := rfl
@[simp] lemma  complexity_orPP : (P ⋎ Q).complexity = max P.complexity Q.complexity + 1 := rfl
@[simp] lemma complexity_andNN : (N ⋏ M).complexity = max N.complexity M.complexity + 1 := rfl
@[simp] lemma  complexity_orPN : (P ⋎ M).complexity = max P.complexity M.complexity + 1 := rfl
@[simp] lemma  complexity_orNP : (N ⋎ Q).complexity = max N.complexity Q.complexity + 1 := rfl

end complexity

mutual

def PositiveFormula.neg : PositiveFormula → NegativeFormula
  |  .atom a => NegativeFormula.natom a
  | (P : PositiveFormula) ⋏ (Q : PositiveFormula) => P.neg ⋎ Q.neg
  | (P : PositiveFormula) ⋏ (N : NegativeFormula) => P.neg ⋎ N.neg
  | (N : NegativeFormula) ⋏ (P : PositiveFormula) => N.neg ⋎ P.neg
  | (P : PositiveFormula) ⋎ (Q : PositiveFormula) => P.neg ⋏ Q.neg

def NegativeFormula.neg : NegativeFormula → PositiveFormula
  |  .natom a => PositiveFormula.atom a
  | (N : NegativeFormula) ⋏ (M : NegativeFormula) => N.neg ⋎ M.neg
  | (P : PositiveFormula) ⋎ (N : NegativeFormula) => P.neg ⋏ N.neg
  | (N : NegativeFormula) ⋎ (P : PositiveFormula) => N.neg ⋏ P.neg
  | (N : NegativeFormula) ⋎ (M : NegativeFormula) => N.neg ⋏ M.neg

end

instance : HTilde PositiveFormula NegativeFormula := ⟨PositiveFormula.neg⟩
instance : HTilde NegativeFormula PositiveFormula := ⟨NegativeFormula.neg⟩

section neg

variable {P Q : PositiveFormula} {N M : NegativeFormula}

@[simp] lemma  neg_atom (p : ℕ) : ∼PositiveFormula.atom p = NegativeFormula.natom p := rfl
@[simp] lemma neg_natom (p : ℕ) : ∼NegativeFormula.natom p = PositiveFormula.atom p := rfl
@[simp] lemma neg_andPP : ∼(P ⋏ Q) = ∼P ⋎ ∼Q := rfl
@[simp] lemma neg_andPN : ∼(P ⋏ M) = ∼P ⋎ ∼M := rfl
@[simp] lemma neg_andNP : ∼(N ⋏ Q) = ∼N ⋎ ∼Q := rfl
@[simp] lemma neg_andNN : ∼(N ⋏ M) = ∼N ⋎ ∼M := rfl
@[simp] lemma  neg_orPP : ∼(P ⋎ Q) = ∼P ⋏ ∼Q := rfl
@[simp] lemma  neg_orPN : ∼(P ⋎ M) = ∼P ⋏ ∼M := rfl
@[simp] lemma  neg_orNP : ∼(N ⋎ Q) = ∼N ⋏ ∼Q := rfl
@[simp] lemma  neg_orNN : ∼(N ⋎ M) = ∼N ⋏ ∼M := rfl

end neg

mutual

@[simp] lemma PositiveFormula.neg_neg (P : PositiveFormula) : ∼∼P = P := by
  match P with
  |  .atom a => rfl
  | (P : PositiveFormula) ⋏ (Q : PositiveFormula) => simp [P.neg_neg, Q.neg_neg]
  | (P : PositiveFormula) ⋏ (M : NegativeFormula) => simp [P.neg_neg, M.neg_neg]
  | (N : NegativeFormula) ⋏ (Q : PositiveFormula) => simp [N.neg_neg, Q.neg_neg]
  | (P : PositiveFormula) ⋎ (Q : PositiveFormula) => simp [P.neg_neg, Q.neg_neg]

@[simp] lemma NegativeFormula.neg_neg (N : NegativeFormula) : ∼∼N = N := by
  match N with
  |  .natom a => rfl
  | (N : NegativeFormula) ⋏ (M : NegativeFormula) => simp [N.neg_neg, M.neg_neg]
  | (P : PositiveFormula) ⋎ (M : NegativeFormula) => simp [P.neg_neg, M.neg_neg]
  | (N : NegativeFormula) ⋎ (Q : PositiveFormula) => simp [N.neg_neg, Q.neg_neg]
  | (N : NegativeFormula) ⋎ (M : NegativeFormula) => simp [N.neg_neg, M.neg_neg]

end

structure Sequent where
  body : List (NegativeFormula ⊕ PositiveFormula)
  stoup : Option PositiveFormula

scoped infixl:55 " ;; " => Sequent.mk

inductive Derivation : Sequent → Type _
  /-- axiom -/
  | ax (p : ℕ) : Derivation ([.inl (.natom p)];; some (.atom p))
  /-- cut rule -/
  | cut : Derivation (Γ ;; some P) → Derivation ((.inl (∼P) :: Δ) ;; Ξ) → Derivation (Γ ++ Δ ;; Ξ)
  /-- structural rules -/
  | exchange : Derivation (Γ ;; Ξ) → Γ.Perm Δ → Derivation (Δ ;; Ξ)
  | weakening : Derivation (Γ ;; Ξ) → Derivation (A :: Γ ;; Ξ)
  | contraction : Derivation (A :: A :: Γ ;; Ξ) → Derivation (A :: Γ ;; Ξ)
  | dereliction : Derivation (Γ ;; some P) → Derivation (.inr P :: Γ ;; none)
  /-- logical rules -/
  | and_pos_pos :
    Derivation (Δ ;; some P) → Derivation (Γ ;; some Q) → Derivation (Δ ++ Γ ;; some (P ⋏ Q))
  | and_pos_neg {P : PositiveFormula} {M : NegativeFormula} :
    Derivation (Δ ;; some P) → Derivation (.inl M :: Γ ;; none) → Derivation (Δ ++ Γ ;; some (P ⋏ M))
  | and_neg_pos {N : NegativeFormula} :
    Derivation (.inl N :: Δ ;; none) → Derivation (Γ ;; some Q) → Derivation (Δ ++ Γ ;; some (N ⋏ Q))
  | and_neg_neg :
    Derivation (.inl N :: Δ ;; Ξ) → Derivation (.inl M :: Γ ;; Ξ) → Derivation (.inl (N ⋏ M) :: (Δ ++ Γ) ;; Ξ)
  | or_pos_pos_left (P Q : PositiveFormula) :
    Derivation (Γ ;; some P) → Derivation (Γ ;; some (P ⋎ Q))
  | or_pos_pos_right (P Q : PositiveFormula) :
    Derivation (Γ ;; some Q) → Derivation (Γ ;; some (P ⋎ Q))
  | or_pos_neg_left (P : PositiveFormula) (M : NegativeFormula) :
    Derivation (.inr P :: .inl M :: Γ ;; Ξ) → Derivation (.inl (P ⋎ M) :: Γ ;; Ξ)
  | or_pos_neg_right (N : NegativeFormula) (Q : PositiveFormula) :
    Derivation (.inl N :: .inr Q :: Γ ;; Ξ) → Derivation (.inl (N ⋎ Q) :: Γ ;; Ξ)
  | or_neg_neg {N M : NegativeFormula} :
    Derivation (.inl N :: .inl M :: Γ ;; Ξ) → Derivation (.inl (N ⋎ M) :: Γ ;; Ξ)

end LO.Propositional.LC

end
