module

public import Foundation.Logic.Entailment
public import LinearLogic.LogicSymbol
public import LinearLogic.Vorspiel.Multiset

/-!
# Propositional linear logic without neutrals
-/

@[expose] public section

namespace LO.Propositional.LinearLogic

inductive Formula where
  | atom : ℕ → Formula
  | natom : ℕ → Formula
  | tensor : Formula → Formula → Formula
  | par : Formula → Formula → Formula
  | plus : Formula → Formula → Formula
  | with : Formula → Formula → Formula
  | bang : Formula → Formula
  | quest : Formula → Formula

namespace Formula

instance : MultiplicativeConnective Formula where
  tensor := tensor
  par := par
  tensor_injective _ _ _ _ := by simp [tensor.injEq]
  par_injective _ _ _ _ := by simp [par.injEq]

instance : AdditiveConnective Formula where
  plus := plus
  with' := .with
  plus_injective _ _ _ _ := by simp [plus.injEq]
  with_injective _ _ _ _ := by simp [with.injEq]

instance : ExponentialConnective Formula where
  bang := bang
  quest := quest
  bang_injective _ _ := by simp [bang.injEq]
  quest_injective _ _ := by simp [quest.injEq]

variable {α : Type*}

def neg : Formula → Formula
  |  atom X => natom X
  | natom X => atom X
  |   A ⨂ B => A.neg ⅋ B.neg
  |   A ⅋ B => A.neg ⨂ B.neg
  |   A ⨁ B => A.neg ＆ B.neg
  |  A ＆ B => A.neg ⨁ B.neg
  |     ！A => ？A.neg
  |     ？A => ！A.neg

instance : Tilde Formula := ⟨neg⟩

@[simp] lemma neg_atom (p : ℕ) : ∼atom p = natom p := rfl

@[simp] lemma neg_natom (p : ℕ) : ∼natom p = atom p := rfl

instance : MultiplicativeConnective.DeMorgan Formula where
  tensor _ _ := rfl
  par _ _ := rfl

instance : AdditiveConnective.DeMorgan Formula where
  plus _ _ := rfl
  with_ _ _ := rfl

instance : ExponentialConnective.DeMorgan Formula where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_neg (A : Formula) : ∼∼A = A := by
  match A with
  |  atom X => rfl
  | natom X => rfl
  |   A ⨂ B => simp [neg_neg A, neg_neg B]
  |   A ⅋ B => simp [neg_neg A, neg_neg B]
  |   A ⨁ B => simp [neg_neg A, neg_neg B]
  |  A ＆ B => simp [neg_neg A, neg_neg B]
  |     ！A => simp [neg_neg A]
  |     ？A => simp [neg_neg A]

instance : TildeInvolutive Formula where
  tilde_involutive := neg_neg

lemma lolli_def (A B : Formula) : A ⊸ B = ∼A ⅋ B := rfl

inductive IsQuest : Formula → Prop
  | intro : IsQuest (？A)

@[simp] lemma IsQuest.not_atom (p : ℕ) : ¬IsQuest (atom p) := by intro h; cases h
@[simp] lemma IsQuest.not_natom (p : ℕ) : ¬IsQuest (natom p) := by intro h; cases h
@[simp] lemma IsQuest.not_tensor (A B : Formula) : ¬IsQuest (A ⨂ B) := by intro h; cases h
@[simp] lemma IsQuest.not_par (A B : Formula) : ¬IsQuest (A ⅋ B) := by intro h; cases h
@[simp] lemma IsQuest.not_plus (A B : Formula) : ¬IsQuest (A ⨁ B) := by intro h; cases h
@[simp] lemma IsQuest.not_with (A B : Formula) : ¬IsQuest (A ＆ B) := by intro h; cases h
@[simp] lemma IsQuest.not_bang (A : Formula) : ¬IsQuest (！A) := by intro h; cases h
@[simp] lemma IsQuest.quest (A : Formula) : IsQuest (？A) := by constructor

end Formula

variable {α : Type*}

abbrev Sequent := Multiset Formula

namespace Sequent

def IsQuest (Γ : Sequent) : Prop := ∀ A ∈ Γ, Formula.IsQuest A

@[simp] lemma IsQuest.nil : IsQuest 0 := by simp [IsQuest]

@[simp] lemma IsQuest.cons {A : Formula} {Γ : Sequent} :
    IsQuest (A ::ₘ Γ) ↔ Formula.IsQuest A ∧ IsQuest Γ := by
  simp [IsQuest]

@[simp] lemma IsQuest.singleton {A : Formula} : IsQuest ⦃A⦄ ↔ A.IsQuest := by
  simp [IsQuest]

end Sequent

inductive LL where
  | ll

notation "𝐋𝐋⁰" => LL.ll

namespace LL

inductive Derivation : Sequent → Type _
  /-- axiom  -/
  | ax (p : ℕ) : Derivation ⦃.atom p, .natom p⦄
  /-- cut rule -/
  | cut : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃∼A⦄) → Derivation (Γ + Δ)
  /-- structural rules -/
  | weakening : Derivation Γ → Derivation (Γ + ⦃？A⦄)
  | contraction : Derivation (Γ + ⦃？A⦄ + ⦃？A⦄) → Derivation (Γ + ⦃？A⦄)
  /-- multiplicative rules -/
  | tensor : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃B⦄) → Derivation (Γ + Δ + ⦃A ⨂ B⦄)
  | par : Derivation (Γ + ⦃A⦄ + ⦃B⦄) → Derivation (Γ + ⦃A ⅋ B⦄)
  /-- additive rules -/
  | plusLeft : Derivation (Γ + ⦃A⦄) → Derivation (Γ + ⦃A ⨁ B⦄)
  | plusRight : Derivation (Γ + ⦃B⦄) → Derivation (Γ + ⦃A ⨁ B⦄)
  | with : Derivation (Γ + ⦃A⦄) → Derivation (Γ + ⦃B⦄) → Derivation (Γ + ⦃A ＆ B⦄)
  /-- exponential rules -/
  | dereliction : Derivation (Γ + ⦃A⦄) → Derivation (Γ + ⦃？A⦄)
  | bang : Derivation (Γ + ⦃A⦄) → (_ : Sequent.IsQuest Γ := by simp) → Derivation (Γ + ⦃！A⦄)

abbrev Proof (A : Formula) : Type _ := Derivation ⦃A⦄

instance : Entailment LL Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ := by abel) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! ⦃A⦄ + Γ) : ⊢! Γ + ⦃A⦄ := d.cast

def swap (d : ⊢! ⦃A⦄ + ⦃B⦄) : ⊢! ⦃B⦄ + ⦃A⦄ := d.cast

def cutEq (dA : ⊢! Γ + ⦃A⦄) (dB : ⊢! Δ + ⦃B⦄) (e : B = ∼A := by simp) : ⊢! Γ + Δ :=
  have : ⊢! Δ + ⦃∼A⦄ := dB.cast (by rw [e])
  cut dA this

def eta : (A : Formula) → ⊢! ⦃A, ∼A⦄
  |  .atom X => .ax X
  | .natom X => (ax X).swap
  |    A ⨂ B =>
    have d : ⊢! ⦃A ⨂ B, ∼A, ∼B⦄ :=
      ((eta A).swap.tensor (eta B).swap).cast
    d.par
  |    A ⅋ B =>
    have d : ⊢! ⦃∼A ⨂ ∼B, A, B⦄ :=
      ((eta A).tensor (eta B)).cast
    d.par.swap
  |    A ⨁ B => (eta A).swap.plusLeft.swap.with (eta B).swap.plusRight.swap
  |   A ＆ B => ((eta A).plusLeft.swap.with (eta B).plusRight.swap).swap
  |      ！A => (eta A).dereliction.swap.bang.swap
  |      ？A => (eta A).swap.dereliction.swap.bang

end Derivation

namespace Proof

open Derivation

def ax' : 𝐋𝐋⁰ ⊢! A ⊸ A :=
  have d : ⊢! ⦃⦄ + ⦃∼A⦄ + ⦃A⦄ := (eta A).swap.cast
  d.par |>.cast (by simp [Formula.lolli_def])

def modusPonens (d₁ : 𝐋𝐋⁰ ⊢! A ⊸ B) (d₂ : 𝐋𝐋⁰ ⊢! A) : 𝐋𝐋⁰ ⊢! B :=
  have d₁ : ⊢! ⦃⦄ + ⦃∼(A ⨂ ∼B)⦄ := d₁.cast (by simp [Formula.lolli_def])
  have b : ⊢! ⦃∼A, B, A ⨂ ∼B⦄ := (eta A).swap.tensor (eta B)
  have c : ⊢! ⦃∼A, B⦄ := (cut b d₁).cast
  have d₂ : ⊢! ⦃⦄ + ⦃A⦄ := d₂.cast
  (cut d₂ c.swap).cast

end Proof

end LO.Propositional.LinearLogic.LL

end
