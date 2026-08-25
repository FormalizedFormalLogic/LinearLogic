module

public import Foundation.Logic.Entailment
public import LinearLogic.LogicSymbol
public import LinearLogic.Vorspiel.Multiset

/-!
# Multiplicative linear logic without neutrals
-/

@[expose] public section

namespace LO.Propositional.MultiplicativeLinearLogic

inductive Formula where
  | atom : ℕ → Formula
  | natom : ℕ → Formula
  | tensor : Formula → Formula → Formula
  | par : Formula → Formula → Formula

namespace Formula

instance : MultiplicativeConnective Formula where
  tensor := tensor
  par := par
  tensor_injective _ _ _ _ := by simp [tensor.injEq]
  par_injective _ _ _ _ := by simp [par.injEq]

variable {α : Type*}

def neg : Formula → Formula
  |  atom X => natom X
  | natom X => atom X
  |   A ⨂ B => neg A ⅋ neg B
  |   A ⅋ B => neg A ⨂ neg B

instance : Tilde Formula := ⟨neg⟩

@[simp] lemma neg_atom (X : ℕ) : ∼atom X = natom X := rfl

@[simp] lemma neg_natom (X : ℕ) : ∼natom X = atom X := rfl

instance : MultiplicativeConnective.DeMorgan Formula where
  tensor _ _ := rfl
  par _ _ := rfl

@[simp] lemma neg_neg (A : Formula) : ∼∼A = A := by
  match A with
  |  atom X => rfl
  | natom X => rfl
  |   A ⨂ B => simp [neg_neg A, neg_neg B]
  |   A ⅋ B => simp [neg_neg A, neg_neg B]

instance : TildeInvolutive Formula where
  tilde_involutive := neg_neg

lemma lolli_def (A B : Formula) : A ⊸ B = ∼A ⅋ B := rfl

end Formula

variable {α : Type*}

abbrev Sequent := Multiset Formula

inductive Derivation : Sequent → Type _
  /-- axiom -/
  | ax (X : ℕ) : Derivation ⦃.atom X, .natom X⦄
  /-- cut rule -/
  | cut : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃∼A⦄) → Derivation (Γ + Δ)
  /-- multiplicative rules -/
  | tensor : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃B⦄) → Derivation (Γ + Δ + ⦃A ⨂ B⦄)
  | par : Derivation (Γ + ⦃A⦄ + ⦃B⦄) → Derivation (Γ + ⦃A ⅋ B⦄)

abbrev Proof (A : Formula) : Type _ := Derivation ⦃A⦄

inductive Symbol where
  | mll

notation "𝐌𝐋𝐋⁰" => Symbol.mll

instance : Entailment Symbol Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ := by abel) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! ⦃A⦄ + Γ) : ⊢! Γ + ⦃A⦄ := d.cast

def swap (d : ⊢! ⦃A⦄ + ⦃B⦄) : ⊢! ⦃B⦄ + ⦃A⦄ := d.cast

def eta : (A : Formula) → ⊢! ⦃A, ∼A⦄
  |  .atom X => ax X
  | .natom X => (ax X).swap
  |    A ⨂ B =>
    have d : ⊢! ⦃A ⨂ B, ∼A, ∼B⦄ := ((eta A).swap.tensor (eta B).swap).cast
    d.par
  |    A ⅋ B =>
    have d : ⊢! ⦃∼A ⨂ ∼B, A, B⦄ := ((eta A).tensor (eta B)).cast
    d.par.swap

end Derivation

namespace Proof

open Derivation

def eta' : 𝐌𝐋𝐋⁰ ⊢! A ⊸ A :=
  have d : ⊢! ⦃⦄ + ⦃∼A⦄ + ⦃A⦄ := (eta A).swap.cast
  d.par |>.cast (by simp [Formula.lolli_def])

def modusPonens (d₁ : 𝐌𝐋𝐋⁰ ⊢! A ⊸ B) (d₂ : 𝐌𝐋𝐋⁰ ⊢! A) : 𝐌𝐋𝐋⁰ ⊢! B :=
  have d₁ : ⊢! ⦃⦄ + ⦃∼(A ⨂ ∼B)⦄ := d₁.cast (by simp [Formula.lolli_def])
  have b : ⊢! ⦃∼A, B, A ⨂ ∼B⦄ := (eta A).swap.tensor (eta B)
  have c : ⊢! ⦃∼A, B⦄ := (cut b d₁).cast
  have d₂ : ⊢! ⦃⦄ + ⦃A⦄ := d₂.cast
  (cut d₂ c.swap).cast

end Proof

example : 𝐌𝐋𝐋⁰ ⊢ A ⅋ ∼A := ⟨by
  have d : ⊢! ⦃⦄ + ⦃A⦄ + ⦃∼A⦄ := (Derivation.eta A).cast
  exact d.par.cast⟩

end LO.Propositional.MultiplicativeLinearLogic

end
