module

public import Foundation.Logic.Entailment
public import LinearLogic.LL.Propositional

/-!
# Propositional elementary linear logic without neutrals

## References
- J.-Y. Girard, Light linear logic.
-/

@[expose] public section

namespace LO.Propositional.LinearLogic

inductive ELL where
  | ell

notation "𝐄𝐋𝐋⁰" => ELL.ell

namespace ELL

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
  /-- exponential rule -/
  | promotion : Derivation (Γ + ⦃A⦄) → Derivation (Γ.map (？·) + ⦃！A⦄)

abbrev Proof (A : Formula) : Type _ := Derivation ⦃A⦄

instance : Entailment ELL Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ := by abel) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! ⦃A⦄ + Γ) : ⊢! Γ + ⦃A⦄ := d.cast

def swap (d : ⊢! ⦃A⦄ + ⦃B⦄) : ⊢! ⦃B⦄ + ⦃A⦄ := d.cast

def eta : (A : Formula) → ⊢! ⦃A, ∼A⦄
  |  .atom X => .ax X
  | .natom X => (ax X).swap
  |    A ⨂ B =>
    have d : ⊢! ⦃A ⨂ B, ∼A, ∼B⦄ := ((eta A).swap.tensor (eta B).swap).cast
    d.par
  |    A ⅋ B =>
    have d : ⊢! ⦃∼A ⨂ ∼B, A, B⦄ := ((eta A).tensor (eta B)).cast
    d.par.swap
  |    A ⨁ B => (eta A).swap.plusLeft.swap.with (eta B).swap.plusRight.swap
  |   A ＆ B => ((eta A).plusLeft.swap.with (eta B).plusRight.swap).swap
  |      ！A => (eta A).swap.promotion.swap
  |      ？A => (eta A).promotion

end Derivation

namespace Proof

open Derivation

def ax' : 𝐄𝐋𝐋⁰ ⊢! A ⊸ A :=
  have d : ⊢! ⦃⦄ + ⦃∼A⦄ + ⦃A⦄ := (eta A).swap.cast
  d.par |>.cast (by simp [Formula.lolli_def])

def modusPonens (d₁ : 𝐄𝐋𝐋⁰ ⊢! A ⊸ B) (d₂ : 𝐄𝐋𝐋⁰ ⊢! A) : 𝐄𝐋𝐋⁰ ⊢! B :=
  have d₁ : ⊢! ⦃⦄ + ⦃∼(A ⨂ ∼B)⦄ := d₁.cast (by simp [Formula.lolli_def])
  have b : ⊢! ⦃∼A, B, A ⨂ ∼B⦄ := (eta A).swap.tensor (eta B)
  have c : ⊢! ⦃∼A, B⦄ := (cut b d₁).cast
  have d₂ : ⊢! ⦃⦄ + ⦃A⦄ := d₂.cast
  (cut d₂ c.swap).cast

end Proof

end LO.Propositional.LinearLogic.ELL

end
