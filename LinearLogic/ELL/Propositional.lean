module

public import Foundation.Logic.Entailment
public import LinearLogic.LL.Propositional

/-!
# Propositional linear logic without neutrals
-/

@[expose] public section

namespace LO.Propositional.LinearLogic

inductive ELL where
  | ell

notation "𝐄𝐋𝐋⁰" => ELL.ell

namespace ELL

inductive Derivation : Sequent → Type _
  /-- axiom  -/
  | ax (p : ℕ) : Derivation [.atom p, .natom p]
  /-- cut rule -/
  | cut : Derivation (A :: Γ) → Derivation (∼A :: Δ) → Derivation (Γ ++ Δ)
  /-- structural rules -/
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | weakening : Derivation Γ → Derivation (？A :: Γ)
  | contraction : Derivation (？A :: ？A :: Γ) → Derivation (？A :: Γ)
  /-- multiplicative rules -/
  | tensor : Derivation (A :: Γ) → Derivation (B :: Δ) → Derivation (A ⨂ B :: (Γ ++ Δ))
  | par : Derivation (A :: B :: Γ) → Derivation (A ⅋ B :: Γ)
  /-- additive rules -/
  | plusLeft : Derivation (A :: Γ) → Derivation (A ⨁ B :: Γ)
  | plusRight : Derivation (B :: Γ) → Derivation (A ⨁ B :: Γ)
  | with : Derivation (A :: Γ) → Derivation (B :: Γ) → Derivation (A ＆ B :: Γ)
  /-- exponential rule -/
  | promotion : Derivation (A :: Γ) → Derivation (！A :: ？Γ)

abbrev Proof (A : Formula) : Type _ := Derivation [A]

instance : Entailment ELL Formula := ⟨fun _ ↦ Proof⟩

scoped prefix:45 "⊢! " => Derivation

abbrev Derivable (Γ : Sequent) : Prop := Nonempty (Derivation Γ)

scoped prefix:45 "⊢ " => Derivable

namespace Derivation

def cast (d : ⊢! Γ) (e : Γ = Δ) : ⊢! Δ := e ▸ d

def rotate (d : ⊢! A :: Γ) : ⊢! Γ ++ [A] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def eta : (A : Formula) → ⊢! [A, ∼A]
  |  .atom X => .ax X
  | .natom X => (ax X).rotate
  |    A ⨂ B => ((eta A).tensor (eta B)).rotate.par.rotate
  |    A ⅋ B => ((eta A).rotate.tensor (eta B).rotate).rotate.par
  |    A ⨁ B => ((eta A).plusLeft.rotate.with (eta B).plusRight.rotate).rotate
  |   A ＆ B => (eta A).rotate.plusLeft.rotate.with (eta B).rotate.plusRight.rotate
  |      ！A => (eta A).promotion
  |      ？A => (eta A).rotate.promotion.rotate

end Derivation

namespace Proof

open Derivation

def ax' : 𝐄𝐋𝐋⁰ ⊢! A ⊸ A := (eta A).rotate.par

def modusPonens (d₁ : 𝐄𝐋𝐋⁰ ⊢! A ⊸ B) (d₂ : 𝐄𝐋𝐋⁰ ⊢! A) : 𝐄𝐋𝐋⁰ ⊢! B :=
  have d₁ : ⊢! [∼(A ⨂ ∼B)] := d₁.cast <| by simp [Formula.lolli_def]
  have b : ⊢! [A ⨂ ∼B, ∼A, B] := (eta A).tensor (eta B).rotate
  cut d₂ (cut b d₁)

end Proof

end LO.Propositional.LinearLogic.ELL

end
