module

public import Foundation.Logic.Entailment
public import LinearLogic.LogicSymbol
public import LinearLogic.PhaseSpace.Basic
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

@[elab_as_elim]
def cases' {C : Formula → Sort*}
    (hAtom : ∀ X, C (atom X))
    (hNAtom : ∀ X, C (natom X))
    (hTensor : ∀ A B, C (A ⨂ B))
    (hPar : ∀ A B, C (A ⅋ B)) :
    (A : Formula) → C A
  | atom X => hAtom X
  | natom X => hNAtom X
  | A ⨂ B => hTensor A B
  | A ⅋ B => hPar A B

@[elab_as_elim]
def rec' {C : Formula → Sort w}
    (hAtom : ∀ X, C (atom X))
    (hNAtom : ∀ X, C (natom X))
    (hTensor : ∀ A B, C A → C B → C (A ⨂ B))
    (hPar : ∀ A B, C A → C B → C (A ⅋ B)) :
    (A : Formula) → C A
  | atom X => hAtom X
  | natom X => hNAtom X
  | A ⨂ B => hTensor A B (rec' hAtom hNAtom hTensor hPar A) (rec' hAtom hNAtom hTensor hPar B)
  | A ⅋ B => hPar A B (rec' hAtom hNAtom hTensor hPar A) (rec' hAtom hNAtom hTensor hPar B)

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

namespace PhaseSemantics

variable {M : Type*} [PhaseSpace M]

open PhaseSpace PhaseSpace.Fact

def Val (v : ℕ → Fact M) : Formula → Fact M
  | .atom X => v X
  | .natom X => ∼v X
  | A ⨂ B => Val v A ⨂ Val v B
  | A ⅋ B => Val v A ⅋ Val v B

scoped infix:45 " ⊩ " => Val

namespace Val

variable {v : ℕ → Fact M} {A B : Formula}

@[simp] lemma atom_eq : (v ⊩ .atom X) = v X := rfl

@[simp] lemma natom_eq : (v ⊩ .natom X) = ∼v X := rfl

@[simp] lemma tensor_eq : (v ⊩ A ⨂ B) = (v ⊩ A) ⨂ (v ⊩ B) := rfl

@[simp] lemma par_eq : (v ⊩ A ⅋ B) = (v ⊩ A) ⅋ (v ⊩ B) := rfl

@[simp] lemma neg_eq : (v ⊩ ∼A) = ∼(v ⊩ A) := by
  induction A using Formula.rec' <;> simp [*]

end Val

theorem derivation_sound (v : ℕ → Fact M) {Γ : Sequent} : ⊢! Γ →
    (bigPar (Γ.map (Val v))).IsTrue
  | .ax X => by simpa using Fact.IsTrue.par_neg (A := v X)
  | .cut (A := A) dA dN => by
    simpa using Fact.IsTrue.cut (A := v ⊩ A)
      (by simpa using derivation_sound v dA) (by simpa using derivation_sound v dN)
  | .tensor (A := A) (B := B) dA dB => by
    simpa [par_assoc] using Fact.IsTrue.tensor (A := v ⊩ A) (B := v ⊩ B)
      (by simpa using derivation_sound v dA) (by simpa using derivation_sound v dB)
  | .par d => by
    simpa [par_assoc] using derivation_sound v d

theorem provable_sound (v : ℕ → Fact M) : 𝐌𝐋𝐋⁰ ⊢ A → (v ⊩ A).IsTrue := by
  rintro ⟨d⟩
  simpa using derivation_sound v d

instance : Semantics (PSigma PhaseSpace) Formula :=
  ⟨fun ⟨M, _⟩ A ↦ ∀ v : ℕ → Fact M, (v ⊩ A).IsTrue⟩

instance (M : Type*) [PhaseSpace M] : Sound 𝐌𝐋𝐋⁰ (⟨M, inferInstance⟩ : PSigma PhaseSpace) :=
  ⟨fun h v ↦ provable_sound v h⟩

end PhaseSemantics

example : 𝐌𝐋𝐋⁰ ⊢ A ⅋ ∼A := ⟨by
  have d : ⊢! ⦃⦄ + ⦃A⦄ + ⦃∼A⦄ := (Derivation.eta A).cast
  exact d.par.cast⟩

end LO.Propositional.MultiplicativeLinearLogic

end
