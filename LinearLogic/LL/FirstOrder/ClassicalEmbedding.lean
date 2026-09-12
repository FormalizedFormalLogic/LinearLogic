module

public import Foundation.Logic.Embedding
public import Foundation.FirstOrder.Polarity
public import LinearLogic.LL.FirstOrder.Calculus

/-! # Girard's embedding of classical logic into linear logic -/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language}

/-! ## $\mathbf{LL}$ to $\mathbf{LK}$ -/

namespace LinearLogic

namespace Semiformula

/-- Forget the linear structure and return a classical first-order formula. -/
def forget : Semiformula L ξ n → FirstOrder.Semiformula L ξ n
  |  rel r v => .rel r v
  | nrel r v => .nrel r v
  | 1 | ⊤ => ⊤
  | ⊥ | 0 => ⊥
  | A ⨂ B | A ＆ B => A.forget ⋏ B.forget
  | A ⅋ B | A ⨁ B => A.forget ⋎ B.forget
  | ∀¹ A => ∀¹ A.forget
  | ∃¹ A => ∃¹ A.forget
  | ！A => A.forget
  | ？A => A.forget

@[simp] lemma forget_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).forget = .rel r v := rfl

@[simp] lemma forget_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).forget = .nrel r v := rfl

@[simp] lemma forget_one : (1 : Semiformula L ξ n).forget = ⊤ := rfl

@[simp] lemma forget_verum : (⊤ : Semiformula L ξ n).forget = ⊤ := rfl

@[simp] lemma forget_falsum : (⊥ : Semiformula L ξ n).forget = ⊥ := rfl

@[simp] lemma forget_zero : (0 : Semiformula L ξ n).forget = ⊥ := rfl

@[simp] lemma forget_tensor (A B : Semiformula L ξ n) : (A ⨂ B).forget = A.forget ⋏ B.forget := rfl

@[simp] lemma forget_with (A B : Semiformula L ξ n) : (A ＆ B).forget = A.forget ⋏ B.forget := rfl

@[simp] lemma forget_par (A B : Semiformula L ξ n) : (A ⅋ B).forget = A.forget ⋎ B.forget := rfl

@[simp] lemma forget_plus (A B : Semiformula L ξ n) : (A ⨁ B).forget = A.forget ⋎ B.forget := rfl

@[simp] lemma forget_all (A : Semiformula L ξ (n + 1)) : (∀¹ A).forget = ∀¹ A.forget := rfl

@[simp] lemma forget_exs (A : Semiformula L ξ (n + 1)) : (∃¹ A).forget = ∃¹ A.forget := rfl

@[simp] lemma forget_bang (A : Semiformula L ξ n) : (！A).forget = A.forget := rfl

@[simp] lemma forget_quest (A : Semiformula L ξ n) : (？A).forget = A.forget := rfl

@[simp] lemma forget_neg (A : Semiformula L ξ n) : (∼A).forget = ∼(A.forget) := by
  induction A using rec' <;> simp [*]

@[simp] lemma forget_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (A : Semiformula L ξ₁ n₁) :
    (ω ▹ A).forget = ω ▹ A.forget := by
  induction A using rec' generalizing n₂ <;>
    simp [*, rew_rel, rew_nrel, Function.comp_def]

end Semiformula

abbrev Sequent.forget (Γ : Sequent L) : FirstOrder.Sequent L :=
  Γ.map Semiformula.forget

namespace Sequent

@[simp] lemma forget_shift (Γ : Sequent L) : Sequent.forget (Γ⁺) = (Γ.forget)⁺ := by
  simp [Sequent.forget, Rewriting.shifts]

end Sequent

namespace Derivation

def forget [L.DecidableEq] {Γ : Sequent L} :
    ⊢ᴸ Γ → Γ.Traversal → ⊢ᴸᴷ¹ Γ.forget
  | ax A, _ => (FirstOrder.Derivation.eta A.forget).cast (by simp [Sequent.forget])
  | cut (A := A) (Γ := Γ) (Δ := Δ) d₁ d₂, t =>
    let tΓ := t.restrict (Multiset.le_add_right Γ Δ)
    let tΔ := t.restrict (Multiset.le_add_left Δ Γ)
    have dp : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget⦄ :=
      (d₁.forget (tΓ.succ A)).cast (by simp [Sequent.forget])
    have dn : ⊢ᴸᴷ¹ Sequent.forget Δ + ⦃∼A.forget⦄ :=
      (d₂.forget (tΔ.succ (∼A))).cast (by simp [Sequent.forget])
    (dp.cut dn).cast (by simp [Sequent.forget])
  | one, _ => .verum
  | falsum d, t => ((d.forget t.remove).weakening (φ := ⊥)).cast (by simp [Sequent.forget])
  | par (Γ := Γ) (A := A) (B := B) d, t =>
    have d : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget, B.forget⦄ :=
      (d.forget ((t.remove.succ A).succ B)).cast (by simp [Sequent.forget, add_assoc])
    d.or.cast (by simp [Sequent.forget])
  | tensor (Γ := Γ) (Δ := Δ) (A := A) (B := B) d₁ d₂, t =>
    let tΓ := t.remove.restrict (Multiset.le_add_right Γ Δ)
    let tΔ := t.remove.restrict (Multiset.le_add_left Δ Γ)
    have dA : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget⦄ :=
      (d₁.forget (tΓ.succ A)).cast (by simp [Sequent.forget])
    have dB : ⊢ᴸᴷ¹ Sequent.forget Δ + ⦃B.forget⦄ :=
      (d₂.forget (tΔ.succ B)).cast (by simp [Sequent.forget])
    (FirstOrder.Derivation.tensor (tΓ.map Semiformula.forget)
      (tΔ.map Semiformula.forget) dA dB).cast (by simp [Sequent.forget, add_assoc])
  | verum Γ, t =>
    (Structural.weakenMany (t.remove.map Semiformula.forget)
      FirstOrder.Derivation.verum).cast (by simp [Sequent.forget, add_comm])
  | .with (Γ := Γ) (A := A) (B := B) d₁ d₂, t =>
    have dA : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget⦄ :=
      (d₁.forget (t.remove.succ A)).cast (by simp [Sequent.forget])
    have dB : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃B.forget⦄ :=
      (d₂.forget (t.remove.succ B)).cast (by simp [Sequent.forget])
    (dA.and dB).cast (by simp [Sequent.forget])
  | plusRight (Γ := Γ) (A := A) (B := B) d, t =>
    have d : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget, B.forget⦄ :=
      ((d.forget (t.remove.succ A)).weakening (φ := B.forget)).cast
        (by simp [Sequent.forget, add_assoc])
    d.or.cast (by simp [Sequent.forget])
  | plusLeft (Γ := Γ) (A := A) (B := B) d, t =>
    have d : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget, B.forget⦄ :=
      ((d.forget (t.remove.succ B)).weakening (φ := A.forget)).cast
        (by simp [Sequent.forget, add_assoc, add_comm])
    d.or.cast (by simp [Sequent.forget])
  | all (Γ := Γ) (A := A) d, t =>
    have d : ⊢ᴸᴷ¹ (Sequent.forget Γ)⁺ + ⦃A.forget.free⦄ :=
      (d.forget ((t.remove.map (Rew.shift ▹ ·)).succ A.free)).cast (by simp)
    d.all.cast (by simp [Sequent.forget])
  | exs (Γ := Γ) (A := A) s d, t =>
    have d : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget/[s]⦄ :=
      (d.forget (t.remove.succ (A/[s]))).cast (by simp)
    d.exs.cast (by simp [Sequent.forget])
  | weakening d A, t =>
    ((d.forget t.remove).weakening (φ := A.forget)).cast (by simp [Sequent.forget])
  | contraction (Γ := Γ) (A := A) d, t =>
    have d : ⊢ᴸᴷ¹ Sequent.forget Γ + ⦃A.forget, A.forget⦄ :=
      (d.forget (t.succ (？A))).cast (by simp [Sequent.forget, add_assoc])
    d.contraction.cast (by simp [Sequent.forget])
  | dereliction (A := A) d, t =>
    (d.forget (t.remove.succ A)).cast (by simp)
  | ofCourse (A := A) d _, t =>
    (d.forget (t.remove.succ A)).cast (by simp)

end Derivation

namespace Proof

theorem forget [L.DecidableEq] {A : Proposition L} : 𝐋𝐋¹ ⊢ A → 𝐋𝐊¹ ⊢ A.forget := fun h ↦
  ⟨by simpa using! Derivation.forget h.get (.atom A)⟩

end Proof

end LinearLogic

/-! ## $\mathbf{LK}$ to $\mathbf{LL}$ -/


namespace Semiformula

/-- Girard embedding -/
def girard {n} : (A : Semiformula L ξ n) → LinearLogic.Semiformula L ξ n
  |  rel r v => ！.rel r v
  | nrel r v => ？.nrel r v
  |        ⊤ => 1
  |        ⊥ => ⊥
  |    A ⋏ B =>
    match A.polarity, B.polarity with
    |  true,  true => A.girard ⨂ B.girard
    |  true, false => A.girard ⨂ ！B.girard
    | false,  true => ！A.girard ⨂ B.girard
    | false, false => A.girard ＆ B.girard
  |    A ⋎ B =>
    match A.polarity, B.polarity with
    |  true,  true => A.girard ⨁ B.girard
    |  true, false => ？A.girard ⅋ B.girard
    | false,  true => A.girard ⅋ ？B.girard
    | false, false => A.girard ⅋ B.girard
  |     ∀¹ A =>
    match A.polarity with
    |  true => ∀¹ ？A.girard
    | false => ∀¹ A.girard
  |     ∃¹ A =>
    match A.polarity with
    |  true => ∃¹ A.girard
    | false => ∃¹ ！A.girard

@[simp] lemma girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).girard = ！.rel r v := rfl

@[simp] lemma girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girard = ？.nrel r v := rfl

@[simp] lemma girard_verum : (⊤ : Semiformula L ξ n).girard = 1 := rfl

@[simp] lemma girard_falsum : (⊥ : Semiformula L ξ n).girard = ⊥ := rfl

@[simp] lemma girard_neg (A : Semiformula L ξ n) : (∼A).girard = ∼(A.girard) := by
  match A with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    A ⋏ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => simp [girard, hA, hB, girard_neg A, girard_neg B]
    |  true, false => simp [girard, hA, hB, girard_neg A, girard_neg B]
    | false,  true => simp [girard, hA, hB, girard_neg A, girard_neg B]
    | false, false => simp [girard, hA, hB, girard_neg A, girard_neg B]
  |    A ⋎ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => simp [girard, hA, hB, girard_neg A, girard_neg B]
    |  true, false => simp [girard, hA, hB, girard_neg A, girard_neg B]
    | false,  true => simp [girard, hA, hB, girard_neg A, girard_neg B]
    | false, false => simp [girard, hA, hB, girard_neg A, girard_neg B]
  |     ∀¹ A =>
    match hA : A.polarity with
    |  true => simp [girard, hA, girard_neg A]
    | false => simp [girard, hA, girard_neg A]
  |     ∃¹ A =>
    match hA : A.polarity with
    |  true => simp [girard, hA, girard_neg A]
    | false => simp [girard, hA, girard_neg A]

@[simp] lemma girard_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (A : Semiformula L ξ₁ n₁) :
    (ω ▹ A).girard = ω ▹ A.girard :=
  match A with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    A ⋏ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    |  true, false => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    | false,  true => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    | false, false => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
  |    A ⋎ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    |  true, false => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    | false,  true => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
    | false, false => by simp [girard, hA, hB, girard_rew ω A, girard_rew ω B]
  |     ∀¹ A =>
    match hA : A.polarity with
    |  true => by simp [girard, hA, girard_rew _ A]
    | false => by simp [girard, hA, girard_rew _ A]
  |     ∃¹ A =>
    match hA : A.polarity with
    |  true => by simp [girard, hA, girard_rew _ A]
    | false => by simp [girard, hA, girard_rew _ A]

def Girard (A : Semiformula L ξ n) : LinearLogic.Semiformula L ξ n :=
  match A.polarity with
  |  true => ？A.girard
  | false => A.girard

@[simp] lemma Girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).Girard = ？！.rel r v := rfl

@[simp] lemma Girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).Girard = ？.nrel r v := rfl

@[simp] lemma Girard_verum : (⊤ : Semiformula L ξ n).Girard = ？1 := rfl

@[simp] lemma Girard_falsum : (⊥ : Semiformula L ξ n).Girard = ⊥ := rfl

@[simp] lemma Girard_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (A : Semiformula L ξ₁ n₁) :
    (ω ▹ A).Girard = ω ▹ A.Girard := by
  match h : A.polarity with
  |  true => simp [Girard, h, girard_rew ω A]
  | false => simp [Girard, h, girard_rew ω A]

lemma girard_negative {A : Semiformula L ξ n} (h : A.Negative) : A.girard.Negative := by
  match A with
  |  rel _ _ => simp_all
  | nrel _ _ => simp_all
  |        ⊤ => simp_all
  |        ⊥ => simp_all
  |    A ⋏ B =>
    have hA : A.polarity = false := by simp [Negative] at h; tauto
    have hB : B.polarity = false := by simp [Negative] at h; tauto
    simp [girard, hA, hB, girard_negative hA, girard_negative hB]
  |    A ⋎ B =>
    have hA : A.polarity = false ∨ B.polarity = false := by simp [Negative] at h; grind
    rcases hA with (hA | hB)
    · match hB : B.polarity with
      |  true => simp [girard, hA, hB, girard_negative hA]
      | false => simp [girard, hA, hB, girard_negative hA, girard_negative hB]
    · match hA : A.polarity with
      |  true => simp [girard, hA, hB, girard_negative hB]
      | false => simp [girard, hA, hB, girard_negative hA, girard_negative hB]
  |     ∀¹ A =>
    match hA : A.polarity with
    |  true => simp [girard, hA]
    | false => simp [girard, hA, girard_negative hA]

lemma girard_positive {A : Semiformula L ξ n} (h : A.Positive) : A.girard.Positive := by
  have : (∼A).Negative := by simpa
  simpa using girard_negative this

@[simp] lemma girard_negative_iff {A : Semiformula L ξ n} : A.girard.Negative ↔ A.Negative := by
  constructor
  · contrapose
    intro h
    have : A.girard.Positive := girard_positive (by simpa using h)
    grind
  · intro h; exact girard_negative h

@[simp] lemma girard_positive_iff {A : Semiformula L ξ n} : A.girard.Positive ↔ A.Positive := by
  constructor
  · contrapose
    intro h
    have : A.girard.Negative := girard_negative (by simpa using h)
    grind
  · intro h; exact girard_positive h

@[simp] lemma Girard_negative (A : Semiformula L ξ n) : A.Girard.Negative :=
  match h : A.polarity with
  |  true => by simp [Girard, h]
  | false => by simp [Girard, h, girard_negative h]

@[simp] lemma forget_girard (A : Semiformula L ξ n) : A.girard.forget = A :=
  match A with
  |  rel _ _ => rfl
  | nrel _ _ => rfl
  |        ⊤ => rfl
  |        ⊥ => rfl
  |    A ⋏ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    |  true, false => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    | false,  true => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    | false, false => by simp [girard, hA, hB, forget_girard A, forget_girard B]
  |    A ⋎ B =>
    match hA : A.polarity, hB : B.polarity with
    |  true,  true => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    |  true, false => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    | false,  true => by simp [girard, hA, hB, forget_girard A, forget_girard B]
    | false, false => by simp [girard, hA, hB, forget_girard A, forget_girard B]
  |     ∀¹ A =>
    match hA : A.polarity with
    |  true => by simp [girard, hA, forget_girard A]
    | false => by simp [girard, hA, forget_girard A]
  |     ∃¹ A =>
    match hA : A.polarity with
    |  true => by simp [girard, hA, forget_girard A]
    | false => by simp [girard, hA, forget_girard A]

@[simp] lemma forget_Girard (A : Semiformula L ξ n) : A.Girard.forget = A :=
  match h : A.polarity with
  |  true => by simp [Girard, h]
  | false => by simp [Girard, h]

end Semiformula

abbrev Sequent.Girard (Γ : Sequent L) : LinearLogic.Sequent L :=
  Γ.map Semiformula.Girard

namespace Sequent

@[simp] lemma girard_negative (Γ : Sequent L) : Γ.Girard.Negative := by
  simp [Sequent.Girard, LinearLogic.Sequent.Negative]

@[simp] lemma shifts_Girard (Γ : Sequent L) : (Γ.Girard)⁺ = Girard (Γ⁺ : Sequent L) := by
  simp [Sequent.Girard, Rewriting.shifts]

end Sequent

namespace Derivation

open LinearLogic

variable [L.DecidableEq]

local postfix:max "†" => Semiformula.girard
local postfix:max "‡" => Semiformula.Girard
local postfix:max "‡" => Sequent.Girard

def toLL {Γ : Sequent L} : ⊢ᴸᴷ¹ Γ → ⊢ᴸ Γ‡
  | .identity R v =>
    have d : ⊢ᴸ ⦃？.nrel R v⦄ + ⦃！.rel R v⦄ :=
      (LinearLogic.Derivation.ax (！.rel R v)).cast (by abel)
    d.dereliction.cast (by simp [Sequent.Girard, Semiformula.Girard, add_comm])
  | .cut (φ := A) (Γ := Γ₁) (Δ := Δ₁) d₁ d₂ =>
    match h : A.polarity with
    |  true =>
      have b₁ : ⊢ᴸ Γ₁‡ + ⦃？A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have d : ⊢ᴸ Δ₁‡ + ⦃∼A†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have b₂ : ⊢ᴸ Δ₁‡ + ⦃∼？A†⦄ :=
        d.negativeOfCourse (d₂.traversal.remove.map Semiformula.Girard) (by simp)
      (b₁.cut b₂).cast (by simp [Sequent.Girard])
    | false =>
      have b₂ : ⊢ᴸ Δ₁‡ + ⦃∼！A†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have d : ⊢ᴸ Γ₁‡ + ⦃A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have b₁ : ⊢ᴸ Γ₁‡ + ⦃！A†⦄ :=
        d.negativeOfCourse (d₁.traversal.remove.map Semiformula.Girard) (by simp)
      (b₁.cut b₂).cast (by simp [Sequent.Girard])
  | .contraction (Γ := Γ) (φ := A) d =>
    have d : ⊢ᴸ Γ‡ + ⦃A‡⦄ + ⦃A‡⦄ := d.toLL.cast (by simp [Sequent.Girard, add_assoc])
    (d.negativeContraction (by simp)).cast (by simp [Sequent.Girard])
  | .weakening (φ := A) d =>
    (d.toLL.negativeWeakening (ν := A‡) (by simp)).cast (by simp [Sequent.Girard])
  | .verum =>
    ((LinearLogic.Derivation.one.cast : ⊢ᴸ ⦃⦄ + ⦃1⦄).dereliction : ⊢ᴸ ⦃⦄ + ⦃？1⦄).cast
  | .and (Γ := Γ) (φ := A) (ψ := B) d₁ d₂ =>
    let tΓ := d₁.traversal.remove.map Semiformula.Girard
    let questTensorQuest (dA : ⊢ᴸ Γ‡ + ⦃？A†⦄) (dB : ⊢ᴸ Γ‡ + ⦃？B†⦄)
        (hB : B†.Positive) : ⊢ᴸ Γ‡ + ⦃？(A† ⨂ B†)⦄ :=
      have d : ⊢ᴸ ⦃∼A†, ∼B†, ？(A† ⨂ B†)⦄ :=
        (LinearLogic.Derivation.tensorAxiom A† B†).dereliction
      have d : ⊢ᴸ ⦃∼B†, ？(A† ⨂ B†)⦄ + ⦃∼A†⦄ := d.cast
      have d : ⊢ᴸ ⦃∼B†, ？(A† ⨂ B†)⦄ + ⦃∼？A†⦄ :=
        d.negativeOfCourse ((Multiset.Traversal.atom _).succ _) (by simp [hB])
      have d : ⊢ᴸ Γ‡ + ⦃∼B†, ？(A† ⨂ B†)⦄ := (dA.cut d).cast
      have d : ⊢ᴸ Γ‡ + ⦃？(A† ⨂ B†)⦄ + ⦃∼B†⦄ := d.cast
      have d : ⊢ᴸ Γ‡ + ⦃？(A† ⨂ B†)⦄ + ⦃∼？B†⦄ :=
        d.negativeOfCourse (tΓ.succ _) (by simp) |>.cast
      have d : ⊢ᴸ Γ‡ + (Γ‡ + ⦃？(A† ⨂ B†)⦄) := dB.cut d
      (d.cast.negativeContractMany (Δ := ⦃？(A† ⨂ B†)⦄) tΓ (by simp)).cast
    let questTensorPlain (dA : ⊢ᴸ Γ‡ + ⦃？A†⦄) (dB : ⊢ᴸ Γ‡ + ⦃B†⦄) :
        ⊢ᴸ Γ‡ + ⦃？(A† ⨂ ！B†)⦄ :=
      have dB : ⊢ᴸ Γ‡ + ⦃！B†⦄ := dB.negativeOfCourse tΓ (by simp)
      have d : ⊢ᴸ ⦃∼A†, ∼！B†, ？(A† ⨂ ！B†)⦄ :=
        (LinearLogic.Derivation.tensorAxiom A† (！B†)).dereliction
      have d : ⊢ᴸ ⦃∼！B†, ？(A† ⨂ ！B†)⦄ + ⦃∼A†⦄ := d.cast
      have d : ⊢ᴸ ⦃∼！B†, ？(A† ⨂ ！B†)⦄ + ⦃∼？A†⦄ := d.ofCourse (by simp)
      have d : ⊢ᴸ Γ‡ + ⦃∼！B†, ？(A† ⨂ ！B†)⦄ := (dA.cut d).cast
      have d : ⊢ᴸ Γ‡ + ⦃？(A† ⨂ ！B†)⦄ + ⦃∼！B†⦄ := d.cast
      have d : ⊢ᴸ Γ‡ + (Γ‡ + ⦃？(A† ⨂ ！B†)⦄) := dB.cut d
      (d.cast.negativeContractMany (Δ := ⦃？(A† ⨂ ！B†)⦄) tΓ (by simp)).cast
    let plainTensorQuest (dA : ⊢ᴸ Γ‡ + ⦃A†⦄) (dB : ⊢ᴸ Γ‡ + ⦃？B†⦄) :
        ⊢ᴸ Γ‡ + ⦃？(！A† ⨂ B†)⦄ :=
      have dA : ⊢ᴸ Γ‡ + ⦃！A†⦄ := dA.negativeOfCourse tΓ (by simp)
      have d : ⊢ᴸ ⦃∼！A†, ∼B†, ？(！A† ⨂ B†)⦄ :=
        (LinearLogic.Derivation.tensorAxiom (！A†) B†).dereliction
      have d : ⊢ᴸ ⦃∼！A†, ？(！A† ⨂ B†)⦄ + ⦃∼B†⦄ := d.cast
      have d : ⊢ᴸ ⦃∼！A†, ？(！A† ⨂ B†)⦄ + ⦃∼？B†⦄ := d.ofCourse (by simp)
      have d : ⊢ᴸ ⦃？(！A† ⨂ B†), ∼？B†⦄ + ⦃∼！A†⦄ := d.cast
      have d : ⊢ᴸ Γ‡ + ⦃∼？B†, ？(！A† ⨂ B†)⦄ := (dA.cut d).cast
      have d : ⊢ᴸ Γ‡ + ⦃？(！A† ⨂ B†)⦄ + ⦃∼？B†⦄ := d.cast
      have d : ⊢ᴸ Γ‡ + (Γ‡ + ⦃？(！A† ⨂ B†)⦄) := dB.cut d
      (d.cast.negativeContractMany (Δ := ⦃？(！A† ⨂ B†)⦄) tΓ (by simp)).cast
    match h₁ : A.polarity, h₂ : B.polarity with
    | true, true =>
      have dA : ⊢ᴸ Γ‡ + ⦃？A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ Γ‡ + ⦃？B†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (questTensorQuest dA dB (Semiformula.girard_positive h₂)).cast
        (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂])
    | true, false =>
      have dA : ⊢ᴸ Γ‡ + ⦃？A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ Γ‡ + ⦃B†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (questTensorPlain dA dB).cast (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂])
    | false, true =>
      have dA : ⊢ᴸ Γ‡ + ⦃A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ Γ‡ + ⦃？B†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (plainTensorQuest dA dB).cast (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂])
    | false, false =>
      have dA : ⊢ᴸ Γ‡ + ⦃A†⦄ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ Γ‡ + ⦃B†⦄ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (dA.with dB).cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .or (Γ := Γ) (φ := A) (ψ := B) d =>
    match h₁ : A.polarity, h₂ : B.polarity with
    | true, true =>
      have d : ⊢ᴸ Γ‡ + ⦃？A†, ？B†⦄ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ Γ‡ + ⦃？A†⦄ + ⦃？B†⦄ := d.cast
      have d : ⊢ᴸ Γ‡ + ⦃∼(！∼A† ⨂ ！∼B†)⦄ := d.par.cast (by simp)
      have e : ⊢ᴸ ⦃！∼A† ⨂ ！∼B†, ？(A† ⨁ B†)⦄ := LinearLogic.Derivation.expComm _ _
      have e : ⊢ᴸ ⦃？(A† ⨁ B†)⦄ + ⦃！∼A† ⨂ ！∼B†⦄ := e.cast
      e.cut d |>.cast (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂, add_comm])
    | true, false =>
      have d : ⊢ᴸ Γ‡ + ⦃？A†, B†⦄ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ Γ‡ + ⦃？A†⦄ + ⦃B†⦄ := d.cast
      d.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, true =>
      have d : ⊢ᴸ Γ‡ + ⦃A†, ？B†⦄ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ Γ‡ + ⦃A†⦄ + ⦃？B†⦄ := d.cast
      d.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, false =>
      have d : ⊢ᴸ Γ‡ + ⦃A†, B†⦄ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ Γ‡ + ⦃A†⦄ + ⦃B†⦄ := d.cast
      d.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .all (φ := A) (Γ := Γ) d =>
    match h : A.polarity with
    |  true =>
      have d : ⊢ᴸ (Γ‡)⁺ + ⦃(？A†).free⦄ := d.toLL.cast (by simp [Semiformula.Girard, h])
      d.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have d : ⊢ᴸ (Γ‡)⁺ + ⦃A†.free⦄ := d.toLL.cast (by simp [Semiformula.Girard, h])
      d.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
  | .exs (Γ := Γ) (φ := A) (t := t) d =>
    let tΓ := d.traversal.remove.map Semiformula.Girard
    match h : A.polarity with
    |  true =>
      have d : ⊢ᴸ Γ‡ + ⦃(？A†)/[t]⦄ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have e : ⊢ᴸ ⦃∼A†/[t]⦄ + ⦃A†/[t]⦄ :=
        (LinearLogic.Derivation.ax (A†/[t])).cast (by abel)
      have e : ⊢ᴸ ⦃∼A†/[t]⦄ + ⦃∃¹ A†⦄ := e.exs
      have e : ⊢ᴸ ⦃∼A†/[t]⦄ + ⦃？(∃¹ A†)⦄ := e.dereliction
      have e : ⊢ᴸ ⦃？(∃¹ A†)⦄ + ⦃！(∼A†/[t])⦄ := e.cast |>.ofCourse (by simp)
      have e : ⊢ᴸ ⦃∼(？A†)/[t], ？(∃¹ A†)⦄ := e.cast (by simp [add_comm])
      have e : ⊢ᴸ ⦃？(∃¹ A†)⦄ + ⦃∼(？A†)/[t]⦄ := e.cast
      (d.cut e).cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have d : ⊢ᴸ Γ‡ + ⦃A†/[t]⦄ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have d : ⊢ᴸ Γ‡ + ⦃(！A†)/[t]⦄ := d.negativeOfCourse tΓ (by simp)
      d.exs.dereliction.cast (by simp [Semiformula.Girard, Semiformula.girard, h])

end Derivation

namespace Proof

variable [L.DecidableEq]

theorem girard {A : Proposition L} : 𝐋𝐊¹ ⊢ A → 𝐋𝐋¹ ⊢ A.Girard := fun h ↦
  ⟨by simpa using! Derivation.toLL h.get⟩

theorem girard_faithful {A : Proposition L} : 𝐋𝐋¹ ⊢ A.Girard ↔ 𝐋𝐊¹ ⊢ A :=
  ⟨fun h ↦ by simpa using LinearLogic.Proof.forget h, girard⟩

instance : Entailment.FaithfullyEmbeddable (𝐋𝐊¹ : LK L) (𝐋𝐋¹ : LinearLogic.LL L) where
  prop := ⟨Semiformula.Girard, fun _ ↦ girard_faithful⟩

end Proof

end FFL.FirstOrder
