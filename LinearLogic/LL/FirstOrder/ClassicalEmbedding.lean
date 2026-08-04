module

public import Foundation.Logic.Embedding
public import Foundation.FirstOrder.Polarity
public import LinearLogic.LL.FirstOrder.Calculus

/-! # Girard's embedding of classical logic into linear logic -/

@[expose] public section

namespace LO.FirstOrder

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

def forget {Γ : Sequent L} : ⊢ᴸ Γ → ⊢ᴸᴷ¹ Γ.forget
  | ax A => FirstOrder.Derivation.close A.forget (by simp) (by simp)
  | cut (A := A) (Γ := Γ) (Δ := Δ) d₁ d₂ =>
    have dp : ⊢ᴸᴷ¹ A.forget :: Sequent.forget Γ := d₁.forget.cast (by simp)
    have dn : ⊢ᴸᴷ¹ ∼A.forget :: Sequent.forget Δ := d₂.forget.cast (by simp)
    (dp.cut dn).cast (by simp)
  | exchange d h => d.forget.contra (by have := h.subset; grind)
  | one => .verum
  | falsum d => d.forget.contra <| by simp
  | par (Γ := Γ) (A := A) (B := B) d =>
    have : ⊢ᴸᴷ¹ A.forget :: B.forget :: Sequent.forget Γ := d.forget.cast (by simp)
    this.or
  | tensor (Γ := Γ) (Δ := Δ) (A := A) (B := B) d₁ d₂ =>
    have dA : ⊢ᴸᴷ¹ A.forget :: Sequent.forget (Γ ++ Δ) := d₁.forget.contra (by simp)
    have dB : ⊢ᴸᴷ¹ B.forget :: Sequent.forget (Γ ++ Δ) := d₂.forget.contra (by simp)
    dA.and dB
  | verum _ => .top <| by simp
  | .with (Γ := Γ) (A := A) (B := B) d₁ d₂ =>
    have dA : ⊢ᴸᴷ¹ A.forget :: Sequent.forget Γ := d₁.forget.cast (by simp)
    have dB : ⊢ᴸᴷ¹ B.forget :: Sequent.forget Γ := d₂.forget.cast (by simp)
    dA.and dB
  | plusRight (Γ := Γ) (A := A) (B := B) d =>
    have : ⊢ᴸᴷ¹ A.forget :: B.forget :: Sequent.forget Γ := d.forget.contra (by simp)
    this.or
  | plusLeft (Γ := Γ) (A := A) (B := B) d =>
    have : ⊢ᴸᴷ¹ A.forget :: B.forget :: Sequent.forget Γ := d.forget.contra (by simp)
    this.or
  | all (Γ := Γ) (A := A) d =>
    have : ⊢ᴸᴷ¹ A.forget.free :: (Sequent.forget Γ)⁺ := d.forget.cast (by simp)
    this.all
  | exs (Γ := Γ) (A := A) t d =>
    have : ⊢ᴸᴷ¹ A.forget/[t] :: Sequent.forget Γ := d.forget.cast (by simp)
    this.exs
  | weakening (Γ := Γ) (A := A) d => d.forget.contra (by simp)
  | contraction (Γ := Γ) (A := A) d => d.forget.contra (by simp)
  | dereliction (Γ := Γ) (A := A) d =>  d.forget.cast (by simp)
  | ofCourse d _ => d.forget.cast (by simp)

end Derivation

namespace Proof

theorem forget {A : Proposition L} : 𝐋𝐋¹ ⊢ A → 𝐋𝐊¹ ⊢ A.forget := fun h ↦
  ⟨by simpa using! Derivation.forget h.get⟩

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
    have : ⊢ᴸ [？！.rel R v, ？.nrel R v] :=
      LinearLogic.Derivation.ax (！.rel R v) |>.dereliction
    this
  | .cut (φ := A) (Γ := Γ₁) (Δ := Δ₁) d₁ d₂ =>
    match h : A.polarity with
    |  true =>
      have b₁ : ⊢ᴸ ？A† :: Γ₁‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ ∼A† :: Δ₁‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have b₂ : ⊢ᴸ ∼？A† :: Δ₁‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).cast (by simp)
    | false =>
      have b₂ : ⊢ᴸ ∼！A† :: Δ₁‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ A† :: Γ₁‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h])
      have b₁ : ⊢ᴸ ！A† :: Γ₁‡ := this.negativeOfCourse <| by simp
      (b₁.cut b₂).cast (by simp)
  | .contraction d h => d.toLL.negativeWk (List.map_subset Semiformula.Girard h) (by simp)
  | .verum => LinearLogic.Derivation.one.dereliction
  | .and (Γ := Γ) (φ := A) (ψ := B) d₁ d₂ =>
    match h₁ : A.polarity, h₂ : B.polarity with
    | true, true =>
      have dA : ⊢ᴸ ？A† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ ？B† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼A†, ∼B†, ？(A† ⨂ B†)] := (LinearLogic.Derivation.ax A†).tensor (LinearLogic.Derivation.ax B†) |>.dereliction.rotate
      have : ⊢ᴸ [∼？A†, ∼B†, ？(A† ⨂ B†)] := this.negativeOfCourse (by simpa using h₂)
      have : ⊢ᴸ ∼B† :: ？(A† ⨂ B†) :: Γ‡ := (dA.cut this).exchange (by grind)
      have : ⊢ᴸ ∼？B† :: ？(A† ⨂ B†) :: Γ‡ := this.negativeOfCourse (by simp)
      (dB.cut this).negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | true, false =>
      have dA : ⊢ᴸ ？A† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ B† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼A†, ∼！B†, ？(A† ⨂ ！B†)] := (LinearLogic.Derivation.ax A†).tensor (LinearLogic.Derivation.ax (！B†)) |>.dereliction.rotate
      have : ⊢ᴸ [∼？A†, ∼！B†, ？(A† ⨂ ！B†)] := this.ofCourse (by simp)
      have : ⊢ᴸ ∼！B† :: ？(A† ⨂ ！B†) :: Γ‡ := (dA.cut this).exchange (by grind)
      (dB.negativeOfCourse (by simp)).cut this |>.negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | false, true =>
      have : ⊢ᴸ A† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dA : ⊢ᴸ ！A† :: Γ‡ := this.negativeOfCourse (by simp)
      have dB : ⊢ᴸ ？B† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      have : ⊢ᴸ [∼！A†, ∼B†, ？(！A† ⨂ B†)] := (LinearLogic.Derivation.ax (！A†)).tensor (LinearLogic.Derivation.ax B†) |>.dereliction.rotate
      have : ⊢ᴸ [∼！A†, ∼？B†, ？(！A† ⨂ B†)] := (this.rotate.ofCourse (by simp)).invRotate
      have : ⊢ᴸ ∼？B† :: ？(！A† ⨂ B†) :: Γ‡ := (dA.cut this).exchange (by grind)
      (dB.cut this).negativeWk (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]) (by simp)
    | false, false =>
      have dA : ⊢ᴸ A† :: Γ‡ := d₁.toLL.cast (by simp [Semiformula.Girard, h₁])
      have dB : ⊢ᴸ B† :: Γ‡ := d₂.toLL.cast (by simp [Semiformula.Girard, h₂])
      (dA.with dB).cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .or (Γ := Γ) (φ := A) (ψ := B) d =>
    match h₁ : A.polarity, h₂ : B.polarity with
    | true, true =>
      have : ⊢ᴸ ？A† :: ？B† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      have d : ⊢ᴸ ∼(！∼A† ⨂ ！∼B†) :: Γ‡ := this.par.cast (by simp)
      have : ⊢ᴸ [！∼A† ⨂ ！∼B†, ？(A† ⨁ B†)] := LinearLogic.Derivation.expComm _ _
      this.cut d |>.cast (by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂])
    | true, false =>
      have : ⊢ᴸ ？A† :: B† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, true =>
      have : ⊢ᴸ A† :: ？B† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
    | false, false =>
      have : ⊢ᴸ A† :: B† :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h₁, h₂])
      this.par.cast <| by simp [Semiformula.Girard, Semiformula.girard, h₁, h₂]
  | .all (φ := A) (Γ := Γ) d =>
    match h : A.polarity with
    |  true =>
      have : ⊢ᴸ (？A†).free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girard, h])
      this.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have : ⊢ᴸ A†.free :: (Γ‡)⁺ := d.toLL.cast (by simp [Semiformula.Girard, h])
      this.all.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
  | .exs (Γ := Γ) (φ := A) (t := t) d =>
    match h : A.polarity with
    |  true =>
      have d : ⊢ᴸ (？A†)/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have e : ⊢ᴸ [∼(？A†)/[t], ？(∃¹ A†)] :=
        (LinearLogic.Derivation.ax (A†/[t])).exs.dereliction.rotate.ofCourse (by simp)
      (d.cut e).invRotate.cast (by simp [Semiformula.Girard, Semiformula.girard, h])
    | false =>
      have : ⊢ᴸ A†/[t] :: Γ‡ := d.toLL.cast (by simp [Semiformula.Girard, h])
      have : ⊢ᴸ (！A†)/[t] :: Γ‡ := this.negativeOfCourse (by simp)
      this.exs.dereliction.cast (by simp [Semiformula.Girard, Semiformula.girard, h])

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

end LO.FirstOrder
