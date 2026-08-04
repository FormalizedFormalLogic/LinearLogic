module

public import LinearLogic.Vorspiel.List.Perm
public import LinearLogic.LL.FirstOrder.Rew

/-! # One-sided sequent calculus for first-order linear logic -/

@[expose] public section

namespace LO.FirstOrder.LinearLogic

variable {L : Language}

abbrev Sequent (L : Language) := List (Proposition L)

def Sequent.IsQuest (Γ : Sequent L) : Prop := ∀ A ∈ Γ, A.IsQuest

def Sequent.Negative (Γ : Sequent L) : Prop := ∀ A ∈ Γ, A.Negative

namespace Sequent

namespace IsQuest

@[simp] lemma nil : Sequent.IsQuest ([] : Sequent L) := by simp [Sequent.IsQuest]

@[simp] lemma cons (A : Proposition L) (Γ : Sequent L) :
    Sequent.IsQuest (A :: Γ) ↔ A.IsQuest ∧ Sequent.IsQuest Γ := by simp [Sequent.IsQuest]

end IsQuest

namespace Negative

@[simp] lemma nil : Sequent.Negative ([] : Sequent L) := by simp [Sequent.Negative]

@[simp] lemma cons (A : Proposition L) (Γ : Sequent L) :
    Sequent.Negative (A :: Γ) ↔ A.Negative ∧ Sequent.Negative Γ := by simp [Sequent.Negative]

end Negative

@[simp] lemma quest_isQuest (Γ : Sequent L) : Sequent.IsQuest (？Γ) := by
  simp [Sequent.IsQuest, ExponentialConnective.listQuest_def]

end Sequent

/-- Derivation of first-order linear logic -/
inductive Derivation : Sequent L → Type _ where
  /-- axiom -/
  | ax (A) : Derivation [A, ∼A]
  /-- cut rule -/
  | cut : Derivation (A :: Γ) → Derivation (∼A :: Δ) → Derivation (Γ ++ Δ)
  /-- structural rules -/
  | exchange : Derivation Γ → Γ.Perm Δ → Derivation Δ
  | weakening : Derivation Γ → (A : Proposition L) → Derivation (？A :: Γ)
  | contraction : Derivation (？A :: ？A :: Γ) → Derivation (？A :: Γ)
  /-- multiplicative rules -/
  | one : Derivation [1]
  | falsum : Derivation Γ → Derivation (⊥ :: Γ)
  | tensor : Derivation (A :: Γ) → Derivation (B :: Δ) → Derivation (A ⨂ B :: (Γ ++ Δ))
  | par : Derivation (A :: B :: Γ) → Derivation (A ⅋ B :: Γ)
  /-- additive rules -/
  | verum (Γ) : Derivation (⊤ :: Γ)
  | with : Derivation (A :: Γ) → Derivation (B :: Γ) → Derivation (A ＆ B :: Γ)
  | plusLeft : Derivation (B :: Γ) → (A : Proposition L) → Derivation (A ⨁ B :: Γ)
  | plusRight : Derivation (A :: Γ) → (B : Proposition L) → Derivation (A ⨁ B :: Γ)
  /-- exponential rules -/
  | ofCourse : Derivation (A :: Γ) → Sequent.IsQuest Γ → Derivation (！A :: Γ)
  | dereliction : Derivation (A :: Γ) → Derivation (？A :: Γ)
  /-- quantifier rules -/
  | all : Derivation (A.free :: Γ⁺) → Derivation ((∀¹ A) :: Γ)
  | exs (t) : Derivation (A/[t] :: Γ) → Derivation ((∃¹ A) :: Γ)

abbrev Proposition.Proof (A : Proposition L) : Type _ := Derivation [A]

abbrev Sentence.Proof (σ : Sentence L) : Type _ := Derivation [(σ : Proposition L)]

inductive LL (L : Language) where
  | ll : LL L

notation "𝐋𝐋¹" => LL.ll

instance : Entailment (LL L) (Proposition L) := ⟨fun _ ↦ Proposition.Proof⟩

scoped prefix:45 "⊢ᴸ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢ᴸ Γ) (e : Γ = Δ) : ⊢ᴸ Δ := e ▸ d

def rotate (d : ⊢ᴸ A :: Γ) : ⊢ᴸ Γ ++ [A] :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def invRotate (d : ⊢ᴸ Γ ++ [A]) : ⊢ᴸ A :: Γ :=
  d.exchange (by grind only [List.perm_comm, List.perm_append_singleton])

def height {Γ : Sequent L} : ⊢ᴸ Γ → ℕ
  |          ax _ => 0
  |     cut d₁ d₂ => max d₁.height d₂.height + 1
  |  exchange d _ => d.height
  |           one => 0
  |      falsum d => d.height + 1
  |  tensor d₁ d₂ => max d₁.height d₂.height + 1
  |         par d => d.height + 1
  |       verum _ => 0
  |   .with d₁ d₂ => max d₁.height d₂.height + 1
  |  plusLeft d _ => d.height + 1
  | plusRight d _ => d.height + 1
  |  ofCourse d _ => d.height + 1
  | weakening d _ => d.height + 1
  | dereliction d => d.height + 1
  | contraction d => d.height + 1
  |         all d => d.height + 1
  |       exs _ d => d.height + 1

section height

@[simp] lemma height_id (A : Proposition L) :
    (ax A).height = 0 := rfl

@[simp] lemma height_cut (d₁ : ⊢ᴸ A :: Γ) (d₂ : ⊢ᴸ ∼A :: Δ) :
    (d₁.cut d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_exchange (d : ⊢ᴸ Γ) (p : Γ.Perm Δ) :
    (d.exchange p).height = d.height := rfl

@[simp] lemma height_one :
    (one (L := L)).height = 0 := rfl

@[simp] lemma height_falsum (d : ⊢ᴸ Γ) :
    d.falsum.height = d.height + 1 := rfl

@[simp] lemma height_tensor (d₁ : ⊢ᴸ A :: Γ) (d₂ : ⊢ᴸ B :: Δ) :
    (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_par (d : ⊢ᴸ A :: B :: Γ) :
    d.par.height = d.height + 1 := rfl

@[simp] lemma height_verum (Γ : Sequent L) :
    (verum Γ).height = 0 := rfl

@[simp] lemma height_with (d₁ : ⊢ᴸ A :: Γ) (d₂ : ⊢ᴸ B :: Γ) :
    (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_plusLeft (d : ⊢ᴸ A :: Γ) (B) :
    (d.plusLeft B).height = d.height + 1 := rfl

@[simp] lemma height_plusRight (d : ⊢ᴸ B :: Γ) (A) :
    (d.plusRight A).height = d.height + 1 := rfl

@[simp] lemma height_ofCourse (d : ⊢ᴸ A :: Γ) (hΓ : Sequent.IsQuest Γ) :
    (d.ofCourse hΓ).height = d.height + 1 := rfl

@[simp] lemma height_weakening (d : ⊢ᴸ Γ) (A) :
    (d.weakening A).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢ᴸ A :: Γ) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢ᴸ ？A :: ？A :: Γ) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {A : Semiproposition L 1} (d : ⊢ᴸ A.free :: Γ⁺) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_exs {A : Semiproposition L 1} {t} (d : ⊢ᴸ A/[t] :: Γ) :
    (d.exs t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢ᴸ Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def eta : (A : Proposition L) → ⊢ᴸ [A, ∼A]
  |  .rel r v => ax _
  | .nrel r v => ax _
  |         1 => one.falsum.rotate
  |         ⊥ => one.falsum
  |     A ⨂ B => ((eta A).tensor (eta B)).rotate.par.rotate
  |     A ⅋ B => ((eta A).rotate.tensor (eta B).rotate).rotate.par
  |         ⊤ => verum _
  |         0 => (verum [0]).rotate
  |     A ＆ B => ((eta A).rotate.plusRight (∼B)).rotate.with ((eta B).rotate.plusLeft (∼A)).rotate
  |     A ⨁ B => (((eta A).plusRight B).rotate.with ((eta B).plusLeft A).rotate).rotate
  |        ！A => (eta A).rotate.dereliction.rotate.ofCourse (by simp)
  |        ？A => (eta A).dereliction.rotate.ofCourse (by simp) |>.rotate
  |      ∀¹ A =>
    have : ⊢ᴸ [(∼A.shift)/[&0], A.free] := (eta A.free).rotate.cast (by simp)
    have : ⊢ᴸ A.free :: [∃¹ ∼A]⁺ := (this.exs _).rotate.cast (by simp)
    this.all
  |      ∃¹ A =>
    have : ⊢ᴸ [A.shift/[&0], ∼A.free] := (eta A.free).cast (by simp)
    have : ⊢ᴸ (∼A).free :: [∃¹ A]⁺ := (this.exs _).rotate.cast (by simp)
    this.all.rotate
  termination_by A => A.complexity

def expComm (A B : Proposition L) : ⊢ᴸ [！∼A ⨂ ！∼B, ？(A ⨁ B)] :=
  have dA : ⊢ᴸ [！∼A, ？(A ⨁ B)] := ((ax A).plusRight B).dereliction.rotate.ofCourse (by simp)
  have dB : ⊢ᴸ [！∼B, ？(A ⨁ B)] := ((ax B).plusLeft A).dereliction.rotate.ofCourse (by simp)
  have : ⊢ᴸ [！∼A ⨂ ！∼B, ？(A ⨁ B), ？(A ⨁ B)] := dA.tensor dB
  this.rotate.contraction.rotate

def ofNegative : (ν : Proposition L) → ν.Negative → ⊢ᴸ [∼？ν, ν]
  |    ？A, h => (ax (？A)).rotate.ofCourse (by simp)
  |     ⊥, h => (one.ofCourse (by simp)).falsum.rotate
  |     ⊤, h => (verum [！0]).rotate
  | ν ⅋ μ, h =>
    have ihν : ⊢ᴸ [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢ᴸ [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢ᴸ [！(∼ν ⨂ ∼μ), ？ν, ？μ] :=
      (((ax ν).rotate.tensor (ax μ).rotate).rotate.dereliction.rotate.dereliction.rotate).ofCourse (by simp)
    have : ⊢ᴸ [！(∼ν ⨂ ∼μ), ν, μ] := (this.rotate.cut ihν).cut ihμ
    this.rotate.par.rotate
  | ν ＆ μ, h =>
    have ihν : ⊢ᴸ [∼？ν, ν] := ofNegative ν (by rcases h; assumption)
    have ihμ : ⊢ᴸ [∼？μ, μ] := ofNegative μ (by rcases h; assumption)
    have : ⊢ᴸ [！(∼ν ⨁ ∼μ), ？ν] := ((ax ν).rotate.plusRight (∼μ)).rotate.dereliction.rotate.ofCourse (by simp)
    have dν : ⊢ᴸ [ν, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihν).rotate
    have : ⊢ᴸ [！(∼ν ⨁ ∼μ), ？μ] := ((ax μ).rotate.plusLeft (∼ν)).rotate.dereliction.rotate.ofCourse (by simp)
    have dμ : ⊢ᴸ [μ, ！(∼ν ⨁ ∼μ)] := (this.rotate.cut ihμ).rotate
    (dν.with dμ).rotate
  |   ∀¹ ν, h =>
    have ih : ⊢ᴸ [∼？ν.free, ν.free] := ofNegative ν.free (by rcases h; simpa)
    have : ⊢ᴸ [！(∃¹ ∼ν.shift), ？ν.free] := (exs &0 <| (ax ν.free).dereliction.rotate.cast (by simp)).ofCourse (by simp)
    have : ⊢ᴸ (ν).free :: [∼？(∀¹ ν)]⁺ := (this.rotate.cut ih).rotate.cast (by simp)
    this.all.rotate
  termination_by ν => ν.complexity

def removeQuest (h : ν.Negative) (d : ⊢ᴸ ？ν :: Γ) : ⊢ᴸ ν :: Γ :=
  (d.cut (ofNegative ν h)).invRotate

def negativeWeakening {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸ Γ) :
    ⊢ᴸ ν :: Γ := ((d.weakening ν).cut (ofNegative ν h)).invRotate

def negativeContraction {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸ ν :: ν :: Γ) :
    ⊢ᴸ ν :: Γ :=
  have : ⊢ᴸ ？ν :: ？ν :: Γ := d.dereliction.rotate.dereliction.exchange (by simp)
  have : ⊢ᴸ ？ν :: Γ := this.contraction
  this.cut (ofNegative ν h) |>.invRotate

def negativeWk [L.DecidableEq] (d : ⊢ᴸ Γ) (ss : Γ ⊆ Δ) (hΔ : Δ.Negative) :
    ⊢ᴸ Δ :=
  let rec wk {Γ Δ : Sequent L} (c : Γ.CompSubset Δ) (d : ⊢ᴸ Γ) (hΔ : ∀ ν ∈ Δ, ν.Negative) :
      ⊢ᴸ Δ :=
    match c with
    |            .refl _ => d
    |         .perm c hp => (wk c d (by grind)).exchange hp
    |           .add ν c =>
      have : ν.Negative := hΔ ν (by simp)
      (wk c d (by grind)).negativeWeakening this
    | .double (a := ν) c =>
      have : ν.Negative := hΔ ν (by simp)
      (wk c d (by grind)).negativeContraction this
  wk (List.Subset.toCompSubst ss) d hΔ

def addQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ ++ Δ) : ⊢ᴸ Γ ++ ？Δ :=
  match Δ with
  |      [] => d
  | ν :: Δ =>
    have : ⊢ᴸ ν :: Γ ++ Δ := d.exchange (by simp)
    have : ⊢ᴸ ？ν :: Γ ++ ？Δ := (addQuestAppendRight this).dereliction
    this.exchange (by simpa using List.Perm.symm List.perm_middle)

def addQuestTail {Γ : Sequent L} (d : ⊢ᴸ A :: Γ) : ⊢ᴸ A :: ？Γ :=
  have : ⊢ᴸ [A] ++ Γ := d
  addQuestAppendRight this

def removeQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ ++ ？Δ) (h : Δ.Negative) : ⊢ᴸ Γ ++ Δ :=
  match Δ with
  |      [] => d
  | ν :: Δ =>
    have hν : ν.Negative := h ν (by simp)
    have hΔ : Sequent.Negative Δ := by simp [Sequent.Negative] at h; tauto
    have : ⊢ᴸ ？ν :: Γ ++ ？Δ := d.exchange (by simp)
    have : ⊢ᴸ ν :: Γ ++ Δ := (removeQuestAppendRight this hΔ).cut (ofNegative ν hν) |>.invRotate
    this.exchange (by simpa using List.Perm.symm List.perm_middle)

def removeQuestTail {Γ : Sequent L} (d : ⊢ᴸ A :: ？Γ) (h : Γ.Negative) : ⊢ᴸ A :: Γ :=
  have : ⊢ᴸ [A] ++ ？Γ := d
  removeQuestAppendRight this h

def negativeOfCourse {Γ : Sequent L} (d : ⊢ᴸ A :: Γ) (h : Γ.Negative) : ⊢ᴸ ！A :: Γ :=
  have : ⊢ᴸ ！A :: ？Γ := d.addQuestTail.ofCourse (by simp)
  this.removeQuestTail h

end Derivation

end LO.FirstOrder.LinearLogic
