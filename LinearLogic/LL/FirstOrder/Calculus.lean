module

public import LinearLogic.LL.FirstOrder.Rew
public import LinearLogic.Vorspiel.Multiset

/-! # One-sided sequent calculus for first-order linear logic -/

@[expose] public section

namespace FFL.FirstOrder.LinearLogic

variable {L : Language}

abbrev Sequent (L : Language) := Multiset (Proposition L)

def Sequent.IsQuest (Γ : Sequent L) : Prop := ∀ A ∈ Γ, A.IsQuest

def Sequent.Negative (Γ : Sequent L) : Prop := ∀ A ∈ Γ, A.Negative

namespace Sequent

namespace IsQuest

@[simp] lemma zero : Sequent.IsQuest (0 : Sequent L) := by simp [Sequent.IsQuest]

@[simp] lemma add (Γ Δ : Sequent L) :
    Sequent.IsQuest (Γ + Δ) ↔ Γ.IsQuest ∧ Δ.IsQuest := Multiset.forall_mem_add

@[simp] lemma singleton (A : Proposition L) : Sequent.IsQuest ⦃A⦄ ↔ A.IsQuest := by
  simp [Sequent.IsQuest]

end IsQuest

namespace Negative

@[simp] lemma zero : Sequent.Negative (0 : Sequent L) := by simp [Sequent.Negative]

@[simp] lemma add (Γ Δ : Sequent L) :
    Sequent.Negative (Γ + Δ) ↔ Γ.Negative ∧ Δ.Negative := Multiset.forall_mem_add

@[simp] lemma singleton (A : Proposition L) : Sequent.Negative ⦃A⦄ ↔ A.Negative := by
  simp [Sequent.Negative]

end Negative

@[simp] lemma quest_isQuest (Γ : Sequent L) : Sequent.IsQuest (？Γ) := by
  simp [Sequent.IsQuest, ExponentialConnective.multisetQuest_def]

end Sequent

/-- Derivation of first-order linear logic -/
inductive Derivation : Sequent L → Type _ where
  /-- axiom -/
  | ax (A) : Derivation ⦃A, ∼A⦄
  /-- cut rule -/
  | cut : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃∼A⦄) → Derivation (Γ + Δ)
  /-- structural rules -/
  | weakening : Derivation Γ → (A : Proposition L) → Derivation (Γ + ⦃？A⦄)
  | contraction : Derivation (Γ + ⦃？A⦄ + ⦃？A⦄) → Derivation (Γ + ⦃？A⦄)
  /-- multiplicative rules -/
  | one : Derivation ⦃1⦄
  | falsum : Derivation Γ → Derivation (Γ + ⦃⊥⦄)
  | tensor : Derivation (Γ + ⦃A⦄) → Derivation (Δ + ⦃B⦄) → Derivation (Γ + Δ + ⦃A ⨂ B⦄)
  | par : Derivation (Γ + ⦃A⦄ + ⦃B⦄) → Derivation (Γ + ⦃A ⅋ B⦄)
  /-- additive rules -/
  | verum (Γ) : Derivation (Γ + ⦃⊤⦄)
  | with : Derivation (Γ + ⦃A⦄) → Derivation (Γ + ⦃B⦄) → Derivation (Γ + ⦃A ＆ B⦄)
  | plusLeft : Derivation (Γ + ⦃B⦄) → (A : Proposition L) → Derivation (Γ + ⦃A ⨁ B⦄)
  | plusRight : Derivation (Γ + ⦃A⦄) → (B : Proposition L) → Derivation (Γ + ⦃A ⨁ B⦄)
  /-- exponential rules -/
  | ofCourse : Derivation (Γ + ⦃A⦄) → Sequent.IsQuest Γ → Derivation (Γ + ⦃！A⦄)
  | dereliction : Derivation (Γ + ⦃A⦄) → Derivation (Γ + ⦃？A⦄)
  /-- quantifier rules -/
  | all : Derivation (Γ⁺ + ⦃A.free⦄) → Derivation (Γ + ⦃∀¹ A⦄)
  | exs (t) : Derivation (Γ + ⦃A/[t]⦄) → Derivation (Γ + ⦃∃¹ A⦄)

abbrev Proposition.Proof (A : Proposition L) : Type _ := Derivation ⦃A⦄

abbrev Sentence.Proof (σ : Sentence L) : Type _ := Derivation ⦃(σ : Proposition L)⦄

inductive LL (L : Language) where
  | ll : LL L

notation "𝐋𝐋¹" => LL.ll

instance : Entailment (LL L) (Proposition L) := ⟨fun _ ↦ Proposition.Proof⟩

prefix:45 "⊢ᴸᴸ¹ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢ᴸᴸ¹ Γ) (e : Γ = Δ := by abel) : ⊢ᴸᴸ¹ Δ := e ▸ d

def rotate (d : ⊢ᴸᴸ¹ ⦃A⦄ + Γ) : ⊢ᴸᴸ¹ Γ + ⦃A⦄ := d.cast

def invRotate (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) : ⊢ᴸᴸ¹ ⦃A⦄ + Γ := d.cast

def height {Γ : Sequent L} : ⊢ᴸᴸ¹ Γ → ℕ
  |          ax _ => 0
  |     cut d₁ d₂ => max d₁.height d₂.height + 1
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

@[simp] lemma height_cut (d₁ : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (d₂ : ⊢ᴸᴸ¹ Δ + ⦃∼A⦄) :
    (d₁.cut d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_one :
    (one (L := L)).height = 0 := rfl

@[simp] lemma height_falsum (d : ⊢ᴸᴸ¹ Γ) :
    d.falsum.height = d.height + 1 := rfl

@[simp] lemma height_tensor (d₁ : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (d₂ : ⊢ᴸᴸ¹ Δ + ⦃B⦄) :
    (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_par (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄ + ⦃B⦄) :
    d.par.height = d.height + 1 := rfl

@[simp] lemma height_verum (Γ : Sequent L) :
    (verum Γ).height = 0 := rfl

@[simp] lemma height_with (d₁ : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (d₂ : ⊢ᴸᴸ¹ Γ + ⦃B⦄) :
    (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_plusLeft (d : ⊢ᴸᴸ¹ Γ + ⦃B⦄) (A : Proposition L) :
    (d.plusLeft A).height = d.height + 1 := rfl

@[simp] lemma height_plusRight (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (B : Proposition L) :
    (d.plusRight B).height = d.height + 1 := rfl

@[simp] lemma height_ofCourse (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (hΓ : Sequent.IsQuest Γ) :
    (d.ofCourse hΓ).height = d.height + 1 := rfl

@[simp] lemma height_weakening (d : ⊢ᴸᴸ¹ Γ) (A) :
    (d.weakening A).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢ᴸᴸ¹ Γ + ⦃？A⦄ + ⦃？A⦄) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {A : Semiproposition L 1} (d : ⊢ᴸᴸ¹ Γ⁺ + ⦃A.free⦄) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_exs {A : Semiproposition L 1} {t} (d : ⊢ᴸᴸ¹ Γ + ⦃A/[t]⦄) :
    (d.exs t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢ᴸᴸ¹ Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def eta : (A : Proposition L) → ⊢ᴸᴸ¹ ⦃A, ∼A⦄
  | .rel _ _ => ax _
  | .nrel _ _ => ax _
  | 1 => one.falsum
  | ⊥ => one.falsum.cast (by simp [add_comm])
  | A ⨂ B =>
    have d : ⊢ᴸᴸ¹ ⦃A ⨂ B, ∼A, ∼B⦄ := ((eta A).rotate.tensor (eta B).rotate).cast
    d.par
  | A ⅋ B =>
    have d : ⊢ᴸᴸ¹ ⦃∼A ⨂ ∼B, A, B⦄ := ((eta A).tensor (eta B)).cast
    d.par.cast (by simp [add_comm])
  | ⊤ => (verum ⦃0⦄).cast (by simp [add_comm])
  | 0 => verum ⦃0⦄
  | A ＆ B =>
    ((eta A).plusRight (∼B)).rotate.with ((eta B).plusLeft (∼A)).rotate |>.cast (by simp [add_comm])
  | A ⨁ B =>
    (((eta A).rotate.plusRight B).rotate.with ((eta B).rotate.plusLeft A).rotate)
  | ！A => (eta A).dereliction.rotate.ofCourse (by simp) |>.cast (by simp [add_comm])
  | ？A => (eta A).rotate.dereliction.rotate.ofCourse (by simp)
  | ∀¹ A =>
    have d : ⊢ᴸᴸ¹ ⦃A.free⦄ + ⦃(∼A.shift)/[&0]⦄ := (eta A.free).cast (by simp)
    have d : ⊢ᴸᴸ¹ ⦃∃¹ ∼A⦄⁺ + ⦃A.free⦄ := (d.exs &0).cast (by simp [add_comm])
    d.all.cast (by simp [add_comm])
  | ∃¹ A =>
    have d : ⊢ᴸᴸ¹ ⦃∼A.free⦄ + ⦃A.shift/[&0]⦄ := (eta A.free).cast (by simp [add_comm])
    have d : ⊢ᴸᴸ¹ ⦃∃¹ A⦄⁺ + ⦃(∼A).free⦄ := (d.exs &0).cast (by
      simpa using (add_comm ⦃∼A.free⦄ ⦃∃¹ A.shift⦄))
    d.all
  termination_by A => A.complexity

def tensorAxiom (A B : Proposition L) : ⊢ᴸᴸ¹ ⦃∼A, ∼B, A ⨂ B⦄ :=
  have dA : ⊢ᴸᴸ¹ ⦃∼A⦄ + ⦃A⦄ := (ax A).cast
  have dB : ⊢ᴸᴸ¹ ⦃∼B⦄ + ⦃B⦄ := (ax B).cast
  (dA.tensor dB).cast

def expComm (A B : Proposition L) : ⊢ᴸᴸ¹ ⦃！∼A ⨂ ！∼B, ？(A ⨁ B)⦄ :=
  have dA : ⊢ᴸᴸ¹ ⦃？(A ⨁ B)⦄ + ⦃！∼A⦄ :=
    ((ax A).cast.plusRight B).dereliction.rotate.ofCourse (by simp)
  have dB : ⊢ᴸᴸ¹ ⦃？(A ⨁ B)⦄ + ⦃！∼B⦄ :=
    ((ax B).cast.plusLeft A).dereliction.rotate.ofCourse (by simp)
  have d : ⊢ᴸᴸ¹ ⦃！∼A ⨂ ！∼B⦄ + ⦃？(A ⨁ B)⦄ + ⦃？(A ⨁ B)⦄ :=
    (dA.tensor dB).cast
  d.contraction.cast

def ofNegative : (ν : Proposition L) → ν.Negative → ⊢ᴸᴸ¹ ⦃∼？ν, ν⦄
  |    ？A, _ => (ax (？A)).ofCourse (by simp) |>.cast
  |     ⊥, _ =>
    have d : ⊢ᴸᴸ¹ ⦃！1⦄ := ((one (L := L)).cast : ⊢ᴸᴸ¹ ⦃⦄ + ⦃1⦄).ofCourse (by simp) |>.cast
    d.falsum
  |     ⊤, _ => verum ⦃！0⦄
  | ν ⅋ μ, h =>
    have ihν := ofNegative ν (by rcases h; assumption)
    have ihμ := ofNegative μ (by rcases h; assumption)
    have aν : ⊢ᴸᴸ¹ ⦃∼ν⦄ + ⦃ν⦄ := (ax ν).cast
    have aμ : ⊢ᴸᴸ¹ ⦃∼μ⦄ + ⦃μ⦄ := (ax μ).cast
    have dν : ⊢ᴸᴸ¹ ⦃？ν⦄ + ⦃∼ν⦄ := aν.dereliction.cast
    have dμ : ⊢ᴸᴸ¹ ⦃？μ⦄ + ⦃∼μ⦄ := aμ.dereliction.cast
    have d : ⊢ᴸᴸ¹ ⦃？ν, ？μ⦄ + ⦃！(∼ν ⨂ ∼μ)⦄ :=
      (dν.tensor dμ).ofCourse (by simp)
    have d : ⊢ᴸᴸ¹ ⦃！(∼ν ⨂ ∼μ), ？μ, ν⦄ :=
      ((d.cast : ⊢ᴸᴸ¹ ⦃！(∼ν ⨂ ∼μ), ？μ⦄ + ⦃？ν⦄).cut
        (ihν.cast : ⊢ᴸᴸ¹ ⦃ν⦄ + ⦃∼？ν⦄)).cast
    have d : ⊢ᴸᴸ¹ ⦃！(∼ν ⨂ ∼μ), ν, μ⦄ :=
      ((d.cast : ⊢ᴸᴸ¹ ⦃！(∼ν ⨂ ∼μ), ν⦄ + ⦃？μ⦄).cut
        (ihμ.cast : ⊢ᴸᴸ¹ ⦃μ⦄ + ⦃∼？μ⦄)).cast
    d.par.cast (by simp)
  | ν ＆ μ, h =>
    have ihν := ofNegative ν (by rcases h; assumption)
    have ihμ := ofNegative μ (by rcases h; assumption)
    have eν : ⊢ᴸᴸ¹ ⦃？ν⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((ax ν).plusRight (∼μ) |>.cast : ⊢ᴸᴸ¹ ⦃∼ν ⨁ ∼μ⦄ + ⦃ν⦄)
        |>.dereliction.rotate.ofCourse (by simp)
    have dν : ⊢ᴸᴸ¹ ⦃ν⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((eν.cast : ⊢ᴸᴸ¹ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃？ν⦄).cut
        (ihν.cast : ⊢ᴸᴸ¹ ⦃ν⦄ + ⦃∼？ν⦄)).cast
    have eμ : ⊢ᴸᴸ¹ ⦃？μ⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((ax μ).plusLeft (∼ν) |>.cast : ⊢ᴸᴸ¹ ⦃∼ν ⨁ ∼μ⦄ + ⦃μ⦄)
        |>.dereliction.rotate.ofCourse (by simp)
    have dμ : ⊢ᴸᴸ¹ ⦃μ⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((eμ.cast : ⊢ᴸᴸ¹ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃？μ⦄).cut
        (ihμ.cast : ⊢ᴸᴸ¹ ⦃μ⦄ + ⦃∼？μ⦄)).cast
    have dν : ⊢ᴸᴸ¹ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃ν⦄ := dν.cast
    have dμ : ⊢ᴸᴸ¹ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃μ⦄ := dμ.cast
    (dν.with dμ).cast (by simp)
  |   ∀¹ ν, h =>
    have ih := ofNegative ν.free (by rcases h; simpa)
    have a : ⊢ᴸᴸ¹ ⦃∼ν.free⦄ + ⦃ν.free⦄ := (ax ν.free).cast
    have e : ⊢ᴸᴸ¹ ⦃？ν.free⦄ + ⦃∃¹ ∼ν.shift⦄ :=
      (a.dereliction.cast (by simp; abel) :
        ⊢ᴸᴸ¹ ⦃？ν.free⦄ + ⦃(∼ν.shift)/[&0]⦄).exs &0
    have d : ⊢ᴸᴸ¹ ⦃？ν.free⦄ + ⦃！(∃¹ ∼ν.shift)⦄ :=
      e.ofCourse (by simp)
    have d : ⊢ᴸᴸ¹ ⦃ν.free⦄ + ⦃！(∃¹ ∼ν.shift)⦄ :=
      ((d.cast : ⊢ᴸᴸ¹ ⦃！(∃¹ ∼ν.shift)⦄ + ⦃？ν.free⦄).cut
        (ih.cast : ⊢ᴸᴸ¹ ⦃ν.free⦄ + ⦃∼？ν.free⦄)).cast
    ((d.cast (by simp [add_comm]) : ⊢ᴸᴸ¹ ⦃∼？(∀¹ ν)⦄⁺ + ⦃ν.free⦄).all).cast
  termination_by ν => ν.complexity

def removeQuest (h : ν.Negative) (d : ⊢ᴸᴸ¹ Γ + ⦃？ν⦄) : ⊢ᴸᴸ¹ Γ + ⦃ν⦄ :=
  d.cut (ofNegative ν h).cast

def negativeWeakening {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸᴸ¹ Γ) :
    ⊢ᴸᴸ¹ Γ + ⦃ν⦄ := (d.weakening ν).removeQuest h

def negativeContraction {ν : Proposition L} (h : ν.Negative)
    (d : ⊢ᴸᴸ¹ Γ + ⦃ν⦄ + ⦃ν⦄) : ⊢ᴸᴸ¹ Γ + ⦃ν⦄ :=
  have d : ⊢ᴸᴸ¹ Γ + ⦃？ν⦄ + ⦃？ν⦄ := (d.dereliction.cast : ⊢ᴸᴸ¹ Γ + ⦃？ν⦄ + ⦃ν⦄).dereliction
  d.contraction.removeQuest h

/-- Contract a duplicated negative context in the supplied traversal order. -/
def negativeContractMany {Γ Δ : Sequent L} (d : ⊢ᴸᴸ¹ Δ + Γ + Γ)
    (t : Γ.Traversal) (h : Γ.Negative) : ⊢ᴸᴸ¹ Δ + Γ :=
  match t with
  | .zero => d.cast
  | .succ (s := Γ) A t =>
    have h : Sequent.Negative Γ ∧ A.Negative := by simpa using h
    have d : ⊢ᴸᴸ¹ (Δ + ⦃A⦄ + ⦃A⦄) + Γ + Γ := d.cast
    have d : ⊢ᴸᴸ¹ (Δ + Γ) + ⦃A⦄ + ⦃A⦄ := (d.negativeContractMany t h.1).cast
    (d.negativeContraction h.2).cast

def addQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸᴸ¹ Γ + Δ) (t : Δ.Traversal) : ⊢ᴸᴸ¹ Γ + ？Δ :=
  match t with
  | .zero => d.cast (by simp)
  | .succ (s := Δ) A t =>
    have d : ⊢ᴸᴸ¹ (Γ + ⦃A⦄) + Δ := d.cast
    have d := d.addQuestAppendRight t
    (d.cast : ⊢ᴸᴸ¹ Γ + ？Δ + ⦃A⦄).dereliction.cast (by simp [add_assoc])

def addQuestTail (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (t : Γ.Traversal) : ⊢ᴸᴸ¹ ？Γ + ⦃A⦄ :=
  ((d.cast : ⊢ᴸᴸ¹ ⦃A⦄ + Γ).addQuestAppendRight t).cast

def removeQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸᴸ¹ Γ + ？Δ) (t : Δ.Traversal)
    (h : Δ.Negative) : ⊢ᴸᴸ¹ Γ + Δ :=
  match t with
  | .zero => d.cast (by simp)
  | .succ (s := Δ) A t =>
    have h' : Sequent.Negative Δ ∧ A.Negative := by simpa using h
    have d : ⊢ᴸᴸ¹ (Γ + ⦃？A⦄) + ？Δ := d.cast (by simp [add_assoc, add_comm])
    have d := d.removeQuestAppendRight t h'.1
    (d.cast : ⊢ᴸᴸ¹ Γ + Δ + ⦃？A⦄).removeQuest h'.2 |>.cast

def removeQuestTail (d : ⊢ᴸᴸ¹ ？Γ + ⦃A⦄) (t : Γ.Traversal)
    (h : Γ.Negative) : ⊢ᴸᴸ¹ Γ + ⦃A⦄ :=
  ((d.cast : ⊢ᴸᴸ¹ ⦃A⦄ + ？Γ).removeQuestAppendRight t h).cast

def negativeOfCourse (d : ⊢ᴸᴸ¹ Γ + ⦃A⦄) (t : Γ.Traversal)
    (h : Γ.Negative) : ⊢ᴸᴸ¹ Γ + ⦃！A⦄ :=
  (d.addQuestTail t).ofCourse (by simp) |>.removeQuestTail t h
end Derivation

end FFL.FirstOrder.LinearLogic
