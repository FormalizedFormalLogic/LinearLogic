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

scoped prefix:45 "⊢ᴸ " => Derivation

namespace Derivation

variable {Γ Δ : Sequent L}

def cast (d : ⊢ᴸ Γ) (e : Γ = Δ := by abel) : ⊢ᴸ Δ := e ▸ d

def rotate (d : ⊢ᴸ ⦃A⦄ + Γ) : ⊢ᴸ Γ + ⦃A⦄ := d.cast

def invRotate (d : ⊢ᴸ Γ + ⦃A⦄) : ⊢ᴸ ⦃A⦄ + Γ := d.cast

def height {Γ : Sequent L} : ⊢ᴸ Γ → ℕ
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

@[simp] lemma height_cut (d₁ : ⊢ᴸ Γ + ⦃A⦄) (d₂ : ⊢ᴸ Δ + ⦃∼A⦄) :
    (d₁.cut d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_one :
    (one (L := L)).height = 0 := rfl

@[simp] lemma height_falsum (d : ⊢ᴸ Γ) :
    d.falsum.height = d.height + 1 := rfl

@[simp] lemma height_tensor (d₁ : ⊢ᴸ Γ + ⦃A⦄) (d₂ : ⊢ᴸ Δ + ⦃B⦄) :
    (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_par (d : ⊢ᴸ Γ + ⦃A⦄ + ⦃B⦄) :
    d.par.height = d.height + 1 := rfl

@[simp] lemma height_verum (Γ : Sequent L) :
    (verum Γ).height = 0 := rfl

@[simp] lemma height_with (d₁ : ⊢ᴸ Γ + ⦃A⦄) (d₂ : ⊢ᴸ Γ + ⦃B⦄) :
    (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl

@[simp] lemma height_plusLeft (d : ⊢ᴸ Γ + ⦃B⦄) (A : Proposition L) :
    (d.plusLeft A).height = d.height + 1 := rfl

@[simp] lemma height_plusRight (d : ⊢ᴸ Γ + ⦃A⦄) (B : Proposition L) :
    (d.plusRight B).height = d.height + 1 := rfl

@[simp] lemma height_ofCourse (d : ⊢ᴸ Γ + ⦃A⦄) (hΓ : Sequent.IsQuest Γ) :
    (d.ofCourse hΓ).height = d.height + 1 := rfl

@[simp] lemma height_weakening (d : ⊢ᴸ Γ) (A) :
    (d.weakening A).height = d.height + 1 := rfl

@[simp] lemma height_dereliction (d : ⊢ᴸ Γ + ⦃A⦄) :
    d.dereliction.height = d.height + 1 := rfl

@[simp] lemma height_contraction (d : ⊢ᴸ Γ + ⦃？A⦄ + ⦃？A⦄) :
    d.contraction.height = d.height + 1 := rfl

@[simp] lemma height_all {A : Semiproposition L 1} (d : ⊢ᴸ Γ⁺ + ⦃A.free⦄) :
    d.all.height = d.height + 1 := rfl

@[simp] lemma height_exs {A : Semiproposition L 1} {t} (d : ⊢ᴸ Γ + ⦃A/[t]⦄) :
    (d.exs t).height = d.height + 1 := rfl

@[simp] lemma height_cast (d : ⊢ᴸ Γ) (e : Γ = Δ) :
    (d.cast e).height = d.height := by rcases e; rfl

end height

def eta : (A : Proposition L) → ⊢ᴸ ⦃A, ∼A⦄
  | .rel _ _ => ax _
  | .nrel _ _ => ax _
  | 1 => one.falsum
  | ⊥ => one.falsum.cast (by simp [add_comm])
  | A ⨂ B =>
    have d : ⊢ᴸ ⦃A ⨂ B, ∼A, ∼B⦄ := ((eta A).rotate.tensor (eta B).rotate).cast
    d.par
  | A ⅋ B =>
    have d : ⊢ᴸ ⦃∼A ⨂ ∼B, A, B⦄ := ((eta A).tensor (eta B)).cast
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
    have d : ⊢ᴸ ⦃A.free⦄ + ⦃(∼A.shift)/[&0]⦄ := (eta A.free).cast (by simp)
    have d : ⊢ᴸ ⦃∃¹ ∼A⦄⁺ + ⦃A.free⦄ := (d.exs &0).cast (by simp [add_comm])
    d.all.cast (by simp [add_comm])
  | ∃¹ A =>
    have d : ⊢ᴸ ⦃∼A.free⦄ + ⦃A.shift/[&0]⦄ := (eta A.free).cast (by simp [add_comm])
    have d : ⊢ᴸ ⦃∃¹ A⦄⁺ + ⦃(∼A).free⦄ := (d.exs &0).cast (by
      simpa using (add_comm ⦃∼A.free⦄ ⦃∃¹ A.shift⦄))
    d.all
  termination_by A => A.complexity

def tensorAxiom (A B : Proposition L) : ⊢ᴸ ⦃∼A, ∼B, A ⨂ B⦄ :=
  have dA : ⊢ᴸ ⦃∼A⦄ + ⦃A⦄ := (ax A).cast
  have dB : ⊢ᴸ ⦃∼B⦄ + ⦃B⦄ := (ax B).cast
  (dA.tensor dB).cast

def expComm (A B : Proposition L) : ⊢ᴸ ⦃！∼A ⨂ ！∼B, ？(A ⨁ B)⦄ :=
  have dA : ⊢ᴸ ⦃？(A ⨁ B)⦄ + ⦃！∼A⦄ :=
    ((ax A).cast.plusRight B).dereliction.rotate.ofCourse (by simp)
  have dB : ⊢ᴸ ⦃？(A ⨁ B)⦄ + ⦃！∼B⦄ :=
    ((ax B).cast.plusLeft A).dereliction.rotate.ofCourse (by simp)
  have d : ⊢ᴸ ⦃！∼A ⨂ ！∼B⦄ + ⦃？(A ⨁ B)⦄ + ⦃？(A ⨁ B)⦄ :=
    (dA.tensor dB).cast
  d.contraction.cast

def ofNegative : (ν : Proposition L) → ν.Negative → ⊢ᴸ ⦃∼？ν, ν⦄
  |    ？A, _ => (ax (？A)).ofCourse (by simp) |>.cast
  |     ⊥, _ =>
    have d : ⊢ᴸ ⦃！1⦄ := ((one (L := L)).cast : ⊢ᴸ ⦃⦄ + ⦃1⦄).ofCourse (by simp) |>.cast
    d.falsum
  |     ⊤, _ => verum ⦃！0⦄
  | ν ⅋ μ, h =>
    have ihν := ofNegative ν (by rcases h; assumption)
    have ihμ := ofNegative μ (by rcases h; assumption)
    have aν : ⊢ᴸ ⦃∼ν⦄ + ⦃ν⦄ := (ax ν).cast
    have aμ : ⊢ᴸ ⦃∼μ⦄ + ⦃μ⦄ := (ax μ).cast
    have dν : ⊢ᴸ ⦃？ν⦄ + ⦃∼ν⦄ := aν.dereliction.cast
    have dμ : ⊢ᴸ ⦃？μ⦄ + ⦃∼μ⦄ := aμ.dereliction.cast
    have d : ⊢ᴸ ⦃？ν, ？μ⦄ + ⦃！(∼ν ⨂ ∼μ)⦄ :=
      (dν.tensor dμ).ofCourse (by simp)
    have d : ⊢ᴸ ⦃！(∼ν ⨂ ∼μ), ？μ, ν⦄ :=
      ((d.cast : ⊢ᴸ ⦃！(∼ν ⨂ ∼μ), ？μ⦄ + ⦃？ν⦄).cut
        (ihν.cast : ⊢ᴸ ⦃ν⦄ + ⦃∼？ν⦄)).cast
    have d : ⊢ᴸ ⦃！(∼ν ⨂ ∼μ), ν, μ⦄ :=
      ((d.cast : ⊢ᴸ ⦃！(∼ν ⨂ ∼μ), ν⦄ + ⦃？μ⦄).cut
        (ihμ.cast : ⊢ᴸ ⦃μ⦄ + ⦃∼？μ⦄)).cast
    d.par.cast (by simp)
  | ν ＆ μ, h =>
    have ihν := ofNegative ν (by rcases h; assumption)
    have ihμ := ofNegative μ (by rcases h; assumption)
    have eν : ⊢ᴸ ⦃？ν⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((ax ν).plusRight (∼μ) |>.cast : ⊢ᴸ ⦃∼ν ⨁ ∼μ⦄ + ⦃ν⦄)
        |>.dereliction.rotate.ofCourse (by simp)
    have dν : ⊢ᴸ ⦃ν⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((eν.cast : ⊢ᴸ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃？ν⦄).cut
        (ihν.cast : ⊢ᴸ ⦃ν⦄ + ⦃∼？ν⦄)).cast
    have eμ : ⊢ᴸ ⦃？μ⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((ax μ).plusLeft (∼ν) |>.cast : ⊢ᴸ ⦃∼ν ⨁ ∼μ⦄ + ⦃μ⦄)
        |>.dereliction.rotate.ofCourse (by simp)
    have dμ : ⊢ᴸ ⦃μ⦄ + ⦃！(∼ν ⨁ ∼μ)⦄ :=
      ((eμ.cast : ⊢ᴸ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃？μ⦄).cut
        (ihμ.cast : ⊢ᴸ ⦃μ⦄ + ⦃∼？μ⦄)).cast
    have dν : ⊢ᴸ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃ν⦄ := dν.cast
    have dμ : ⊢ᴸ ⦃！(∼ν ⨁ ∼μ)⦄ + ⦃μ⦄ := dμ.cast
    (dν.with dμ).cast (by simp)
  |   ∀¹ ν, h =>
    have ih := ofNegative ν.free (by rcases h; simpa)
    have a : ⊢ᴸ ⦃∼ν.free⦄ + ⦃ν.free⦄ := (ax ν.free).cast
    have e : ⊢ᴸ ⦃？ν.free⦄ + ⦃∃¹ ∼ν.shift⦄ :=
      (a.dereliction.cast (by simp; abel) :
        ⊢ᴸ ⦃？ν.free⦄ + ⦃(∼ν.shift)/[&0]⦄).exs &0
    have d : ⊢ᴸ ⦃？ν.free⦄ + ⦃！(∃¹ ∼ν.shift)⦄ :=
      e.ofCourse (by simp)
    have d : ⊢ᴸ ⦃ν.free⦄ + ⦃！(∃¹ ∼ν.shift)⦄ :=
      ((d.cast : ⊢ᴸ ⦃！(∃¹ ∼ν.shift)⦄ + ⦃？ν.free⦄).cut
        (ih.cast : ⊢ᴸ ⦃ν.free⦄ + ⦃∼？ν.free⦄)).cast
    ((d.cast (by simp [add_comm]) : ⊢ᴸ ⦃∼？(∀¹ ν)⦄⁺ + ⦃ν.free⦄).all).cast
  termination_by ν => ν.complexity

def removeQuest (h : ν.Negative) (d : ⊢ᴸ Γ + ⦃？ν⦄) : ⊢ᴸ Γ + ⦃ν⦄ :=
  d.cut (ofNegative ν h).cast

def negativeWeakening {ν : Proposition L} (h : ν.Negative) (d : ⊢ᴸ Γ) :
    ⊢ᴸ Γ + ⦃ν⦄ := (d.weakening ν).removeQuest h

def negativeContraction {ν : Proposition L} (h : ν.Negative)
    (d : ⊢ᴸ Γ + ⦃ν⦄ + ⦃ν⦄) : ⊢ᴸ Γ + ⦃ν⦄ :=
  have d : ⊢ᴸ Γ + ⦃？ν⦄ + ⦃？ν⦄ := (d.dereliction.cast : ⊢ᴸ Γ + ⦃？ν⦄ + ⦃ν⦄).dereliction
  d.contraction.removeQuest h

/-- Contract a duplicated negative context in the supplied traversal order. -/
def negativeContractMany {Γ Δ : Sequent L} (d : ⊢ᴸ Δ + Γ + Γ)
    (t : Γ.Traversal) (h : Γ.Negative) : ⊢ᴸ Δ + Γ :=
  match t with
  | .zero => d.cast
  | .succ (s := Γ) A t =>
    have h : Sequent.Negative Γ ∧ A.Negative := by simpa using h
    have d : ⊢ᴸ (Δ + ⦃A⦄ + ⦃A⦄) + Γ + Γ := d.cast
    have d : ⊢ᴸ (Δ + Γ) + ⦃A⦄ + ⦃A⦄ := (d.negativeContractMany t h.1).cast
    (d.negativeContraction h.2).cast

def addQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ + Δ) (t : Δ.Traversal) : ⊢ᴸ Γ + ？Δ :=
  match t with
  | .zero => d.cast (by simp)
  | .succ (s := Δ) A t =>
    have d : ⊢ᴸ (Γ + ⦃A⦄) + Δ := d.cast
    have d := d.addQuestAppendRight t
    (d.cast : ⊢ᴸ Γ + ？Δ + ⦃A⦄).dereliction.cast (by simp [add_assoc])

def addQuestTail (d : ⊢ᴸ Γ + ⦃A⦄) (t : Γ.Traversal) : ⊢ᴸ ？Γ + ⦃A⦄ :=
  ((d.cast : ⊢ᴸ ⦃A⦄ + Γ).addQuestAppendRight t).cast

def removeQuestAppendRight {Γ Δ : Sequent L} (d : ⊢ᴸ Γ + ？Δ) (t : Δ.Traversal)
    (h : Δ.Negative) : ⊢ᴸ Γ + Δ :=
  match t with
  | .zero => d.cast (by simp)
  | .succ (s := Δ) A t =>
    have h' : Sequent.Negative Δ ∧ A.Negative := by simpa using h
    have d : ⊢ᴸ (Γ + ⦃？A⦄) + ？Δ := d.cast (by simp [add_assoc, add_comm])
    have d := d.removeQuestAppendRight t h'.1
    (d.cast : ⊢ᴸ Γ + Δ + ⦃？A⦄).removeQuest h'.2 |>.cast

def removeQuestTail (d : ⊢ᴸ ？Γ + ⦃A⦄) (t : Γ.Traversal)
    (h : Γ.Negative) : ⊢ᴸ Γ + ⦃A⦄ :=
  ((d.cast : ⊢ᴸ ⦃A⦄ + ？Γ).removeQuestAppendRight t h).cast

def negativeOfCourse (d : ⊢ᴸ Γ + ⦃A⦄) (t : Γ.Traversal)
    (h : Γ.Negative) : ⊢ᴸ Γ + ⦃！A⦄ :=
  (d.addQuestTail t).ofCourse (by simp) |>.removeQuestTail t h
end Derivation

end FFL.FirstOrder.LinearLogic
