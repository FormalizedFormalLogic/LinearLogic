module

public import Foundation.FirstOrder.Basic
public import LinearLogic.LogicSymbol

/-!
# First-order linear logic
-/

@[expose] public section

namespace LO.FirstOrder.LinearLogic

open FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  /-- Literals -/
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  /-- Multiplicative connectives -/
  |    one : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  | tensor : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    par : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Additive connectives -/
  |  verum : Semiformula L ξ n
  |   zero : Semiformula L ξ n
  |   with : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |   plus : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Exponentials -/
  |   bang : Semiformula L ξ n → Semiformula L ξ n
  |  quest : Semiformula L ξ n → Semiformula L ξ n
  /-- Quantifiers -/
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |    exs : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

abbrev Sentence (L : Language) := Semiformula L Empty 0

abbrev Semiproposition (L : Language) (n : ℕ) := Semiformula L ℕ n

abbrev Proposition (L : Language) := Formula L ℕ

namespace Semiformula

variable {L : Language} {ξ : Type*}

instance : MultiplicativeConnective (Semiformula L ξ n) where
  tensor := tensor
  par := par
  tensor_injective _ _ _ _ := by simp [tensor.injEq]
  par_injective _ _ _ _ := by simp [par.injEq]

instance : MultiplicativeNeutral (Semiformula L ξ n) where
  one := one
  bot := falsum

instance : AdditiveConnective (Semiformula L ξ n) where
  with' := .with
  plus := plus
  with_injective _ _ _ _ := by simp [with.injEq]
  plus_injective _ _ _ _ := by simp [plus.injEq]

instance : AdditiveNeutral (Semiformula L ξ n) where
  top := verum
  zero := zero

instance : ExponentialConnective (Semiformula L ξ n) where
  bang := bang
  quest := quest
  bang_injective _ _ := by simp [bang.injEq]
  quest_injective _ _ := by simp [quest.injEq]

instance : Quantifier (Semiformula L ξ) where
  all := all
  exs := exs

@[simp] lemma all_inj {A₁ A₂ : Semiformula L ξ (n + 1)} :
    ∀¹ A₁ = ∀¹ A₂ ↔ A₁ = A₂ := iff_of_eq (by apply all.injEq)

@[simp] lemma exs_inj {A₁ A₂ : Semiformula L ξ (n + 1)} :
    ∃¹ A₁ = ∃¹ A₂ ↔ A₁ = A₂ := iff_of_eq (by apply exs.injEq)

def neg : Semiformula L ξ n → Semiformula L ξ n
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |        1 => ⊥
  |        ⊥ => 1
  |    A ⨂ B => A.neg ⅋ B.neg
  |    A ⅋ B => A.neg ⨂ B.neg
  |        ⊤ => 0
  |        0 => ⊤
  |    A ＆ B => A.neg ⨁ B.neg
  |    A ⨁ B => A.neg ＆ B.neg
  |       ！A => ？A.neg
  |       ？A => ！A.neg
  |     ∀¹ A => ∃¹ A.neg
  |     ∃¹ A => ∀¹ A.neg

instance : Tilde (Semiformula L ξ n) := ⟨neg⟩

instance : MultiplicativeConnective.DeMorgan (Semiformula L ξ n) where
  tensor _ _ := rfl
  par _ _ := rfl

instance : MultiplicativeNeutral.DeMorgan (Semiformula L ξ n) where
  one := rfl
  bot := rfl

instance : AdditiveConnective.DeMorgan (Semiformula L ξ n) where
  with_ _ _ := rfl
  plus _ _ := rfl

instance : AdditiveNeutral.DeMorgan (Semiformula L ξ n) where
  top := rfl
  zero := rfl

instance : ExponentialConnective.DeMorgan (Semiformula L ξ n) where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼rel R v = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼nrel R v = rel R v := rfl

@[simp] lemma neg_all (A : Semiformula L ξ (n + 1)) :
  ∼(∀¹ A) = ∃¹ ∼A := rfl

@[simp] lemma neg_exs (A : Semiformula L ξ (n + 1)) :
  ∼(∃¹ A) = ∀¹ ∼A := rfl

lemma neg_neg {n} (A : Semiformula L ξ n) : ∼∼A = A := by
  match A with
  |  rel R v => rfl
  | nrel R v => rfl
  |        1 => rfl
  |        ⊥ => rfl
  |    A ⨂ B => simp [neg_neg A, neg_neg B]
  |    A ⅋ B => simp [neg_neg A, neg_neg B]
  |        ⊤ => rfl
  |        0 => rfl
  |    A ＆ B => simp [neg_neg A, neg_neg B]
  |    A ⨁ B => simp [neg_neg A, neg_neg B]
  |       ！A => simp [neg_neg A]
  |       ？A => simp [neg_neg A]
  |     ∀¹ A => simp [neg_neg A]
  |     ∃¹ A => simp [neg_neg A]

instance : TildeInvolutive (Semiformula L ξ n) := ⟨neg_neg⟩

/-- Usual logical connectives are defined to align with `⊤` and `⊥` -/
instance : LogicalConnective (Semiformula L ξ n) where
  wedge := .with
  vee := .par
  arrow A B := A ⊸ B

instance : LogicalNeutral (Semiformula L ξ n) where

lemma wedge_def (A B : Semiformula L ξ n) : A ⋏ B = A ＆ B := rfl

lemma vee_def (A B : Semiformula L ξ n) :  A ⋎ B = A ⅋ B := rfl

lemma imply_def (A B : Semiformula L ξ n) : A 🡒 B = A ⊸ B := rfl

lemma imply_def' (A B : Semiformula L ξ n) : A 🡒 B = ∼A ⅋ B := rfl

@[simp] lemma neg_inj {A B : Semiformula L ξ n} : ∼A = ∼B ↔ A = B := by
  constructor
  · intro h; rw [←neg_neg A, ←neg_neg B, h]
  · intro h; rw [h]

instance : LCWQ (Semiformula L ξ) where
  connectives _ := inferInstance
  neutrals _ := inferInstance

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hOne : ∀ {n : ℕ}, C n 1)
    (hFalsum : ∀ {n : ℕ}, C n ⊥)
    (hTensor : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n (A ⨂ B))
    (hPar : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n (A ⅋ B))
    (hVerum : ∀ {n : ℕ}, C n ⊤)
    (hZero : ∀ {n : ℕ}, C n 0)
    (hWith : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n (A ＆ B))
    (hPlus : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n (A ⨁ B))
    (hBang : ∀ {n : ℕ} (A : Semiformula L ξ n), C n (！A))
    (hQuest : ∀ {n : ℕ} (A : Semiformula L ξ n), C n (？A))
    (hAll : ∀ {n : ℕ} (A : Semiformula L ξ (n + 1)), C n (∀¹ A))
    (hExs : ∀ {n : ℕ} (A : Semiformula L ξ (n + 1)), C n (∃¹ A)) {n} :
    (A : Semiformula L ξ n) → C n A
  | rel r v => hRel r v
  | nrel r v => hNrel r v
  | 1 => hOne
  | ⊥ => hFalsum
  | A ⨂ B => hTensor A B
  | A ⅋ B => hPar A B
  | ⊤ => hVerum
  | 0 => hZero
  | A ＆ B => hWith A B
  | A ⨁ B => hPlus A B
  | ！A => hBang A
  | ？A => hQuest A
  | ∀¹ A => hAll A
  | ∃¹ A => hExs A

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hRel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hNrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hOne : ∀ {n : ℕ}, C n 1)
  (hFalsum : ∀ {n : ℕ}, C n ⊥)
  (hTensor : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n A → C n B → C n (A ⨂ B))
  (hPar : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n A → C n B → C n (A ⅋ B))
  (hVerum : ∀ {n : ℕ}, C n ⊤)
  (hZero : ∀ {n : ℕ}, C n 0)
  (hWith : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n A → C n B → C n (A ＆ B))
  (hPlus : ∀ {n : ℕ} (A B : Semiformula L ξ n), C n A → C n B → C n (A ⨁ B))
  (hBang : ∀ {n : ℕ} (A : Semiformula L ξ n), C n A → C n (！A))
  (hQuest : ∀ {n : ℕ} (A : Semiformula L ξ n), C n A → C n (？A))
  (hAll : ∀ {n : ℕ} (A : Semiformula L ξ (n + 1)), C (n + 1) A → C n (∀¹ A))
  (hExs : ∀ {n : ℕ} (A : Semiformula L ξ (n + 1)), C (n + 1) A → C n (∃¹ A)) {n} :
    (A : Semiformula L ξ n) → C n A
  | rel r v => hRel r v
  | nrel r v => hNrel r v
  | 1 => hOne
  | ⊥ => hFalsum
  | A ⨂ B => hTensor A B (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs B)
  | A ⅋ B => hPar A B (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs B)
  | ⊤ => hVerum
  | 0 => hZero
  | A ＆ B => hWith A B (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs B)
  | A ⨁ B => hPlus A B (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
      (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs B)
  | ！A => hBang A (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
  | ？A => hQuest A (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
  | ∀¹ A => hAll A (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)
  | ∃¹ A => hExs A (rec' hRel hNrel hOne hFalsum hTensor hPar hVerum hZero hWith hPlus hBang hQuest hAll hExs A)

def complexity : Semiformula L ξ n → ℕ
  |  rel _ _ => 0
  | nrel _ _ => 0
  |        1 => 0
  |        ⊥ => 0
  |    A ⨂ B => max (complexity A) (complexity B) + 1
  |    A ⅋ B => max (complexity A) (complexity B) + 1
  |        ⊤ => 0
  |        0 => 0
  |    A ＆ B => max (complexity A) (complexity B) + 1
  |    A ⨁ B => max (complexity A) (complexity B) + 1
  |       ！A => complexity A + 1
  |       ？A => complexity A + 1
  |     ∀¹ A => complexity A + 1
  |     ∃¹ A => complexity A + 1

@[simp] lemma complexity_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (rel R v) = 0 := rfl

@[simp] lemma complexity_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    complexity (nrel R v) = 0 := rfl

@[simp] lemma complexity_one : (1 : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_one' : (.one : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_falsum : (⊥ : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_falsum' : (.falsum : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_tensor (A B : Semiformula L ξ n) :
    (A ⨂ B).complexity = max A.complexity B.complexity + 1 := rfl
@[simp] lemma complexity_tensor' (A B : Semiformula L ξ n) :
    (A.tensor B).complexity = max A.complexity B.complexity + 1 := rfl

@[simp] lemma complexity_par (A B : Semiformula L ξ n) :
    (A ⅋ B).complexity = max A.complexity B.complexity + 1 := rfl
@[simp] lemma complexity_par' (A B : Semiformula L ξ n) :
    (A.par B).complexity = max A.complexity B.complexity + 1 := rfl

@[simp] lemma complexity_verum : (⊤ : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_verum' : (.verum : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_zero : (0 : Semiformula L ξ n).complexity = 0 := rfl
@[simp] lemma complexity_zero' : (.zero : Semiformula L ξ n).complexity = 0 := rfl

@[simp] lemma complexity_with (A B : Semiformula L ξ n) :
    (A ＆ B).complexity = max A.complexity B.complexity + 1 := rfl
@[simp] lemma complexity_with' (A B : Semiformula L ξ n) :
    (A.with B).complexity = max A.complexity B.complexity + 1 := rfl

@[simp] lemma complexity_plus (A B : Semiformula L ξ n) :
    (A ⨁ B).complexity = max A.complexity B.complexity + 1 := rfl
@[simp] lemma complexity_plus' (A B : Semiformula L ξ n) :
    (A.plus B).complexity = max A.complexity B.complexity + 1 := rfl

@[simp] lemma complexity_bang (A : Semiformula L ξ n) :
    (！A).complexity = A.complexity + 1 := rfl
@[simp] lemma complexity_bang' (A : Semiformula L ξ n) :
    (A.bang).complexity = A.complexity + 1 := rfl

@[simp] lemma complexity_quest (A : Semiformula L ξ n) :
    (？A).complexity = A.complexity + 1 := rfl
@[simp] lemma complexity_quest' (A : Semiformula L ξ n) :
    (A.quest).complexity = A.complexity + 1 := rfl

@[simp] lemma complexity_all (A : Semiformula L ξ (n + 1)) :
    (∀¹ A).complexity = A.complexity + 1 := rfl
@[simp] lemma complexity_all' (A : Semiformula L ξ (n + 1)) :
    A.all.complexity = A.complexity + 1 := rfl

@[simp] lemma complexity_exs (A : Semiformula L ξ (n + 1)) :
    (∃¹ A).complexity = A.complexity + 1 := rfl
@[simp] lemma complexity_exs' (A : Semiformula L ξ (n + 1)) :
    A.exs.complexity = A.complexity + 1 := rfl

@[simp] lemma complexity_neg (A : Semiformula L ξ n) :
    (∼A).complexity = A.complexity := by
  induction A using rec' <;> simp [*]

instance [L.DecidableEq] [DecidableEq ξ] : DecidableEq (Semiformula L ξ n) :=
  let rec dc {n} : (A B : Semiformula L ξ n) → Decidable (A = B)
    | .rel (arity := ar₁) R₁ v₁, A₂ =>
      match A₂ with
      | .rel (arity := ar₂) R₂ v₂ => by
        by_cases har : ar₁ = ar₂
        · rcases har
          exact match decEq R₁ R₂ with
            |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v₁ i) (v₂ i)
            | isFalse h => isFalse (by simp_all)
        · exact isFalse (by simp_all)
      | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | .nrel (arity := ar₁) R₁ v₁, A₂ =>
      match A₂ with
      | .nrel (arity := ar₂) R₂ v₂ => by
        by_cases har : ar₁ = ar₂
        · rcases har
          exact match decEq R₁ R₂ with
            |  isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ decEq (v₁ i) (v₂ i)
            | isFalse h => isFalse (by simp_all)
        · exact isFalse (by simp_all)
      | .rel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | 1, A₂ =>
      match A₂ with
      | 1 => isTrue rfl
      | .rel _ _ | .nrel _ _ | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | ⊥, A₂ =>
      match A₂ with
      | ⊥ => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | A₁ ⨂ B₁, A₂ =>
      match A₂ with
      | A₂ ⨂ B₂ =>
        match dc A₁ A₂, dc B₁ B₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | A₁ ⅋ B₁, A₂ =>
      match A₂ with
      | A₂ ⅋ B₂ =>
        match dc A₁ A₂, dc B₁ B₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | ⊤, A₂ =>
      match A₂ with
      | ⊤ => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | 0, A₂ =>
      match A₂ with
      | 0 => isTrue rfl
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | A₁ ＆ B₁, A₂ =>
      match A₂ with
      | A₂ ＆ B₂ =>
        match dc A₁ A₂, dc B₁ B₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ⨁ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | A₁ ⨁ B₁, A₂ =>
      match A₂ with
      | A₂ ⨁ B₂ =>
        match dc A₁ A₂, dc B₁ B₂ with
        |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
        | isFalse h₁,          _ => isFalse (by simp_all)
        |          _, isFalse h₂ => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | ！_ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | ！A₁, A₂ =>
      match A₂ with
      | ！A₂ =>
        match dc A₁ A₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ？_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | ？A₁, A₂ =>
      match A₂ with
      | ？A₂ =>
        match dc A₁ A₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ∀¹ _ | ∃¹ _ =>
        isFalse (by simp_all)
    | ∀¹ A₁, A₂ =>
      match A₂ with
      | ∀¹ A₂ =>
        match dc A₁ A₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∃¹ _ =>
        isFalse (by simp_all)
    | ∃¹ A₁, A₂ =>
      match A₂ with
      | ∃¹ A₂ =>
        match dc A₁ A₂ with
        |  isTrue h => isTrue (by simp_all)
        | isFalse h => isFalse (by simp_all)
      | .rel _ _ | .nrel _ _ | 1 | ⊥ | _ ⨂ _ | _ ⅋ _ | ⊤ | 0 | _ ＆ _ | _ ⨁ _ | ！_ | ？_ | ∀¹ _ =>
        isFalse (by simp_all)
  dc

inductive IsQuest : Semiformula L ξ n → Prop
  | intro : IsQuest (？A)

@[simp] lemma IsQuest.not_one : ¬IsQuest (1 : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_falsum : ¬IsQuest (⊥ : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_tensor (A B : Semiformula L ξ n) : ¬IsQuest (A ⨂ B) := by intro h; cases h
@[simp] lemma IsQuest.not_par (A B : Semiformula L ξ n) : ¬IsQuest (A ⅋ B) := by intro h; cases h
@[simp] lemma IsQuest.not_verum : ¬IsQuest (⊤ : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_zero : ¬IsQuest (0 : Semiformula L ξ n) := by intro h; cases h
@[simp] lemma IsQuest.not_with (A B : Semiformula L ξ n) : ¬IsQuest (A ＆ B) := by intro h; cases h
@[simp] lemma IsQuest.not_plus (A B : Semiformula L ξ n) : ¬IsQuest (A ⨁ B) := by intro h; cases h
@[simp] lemma IsQuest.not_bang (A : Semiformula L ξ n) : ¬IsQuest (！A) := by intro h; cases h
@[simp] lemma IsQuest.quest (A : Semiformula L ξ n) : IsQuest (？A) := .intro
@[simp] lemma IsQuest.not_all (A : Semiformula L ξ (n + 1)) : ¬IsQuest (∀¹ A) := by intro h; cases h
@[simp] lemma IsQuest.not_exs (A : Semiformula L ξ (n + 1)) : ¬IsQuest (∃¹ A) := by intro h; cases h

/-! ### Polarity -/

inductive Negative : Semiformula L ξ n → Prop
  | quest (A : Semiformula L ξ n) : Negative (？A)
  | verum : Negative (⊤ : Semiformula L ξ n)
  | falsum : Negative (⊥ : Semiformula L ξ n)
  | par : Negative A → Negative B → Negative (A ⅋ B)
  | with : Negative A → Negative B → Negative (A ＆ B)
  | all : Negative A → Negative (∀¹ A)

namespace Negative

attribute [simp] quest verum falsum

@[simp] lemma par_iff {A B : Semiformula L ξ n} :
    Negative (A ⅋ B) ↔ Negative A ∧ Negative B := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact par h₁ h₂

@[simp] lemma with_iff {A B : Semiformula L ξ n} :
    Negative (A ＆ B) ↔ Negative A ∧ Negative B := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact .with h₁ h₂

@[simp] lemma all_iff {A : Semiformula L ξ (n + 1)} :
    Negative (∀¹ A) ↔ Negative A := by
  constructor
  · rintro ⟨h⟩; assumption
  · rintro h; exact all h

@[simp] lemma not_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Negative (rel R v) := by rintro ⟨⟩

@[simp] lemma not_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Negative (nrel R v) := by rintro ⟨⟩

@[simp] lemma not_one : ¬Negative (1 : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_zero : ¬Negative (0 : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_tensor (A B : Semiformula L ξ n) : ¬Negative (A ⨂ B) := by rintro ⟨⟩

@[simp] lemma not_plus (A B : Semiformula L ξ n) : ¬Negative (A ⨁ B) := by rintro ⟨⟩

@[simp] lemma not_bang (A : Semiformula L ξ n) : ¬Negative (！A) := by rintro ⟨⟩

@[simp] lemma not_exs (A : Semiformula L ξ (n + 1)) : ¬Negative (∃¹ A) := by rintro ⟨⟩

instance (A : Semiformula L ξ n) : Decidable A.Negative :=
  let rec dc {n} : (A : Semiformula L ξ n) → Decidable A.Negative
  |       ？A => isTrue (by simp)
  |        ⊤ => isTrue (by simp)
  |        ⊥ => isTrue (by simp)
  |    A ⅋ B =>
    match dc A, dc B with
    |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
    |  isTrue h₁, isFalse h₂ => isFalse (by simp_all)
    | isFalse h₁,  isTrue h₂ => isFalse (by simp_all)
    | isFalse h₁, isFalse h₂ => isFalse (by simp_all)
  | A ＆ B =>
    match dc A, dc B with
    |  isTrue h₁,  isTrue h₂ => isTrue (by simp_all)
    |  isTrue h₁, isFalse h₂ => isFalse (by simp_all)
    | isFalse h₁,  isTrue h₂ => isFalse (by simp_all)
    | isFalse h₁, isFalse h₂ => isFalse (by simp_all)
  | ∀¹ A =>
    match dc A with
    | isTrue h => isTrue (by simp_all)
    | isFalse h => isFalse (by simp_all)
  | rel _ _ | nrel _ _ | 1 | 0 | A ⨂ B | A ⨁ B | ！A | ∃¹ A => isFalse (by simp)
  dc A

end Negative

inductive Positive : Semiformula L ξ n → Prop
  | ofCourse (A : Semiformula L ξ n) : Positive (！A)
  | zero : Positive (0 : Semiformula L ξ n)
  | one : Positive (1 : Semiformula L ξ n)
  | tensor : Positive A → Positive B → Positive (A ⨂ B)
  | plus : Positive A → Positive B → Positive (A ⨁ B)
  | exs : Positive A → Positive (∃¹ A)

namespace Positive

attribute [simp] ofCourse zero one

@[simp] lemma tensor_iff {A B : Semiformula L ξ n} :
    Positive (A ⨂ B) ↔ Positive A ∧ Positive B := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact tensor h₁ h₂

@[simp] lemma plus_iff {A B : Semiformula L ξ n} :
    Positive (A ⨁ B) ↔ Positive A ∧ Positive B := by
  constructor
  · rintro ⟨h₁, h₂⟩; grind
  · rintro ⟨h₁, h₂⟩; exact plus h₁ h₂

@[simp] lemma exs_iff {A : Semiformula L ξ (n + 1)} :
    Positive (∃¹ A) ↔ Positive A := by
  constructor
  · rintro ⟨h⟩; assumption
  · rintro h; exact exs h

@[simp] lemma not_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Positive (rel R v) := by rintro ⟨⟩

@[simp] lemma not_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) : ¬Positive (nrel R v) := by rintro ⟨⟩

@[simp] lemma not_verum : ¬Positive (⊤ : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_falsum : ¬Positive (⊥ : Semiformula L ξ n) := by rintro ⟨⟩

@[simp] lemma not_par (A B : Semiformula L ξ n) : ¬Positive (A ⅋ B) := by rintro ⟨⟩

@[simp] lemma not_with (A B : Semiformula L ξ n) : ¬Positive (A ＆ B) := by rintro ⟨⟩

@[simp] lemma not_quest (A : Semiformula L ξ n) : ¬Positive (？A) := by rintro ⟨⟩

@[simp] lemma not_all (A : Semiformula L ξ (n + 1)) : ¬Positive (∀¹ A) := by rintro ⟨⟩

@[simp] lemma neg_positive_iff_negative (A : Semiformula L ξ n) : Positive (∼A) ↔ Negative A := by
  induction A using rec' <;> simp [*]

@[simp] lemma neg_negative_iff_positive (A : Semiformula L ξ n) : Negative (∼A) ↔ Positive A := by
  induction A using rec' <;> simp [*]

@[simp, grind .] lemma positive_negative_disjoint (A : Semiformula L ξ n) : ¬Positive A ∨ ¬Negative A := by
  induction A using rec' <;> simp [*]

end Positive

end Semiformula

end LO.FirstOrder.LinearLogic

end
