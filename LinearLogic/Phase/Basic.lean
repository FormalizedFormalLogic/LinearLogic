module

public import Foundation.Vorspiel.Nat.Matrix
public import Foundation.Vorspiel.NotationClass
public import LinearLogic.Vorspiel.NotationClass

/-!
# Phase semantics
-/

@[expose] public section

namespace LO

class PhaseSpace (M : Type*) extends CommMonoid M where
  pole : Set M

namespace PhaseSpace

variable {M : Type*} [PhaseSpace M]

scoped notation "⫫" => PhaseSpace.pole

def poler (X : Set M) : Set M := { m | ∀ x ∈ X, m * x ∈ ⫫ }

scoped postfix:max "ᗮ" => poler

def IsFact (X : Set M) : Prop := Xᗮᗮ = X

lemma mem_poler_iff {X : Set M} {m : M} : m ∈ Xᗮ ↔ ∀ x ∈ X, m * x ∈ ⫫ := by
  rfl

@[grind =] lemma mul_mem_pole_comm {x y : M} : x * y ∈ ⫫ ↔ y * x ∈ ⫫ := by
  rw [mul_comm]

@[simp, grind .] lemma subset_bipoler (X : Set M) : X ⊆ Xᗮᗮ := by
  intro x hx y hy
  simpa [mul_comm] using hy x hx

lemma isFact_iff_subset {X : Set M} : IsFact X ↔ Xᗮᗮ ⊆ X := by
  unfold IsFact
  have : X ⊆ Xᗮᗮ := subset_bipoler X
  grind

alias ⟨IsFact.subset, _⟩ := isFact_iff_subset

@[simp] lemma one_mem_poler_pole : (1 : M) ∈ (⫫ : Set M)ᗮ := by
  simp [mem_poler_iff]

@[simp] lemma poler_one_eq_pole : {1}ᗮ = (⫫ : Set M) := by
  ext m; simp [mem_poler_iff]

@[simp] lemma poler_poler_pole : (⫫ : Set M)ᗮᗮ = ⫫ := by
  have : (⫫ : Set M)ᗮᗮ ⊆ ⫫ := by
    intro m hm
    simpa using hm 1 (by simp)
  exact Set.Subset.antisymm this (subset_bipoler ⫫)

@[simp] lemma tripoler_eq (X : Set M) : Xᗮᗮᗮ = Xᗮ := by
  ext m; simp [mem_poler_iff]; grind

@[simp] lemma IsFact.pole : IsFact (⫫ : Set M) := by
  unfold IsFact; simp

@[simp] lemma IsFact.of_poler (X : Set M) : IsFact Xᗮ := by
  unfold IsFact; simp

structure IsPositive (m : M) : Prop where
  idempotent : m * m = m
  exclusive : m ∈ (⫫ : Set M)ᗮ

@[simp] lemma IsPositive.one : IsPositive (1 : M) := ⟨by simp, by simp⟩

variable (M)

structure Fact where
  carrier : Set M
  isFact' : IsFact carrier

variable {M}

namespace Fact

instance : SetLike (Fact M) M where
  coe := Fact.carrier
  coe_injective a b h := by
    cases a; cases b; congr

@[simp] lemma isFact (A : Fact M) : IsFact (A : Set M) := A.isFact'

@[simp] lemma bipoler_coe_eq (A : Fact M) : (A : Set M)ᗮᗮ = A := A.isFact'

@[simp] lemma mem_mk_iff {X : Set M} (h : IsFact X) {m : M} : m ∈ Fact.mk X h ↔ m ∈ X := by
  rfl

lemma ext_set {A B : Fact M} (h : (A : Set M) = (B : Set M)) : A = B := by
  cases A; cases B; congr

@[ext] lemma ext {A B : Fact M} (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B :=
  SetLike.ext h

variable {A B : Fact M}

instance : Lolli (Fact M) := ⟨fun A B ↦ ⟨{f | ∀ a ∈ A, f * a ∈ B}, by
  apply isFact_iff_subset.mpr
  intro g hg a ha
  suffices g * a ∈ Bᗮᗮ by simpa
  intro b' hb'
  have : g * (a * b') ∈ ⫫ := hg (a * b') fun f hf ↦ by
    have : b' * (f * a) ∈ ⫫ := hb' _ (hf a ha)
    grind
  grind⟩⟩

@[simp] lemma mem_lolli_iff : f ∈ A ⊸ B ↔ ∀ a ∈ A, f * a ∈ B := by
  rfl

instance : Bot (Fact M) where
  bot := ⟨⫫, by simp⟩

@[simp] lemma mem_bot : m ∈ (⊥ : Fact M) ↔ m ∈ ⫫ := by
  rfl

instance : Tilde (Fact M) where
  tilde X := ⟨Xᗮ, by simp⟩

lemma coe_neg {A : Fact M} : ((∼A : Fact M) : Set M) = Aᗮ := rfl

lemma mem_neg_iff : m ∈ ∼A ↔ ∀ n ∈ A, m * n ∈ ⫫ := by rfl

@[simp] lemma bipoler_eq (A : Fact M) : ∼∼A = A := by
  apply ext_set; simp [coe_neg]

instance : Top (Fact M) := ⟨Set.univ, isFact_iff_subset.mpr <| by simp⟩

@[simp] lemma mem_top (m : M) : m ∈ (⊤ : Fact M) := by trivial

instance : Par (Fact M) := ⟨fun A B ↦ ⟨(Set.image2 (· * ·) (Aᗮ) (Bᗮ))ᗮ, by simp⟩⟩

@[simp] lemma mem_par_iff : m ∈ A ⅋ B ↔ ∀ u ∈ ∼A, ∀ v ∈ ∼B, m * u * v ∈ ⫫ := calc
  m ∈ A ⅋ B ↔ m ∈ (Set.image2 (· * ·) (∼A) (∼B))ᗮ := by rfl
          _ ↔ ∀ u ∈ ∼A, ∀ v ∈ ∼B, m * u * v ∈ ⫫ := by simp [mem_poler_iff]; grind

instance : With (Fact M) := ⟨fun A B ↦ ⟨A ∩ B, by
  apply isFact_iff_subset.mpr
  intro m hm
  have hA : m ∈ A := A.isFact.subset fun a' ha' ↦ hm a' fun a ha ↦ ha' a (by grind)
  have hB : m ∈ B := B.isFact.subset fun b' hb' ↦ hm b' fun b hb ↦ hb' b (by grind)
  simp_all⟩⟩

@[simp] lemma mem_with_iff : m ∈ A ＆ B ↔ m ∈ A ∧ m ∈ B := by rfl

instance : Quest (Fact M) := ⟨fun A ↦ ⟨{a' ∈ Aᗮ | IsPositive a'}ᗮ, by simp⟩⟩

@[simp] lemma mem_quest_iff : m ∈ ？A ↔ ∀ a' ∈ ∼A, IsPositive a' → m * a' ∈ ⫫ := by
  simp [HQuest.hQuest, Quest.quest, mem_poler_iff, mem_neg_iff]

instance : One (Fact M) := ⟨∼(⊥ : Fact M)⟩

instance : Zero (Fact M) := ⟨∼(⊤ : Fact M)⟩

instance : Tensor (Fact M) := ⟨fun A B ↦ ∼(∼A ⅋ ∼B)⟩

instance : Plus (Fact M) := ⟨fun A B ↦ ∼(∼A ＆ ∼B)⟩

instance : Bang (Fact M) := ⟨fun A ↦ ∼？∼A⟩

variable (A B)

@[simp] lemma neg_bot : ∼(⊥ : Fact M) = 1 := rfl

@[simp] lemma neg_one : ∼(1 : Fact M) = ⊥ := by rw [←neg_bot, bipoler_eq]

@[simp] lemma neg_top : ∼(⊤ : Fact M) = 0 := rfl

@[simp] lemma neg_zero : ∼(0 : Fact M) = ⊤ := by rw [←neg_top, bipoler_eq]

@[simp] lemma neg_par : ∼(A ⅋ B) = ∼A ⨂ ∼B := calc
  ∼(A ⅋ B) = ∼(∼∼A ⅋ ∼∼B) := by simp
         _ = ∼A ⨂ ∼B     := rfl

@[simp] lemma neg_tensor : ∼(A ⨂ B) = ∼A ⅋ ∼B := calc
  ∼(A ⨂ B) = ∼∼(∼A ⅋ ∼B) := by simp
         _ =  ∼A ⅋ ∼B := by rw [bipoler_eq]

@[simp] lemma neg_with : ∼(A ＆ B) = ∼A ⨁ ∼B := calc
  ∼(A ＆ B) = ∼(∼∼A ＆ ∼∼B) := by simp
         _ = ∼A ⨁ ∼B        := rfl

@[simp] lemma neg_plus : ∼(A ⨁ B) = ∼A ＆ ∼B := calc
  ∼(A ⨁ B) = ∼∼(∼A ＆ ∼B) := by simp
         _ = ∼A ＆ ∼B        := by rw [bipoler_eq]

@[simp] lemma neg_quest : ∼？A = ！∼A := calc
  ∼？A = ∼？∼∼A := by simp
     _ = ！∼A   := rfl

@[simp] lemma neg_bang : ∼！A = ？∼A := calc
  ∼！A = ∼∼？∼A := by simp
     _ = ？∼A   := by rw [bipoler_eq]

lemma lolli_eq_neg_par : A ⊸ B = ∼A ⅋ B := by
  ext f
  suffices (∀ a ∈ A, f * a ∈ B) ↔ ∀ u ∈ A, ∀ v ∈ ∼B, f * u * v ∈ ⫫ by simpa
  constructor
  · intro hf a ha b' hb'
    have : b' * (f * a) ∈ ⫫ := hb' _ (hf a ha)
    grind
  · intro hf a ha
    suffices f * a ∈ Bᗮᗮ by simpa
    intro b' hb'
    exact hf a ha b' hb'

@[grind =] lemma par_comm : A ⅋ B = B ⅋ A := by
  ext m; simp; grind

end Fact

end PhaseSpace

end LO
