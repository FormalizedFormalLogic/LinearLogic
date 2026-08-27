module

public import Foundation.Vorspiel.Nat.Matrix
public import Foundation.Vorspiel.NotationClass
public import LinearLogic.Vorspiel.NotationClass
public import LinearLogic.Vorspiel.Multiset

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

lemma IsPositive.mul {x y : M} (hx : IsPositive x) (hy : IsPositive y) : IsPositive (x * y) := by
  constructor
  · calc
      (x * y) * (x * y) = (x * x) * (y * y) := by ac_rfl
      _ = x * y := by rw [hx.idempotent, hy.idempotent]
  · intro p hp
    have := hy.exclusive (x * p) (hx.exclusive p hp)
    grind

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

instance : LE (Fact M) := LE.ofSetLike (Fact M) M

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

instance : Bot (Fact M) := ⟨⟨⫫, by simp⟩⟩

@[simp] lemma mem_bot : m ∈ (⊥ : Fact M) ↔ m ∈ ⫫ := by
  rfl

instance : Tilde (Fact M) := ⟨fun X ↦ ⟨Xᗮ, by simp⟩⟩

lemma coe_neg {A : Fact M} : ((∼A : Fact M) : Set M) = Aᗮ := rfl

lemma mem_neg_iff : m ∈ ∼A ↔ ∀ n ∈ A, m * n ∈ ⫫ := by rfl

@[grind =, simp] lemma bipoler_eq (A : Fact M) : ∼∼A = A := by
  apply ext_set; simp [coe_neg]

@[grind .] lemma neg_antitone {A B : Fact M} (h : A ≤ B) : ∼B ≤ ∼A := by
  intro m hm a ha
  exact hm a (h ha)

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

lemma mem_bang_iff : m ∈ ！A ↔ ∀ v, (∀ a ∈ A, IsPositive a → v * a ∈ ⫫) → m * v ∈ ⫫ := by
  rw [show ！A = ∼？∼A from rfl, mem_neg_iff]
  simp

lemma mem_neg_quest_of_positive {C : Fact M} {a : M} (hpa : IsPositive a)
    (ha : a ∈ ∼C) : a ∈ ∼？C := by
  intro q hq
  simpa only [mul_comm] using (mem_quest_iff.mp hq) a ha hpa

@[simp] lemma quest_quest : ？？A = ？A := by
  ext m
  constructor
  · intro hm
    apply mem_quest_iff.mpr
    intro a ha hpa
    exact (mem_quest_iff.mp hm) a (mem_neg_quest_of_positive hpa ha) hpa
  · intro hm
    apply mem_quest_iff.mpr
    intro a ha _
    simpa only [mul_comm] using ha m hm

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

lemma mul_mem_neg_par {a b : M} (ha : a ∈ ∼A) (hb : b ∈ ∼B) : a * b ∈ ∼(A ⅋ B) := by
  intro m hm
  have := (mem_par_iff.mp hm) a ha b hb
  grind

@[grind =] lemma par_assoc : (A ⅋ B) ⅋ C = A ⅋ (B ⅋ C) := by
  ext m
  rw [mem_par_iff, mem_par_iff]
  constructor
  · intro hm a ha bc hbc
    have hma : m * a ∈ B ⅋ C := by
      apply mem_par_iff.mpr
      intro b hb c hc
      have := hm (a * b) (mul_mem_neg_par (A := A) (B := B) ha hb) c hc
      grind
    have := hbc (m * a) hma
    grind
  · intro hm ab hab c hc
    have hmc : m * c ∈ A ⅋ B := by
      apply mem_par_iff.mpr
      intro a ha b hb
      have := hm a ha (b * c) (mul_mem_neg_par (A := B) (B := C) hb hc)
      grind
    have := hab (m * c) hmc
    grind

@[simp] lemma par_bot_eq : A ⅋ ⊥ = A := by
  ext m
  rw [mem_par_iff]
  constructor
  · intro hm
    apply A.isFact.subset
    intro a ha
    have hone : (1 : M) ∈ ∼(⊥ : Fact M) := by
      change (1 : M) ∈ (⫫ : Set M)ᗮ
      simp
    simpa using hm a ha 1 hone
  · intro hm a ha p hp
    have hma : m * a ∈ ⫫ := by simpa [mul_comm] using ha m hm
    change p ∈ (⫫ : Set M)ᗮ at hp
    have := hp (m * a) hma
    grind

lemma par_mono {A₁ A₂ B₁ B₂ : Fact M}
    (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂) : A₁ ⅋ B₁ ≤ A₂ ⅋ B₂ := by
  intro m hm
  simp only [mem_par_iff] at hm ⊢
  intro a ha b hb
  exact hm a (neg_antitone hA ha) b (neg_antitone hB hb)

lemma bang_par_le (A B : Fact M) : ！(A ⅋ B) ≤ ？A ⅋ ！B := by
  intro m hm
  apply mem_par_iff.mpr
  intro u hu v hv
  have hu : u ∈ ！∼A := by simpa using hu
  have hv : v ∈ ？∼B := by simpa using hv
  have huv := (mem_bang_iff (A ⅋ B)).mp hm (u * v) (by
    intro c hc hpc
    have huvc := (mem_bang_iff (∼A)).mp hu (v * c) (by
      intro a ha hpa
      have hca : c * a ∈ B := by
        apply B.isFact.subset
        intro b hb
        exact (mem_par_iff.mp hc) a ha b hb
      have := (mem_quest_iff.mp hv) (c * a) (by simpa using hca) (hpc.mul hpa)
      grind)
    grind)
  simpa only [mul_assoc] using huv

instance : Std.Commutative (α := Fact M) HPar.hPar := ⟨par_comm⟩

instance : Std.Associative (α := Fact M) HPar.hPar := ⟨par_assoc⟩

def bigPar (Γ : Multiset (Fact M)) : Fact M := Multiset.fold HPar.hPar ⊥ Γ

@[simp] lemma bigPar_zero : bigPar (0 : Multiset (Fact M)) = ⊥ := by simp [bigPar]

@[simp] lemma bigPar_atom (A : Fact M) : bigPar ⦃A⦄ = A := by
  have : ⦃A⦄ = A ::ₘ 0 := by rfl
  unfold bigPar
  rw [this, Multiset.fold_cons_left]
  simp

@[simp] lemma bigPar_add (Γ Δ : Multiset (Fact M)) : bigPar (Γ + Δ) = bigPar Γ ⅋ bigPar Δ :=
  calc
  bigPar (Γ + Δ) = Multiset.fold HPar.hPar (⊥ ⅋ ⊥) (Γ + Δ) := by unfold bigPar; simp
               _ = bigPar Γ ⅋ bigPar Δ := by rw [Multiset.fold_add]; rfl

@[simp] lemma bigPar_cons (A : Fact M) (s : Multiset (Fact M)) :
    bigPar (A ::ₘ s) = A ⅋ bigPar s := by
  rw [show A ::ₘ s = ⦃A⦄ + s from rfl, bigPar_add]
  simp

def IsTrue (A : Fact M) : Prop := 1 ∈ A

namespace IsTrue

lemma par_iff : (Γ ⅋ A).IsTrue ↔ ∼Γ ≤ A := by
  constructor
  · intro h m hm
    apply A.isFact.subset
    intro a ha
    simpa [IsTrue] using (mem_par_iff.mp h) m hm a ha
  · intro h
    rw [IsTrue, mem_par_iff]
    intro m hm a ha
    simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using ha m (h hm)

lemma lolli_iff : (A ⊸ B).IsTrue ↔ A ≤ B := by
  rw [IsTrue, mem_lolli_iff]
  simp only [one_mul]
  rfl

@[simp] lemma one : (1 : Fact M).IsTrue := by
  unfold IsTrue
  rw [←neg_bot, mem_neg_iff]
  simp

lemma par_neg : (A ⅋ ∼A).IsTrue := by
  rw [par_comm, ←lolli_eq_neg_par, lolli_iff]
  exact fun _ h ↦ h

lemma tensor (hA : (Γ ⅋ A).IsTrue) (hB : (Δ ⅋ B).IsTrue) : (Γ ⅋ Δ ⅋ A ⨂ B).IsTrue := by
  rw [par_iff] at hA hB
  rw [←par_assoc, par_iff]
  intro u hu
  apply mem_neg_iff.mpr
  intro v hv
  apply hu v
  apply mem_par_iff.mpr
  intro g hg d hd
  exact (mem_par_iff.mp hv) g (by simpa using hA hg) d (by simpa using hB hd)

lemma plus_left (hA : (Γ ⅋ A).IsTrue) : (Γ ⅋ A ⨁ B).IsTrue := by
  rw [par_iff] at hA ⊢
  intro m hm
  apply mem_neg_iff.mpr
  intro n hn
  simpa only [mul_comm] using hn.1 m (hA hm)

lemma plus_right (hB : (Γ ⅋ B).IsTrue) : (Γ ⅋ A ⨁ B).IsTrue := by
  rw [par_iff] at hB ⊢
  intro m hm
  apply mem_neg_iff.mpr
  intro n hn
  simpa only [mul_comm] using hn.2 m (hB hm)

lemma «with» (hA : (Γ ⅋ A).IsTrue) (hB : (Γ ⅋ B).IsTrue) : (Γ ⅋ A ＆ B).IsTrue := by
  rw [par_iff] at hA hB ⊢
  exact fun _ hm ↦ ⟨hA hm, hB hm⟩

lemma dereliction (hA : (Γ ⅋ A).IsTrue) : (Γ ⅋ ？A).IsTrue := by
  rw [par_iff] at hA ⊢
  intro m hm
  apply mem_quest_iff.mpr
  intro a ha _
  simpa only [mul_comm] using ha m (hA hm)

lemma weakening (hA : Γ.IsTrue) : (Γ ⅋ ？A).IsTrue := by
  rw [par_iff]
  intro m hm
  apply mem_quest_iff.mpr
  intro a _ ha
  have hm : m ∈ ⫫ := by simpa using hm 1 hA
  simpa only [mul_comm] using ha.exclusive m hm

lemma contraction (hA : (Γ ⅋ ？A ⅋ ？A).IsTrue) : (Γ ⅋ ？A).IsTrue := by
  rw [par_iff] at hA ⊢
  intro m hm
  apply mem_quest_iff.mpr
  intro a ha hpa
  have ha' := mem_neg_quest_of_positive hpa ha
  have := (mem_par_iff.mp (hA hm)) a ha' a ha'
  simpa only [mul_assoc, hpa.idempotent] using this

lemma context_free_bang (hA : A.IsTrue) : (！A).IsTrue := by
  rw [IsTrue, mem_bang_iff]
  intro v hv
  simpa using hv 1 hA IsPositive.one

lemma application (hp : (A ⊸ B).IsTrue) (hn : A.IsTrue) : B.IsTrue := by
  exact (lolli_iff (A := A) (B := B)).mp hp hn

lemma promotion (s : Multiset (Fact M)) : (！(bigPar s ⅋ B) ⊸ bigPar (s.map (？·)) ⅋ ！B).IsTrue := by
  rw [lolli_iff]
  induction s using Multiset.induction_on with
  | empty =>
    intro m hm
    rw [bigPar_zero, par_comm, par_bot_eq] at hm
    rw [Multiset.map_zero, bigPar_zero, par_comm, par_bot_eq]
    exact hm
  | @cons C s ih =>
    intro m hm
    rw [bigPar_cons, par_assoc] at hm
    have hm := bang_par_le C (bigPar s ⅋ B) hm
    have hm := par_mono (A₁ := ？C) (A₂ := ？C) (fun _ h ↦ h) ih hm
    simpa only [Multiset.map_cons, bigPar_cons, par_assoc] using hm

lemma bang (hA : (bigPar s ⅋ A).IsTrue) : (bigPar (s.map (？·)) ⅋ ！A).IsTrue := by
  exact application
    (A := ！(bigPar s ⅋ A)) (B := bigPar (s.map (？·)) ⅋ ！A)
    (promotion (B := A) s) (context_free_bang (A := bigPar s ⅋ A) hA)

lemma cut (hp : (Γ ⅋ A).IsTrue) (hn : (Δ ⅋ ∼A).IsTrue) : (Γ ⅋ Δ).IsTrue := by
  have hp : ∀ u ∈ ∼Γ, ∀ v, (∀ n ∈ A, v * n ∈ ⫫) → u * v ∈ ⫫ := by simpa [IsTrue, mem_neg_iff (A := A)] using hp
  have hn : ∀ v ∈ ∼Δ, ∀ a ∈ A, v * a ∈ ⫫ := by simpa [IsTrue] using hn
  suffices ∀ u ∈ ∼Γ, ∀ v ∈ ∼Δ, u * v ∈ ⫫ by simpa [IsTrue] using this
  intro u hu v hv
  exact hp u hu v (hn v hv)

end IsTrue

end Fact

end PhaseSpace

end LO
