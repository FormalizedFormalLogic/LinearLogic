module

public import Mathlib.Data.Finmap
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.TautoSet
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-

namespace Multiset

variable {α β : Type*}

def domain (m : Multiset (α × β)) : Multiset α := m.map Prod.fst

def codomain (m : Multiset (α × β)) : Multiset β := m.map Prod.snd

@[simp] lemma domain_empty : domain (0 : Multiset (α × β)) = 0 := by simp [domain]

@[simp] lemma codomain_empty : codomain (0 : Multiset (α × β)) = 0 := by simp [codomain]

@[simp] lemma domain_cons (a : α) (b : β) (m : Multiset (α × β)) :
    domain ((a, b) ::ₘ m) = a ::ₘ domain m := by simp [domain]

@[simp] lemma codomain_cons (a : α) (b : β) (m : Multiset (α × β)) :
    codomain ((a, b) ::ₘ m) = b ::ₘ codomain m := by simp [codomain]

end Multiset

/-- Undependent version of `Finmap` -/
structure Finfun (α β : Type*) where
  graph : Multiset (α × β)
  domain_nodup : graph.domain.Nodup

infix:80 " ⇢ " => Finfun

namespace Finfun

variable {α β : Type*}

def domain (f : α ⇢ β) : Finset α := ⟨f.graph.domain, f.domain_nodup⟩

def codomain (f : α ⇢ β) : Multiset β := f.graph.codomain

instance : Zero (α ⇢ β) where
  zero := ⟨0, by simp⟩

def of [DecidableEq α] (f : α ⇢ β) (a : α) : Option β :=
  Quotient.liftOn f.graph (List.lookup a) fun l k h ↦ (by { try? })

end Finfun

-/

namespace Finmap

variable {α : Type*} [DecidableEq α] {β : α → Type*}

abbrev of (f : Finmap β) (a : α) : Option (β a) := f.lookup a

@[simp] lemma of_mk_eq_some_iff {m : Multiset (Sigma β)} {h : m.NodupKeys} :
    (Finmap.mk m h).of a = some b ↔ Sigma.mk a b ∈ m := by
  simp [Finmap.of, lookup_eq_some_iff]

lemma fun_ext {f g : Finmap β} (h : ∀ a, f.of a = g.of a) : f = g := ext_lookup h

end Finmap

variable {α β γ : Type*}

abbrev Finfun (α β : Type*) := Finmap fun (_ : α) ↦ β

infix:80 " ⇢ " => Finfun

namespace Finfun

instance [DecidableEq α] : CoeFun (α ⇢ β) fun _ ↦ α → Option β := ⟨Finmap.of⟩

abbrev domain (f : α ⇢ β) : Finset α := f.keys

def range (f : α ⇢ β) : Multiset β := f.entries.map Sigma.snd

def ofMultisetOfPairs (m : Multiset (α × β)) (coh : (m.map Prod.fst).Nodup) : α ⇢ β where
  entries := m.map fun x ↦ ⟨x.1, x.2⟩
  nodupKeys := by simpa [←Multiset.nodup_keys, Multiset.keys] using coh

def toFun [DecidableEq α] (f : α ⇢ β) : f.domain → β := fun a ↦
  (f a.val).get <|
    by simp [Finmap.lookup_isSome, show a.val ∈ f from a.property]

lemma toFun_eq_some_iff [DecidableEq α] (f : α ⇢ β) {a : f.domain} {b : β} :
    f.toFun a = b ↔ f a = b := by
  cases h : f a.val with
  | none =>
      have hmem : a.val ∈ f := by
        exact Finmap.mem_keys.mp a.property
      have : (f a.val).isSome := by
        simpa [Finmap.lookup_isSome] using hmem
      simp [h] at this
  | some b => simp_all [toFun]

abbrev IsInjective (f : α ⇢ β) : Prop := f.range.Nodup

def comp [DecidableEq β] (g : β ⇢ γ) (f : α ⇢ β) : α ⇢ γ where
  entries := f.entries.filterMap fun p ↦ (g p.2).map (Sigma.mk p.1)
  nodupKeys := by
    rcases f with ⟨⟨l⟩, h⟩
    simpa [List.nodupKeys_iff_pairwise] using
      (List.nodupKeys_iff_pairwise.mp h).filterMap
        (S := fun p q : Sigma (fun _ : α ↦ γ) ↦ p.1 ≠ q.1)
        (fun p : Sigma (fun _ : α ↦ β) ↦ (g p.2).map (Sigma.mk p.1))
        (fun _ _ hp _ hout _ hout' ↦ by
          rcases Option.map_eq_some_iff.mp hout with ⟨_, _, rfl⟩
          rcases Option.map_eq_some_iff.mp hout' with ⟨_, _, rfl⟩
          exact hp)

instance : Zero (α ⇢ β) where
  zero := ⟨0, by solve_by_elim⟩

@[simp] lemma zero_eq_empty : (0 : α ⇢ β) = ∅ := Finmap.ext rfl

@[simp] lemma comp_eq_some_iff [DecidableEq α] [DecidableEq β] {g : β ⇢ γ} {f : α ⇢ β}
    {a : α} {c : γ} :
    g.comp f a = c ↔ ∃ b : β, f a = b ∧ g b = c := by
  simp [comp, Finmap.lookup_eq_some_iff]

@[simp] lemma comp_eq_none_iff [DecidableEq α] [DecidableEq β] {g : β ⇢ γ} {f : α ⇢ β}
    {a : α} :
    g.comp f a = none ↔ f a = none ∨ ∃ b : β, f a = b ∧ g b = none := by
  constructor
  · intro hcomp
    cases hf : f a with
    | none => exact Or.inl rfl
    | some b =>
        right
        refine ⟨b, rfl, ?_⟩
        cases hg : g b with
        | none => rfl
        | some c =>
            have : g.comp f a = some c := comp_eq_some_iff.mpr ⟨b, hf, hg⟩
            simp [hcomp] at this
  · rintro (hf | ⟨b, hf, hg⟩)
    · cases hcomp : g.comp f a with
      | none => rfl
      | some c =>
          rcases comp_eq_some_iff.mp hcomp with ⟨b, hb, _⟩
          simp [hf] at hb
    · cases hcomp : g.comp f a with
      | none => rfl
      | some c =>
          rcases comp_eq_some_iff.mp hcomp with ⟨b', hb', hg'⟩
          have hb : b = b' := by simpa [hf] using hb'
          subst b'
          simp [hg] at hg'

lemma comp_assoc [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (h : γ ⇢ δ) (g : β ⇢ γ) (f : α ⇢ β) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  apply Finmap.fun_ext
  intro a
  apply Option.ext
  intro d
  simp [comp_eq_some_iff]; grind

@[simp] lemma zero_comp [DecidableEq α] [DecidableEq β] (f : α ⇢ β) :
    (0 : β ⇢ γ).comp f = 0 := by
  apply Finmap.fun_ext
  intro a
  cases h : f a with
  | none => exact comp_eq_none_iff.mpr (Or.inl h)
  | some b =>
      exact comp_eq_none_iff.mpr (Or.inr ⟨b, h, by simp⟩)

@[simp] lemma comp_zero [DecidableEq α] [DecidableEq β] (f : β ⇢ γ) :
    f.comp (0 : α ⇢ β) = 0 := by
  apply Finmap.fun_ext
  intro a
  exact comp_eq_none_iff.mpr (by simp)

def projection (s : Finset α) : α ⇢ α where
  entries := s.val.map fun a ↦ ⟨a, a⟩
  nodupKeys := by simpa [←Multiset.nodup_keys, Multiset.keys] using s.nodup

instance [DecidableEq α] : Mul (α ⇢ α) where
  mul := comp

lemma mul_assoc [DecidableEq α] (f g h : α ⇢ α) :
    f * (g * h) = (f * g) * h := comp_assoc f g h

@[simp] lemma zero_mul [DecidableEq α] (f : α ⇢ α) : 0 * f = 0 := zero_comp f

@[simp] lemma mul_zero [DecidableEq α] (f : α ⇢ α) : f * 0 = 0 := comp_zero f

end Finfun

structure FinEquiv (α β : Type*) extends Finfun α β where
  injective : (entries.map Sigma.snd).Nodup

namespace FinEquiv

abbrev toFinfun (f : FinEquiv α β) : α ⇢ β := f.toFinmap

abbrev domain (f : FinEquiv α β) : Finset α := f.toFinfun.domain

def range (f : FinEquiv α β) : Finset β := ⟨f.toFinfun.range, f.injective⟩

lemma injective' (f : FinEquiv α β) : f.toFinfun.IsInjective := f.injective

instance [DecidableEq α] : CoeFun (FinEquiv α β) fun _ ↦ α → Option β := ⟨fun f ↦ f.of⟩

lemma mem_ext {f g : FinEquiv α β}
    (h : ∀ a b, ⟨a, b⟩ ∈ f.entries ↔ ⟨a, b⟩ ∈ g.entries) : f = g := by
  cases f
  cases g
  congr
  exact Finmap.ext <|
    (Multiset.Nodup.ext (Finmap.nodup_entries _) (Finmap.nodup_entries _)).mpr
      (fun x ↦ by rcases x; exact h _ _)

lemma fun_ext [DecidableEq α] {f g : FinEquiv α β} (h : ∀ a, f a = g a) : f = g := by
  cases f
  cases g
  congr
  exact Finmap.fun_ext h

def inv (f : FinEquiv α β) : FinEquiv β α where
  entries := f.entries.map fun p ↦ ⟨p.2, p.1⟩
  nodupKeys := by simpa [←Multiset.nodup_keys, Multiset.keys] using f.injective
  injective := by simpa [←Multiset.nodup_keys, Multiset.keys] using f.nodupKeys

@[simp] lemma inv_app_eq_some_iff [DecidableEq α] [DecidableEq β] {f : FinEquiv α β} {a : α} {b : β} :
    f.inv b = a ↔ f a = b := by
  simp [inv, Finmap.lookup_eq_some_iff]

@[simp] lemma inv_app_eq_none_iff [DecidableEq α] [DecidableEq β] {f : FinEquiv α β} {b : β} :
    f.inv b = none ↔ b ∉ f.toFinfun.range := by
  simp [inv, Finmap.lookup_eq_none, ←Finmap.mem_keys, Finmap.keys, Multiset.keys, Finfun.range]

@[simp] lemma inv_inv [DecidableEq α] [DecidableEq β] (f : FinEquiv α β) : f.inv.inv = f := by
  cases f
  simp [inv]

@[simp] lemma domain_inv (f : FinEquiv α β) : f.inv.domain = f.range := by
  ext b
  simp [domain, range, inv, Finfun.domain, Finfun.range, Finmap.keys, Multiset.keys]

@[simp] lemma range_inv (f : FinEquiv α β) : f.inv.range = f.domain := by
  ext a
  simp [domain, range, inv, Finfun.domain, Finfun.range, Finmap.keys, Multiset.keys]

def projection (s : Finset α) : FinEquiv α α where
  entries := s.val.map fun a ↦ ⟨a, a⟩
  nodupKeys := by simpa [←Multiset.nodup_keys, Multiset.keys] using s.nodup
  injective := by simpa [←Multiset.nodup_keys, Multiset.keys] using s.nodup

@[simp] lemma projection_some_eq_app_iff [DecidableEq α] {s : Finset α} {a b : α} :
    some b = (projection s).of a ↔ a = b ∧ a ∈ s := by
  constructor
  · intro h
    have hm := Finmap.of_mk_eq_some_iff.mp h.symm
    rcases Multiset.mem_map.mp hm with ⟨x, hx, hx_eq⟩
    cases hx_eq
    exact ⟨rfl, hx⟩
  · rintro ⟨rfl, ha⟩
    have hm : Sigma.mk a a ∈
        Multiset.map (fun x : α ↦ (Sigma.mk x x : Sigma fun _ : α ↦ α)) s.val :=
      Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    exact (Finmap.of_mk_eq_some_iff.mpr hm).symm

@[simp] lemma projection_app_eq_none_iff [DecidableEq α] {s : Finset α} {a : α} :
    (projection s).of a = none ↔ a ∉ s := by
  constructor
  · intro h hs
    have : some a = (projection s).of a := projection_some_eq_app_iff.mpr ⟨rfl, hs⟩
    simp [h] at this
  · intro hs
    cases h : (projection s).of a with
    | none => rfl
    | some b =>
        exact False.elim (hs (projection_some_eq_app_iff.mp h.symm).2)

def comp [DecidableEq β] (g : FinEquiv β γ) (f : FinEquiv α β) : FinEquiv α γ where
  entries := (g.toFinfun.comp f.toFinfun).entries
  nodupKeys := (g.toFinfun.comp f.toFinfun).nodupKeys
  injective := by
    simpa [Finfun.comp, Finfun.range, Multiset.map_filterMap, Multiset.filterMap_map,
      Function.comp_def] using
      Multiset.Nodup.filterMap (fun b ↦ g b)
        (fun b b' c hb hb' ↦ by
          have hinj :=
            (Multiset.nodup_map_iff_inj_on (Finmap.nodup_entries g.toFinmap)).mp g.injective
          have hbc : Sigma.mk b c ∈ g.entries := Finmap.lookup_eq_some_iff.mp hb
          have hb'c : Sigma.mk b' c ∈ g.entries := Finmap.lookup_eq_some_iff.mp hb'
          exact congrArg Sigma.fst (hinj _ hbc _ hb'c rfl))
        f.injective

lemma comp_assoc [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (h : FinEquiv γ δ) (g : FinEquiv β γ) (f : FinEquiv α β) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  apply mem_ext
  intro a d
  simp [comp, Finfun.comp, Finmap.lookup_eq_some_iff]
  grind

lemma inv_comp [DecidableEq α] [DecidableEq β] (f : FinEquiv α β) :
    f.inv.comp f = projection f.domain := by
  apply mem_ext
  intro a a'
  suffices
      (∃ b, Sigma.mk a b ∈ f.toFinfun.entries ∧ Sigma.mk a' b ∈ f.entries) ↔
        a' ∈ f.toFinfun ∧ a' = a by
    simpa [comp, Finfun.comp, inv, Finmap.lookup_eq_some_iff, projection, FinEquiv.domain,
      Finfun.domain, Finmap.mem_keys] using this
  constructor
  · rintro ⟨b, hab, ha'b⟩
    have ha_eq : a = a' :=
      congrArg Sigma.fst
        ((Multiset.nodup_map_iff_inj_on (Finmap.nodup_entries f.toFinmap)).mp f.injective
          _ hab _ ha'b rfl)
    have hmem : a' ∈ f.toFinfun := by
      simpa [Finmap.mem_def, Multiset.keys] using Multiset.mem_map_of_mem Sigma.fst ha'b
    exact ⟨hmem, ha_eq.symm⟩
  · rintro ⟨hmem, rfl⟩
    rcases Finmap.mem_iff.mp hmem with ⟨b, hb⟩
    have hb' : Sigma.mk a' b ∈ f.entries := Finmap.lookup_eq_some_iff.mp hb
    exact ⟨b, hb', hb'⟩

lemma comp_inv [DecidableEq α] [DecidableEq β] (f : FinEquiv α β) :
    f.comp f.inv = projection f.range := by
  simpa using inv_comp f.inv

instance : Inv (FinEquiv α α) where
  inv := FinEquiv.inv

end FinEquiv

end
