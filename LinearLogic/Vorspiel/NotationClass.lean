module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Basic

/-!
# Supplemental notation classes
-/

@[expose] public section

namespace LO

/-! ## Heterogeneous notations -/

class HTensor (α β : Type*) (γ : outParam Type*) where
  hTensor : α → β → γ

infixr:69 " ⨂ " => HTensor.hTensor
macro_rules | `($x ⨂ $y) => `(binop% HTensor.hTensor $x $y)

class HPar (α β : Type*) (γ : outParam Type*) where
  hPar : α → β → γ

infixr:68 " ⅋ " => HPar.hPar
macro_rules | `($x ⅋ $y) => `(binop% HPar.hPar $x $y)

class HWith (α β : Type*) (γ : outParam Type*) where
  hWith : α → β → γ

/-- Note that this notation "＆" (U+FF06) is distinct from "&" (U+0026) -/
infixr:69 " ＆ " => HWith.hWith
macro_rules | `($x ＆ $y) => `(binop% HWith.hWith $x $y)

class HPlus (α β : Type*) (γ : outParam Type*) where
  hPlus : α → β → γ

infixr:68 " ⨁ " => HPlus.hPlus
macro_rules | `($x ⨁ $y) => `(binop% HPlus.hPlus $x $y)

class HLolli (α β : Type*) (γ : outParam Type*) where
  hLolli : α → β → γ

infixr:60 " ⊸ " => HLolli.hLolli
macro_rules | `($x ⊸ $y) => `(binop% HLolli.hLolli $x $y)

class HBang (α : Type*) (β : outParam Type*) where
  hBang : α → β

/- Note that this notation "！" (U+FF01) is distinct from "!" (U+0021) -/
prefix:75 "！" => HBang.hBang
macro_rules | `(！$x) => `(unop% HBang.hBang $x)

class HQuest (α : Type*) (β : outParam Type*) where
  hQuest : α → β

/- Notice that this notation "？" (U+FF1F) is distinct from "?" (U+003F) -/
prefix:75 "？" => HQuest.hQuest
macro_rules | `(？$x) => `(unop% HQuest.hQuest $x)

attribute [match_pattern]
  HTensor.hTensor
  HPar.hPar
  HWith.hWith
  HPlus.hPlus
  HLolli.hLolli
  HBang.hBang
  HQuest.hQuest

/-! ## Homogeneous notations -/

class Tensor (α : Type*) where
  tensor : α → α → α

class Par (α : Type*) where
  par : α → α → α

class With (α : Type*) where
  with' : α → α → α

class Plus (α : Type*) where
  plus : α → α → α

class Lolli (α : Type*) where
  lolli : α → α → α

class Bang (α : Type*) where
  bang : α → α

class Quest (α : Type*) where
  quest : α → α

attribute [match_pattern]
  Tensor.tensor
  Par.par
  With.with'
  Plus.plus
  Lolli.lolli
  Bang.bang
  Quest.quest

@[default_instance]
instance [Tensor α] : HTensor α α α := ⟨Tensor.tensor⟩

@[default_instance]
instance [Par α] : HPar α α α := ⟨Par.par⟩

@[default_instance]
instance [With α] : HWith α α α := ⟨With.with'⟩

@[default_instance]
instance [Plus α] : HPlus α α α := ⟨Plus.plus⟩

@[default_instance]
instance [Lolli α] : HLolli α α α := ⟨Lolli.lolli⟩

@[default_instance]
instance [Bang α] : HBang α α := ⟨Bang.bang⟩

@[default_instance]
instance [Quest α] : HQuest α α := ⟨Quest.quest⟩

end LO
