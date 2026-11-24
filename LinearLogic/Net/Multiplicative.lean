module

public import LinearLogic.MLL.Propositional
public import Mathlib.Data.Finmap

/-!
# Multiplicative Proof-Net
-/

@[expose] public section

namespace FFL.Propositional.MultiplicativeLinearLogic

namespace Net

inductive LinkType (V : Type*) : Type _ where
| ax (w₁ w₂ : V) : LinkType V
| cut (v₁ v₂ : V) : LinkType V
| tensor (v₁ v₂ w : V) : LinkType V
| par (v₁ v₂ w : V) : LinkType V

namespace LinkType

def premises : LinkType V → List V
  |         ax _ _ => []
  |      cut v₁ v₂ => [v₁, v₂]
  | tensor v₁ v₂ _ => [v₁, v₂]
  |    par v₁ v₂ _ => [v₁, v₂]

def conclusions : LinkType V → List V
  |     ax w₁ w₂ => [w₁, w₂]
  |      cut _ _ => []
  | tensor _ _ w => [w]
  |    par _ _ w => [w]

def vertices (l : Net.LinkType V) : Multiset V :=
  l.premises ++ l.conclusions

end LinkType

end Net

structure Net (V E ω : Type*) [DecidableEq V] [DecidableEq E] where
  hyperedgeMap : Finmap fun (_ : E) ↦ Net.LinkType V
  verticeMap : Finmap fun (_ : V) ↦ ω
  vertices_eq : (verticeMap.keys : Set V) = (⋃ (e) (l ∈ hyperedgeMap.lookup e), l.vertices.toFinset)
  unique_premises :
    (hyperedgeMap.flatMap LinkType.premises).Nodup

namespace Net

variable {V E ω : Type*} [DecidableEq V] [DecidableEq E]

def  hyperedges (𝔑 : Net V E ω) : Finset E := 𝔑.hyperedgeMap.keys

def vertices (𝔑 : Net V E ω) : Finset V := 𝔑.verticeMap.keys

def linkOf (𝔑 : Net V E ω) (i : E) : Option (Net.LinkType V) := 𝔑.hyperedgeMap.lookup i

lemma mem_vertices_iff {𝔑 : Net V E ω} {v : V} :
    v ∈ 𝔑.vertices ↔ ∃ (e : E) (l : Net.LinkType V), l ∈ 𝔑.linkOf e ∧ v ∈ l.vertices :=
  sorry

lemma mem_vertices_of_link {𝔑 : Net V E ω} {v : V} {e : E} {l : Net.LinkType V} :
    l ∈ 𝔑.linkOf e → v ∈ l.vertices → v ∈ 𝔑.vertices :=
  sorry



end Net

end FFL.Propositional.MultiplicativeLinearLogic
