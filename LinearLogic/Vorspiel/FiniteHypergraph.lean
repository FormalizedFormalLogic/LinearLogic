module

public import LinearLogic.Vorspiel.Finmap

@[expose] public section

class HasVertices (E : Type*) (V : outParam Type*) where
  vertices : E → Finset V

structure WeightedHypergraph (V E ν ω : Type*) [DecidableEq E] [DecidableEq V] [HasVertices ν V] where
  hyperedgeMap : E ⇢ ν
  vertexMap : V ⇢ ω
  vertices_subset :
    (vertexMap.domain : Set V) = ⋃ (e) (l ∈ hyperedgeMap.of e), HasVertices.vertices l

end
