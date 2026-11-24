module

public import LinearLogic.LL.Propositional
public import LinearLogic.Vorspiel.GroupTheory.Perm

/-!
# Design: _Dessein_

## References
- Jean-Yves Girard, *Locus solum: From the rules of logic to the logic of rules.*
-/

@[expose] public section

namespace LO.Ludic

abbrev Bias := ℕ

abbrev Ramification := Finset Bias

abbrev Directry := Set Ramification

abbrev Locus := List Bias

inductive Pitchfork
| negative (ξ : Locus) (Λ : Set Locus) : Pitchfork
| positive (Λ : Set Locus) : Pitchfork

infix:40 " ⊢⁻ " => Pitchfork.negative

prefix:40 "⊢⁺ " => Pitchfork.positive

namespace Pitchfork

inductive IsProper : Pitchfork → Prop
| negative (ξ : Locus) (Λ : Set Locus) : ξ ∉ Λ → IsProper (ξ ⊢⁻ Λ)
| positive (Λ : Set Locus) : IsProper (⊢⁺ Λ)

@[simp] lemma IsProper.negative_iff {ξ : Locus} {Λ : Set Locus} :
    (ξ ⊢⁻ Λ).IsProper ↔ ξ ∉ Λ := by
  constructor
  · rintro ⟨⟩; assumption
  · exact IsProper.negative ξ Λ

attribute [simp] IsProper.positive

end Pitchfork

namespace Dessein

inductive NegativeFunctor (α : Type*) : Type _

end Dessein

end LO.Ludic
