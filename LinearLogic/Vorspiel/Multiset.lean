module

public import Foundation.Vorspiel.Multiset

@[expose] public section

namespace Multiset

/-- Restrict an explicit traversal, retaining the requested multiplicities. -/
def Traversal.restrict [DecidableEq α] {Γ Δ : Multiset α}
    (t : Γ.Traversal) (h : Δ ≤ Γ) : Δ.Traversal :=
  match t with
  | .zero => Traversal.zero.cast (le_antisymm (zero_le _) h)
  | .succ (s := Γ) A t =>
    if ha : A ∈ Δ then
      (t.restrict (Δ := Δ.erase A)
        (erase_le_iff_le_cons.mpr (by simpa [add_atom_eq_cons] using h))).succ A |>.cast (by
          simpa [add_atom_eq_cons] using cons_erase ha)
    else
      t.restrict ((le_cons_of_notMem ha).mp (by simpa [add_atom_eq_cons] using h))

end Multiset
