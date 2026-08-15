/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.StallTypeSplit

/-!
# The type-A exchange obstruction

A card-four selection of the `K4` chart is **type A** when its complement is one
of the three perfect matchings `{0, 5}`, `{1, 4}`, `{2, 3}`.  Such a selection is
a four-cycle.  Every other card-four selection contains a triangle.  The split is
`Gtz.kFourCardFour_matchingCompl_or_triangle`.

This module records the combinatorics of a one-label exchange out of a type-A
selection.  An exchange removes one selected label and adds one label from the
complement.

## The results

* `kFourMatchingCompl_exchange_compl_ne_matching` — an exchange out of a
  four-cycle never lands on a four-cycle.
* `kFourMatchingCompl_exchange_containsTriangle` — the exchange therefore
  contains a triangle.  This is the object-level form of the reduction that
  sends type A into type B.
* `kFourMatchingCompl_exchange_not_compl_subset` — **THE OBSTRUCTION.**  An
  exchange keeps one of the two complement labels outside, because it admits
  exactly one new label.

## Why the obstruction matters

The obstruction is the reason an exchange argument cannot close type A.  A probe
over three million exact chart points found 1471 type-A stalls at which no
one-label exchange is positive definite.  At every one of them, each of the 12018
positive definite escape sets contained both complement labels.  A one-label
exchange admits one new label only.  As a result the exchange can never reach
such an escape.

The escape from a type-A stall must therefore pass through a larger selection
first, or move two labels at one time.  A successor must not attempt a direct
exchange argument at type A.
-/

namespace Gtz

/-! ## An exchange out of a four-cycle lands on a triangle -/

/-- The complement of an exchange result is never a perfect matching.

The complement of a type-A selection has two labels.  An exchange admits one of
them and rejects one selected label, so the new complement holds the rejected
label and one former complement label.  Two perfect matchings of `K4` that share
a label are equal, and the new complement holds a label the old one did not. -/
theorem kFourMatchingCompl_exchange_compl_ne_matching
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected) :
    ¬ ((insert entering (selected.erase leaving))ᶜ = {0, 5} ∨
        (insert entering (selected.erase leaving))ᶜ = {1, 4} ∨
        (insert entering (selected.erase leaving))ᶜ = {2, 3}) := by
  revert hcard hmatching hleaving hentering
  revert leaving entering
  revert selected
  decide

/-- **AN EXCHANGE OUT OF A FOUR-CYCLE CONTAINS A TRIANGLE.**  The object-level
reduction that sends type A into type B.

Every one-label exchange out of a type-A selection is a type-B selection.  The
type split is exhaustive, and the exchange result is never a four-cycle. -/
theorem kFourMatchingCompl_exchange_containsTriangle
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected) :
    ({0, 1, 2} ⊆ insert entering (selected.erase leaving) ∨
      {0, 3, 4} ⊆ insert entering (selected.erase leaving) ∨
      {1, 3, 5} ⊆ insert entering (selected.erase leaving) ∨
      {2, 4, 5} ⊆ insert entering (selected.erase leaving)) := by
  have hcardExchange : (insert entering (selected.erase leaving)).card = 4 := by
    have hnotMem : entering ∉ selected.erase leaving := fun hmem =>
      hentering (Finset.mem_of_mem_erase hmem)
    rw [Finset.card_insert_of_notMem hnotMem,
      Finset.card_erase_of_mem hleaving, hcard]
  rcases kFourCardFour_matchingCompl_or_triangle _ hcardExchange with
    hmatchingExchange | htriangle
  · exact absurd hmatchingExchange
      (kFourMatchingCompl_exchange_compl_ne_matching selected hcard hmatching
        leaving hleaving entering hentering)
  · exact htriangle

/-! ## The obstruction -/

/-- **THE TYPE-A EXCHANGE OBSTRUCTION.**  An exchange never holds the whole
complement of a type-A selection.

The complement has two labels and the exchange admits one label only, so one
complement label stays outside.  Any selection that holds both complement labels
is at distance two from the original, and no one-label exchange reaches it. -/
theorem kFourMatchingCompl_exchange_not_compl_subset
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected) :
    ¬ (selectedᶜ ⊆ insert entering (selected.erase leaving)) := by
  revert hcard hmatching hleaving hentering
  revert leaving entering
  revert selected
  decide

/-- The obstruction in the form a successor consumes: a selection that holds both
complement labels of a type-A selection is not an exchange of it. -/
theorem kFourMatchingCompl_compl_subset_ne_exchange
    (selected other : Finset (Fin 6)) (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (hother : selectedᶜ ⊆ other)
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected) :
    other ≠ insert entering (selected.erase leaving) := by
  intro heq
  exact kFourMatchingCompl_exchange_not_compl_subset selected hcard hmatching
    leaving hleaving entering hentering (heq ▸ hother)

end Gtz
