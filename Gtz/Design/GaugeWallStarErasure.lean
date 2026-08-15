/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.TypeAExchangeReduction
import Gtz.Design.GaugeWallKernelLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The matching-star form of the gauge-wall type-A exchange

A type-A selection on the gauge wall is the complement of a matching, and the
three `K4` matchings are `{0, 5}`, `{1, 4}` and `{2, 3}` — each one triangle
label together with one star label.  So a type-A selection is `{i, j}ᶜ` with `i`
a triangle label and `j` a star label.

`KFourGaugeWallTypeAExchange` quantifies over an unstructured one-label
exchange.  Two of the eight exchanges are impossible, because leaving a triangle
label while entering the star label of the matching omits two triangle labels at
once and the gauge-wall rank obstruction kills every such selection.  That
leaves six.

This module narrows the six to **four**, and the narrowing is the content:

* the **leaving** label may always be taken to be a star label other than `j`
* the **entering** label is then the other member of the matching, so the
  exchanged selection is `{i, r}ᶜ` or `{j, r}ᶜ`.

`kFourGaugeWallTypeAExchange_of_matchingStarEscape` discharges the target from
exactly that four-way disjunction.

## What the measurement says

A directed hunt over `3.2 · 10⁶` exact wall points, `8.76 · 10⁶` positive
definite type-A selections and `3.27 · 10⁶` stalls, with bounded additive
integer perturbations:

| candidate set | count | positive definite | stalls |
|---|---|---|---|
| `{i, r}ᶜ` alone | 2 | 81.0% | 49.0% |
| `{j, r}ᶜ` alone | 2 | 97.2% | 92.6% |
| **both, `r` a star other than `j`** | **4** | **100%** | **100%** |
| all six surviving exchanges | 6 | 100% | 100% |

So the four-way disjunction is total where the six-way one is, and **neither
two-element subset is sufficient** — the first fails at more than half of all
stalls.  The stall hypothesis is also unnecessary: the disjunction already holds
at every positive definite type-A selection.
-/

namespace Gtz

open Matrix

/-! ## 1. The residual -/

/-- **THE MATCHING-STAR ESCAPE.**  At a gauge wall point, a positive definite
type-A selection `{i, j}ᶜ` admits a star label `r` other than `j` for which one
of the two selections `{i, r}ᶜ`, `{j, r}ᶜ` is positive definite.

Both candidates drop `r` and keep one member of the matching, so the leaving
label is always a star label other than `j`.  This is the whole content of the
gauge-wall type-A exchange, over four selections rather than six. -/
def KFourGaugeWallMatchingStarEscape : Prop :=
  ∀ (point : DirectionChartPoint 6) (i j : Fin 6),
    (({i, j} : Finset (Fin 6)) = {0, 5} ∨ ({i, j} : Finset (Fin 6)) = {1, 4}
      ∨ ({i, j} : Finset (Fin 6)) = {2, 3}) →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    (directionChartGap kFourDirection point.mass point.weight
      ({i, j} : Finset (Fin 6))ᶜ).PosDef →
    ∃ r ∈ ({3, 4, 5} : Finset (Fin 6)), r ≠ j ∧
      ((directionChartGap kFourDirection point.mass point.weight
          ({i, r} : Finset (Fin 6))ᶜ).PosDef
        ∨ (directionChartGap kFourDirection point.mass point.weight
          ({j, r} : Finset (Fin 6))ᶜ).PosDef)

/-! ## 2. The reduction -/

/-- **THE MATCHING-STAR REDUCTION.**  The matching-star escape discharges the
gauge-wall type-A exchange.

The leaving label is the second star label `r`, and the entering label is
whichever member of the matching the escape's disjunct keeps. -/
theorem kFourGaugeWallTypeAExchange_of_matchingStarEscape
    (hescape : KFourGaugeWallMatchingStarEscape) :
    KFourGaugeWallTypeAExchange := by
  intro point selected _hcard hmatching hcorank hpd _hstall
  have hsel : ∀ pair : Finset (Fin 6), selectedᶜ = pair → selected = pairᶜ := by
    intro pair hpair
    rw [← hpair, compl_compl]
  rcases hmatching with hm | hm | hm
  · -- matching {0, 5}
    have hs : selected = ({0, 5} : Finset (Fin 6))ᶜ := hsel _ hm
    subst hs
    obtain ⟨r, hrmem, hrne, hrpd⟩ :=
      hescape point 0 5 (Or.inl rfl) hcorank hpd
    have hr : r = 3 ∨ r = 4 := by fin_cases hrmem <;> simp_all
    rcases hr with rfl | rfl
    · rcases hrpd with h | h
      · exact ⟨3, by decide, 5, by decide, by
          rw [show insert (5 : Fin 6) ((({0, 5} : Finset (Fin 6))ᶜ).erase 3)
            = ({0, 3} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨3, by decide, 0, by decide, by
          rw [show insert (0 : Fin 6) ((({0, 5} : Finset (Fin 6))ᶜ).erase 3)
            = ({5, 3} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
    · rcases hrpd with h | h
      · exact ⟨4, by decide, 5, by decide, by
          rw [show insert (5 : Fin 6) ((({0, 5} : Finset (Fin 6))ᶜ).erase 4)
            = ({0, 4} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨4, by decide, 0, by decide, by
          rw [show insert (0 : Fin 6) ((({0, 5} : Finset (Fin 6))ᶜ).erase 4)
            = ({5, 4} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
  · -- matching {1, 4}
    have hs : selected = ({1, 4} : Finset (Fin 6))ᶜ := hsel _ hm
    subst hs
    obtain ⟨r, hrmem, hrne, hrpd⟩ :=
      hescape point 1 4 (Or.inr (Or.inl rfl)) hcorank hpd
    have hr : r = 3 ∨ r = 5 := by fin_cases hrmem <;> simp_all
    rcases hr with rfl | rfl
    · rcases hrpd with h | h
      · exact ⟨3, by decide, 4, by decide, by
          rw [show insert (4 : Fin 6) ((({1, 4} : Finset (Fin 6))ᶜ).erase 3)
            = ({1, 3} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨3, by decide, 1, by decide, by
          rw [show insert (1 : Fin 6) ((({1, 4} : Finset (Fin 6))ᶜ).erase 3)
            = ({4, 3} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
    · rcases hrpd with h | h
      · exact ⟨5, by decide, 4, by decide, by
          rw [show insert (4 : Fin 6) ((({1, 4} : Finset (Fin 6))ᶜ).erase 5)
            = ({1, 5} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨5, by decide, 1, by decide, by
          rw [show insert (1 : Fin 6) ((({1, 4} : Finset (Fin 6))ᶜ).erase 5)
            = ({4, 5} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
  · -- matching {2, 3}
    have hs : selected = ({2, 3} : Finset (Fin 6))ᶜ := hsel _ hm
    subst hs
    obtain ⟨r, hrmem, hrne, hrpd⟩ :=
      hescape point 2 3 (Or.inr (Or.inr rfl)) hcorank hpd
    have hr : r = 4 ∨ r = 5 := by fin_cases hrmem <;> simp_all
    rcases hr with rfl | rfl
    · rcases hrpd with h | h
      · exact ⟨4, by decide, 3, by decide, by
          rw [show insert (3 : Fin 6) ((({2, 3} : Finset (Fin 6))ᶜ).erase 4)
            = ({2, 4} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨4, by decide, 2, by decide, by
          rw [show insert (2 : Fin 6) ((({2, 3} : Finset (Fin 6))ᶜ).erase 4)
            = ({3, 4} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
    · rcases hrpd with h | h
      · exact ⟨5, by decide, 3, by decide, by
          rw [show insert (3 : Fin 6) ((({2, 3} : Finset (Fin 6))ᶜ).erase 5)
            = ({2, 5} : Finset (Fin 6))ᶜ from by decide]; exact h⟩
      · exact ⟨5, by decide, 2, by decide, by
          rw [show insert (2 : Fin 6) ((({2, 3} : Finset (Fin 6))ᶜ).erase 5)
            = ({3, 5} : Finset (Fin 6))ᶜ from by decide]; exact h⟩

/-! ## 3. The composed branch -/

/-- The gauge-wall type-A branch from the matching-star escape and a triangle
stall closure.  This is the composition a consumer wants: it names the four-way
star escape rather than the unstructured exchange. -/
theorem kFourGaugeWallTypeAStall_tree_of_matchingStar_of_triangleClosure
    (hescape : KFourGaugeWallMatchingStarEscape)
    (hclose : ∀ (point : DirectionChartPoint 6) (other : Finset (Fin 6)),
      other.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight other).PosDef →
      (∀ label ∈ other, 1 ≤ chartLadderPivot kFourDirection point.mass
        point.weight other label) →
      ({0, 1, 2} ⊆ other ∨ {0, 3, 4} ⊆ other ∨ {1, 3, 5} ⊆ other
        ∨ {2, 4, 5} ⊆ other) →
      ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight tree).PosDef)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (hcorank : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected, 1 ≤ chartLadderPivot kFourDirection point.mass
      point.weight selected label) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  kFourGaugeWallTypeAStall_tree_of_exchange_of_triangleClosure
    (kFourGaugeWallTypeAExchange_of_matchingStarEscape hescape) hclose point
    selected hcard hmatching hcorank hpd hstall

end Gtz
