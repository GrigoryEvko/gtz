import Gtz.Design.CrossEnergyLaw
import Gtz.Design.StallTypeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# Two-term decompositions outside a K4 card-four selection

The six K4 directions are the edges of a tetrahedron written in a rooted
three-dimensional chart.  For each edge there are two disjoint two-edge paths
whose signed incidence vector equals that edge.  A card-four selection omits
only two edges.  After fixing one omitted edge, the other omitted edge can
meet at most one of those two paths.  The remaining path lies in the selection.

Consequently every outside direction is a signed sum of exactly two selected
directions.  This statement is uniform across the matching-complement/type-A
and triangle/type-B stall shapes.  The final theorem transports the raw
direction identity into the chart's scaled ladder vectors, which is the form
needed to close inverse-cross refusal systems using only the inverse data of
the selected four-set.
-/

namespace Gtz

open Finset Matrix

/-- A raw K4 direction is a signed sum of two other directions.  The four
disjuncts keep all coefficients in `{+1,-1}` without introducing an auxiliary
finite sign type. -/
def KFourSignedPairDecomposition (target left right : Fin 6) : Prop :=
  kFourDirection target = kFourDirection left + kFourDirection right ∨
  kFourDirection target = kFourDirection left - kFourDirection right ∨
  kFourDirection target = -kFourDirection left + kFourDirection right ∨
  kFourDirection target = -kFourDirection left - kFourDirection right

/-- The first two-edge path representing a target edge. -/
def kFourPathOneLeft : Fin 6 → Fin 6
  | 0 => 3 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 3 | 5 => 3

def kFourPathOneRight : Fin 6 → Fin 6
  | 0 => 4 | 1 => 5 | 2 => 5 | 3 => 4 | 4 => 0 | 5 => 1

/-- The second, edge-disjoint two-edge path representing a target edge. -/
def kFourPathTwoLeft : Fin 6 → Fin 6
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 4

def kFourPathTwoRight : Fin 6 → Fin 6
  | 0 => 2 | 1 => 2 | 2 => 0 | 3 => 5 | 4 => 5 | 5 => 2

/-- The first path is a signed decomposition of its target. -/
theorem kFour_pathOne_decomposition (target : Fin 6) :
    KFourSignedPairDecomposition target (kFourPathOneLeft target)
      (kFourPathOneRight target) := by
  fin_cases target <;> simp [KFourSignedPairDecomposition, kFourPathOneLeft,
    kFourPathOneRight, kFourDirection]

/-- The second path is a signed decomposition of its target. -/
theorem kFour_pathTwo_decomposition (target : Fin 6) :
    KFourSignedPairDecomposition target (kFourPathTwoLeft target)
      (kFourPathTwoRight target) := by
  fin_cases target <;> simp [KFourSignedPairDecomposition, kFourPathTwoLeft,
    kFourPathTwoRight, kFourDirection]

theorem kFour_pathOne_ne (target : Fin 6) :
    kFourPathOneLeft target ≠ kFourPathOneRight target := by
  fin_cases target <;> decide

theorem kFour_pathTwo_ne (target : Fin 6) :
    kFourPathTwoLeft target ≠ kFourPathTwoRight target := by
  fin_cases target <;> decide

/-- If one edge of the first path is absent from a card-four selection which
also omits the target, the edge-disjoint second path is wholly selected. -/
theorem kFour_pathTwo_mem_of_pathOne_missing
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (target : Fin 6) (htarget : target ∉ selected)
    (hmissing : kFourPathOneLeft target ∉ selected ∨
      kFourPathOneRight target ∉ selected) :
    kFourPathTwoLeft target ∈ selected ∧
      kFourPathTwoRight target ∈ selected := by
  revert hcard htarget hmissing
  revert selected
  fin_cases target <;> decide

/-- **THE OUTSIDE TWO-TERM DECOMPOSITION.**  Every direction outside a
card-four K4 selection is a signed sum of two distinct selected directions.

This is the common circuit statement behind both stall types.  It uses only
the K4 direction table and the fact that a card-four set has a two-element
complement. -/
theorem kFour_exists_signedPairDecomposition_of_cardFour
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (target : Fin 6) (htarget : target ∉ selected) :
    ∃ left ∈ selected, ∃ right ∈ selected,
      left ≠ right ∧ KFourSignedPairDecomposition target left right := by
  by_cases hleft : kFourPathOneLeft target ∈ selected
  · by_cases hright : kFourPathOneRight target ∈ selected
    · exact ⟨kFourPathOneLeft target, hleft, kFourPathOneRight target, hright,
        kFour_pathOne_ne target, kFour_pathOne_decomposition target⟩
    · obtain ⟨hleftTwo, hrightTwo⟩ :=
        kFour_pathTwo_mem_of_pathOne_missing selected hcard target htarget
          (Or.inr hright)
      exact ⟨kFourPathTwoLeft target, hleftTwo, kFourPathTwoRight target,
        hrightTwo, kFour_pathTwo_ne target, kFour_pathTwo_decomposition target⟩
  · obtain ⟨hleftTwo, hrightTwo⟩ :=
      kFour_pathTwo_mem_of_pathOne_missing selected hcard target htarget
        (Or.inl hleft)
    exact ⟨kFourPathTwoLeft target, hleftTwo, kFourPathTwoRight target,
      hrightTwo, kFour_pathTwo_ne target, kFour_pathTwo_decomposition target⟩

/-! ## Scaled transport -/

/-- The positive scale used by a chart ladder vector. -/
noncomputable def chartLadderScale {size : ℕ}
    (mass weight : Fin size → ℝ) (label : Fin size) : ℝ :=
  Real.sqrt (mass label / weight label)

/-- A ladder vector is its raw direction multiplied by `chartLadderScale`. -/
theorem chartLadderVector_eq_scale_smul {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (label : Fin size) :
    chartLadderVector direction mass weight label
      = chartLadderScale mass weight label • direction label := by
  rfl

/-- The ladder scale is strictly positive when mass and weight are positive. -/
theorem chartLadderScale_pos {size : ℕ}
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (label : Fin size) :
    0 < chartLadderScale mass weight label := by
  rw [chartLadderScale]
  exact Real.sqrt_pos.2 (div_pos (hmass label) (hweight label))

/-- Transport a two-term raw direction identity to the scaled ladder vectors.
The coefficient ratios are well-defined because every ladder scale is
positive. -/
theorem chartLadderVector_eq_pair_of_direction_eq
    {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label)
    (target left right : Fin size) (leftCoeff rightCoeff : ℝ)
    (hdirection : direction target
      = leftCoeff • direction left + rightCoeff • direction right) :
    chartLadderVector direction mass weight target
      = (chartLadderScale mass weight target * leftCoeff
          / chartLadderScale mass weight left)
          • chartLadderVector direction mass weight left
        + (chartLadderScale mass weight target * rightCoeff
          / chartLadderScale mass weight right)
          • chartLadderVector direction mass weight right := by
  have hleftNe : chartLadderScale mass weight left ≠ 0 :=
    ne_of_gt (chartLadderScale_pos mass weight hmass hweight left)
  have hrightNe : chartLadderScale mass weight right ≠ 0 :=
    ne_of_gt (chartLadderScale_pos mass weight hmass hweight right)
  rw [chartLadderVector_eq_scale_smul, hdirection, smul_add,
    smul_smul, chartLadderVector_eq_scale_smul,
    chartLadderVector_eq_scale_smul]
  simp only [smul_smul]
  rw [div_mul_cancel₀ _ hleftNe, div_mul_cancel₀ _ hrightNe]

/-- A two-term ladder-vector identity is inherited by the first slot of every
inverse cross pairing. -/
theorem chartLadderCross_left_eq_pair_of_ladderVector_eq
    {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (base : Finset (Fin size))
    (target left right source : Fin size) (leftCoeff rightCoeff : ℝ)
    (hvector : chartLadderVector direction mass weight target
      = leftCoeff • chartLadderVector direction mass weight left
        + rightCoeff • chartLadderVector direction mass weight right) :
    chartLadderCross direction mass weight base target source
      = leftCoeff * chartLadderCross direction mass weight base left source
        + rightCoeff * chartLadderCross direction mass weight base right source := by
  unfold chartLadderCross
  rw [hvector, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]

/-- A two-term ladder-vector identity is inherited by the second slot of every
inverse cross pairing. -/
theorem chartLadderCross_right_eq_pair_of_ladderVector_eq
    {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (base : Finset (Fin size))
    (source target left right : Fin size) (leftCoeff rightCoeff : ℝ)
    (hvector : chartLadderVector direction mass weight target
      = leftCoeff • chartLadderVector direction mass weight left
        + rightCoeff • chartLadderVector direction mass weight right) :
    chartLadderCross direction mass weight base source target
      = leftCoeff * chartLadderCross direction mass weight base source left
        + rightCoeff * chartLadderCross direction mass weight base source right := by
  unfold chartLadderCross
  rw [hvector]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul]

/-- The raw outside decomposition, transported to scaled ladder vectors with
explicit nonzero coefficients.  This is the inverse-form input: applying any
linear functional, in particular multiplication by the inverse gap followed
by a dot product, expresses every outside cross through two selected columns. -/
theorem kFour_exists_ladderPairDecomposition_of_cardFour
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4) (target : Fin 6)
    (htarget : target ∉ selected) :
    ∃ left ∈ selected, ∃ right ∈ selected, ∃ leftCoeff rightCoeff : ℝ,
      left ≠ right ∧ leftCoeff ≠ 0 ∧ rightCoeff ≠ 0 ∧
      chartLadderVector kFourDirection point.mass point.weight target
        = leftCoeff • chartLadderVector kFourDirection point.mass
            point.weight left
          + rightCoeff • chartLadderVector kFourDirection point.mass
            point.weight right := by
  obtain ⟨left, hleft, right, hright, hne, hdecomp⟩ :=
    kFour_exists_signedPairDecomposition_of_cardFour selected hcard target htarget
  rcases hdecomp with hsum | hsub | hnegAdd | hnegSub
  · refine ⟨left, hleft, right, hright,
      chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight left,
      chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight right,
      hne, ?_, ?_, ?_⟩
    · exact div_ne_zero
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos target))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos left))
    · exact div_ne_zero
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos target))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos right))
    · simpa using chartLadderVector_eq_pair_of_direction_eq kFourDirection
        point.mass point.weight point.mass_pos point.weight_pos target left right
        1 1 (by simpa using hsum)
  · refine ⟨left, hleft, right, hright,
      chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight left,
      -chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight right,
      hne, ?_, ?_, ?_⟩
    · exact div_ne_zero
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos target))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos left))
    · exact div_ne_zero
        (neg_ne_zero.mpr (ne_of_gt (chartLadderScale_pos point.mass point.weight
          point.mass_pos point.weight_pos target)))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos right))
    · simpa using chartLadderVector_eq_pair_of_direction_eq kFourDirection
        point.mass point.weight point.mass_pos point.weight_pos target left right
        1 (-1) (by simpa [sub_eq_add_neg] using hsub)
  · refine ⟨left, hleft, right, hright,
      -chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight left,
      chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight right,
      hne, ?_, ?_, ?_⟩
    · exact div_ne_zero
        (neg_ne_zero.mpr (ne_of_gt (chartLadderScale_pos point.mass point.weight
          point.mass_pos point.weight_pos target)))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos left))
    · exact div_ne_zero
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos target))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos right))
    · simpa using chartLadderVector_eq_pair_of_direction_eq kFourDirection
        point.mass point.weight point.mass_pos point.weight_pos target left right
        (-1) 1 (by simpa using hnegAdd)
  · refine ⟨left, hleft, right, hright,
      -chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight left,
      -chartLadderScale point.mass point.weight target
          / chartLadderScale point.mass point.weight right,
      hne, ?_, ?_, ?_⟩
    · exact div_ne_zero
        (neg_ne_zero.mpr (ne_of_gt (chartLadderScale_pos point.mass point.weight
          point.mass_pos point.weight_pos target)))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos left))
    · exact div_ne_zero
        (neg_ne_zero.mpr (ne_of_gt (chartLadderScale_pos point.mass point.weight
          point.mass_pos point.weight_pos target)))
        (ne_of_gt (chartLadderScale_pos point.mass point.weight point.mass_pos
          point.weight_pos right))
    · simpa using chartLadderVector_eq_pair_of_direction_eq kFourDirection
        point.mass point.weight point.mass_pos point.weight_pos target left right
        (-1) (-1) (by simpa [sub_eq_add_neg] using hnegSub)

/-- **THE CLOSED OUTSIDE-CROSS SYSTEM.**  At a card-four K4 selection, every
outside column of the inverse-cross matrix is a nontrivial linear combination
of two selected columns, and the same coefficients describe the corresponding
row.  Thus neither stall type has free outside cross terms: all of them are
functions of the selected inverse Gram. -/
theorem kFour_exists_crossPairDecomposition_of_cardFour
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4) (target : Fin 6)
    (htarget : target ∉ selected) :
    ∃ left ∈ selected, ∃ right ∈ selected, ∃ leftCoeff rightCoeff : ℝ,
      left ≠ right ∧ leftCoeff ≠ 0 ∧ rightCoeff ≠ 0 ∧
      (∀ source : Fin 6,
        chartLadderCross kFourDirection point.mass point.weight selected
            target source
          = leftCoeff * chartLadderCross kFourDirection point.mass point.weight
              selected left source
            + rightCoeff * chartLadderCross kFourDirection point.mass
              point.weight selected right source) ∧
      (∀ source : Fin 6,
        chartLadderCross kFourDirection point.mass point.weight selected
            source target
          = leftCoeff * chartLadderCross kFourDirection point.mass point.weight
              selected source left
            + rightCoeff * chartLadderCross kFourDirection point.mass
              point.weight selected source right) := by
  obtain ⟨left, hleft, right, hright, leftCoeff, rightCoeff, hne,
    hleftCoeff, hrightCoeff, hvector⟩ :=
    kFour_exists_ladderPairDecomposition_of_cardFour point selected hcard target
      htarget
  refine ⟨left, hleft, right, hright, leftCoeff, rightCoeff, hne, hleftCoeff,
    hrightCoeff, ?_, ?_⟩
  · intro source
    exact chartLadderCross_left_eq_pair_of_ladderVector_eq kFourDirection
      point.mass point.weight selected target left right source leftCoeff
      rightCoeff hvector
  · intro source
    exact chartLadderCross_right_eq_pair_of_ladderVector_eq kFourDirection
      point.mass point.weight selected source target left right leftCoeff
      rightCoeff hvector

end Gtz
