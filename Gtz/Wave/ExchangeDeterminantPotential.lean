import Gtz.Wave.TwoOutsideRefusalLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The determinant potential of a chart exchange

For a positive-definite selection `C`, replacing `leaving ∈ C` by
`entering ∉ C` changes the gap determinant by the exact multiplier

`cross(leaving, entering)^2 - (pivot(leaving)-1)(1+pivot(entering))`.

This is precisely the strict margin in the master exchange criterion.  Thus
the exchange graph carries a multiplicative potential, not merely a Boolean
edge relation.  Reversing a positive exchange has reciprocal multiplier, and
the product of the multipliers around every closed exchange walk is one.

The reciprocal law is the algebra needed by a maximal-margin termination
argument for card-four stall escape.
-/

namespace Gtz

open Finset Matrix

/-- The determinant multiplier attached to replacing `leaving` by `entering`
at one chart selection. -/
noncomputable def chartExchangeMultiplier {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size)) (leaving entering : Fin size) : ℝ :=
  chartLadderCross direction mass weight selected leaving entering ^ 2
    - (chartLadderPivot direction mass weight selected leaving - 1)
        * (1 + chartLadderPivot direction mass weight selected entering)

/-- The multiplier is the usual insertion-then-erasure determinant factor. -/
theorem chartExchangeMultiplier_eq_insert_erase_factor {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (_hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    chartExchangeMultiplier direction mass weight selected leaving entering
      = (1 + chartLadderPivot direction mass weight selected entering)
          * (1 - chartLadderPivot direction mass weight
              (insert entering selected) leaving) := by
  have hupdate := chartLadderPivot_insert_cross_update direction mass weight
    hmass hweight selected hentering hpd leaving
  unfold chartExchangeMultiplier
  nlinarith

/-- **THE EXCHANGE DETERMINANT LAW.**  An exchange multiplies the chart-gap
determinant by its master-criterion margin. -/
theorem det_directionChartGap_exchange_eq_mul_multiplier {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight
        (insert entering (selected.erase leaving))).det
      = (directionChartGap direction mass weight selected).det
          * chartExchangeMultiplier direction mass weight selected
              leaving entering := by
  have hne : leaving ≠ entering := by
    rintro rfl
    exact hentering hleaving
  have hbasePD : (directionChartGap direction mass weight
      (insert entering selected)).PosDef :=
    posDef_directionChartGap_of_subset direction mass weight hmass hweight
      (Finset.subset_insert entering selected) hpd
  have hdetErase := det_directionChartGap_erase_eq_det_mul_one_sub_pivot
    direction mass weight hmass hweight (insert entering selected)
      (Finset.mem_insert_of_mem hleaving) hbasePD
  have hdetInsert := det_directionChartGap_insert_eq_det_mul_one_add_pivot
    direction mass weight hmass hweight selected hentering hpd
  rw [← insert_erase_comm_of_ne selected hne] at hdetErase
  rw [hdetInsert] at hdetErase
  rw [hdetErase, chartExchangeMultiplier_eq_insert_erase_factor direction mass
    weight hmass hweight selected hleaving hentering hpd]
  ring

/-- The determinant law recovers the master exchange criterion directly: an
exchange is positive definite exactly when its multiplier is positive. -/
theorem posDef_exchange_iff_multiplier_pos {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (directionChartGap direction mass weight
        (insert entering (selected.erase leaving))).PosDef
      ↔ 0 < chartExchangeMultiplier direction mass weight selected
          leaving entering := by
  rw [posDef_exchange_iff_cross_sq_gt direction mass weight hmass hweight
    selected hleaving hentering hpd]
  unfold chartExchangeMultiplier
  constructor <;> intro h <;> linarith

/-- Set-theoretic involutivity of exchanging `leaving` and `entering`. -/
theorem reverse_exchange_eq {size : ℕ} (selected : Finset (Fin size))
    {leaving entering : Fin size} (hleaving : leaving ∈ selected)
    (hentering : entering ∉ selected) :
    insert leaving ((insert entering (selected.erase leaving)).erase entering)
      = selected := by
  have hne : leaving ≠ entering := by
    rintro rfl
    exact hentering hleaving
  ext label
  by_cases hlabelLeaving : label = leaving
  · subst label
    simp [hleaving, hentering]
  by_cases hlabelEntering : label = entering
  · subst label
    simp [hentering, Ne.symm hne]
  simp [hlabelLeaving, hlabelEntering]

/-- The inserted label belongs to the exchanged selection. -/
theorem entering_mem_exchange {size : ℕ} (selected : Finset (Fin size))
    {leaving entering : Fin size} (_hentering : entering ∉ selected) :
    entering ∈ insert entering (selected.erase leaving) :=
  Finset.mem_insert_self _ _

/-- The erased label does not belong to the exchanged selection. -/
theorem leaving_notMem_exchange {size : ℕ} (selected : Finset (Fin size))
    {leaving entering : Fin size} (hleaving : leaving ∈ selected)
    (hentering : entering ∉ selected) :
    leaving ∉ insert entering (selected.erase leaving) := by
  have hne : leaving ≠ entering := by
    rintro rfl
    exact hentering hleaving
  simp [hne]

/-- **THE RECIPROCAL EXCHANGE LAW.**  Forward and reverse multipliers of a
positive exchange multiply to one. -/
theorem chartExchangeMultiplier_mul_reverse_eq_one {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hpdExchange : (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    chartExchangeMultiplier direction mass weight selected leaving entering
        * chartExchangeMultiplier direction mass weight
            (insert entering (selected.erase leaving)) entering leaving
      = 1 := by
  let exchanged := insert entering (selected.erase leaving)
  have henteringMem : entering ∈ exchanged := Finset.mem_insert_self _ _
  have hleavingOut : leaving ∉ exchanged := by
    have hne : leaving ≠ entering := by
      rintro rfl
      exact hentering hleaving
    simp [exchanged, hne]
  have hforward := det_directionChartGap_exchange_eq_mul_multiplier direction
    mass weight hmass hweight selected hleaving hentering hpd
  have hreverse := det_directionChartGap_exchange_eq_mul_multiplier direction
    mass weight hmass hweight exchanged henteringMem hleavingOut hpdExchange
  have hreverseSet : insert leaving (exchanged.erase entering) = selected := by
    exact reverse_exchange_eq selected hleaving hentering
  change (directionChartGap direction mass weight exchanged).det = _ at hforward
  rw [hreverseSet] at hreverse
  rw [hforward] at hreverse
  have hdetNe : (directionChartGap direction mass weight selected).det ≠ 0 :=
    ne_of_gt hpd.det_pos
  apply (mul_left_cancel₀ hdetNe)
  calc
    (directionChartGap direction mass weight selected).det *
        (chartExchangeMultiplier direction mass weight selected leaving entering
          * chartExchangeMultiplier direction mass weight exchanged entering leaving)
        = ((directionChartGap direction mass weight selected).det
            * chartExchangeMultiplier direction mass weight selected leaving entering)
              * chartExchangeMultiplier direction mass weight exchanged
                  entering leaving := by ring
    _ = (directionChartGap direction mass weight selected).det := hreverse.symm
    _ = (directionChartGap direction mass weight selected).det * 1 := by ring

/-- Every positive exchange has a positive determinant multiplier. -/
theorem chartExchangeMultiplier_pos_of_posDef_exchange {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hpdExchange : (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    0 < chartExchangeMultiplier direction mass weight selected leaving entering :=
  (posDef_exchange_iff_multiplier_pos direction mass weight hmass hweight
    selected hleaving hentering hpd).mp hpdExchange

/-- A positive exchange can always be oriented so that the determinant does
not decrease.  Unless the two determinants agree, one orientation increases
it strictly. -/
theorem chartExchangeMultiplier_eq_one_or_forward_gt_one_or_reverse_gt_one
    {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef)
    (hpdExchange : (directionChartGap direction mass weight
      (insert entering (selected.erase leaving))).PosDef) :
    chartExchangeMultiplier direction mass weight selected leaving entering = 1
      ∨ 1 < chartExchangeMultiplier direction mass weight selected leaving entering
      ∨ 1 < chartExchangeMultiplier direction mass weight
          (insert entering (selected.erase leaving)) entering leaving := by
  have hforwardPos := chartExchangeMultiplier_pos_of_posDef_exchange direction
    mass weight hmass hweight selected hleaving hentering hpd hpdExchange
  have hproduct := chartExchangeMultiplier_mul_reverse_eq_one direction mass
    weight hmass hweight selected hleaving hentering hpd hpdExchange
  rcases lt_trichotomy
      (chartExchangeMultiplier direction mass weight selected leaving entering) 1
      with hsmall | hequal | hbig
  · exact Or.inr (Or.inr (by nlinarith))
  · exact Or.inl hequal
  · exact Or.inr (Or.inl hbig)

/-- Multiplier one is exactly equality of the two gap determinants. -/
theorem chartExchangeMultiplier_eq_one_iff_det_exchange_eq {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (hmass : ∀ label, 0 < mass label) (hweight : ∀ label, 0 < weight label)
    (selected : Finset (Fin size)) {leaving entering : Fin size}
    (hleaving : leaving ∈ selected) (hentering : entering ∉ selected)
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    chartExchangeMultiplier direction mass weight selected leaving entering = 1
      ↔ (directionChartGap direction mass weight
          (insert entering (selected.erase leaving))).det
        = (directionChartGap direction mass weight selected).det := by
  have hdet := det_directionChartGap_exchange_eq_mul_multiplier direction mass
    weight hmass hweight selected hleaving hentering hpd
  have hdetNe : (directionChartGap direction mass weight selected).det ≠ 0 :=
    ne_of_gt hpd.det_pos
  constructor
  · intro hone
    rw [hdet, hone, mul_one]
  · intro heq
    rw [hdet] at heq
    exact (mul_left_cancel₀ hdetNe) (by simpa using heq)

end Gtz
