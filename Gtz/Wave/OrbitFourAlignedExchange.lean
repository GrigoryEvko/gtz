import Gtz.Wave.ActiveKernelExchange
import Gtz.Wave.ActiveBlockKernelPromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The only first-four triple omitted by the canonical orbit-four family. -/
def chartOneTwoThree : Finset (Fin 6) := {1, 2, 3}

theorem chartOneTwoThree_card : chartOneTwoThree.card = 3 := by decide

def chartIdentityReorderThree : Fin 3 → Fin 3 := ![0, 1, 2]

theorem chartOrbitFour_principalPick :
    chartFirstFourPickSix ∘ (![0, 1, 3] : Fin 3 → Fin 4)
      = chartZeroOneThree.orderEmbOfFin chartZeroOneThree_card
          ∘ chartIdentityReorderThree := by
  rw [chartZeroOneThree_orderEmb]
  funext index
  fin_cases index <;> rfl

theorem chartOrbitFour_omittedPick :
    chartOneTwoThree.orderEmbOfFin chartOneTwoThree_card
      = chartFirstFourPickSix ∘ (![1, 2, 3] : Fin 3 → Fin 4) := by
  have hordered : chartOneTwoThree.orderEmbOfFin chartOneTwoThree_card
      = (![1, 2, 3] : Fin 3 → Fin 6) := by
    symm
    apply Finset.orderEmbOfFin_unique chartOneTwoThree_card
    · intro index
      fin_cases index <;> simp [chartOneTwoThree]
    · intro first second hlt
      fin_cases first <;> fin_cases second <;> simp_all
  rw [hordered]
  funext index
  fin_cases index <;> rfl

theorem chartOneTwoThree_not_mem_orbitFourFamily :
    chartOneTwoThree ∉ orbitFourFamily := by decide

/-- An aligned exchange in the canonical orbit-four window forces the omitted
triple `123` into the argmax family. -/
theorem chartOneTwoThree_mem_of_orbitFour_aligned_active_exchange
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = orbitFourFamily)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (chartFirstFourShiftedGap point *ᵥ left) 0 = 0)
    (hleftThree : (chartFirstFourShiftedGap point *ᵥ left) 3 = 0)
    (hrightZero : (chartFirstFourShiftedGap point *ᵥ right) 0 = 0)
    (hrightThree : (chartFirstFourShiftedGap point *ᵥ right) 3 = 0)
    (hpairOne : (chartFirstFourShiftedGap point *ᵥ pair) 1 = 0)
    (hpairTwo : (chartFirstFourShiftedGap point *ᵥ pair) 2 = 0) :
    chartOneTwoThree ∈ chartArgmaxFamily point := by
  have hprincipalActive : chartZeroOneThree ∈ chartArgmaxFamily point := by
    rw [hfamily]
    simp [orbitFourFamily, orbitFourBlockZeroOneThree, chartZeroOneThree]
  exact mem_chartArgmaxFamily_of_aligned_active_exchange_reordered point
    chartFirstFourPickSix chartZeroOneThree chartOneTwoThree
    chartZeroOneThree_card chartOneTwoThree_card chartIdentityReorderThree
    (by decide) chartOrbitFour_principalPick (![1, 2, 3] : Fin 3 → Fin 4)
    (by decide) chartOrbitFour_omittedPick hprincipalActive
    left right pair scale u v hpair hpairShape hv hleftZero hleftThree
    hrightZero hrightThree hpairOne hpairTwo

/-- Therefore the canonical orbit-four family cannot carry the aligned phase. -/
theorem false_of_orbitFour_aligned_active_exchange
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = orbitFourFamily)
    (left right pair : Fin 4 → ℝ) (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0)
    (hleftZero : (chartFirstFourShiftedGap point *ᵥ left) 0 = 0)
    (hleftThree : (chartFirstFourShiftedGap point *ᵥ left) 3 = 0)
    (hrightZero : (chartFirstFourShiftedGap point *ᵥ right) 0 = 0)
    (hrightThree : (chartFirstFourShiftedGap point *ᵥ right) 3 = 0)
    (hpairOne : (chartFirstFourShiftedGap point *ᵥ pair) 1 = 0)
    (hpairTwo : (chartFirstFourShiftedGap point *ᵥ pair) 2 = 0) : False := by
  have homitted := chartOneTwoThree_mem_of_orbitFour_aligned_active_exchange
    point hfamily left right pair scale u v hpair hpairShape hv hleftZero
    hleftThree hrightZero hrightThree hpairOne hpairTwo
  rw [hfamily] at homitted
  exact chartOneTwoThree_not_mem_orbitFourFamily homitted

/-- Tight-direction interface for the canonical orbit-four aligned exit. -/
theorem false_of_orbitFour_aligned_tightDirections
    (point : ChartPoint 6 3)
    (hfamily : chartArgmaxFamily point = orbitFourFamily)
    (ambientLeft ambientRight ambientPair : Fin 6 → ℝ)
    (left right pair : Fin 4 → ℝ)
    (hleftSpread : ambientLeft = selectionInjection chartFirstFourPickSix *ᵥ left)
    (hrightSpread : ambientRight = selectionInjection chartFirstFourPickSix *ᵥ right)
    (hpairSpread : ambientPair = selectionInjection chartFirstFourPickSix *ᵥ pair)
    (hleftTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartZeroOneThree ambientLeft)
    (hrightTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartZeroTwoThree ambientRight)
    (hpairTight : IsChartTightDirection point.chart point.weight
      (chartObjective point) chartZeroOneTwo ambientPair)
    (scale u v : ℝ)
    (hpair : pair = right - scale • left)
    (hpairShape : pair = (![0, u, v, 0] : Fin 4 → ℝ))
    (hv : v ≠ 0) : False := by
  have hpickInjective : Function.Injective chartFirstFourPickSix := by decide
  have hleftZero : (chartFirstFourShiftedGap point *ᵥ left) 0 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroOneThree ambientLeft left
      hleftSpread hleftTight 0 (by simp [chartFirstFourPickSix, chartZeroOneThree])
  have hleftThree : (chartFirstFourShiftedGap point *ᵥ left) 3 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroOneThree ambientLeft left
      hleftSpread hleftTight 3 (by simp [chartFirstFourPickSix, chartZeroOneThree])
  have hrightZero : (chartFirstFourShiftedGap point *ᵥ right) 0 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroTwoThree ambientRight right
      hrightSpread hrightTight 0 (by simp [chartFirstFourPickSix, chartZeroTwoThree])
  have hrightThree : (chartFirstFourShiftedGap point *ᵥ right) 3 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroTwoThree ambientRight right
      hrightSpread hrightTight 3 (by simp [chartFirstFourPickSix, chartZeroTwoThree])
  have hpairOne : (chartFirstFourShiftedGap point *ᵥ pair) 1 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroOneTwo ambientPair pair
      hpairSpread hpairTight 1 (by simp [chartFirstFourPickSix, chartZeroOneTwo])
  have hpairTwo : (chartFirstFourShiftedGap point *ᵥ pair) 2 = 0 := by
    exact shiftedFourWindow_mulVec_eq_zero_of_isChartTightDirection point
      chartFirstFourPickSix hpickInjective chartZeroOneTwo ambientPair pair
      hpairSpread hpairTight 2 (by simp [chartFirstFourPickSix, chartZeroOneTwo])
  exact false_of_orbitFour_aligned_active_exchange point hfamily left right pair
    scale u v hpair hpairShape hv hleftZero hleftThree hrightZero hrightThree
    hpairOne hpairTwo


end Gtz
