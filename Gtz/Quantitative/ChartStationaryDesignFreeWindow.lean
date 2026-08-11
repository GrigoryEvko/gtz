/-
# The chart stationarity value window, DESIGN-FREE, and the sharpness of its upper face

This module is the MERGED first-order value layer.  It carries three things.

**ONE — the design leaf, and what removing it buys.**  A chart stationarity datum
IS a chart point: every field of `Gtz.ChartPoint` is a field of
`Gtz.IsChartStationaryData`, and `Gtz.chartPointHasDesign` is an UNCONDITIONAL
theorem, so the `design` and `projection = projectionOfDesign design` hypotheses
carried by the whole value-floor layer are REDUNDANT.  Thirty-eight declarations
across eleven files carry that pair.

**TWO — the SHARP design-free floor.**  The redundancy is applied to
`Gtz.combinedValueFloor_le_value_of_isChartStationaryData`, which is at least as
good as its Cauchy-Binet parent at every cell
(`Gtz.cauchyBinetValueFloor_le_combinedValueFloor`).  At `(6, 3)` that is
`-4/27`, not `-3/20`; at `(7, 3)` it is `-10/77`, not `-2/15`.

**THREE — the upper face of the window is SHARP, and the strict form is FALSE.**
The landed `Gtz.value_le_one_sub_weight_of_isChartStationaryData` gives
`value + weight c ≤ 1`.  The strict form is NOT a theorem of the bundle: the
identity chart at `size = rank = 4` is a stationarity datum, is an argmax datum,
and attains `value + weight c = 1` at every atom.  So any strict form must
consume a hypothesis the bundle does not carry.  Two candidates, both free on the
route: `value < 0`, and `rank < size`.  The first is landed; the second is not
tested here.

SCOPE, STATED ONCE.  Every floor in this file is a statement about the NEGATIVE
value stratum, and that stratum is conjecturally empty: if `Gtz.GtzWeighted` holds
at the cell then an admissible datum has a nonnegative value and every floor here
is vacuously true.  Sharpening a floor is therefore a statement about the shape of
a counterexample, never a step towards excluding one.
-/
import Mathlib
import Gtz.Quantitative.ElementaryValueFloor
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Reduction.ChartPointFactorisation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
  {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The design leaf -/

/-- **A stationarity datum already IS a chart point.**  Seven fields, all of them
fields of the bundle. -/
noncomputable def chartPointOfIsChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) : ChartPoint size rank where
  chart := projection
  weight := weight
  isSymmetric := hdata.isSymmetric
  isIdempotent := hdata.isIdempotent
  hasTraceRank := hdata.hasTraceRank
  weight_nonneg := fun atomIndex => (hdata.weight_pos atomIndex).le
  weight_sum_one := hdata.weight_sum_one

/-- **THE DESIGN HYPOTHESIS IS REDUNDANT.**  The datum is a chart point with
strictly positive weights, and `Gtz.chartPointHasDesign` realises every such point
as a design, unconditionally. -/
theorem exists_design_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    ∃ design : WeightedDesign size rank, projection = projectionOfDesign design := by
  obtain ⟨design, hpoint⟩ :=
    chartPointHasDesign size rank (chartPointOfIsChartStationaryData hdata) hdata.weight_pos
  exact ⟨design, (congrArg (fun somePoint => ChartPoint.chart somePoint) hpoint).symm⟩

/-! ## The sharp design-free floor -/

/-- **THE COMBINED FLOOR, DESIGN-FREE.**  At least as good as the Cauchy-Binet
floor at every cell, by `Gtz.cauchyBinetValueFloor_le_combinedValueFloor`. -/
theorem combinedValueFloor_le_value_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    combinedValueFloor size rank ≤ value := by
  obtain ⟨design, hchart⟩ := exists_design_of_isChartStationaryData hdata
  exact combinedValueFloor_le_value_of_isChartStationaryData design hchart hargmax hdata

/-- **`-4/27` AT `(6,3)`, DESIGN-FREE.**  Strictly sharper than the design-free
Cauchy-Binet floor `-3/20` at the same cell and off the same hypotheses. -/
theorem neg_four_div_twentySeven_le_value_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hsize : size = 6) (hrank : rank = 3) :
    -(4 / 27 : ℝ) ≤ value := by
  obtain ⟨design, hchart⟩ := exists_design_of_isChartStationaryData hdata
  exact neg_four_div_twentySeven_le_value_of_isChartStationaryData design hchart hargmax hdata
    hsize hrank

/-- **`-10/77` AT `(7,3)`, DESIGN-FREE.**  Sharper than the design-free
Cauchy-Binet floor `-2/15` at that cell. -/
theorem neg_ten_div_seventySeven_le_value_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hsize : size = 7) (hrank : rank = 3) :
    -(10 / 77 : ℝ) ≤ value := by
  obtain ⟨design, hchart⟩ := exists_design_of_isChartStationaryData hdata
  exact neg_ten_div_seventySeven_le_value_of_isChartStationaryData design hchart hargmax hdata
    hsize hrank

/-- **THE FLOOR IS NEVER ATTAINED, DESIGN-FREE.** -/
theorem value_ne_neg_inv_size_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    value ≠ -((size : ℝ))⁻¹ := by
  intro hendpoint
  obtain ⟨design, hchart⟩ := exists_design_of_isChartStationaryData hdata
  exact not_isChartStationaryData_of_value_eq_neg_inv_size design hchart hargmax hendpoint hdata

/-- **`-1/size < value` STRICTLY, DESIGN-FREE.** -/
theorem neg_inv_size_lt_value_of_isChartStationaryData_designFree
    (hargmax : IsChartArgmaxValue rank projection weight value)
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    -((size : ℝ))⁻¹ < value :=
  lt_of_le_of_ne (neg_inv_size_le_value_of_isChartStationaryData hdata)
    fun hendpoint =>
      value_ne_neg_inv_size_of_isChartStationaryData_designFree hargmax hdata hendpoint.symm

/-! ## The two faces of the weight window -/

/-- **THE WEIGHT CAP.**  The shipped floor `-value ≤ t_d` holds at the other
`size - 1` atoms, so they claim `(size - 1)(-value)` of the unit budget and the
chosen atom cannot exceed the remainder. -/
theorem weight_le_one_add_pred_size_mul_value_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    weight atomIndex ≤ 1 + ((size : ℝ) - 1) * value := by
  classical
  have hsizePos : 0 < size := size_pos_of_isChartStationaryData hdata
  have hsplit : weight atomIndex + ∑ other ∈ Finset.univ.erase atomIndex, weight other = 1 := by
    rw [Finset.add_sum_erase _ weight (Finset.mem_univ atomIndex)]
    exact hdata.weight_sum_one
  have hcard : (Finset.univ.erase atomIndex).card = size - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), Finset.card_univ, Fintype.card_fin]
  have hcast : ((size - 1 : ℕ) : ℝ) = (size : ℝ) - 1 := by
    rw [Nat.cast_sub hsizePos, Nat.cast_one]
  have hbelow : ∀ other ∈ Finset.univ.erase atomIndex, -value ≤ weight other :=
    fun other _ => weight_ge_neg_value_of_isChartStationaryData hdata other
  have hsum :=
    Finset.card_nsmul_le_sum (Finset.univ.erase atomIndex) weight (-value) hbelow
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  nlinarith [hsum, hsplit]

/-- **THE WEIGHT WINDOW.**  Both faces at once. -/
theorem weight_mem_window_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (atomIndex : Fin size) :
    -value ≤ weight atomIndex ∧ weight atomIndex ≤ 1 + ((size : ℝ) - 1) * value :=
  ⟨weight_ge_neg_value_of_isChartStationaryData hdata atomIndex,
    weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata atomIndex⟩

/-- **THE UPPER FACE IS STRICT AT A NEGATIVE VALUE.**  This is the half of the
strict dual bound that is free, and it is free exactly because a weight is below
one and the value is below zero. -/
theorem value_add_weight_lt_one_of_isChartStationaryData_of_neg
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0) (atomIndex : Fin size) :
    value + weight atomIndex < 1 := by
  have hcap := weight_le_one_add_pred_size_mul_value_of_isChartStationaryData hdata atomIndex
  have hsizePos : 0 < size := size_pos_of_isChartStationaryData hdata
  have hsizeOne : (1 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsizePos
  nlinarith [hcap, hnegative, hsizeOne]

/-! ## The lower face of the window is ATTAINED, at a landed object -/

/-- **THE EQUALITY CASE OF THE CAP IS INHABITED BY A LANDED, MECHANIZED DATUM.**
The shipped `(6,3)` two-block stationarity datum has value `-1/6` and uniform
weights `1/6`, and `1 + (6 - 1) * (-1/6) = 1/6`, so the cap holds with EQUALITY at
every atom.  The floor face `-value ≤ t_c` reads `1/6 ≤ 1/6` there as well: at the
endpoint value `-1/size` the two faces of the window PINCH, which is the landed
`Gtz.weight_eq_inv_size_of_value_eq_neg_inv_size` seen from the other side. -/
theorem chartTwoBlockTripleWeight_eq_cap (atomIndex : Fin 6) :
    chartTwoBlockTripleWeight atomIndex = 1 + ((6 : ℝ) - 1) * (-(6 : ℝ)⁻¹) := by
  norm_num [chartTwoBlockTripleWeight]

/-- The cap itself, instantiated at that landed datum: the bound is TIGHT, and the
tightness is machine-checked rather than asserted. -/
theorem chartTwoBlockTripleWeight_le_cap (atomIndex : Fin 6) :
    chartTwoBlockTripleWeight atomIndex ≤ 1 + ((6 : ℝ) - 1) * (-(6 : ℝ)⁻¹) := by
  have hcap :=
    weight_le_one_add_pred_size_mul_value_of_isChartStationaryData
      chartTwoBlockTripleProjection_isChartStationaryData atomIndex
  norm_num at hcap ⊢
  exact hcap

/-! ## The identity chart: the upper face is ATTAINED, so the strict form is FALSE -/

/-- The uniform weights of the identity chart at size four. -/
noncomputable def identityChartWeight : Fin 4 → ℝ := fun _ => (4 : ℝ)⁻¹

/-- The single active subset of the identity chart: all four atoms. -/
def identityChartSubset : Unit → Finset (Fin 4) := fun _ => Finset.univ

/-- The single multiplier of the identity chart. -/
def identityChartMultiplierWeight : Unit → ℝ := fun _ => 1

/-- The single tight direction of the identity chart, with every entry `1/2`. -/
noncomputable def identityChartTightDir : Unit → (Fin 4 → ℝ) := fun _ _ => (2 : ℝ)⁻¹

/-- **THE IDENTITY CHART IS A STATIONARITY DATUM.**  `P = 1` at `size = rank = 4`
is symmetric, idempotent and of trace four; the gap is `(3/4) • 1`, so every unit
vector is tight at `value = 3/4`; the assembly is `(1/4) • 1`, whose diagonal is
the required `1/size` and which commutes with everything. -/
theorem identityChart_isChartStationaryData :
    IsChartStationaryData 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) identityChartWeight (3 / 4)
      (Finset.univ : Finset Unit) identityChartSubset identityChartMultiplierWeight
      identityChartTightDir where
  isSymmetric := Matrix.transpose_one
  isIdempotent := Matrix.one_mul 1
  hasTraceRank := by simp
  weight_pos := by intro atomIndex; norm_num [identityChartWeight]
  weight_sum_one := by simp [identityChartWeight]
  activeWeight_nonneg := by intro activeLabel _; norm_num [identityChartMultiplierWeight]
  activeWeight_sum_one := by simp [identityChartMultiplierWeight]
  activeSubset_card := by intro activeLabel _; simp [identityChartSubset]
  tightDir_unit := by
    intro activeLabel _
    simp [identityChartTightDir, dotProduct]
    norm_num
  tightDir_support := by
    intro activeLabel _ atomIndex hnotMem
    simp [identityChartSubset] at hnotMem
  tightDir_isTight := by
    intro activeLabel _ atomIndex _
    simp [chartStationaryGap, identityChartTightDir, identityChartWeight,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_diagonal]
    norm_num
  assembly_diagonal := by
    intro atomIndex
    simp [chartMultiplierAssembly, identityChartMultiplierWeight, identityChartTightDir,
      atomMatrix, Matrix.vecMulVec_apply]
    norm_num
  assembly_commutes := by
    rw [Matrix.one_mul, Matrix.mul_one]

/-- **AND IT IS AN ARGMAX DATUM.**  At `rank = size` the only subset of the right
cardinality is everything, and the first coordinate vector is a probe realising
the value. -/
theorem identityChart_isChartArgmaxValue :
    IsChartArgmaxValue 4 (1 : Matrix (Fin 4) (Fin 4) ℝ) identityChartWeight (3 / 4) := by
  intro chosenSubset hcard
  have huniversal : chosenSubset = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard)
  subst huniversal
  refine ⟨fun atomIndex => if atomIndex = 0 then 1 else 0, ?_, ?_, ?_⟩
  · simp [dotProduct]
  · intro atomIndex hnotMem
    simp at hnotMem
  · simp [chartStationaryGap, identityChartWeight, dotProduct, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_diagonal]
    norm_num

/-- **THE UPPER FACE IS ATTAINED.**  `value + weight c = 1` at every atom of the
identity chart. -/
theorem identityChart_value_add_weight_eq_one (atomIndex : Fin 4) :
    (3 / 4 : ℝ) + identityChartWeight atomIndex = 1 := by
  norm_num [identityChartWeight]

/-- **THE STRICT DUAL BOUND IS NOT A THEOREM OF THE BUNDLE.**  Stated as the
negation of the schema at a fixed size, with the active index type fixed to `Unit`:
no strengthening of `Gtz.value_le_one_sub_weight_of_isChartStationaryData` to a
strict inequality can hold of `Gtz.IsChartStationaryData` alone, even with
`Gtz.IsChartArgmaxValue` supplied.  The witness has `rank = size` and a positive
value; both `value < 0` and `rank < size` remain available as repairs, and the
first is proved above. -/
theorem not_forall_value_add_weight_lt_one_of_isChartStationaryData :
    ¬ ∀ (rankArgument : ℕ) (projectionArgument : Matrix (Fin 4) (Fin 4) ℝ)
        (weightArgument : Fin 4 → ℝ) (valueArgument : ℝ) (activeSetArgument : Finset Unit)
        (activeSubsetArgument : Unit → Finset (Fin 4)) (activeWeightArgument : Unit → ℝ)
        (tightDirArgument : Unit → (Fin 4 → ℝ)),
        IsChartStationaryData rankArgument projectionArgument weightArgument valueArgument
            activeSetArgument activeSubsetArgument activeWeightArgument tightDirArgument →
          IsChartArgmaxValue rankArgument projectionArgument weightArgument valueArgument →
            ∀ atomIndex : Fin 4, valueArgument + weightArgument atomIndex < 1 := by
  intro hstrict
  have hattained :=
    hstrict 4 1 identityChartWeight (3 / 4) Finset.univ identityChartSubset
      identityChartMultiplierWeight identityChartTightDir identityChart_isChartStationaryData
      identityChart_isChartArgmaxValue 0
  rw [identityChart_value_add_weight_eq_one] at hattained
  exact absurd hattained (lt_irrefl 1)

end Gtz
