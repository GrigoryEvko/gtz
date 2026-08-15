import Gtz.Design.ThreeLinesAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The chart reading law and the covering criterion

The chart gap of a selection reads, at any probe, as the selected kappa
readings minus the total mass reading: `sum_{c in C} (m_c/w_c) r_c^2 - sum_c
m_c r_c^2` with `r_c` the probe reading of direction `c`.  On the weight
simplex the total mass reading is a WEIGHTED MEAN of the kappa readings.
Thus the mass reading never exceeds the maximal kappa reading, and it reaches
the maximum only when every kappa reading is equal.

Three consequences, all size-generic:

* **The reading law.**  At every probe some label's kappa reading reaches the
  total mass reading, so every selection through that label reads nonnegative
  there.  No probe direction is negative for all selections at once.
* **The pointwise strictness law.**  If some direction reads nonzero at the
  probe, a selection of two or more labels through a maximal label reads
  STRICTLY positive there.  The flat case dies against the spanning of the
  directions.
* **THE COVERING CRITERION.**  A selection whose labels reach the maximal
  kappa reading at every probe is positive definite outright.  For a spanning
  direction family the criterion needs no tie analysis, no antecedent, and no
  minor computation.

The three-lines instance closes the module: the chart directions span for
every slide, so the target obligation follows from a covering selection at
each chart point.  The obligation's analytic content is now a selection
problem about six explicit quadratic forms.
-/

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-- The general chart quadratic form: selected kappa readings minus the total
mass reading. -/
theorem dotProduct_directionChartGap_mulVec_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe)
      = (∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2)
        - ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2 := by
  rw [directionChartGap, Matrix.sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  · exact Finset.sum_congr rfl fun label _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]

/-- The mass reading of one label is its weight times its kappa reading. -/
theorem massReading_eq_weight_mul_kappaReading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweight : ∀ label, weight label ≠ 0)
    (probe : Fin 3 → ℝ) (label : Fin size) :
    mass label * (direction label ⬝ᵥ probe) ^ 2
      = weight label
        * (mass label / weight label * (direction label ⬝ᵥ probe) ^ 2) := by
  field_simp
  rw [mul_div_assoc, div_self (hweight label), mul_one]

/-- **THE READING LAW.**  The total mass reading is a weighted mean of the
kappa readings, so a maximal kappa reading bounds it. -/
theorem massReading_le_kappaReading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweight : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (probe : Fin 3 → ℝ) {good : Fin size}
    (hmax : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) :
    (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
  calc ∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2
      = ∑ label, weight label
          * (mass label / weight label * (direction label ⬝ᵥ probe) ^ 2) :=
        Finset.sum_congr rfl fun label _ =>
          massReading_eq_weight_mul_kappaReading direction mass weight
            (fun c => ne_of_gt (hweight c)) probe label
    _ ≤ ∑ label, weight label
          * (mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) :=
        Finset.sum_le_sum fun label _ =>
          mul_le_mul_of_nonneg_left (hmax label) (le_of_lt (hweight label))
    _ = mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
        rw [← Finset.sum_mul, hsum, one_mul]

/-- Some label's kappa reading reaches the total mass reading. -/
theorem exists_kappaReading_ge_massReading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweight : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (probe : Fin 3 → ℝ) (hsize : 0 < size) :
    ∃ good : Fin size, (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
  have hnonempty : (Finset.univ : Finset (Fin size)).Nonempty := ⟨⟨0, hsize⟩, mem_univ _⟩
  obtain ⟨good, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun label => mass label / weight label * (direction label ⬝ᵥ probe) ^ 2) hnonempty
  exact ⟨good, massReading_le_kappaReading direction mass weight hweight hsum probe
    fun label => hmax label (mem_univ label)⟩

/-- **The flat law.**  When the mass reading reaches the maximal kappa reading,
every kappa reading equals the maximum. -/
theorem kappaReading_flat_of_massReading_eq (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hweight : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) (probe : Fin 3 → ℝ) {good : Fin size}
    (hmax : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2)
    (heq : (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
      = mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) :
    ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      = mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
  intro label
  by_contra hne
  have hlt : mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 :=
    lt_of_le_of_ne (hmax label) hne
  have hstrict : (∑ c, mass c * (direction c ⬝ᵥ probe) ^ 2)
      < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
    calc ∑ c, mass c * (direction c ⬝ᵥ probe) ^ 2
        = ∑ c, weight c * (mass c / weight c * (direction c ⬝ᵥ probe) ^ 2) :=
          Finset.sum_congr rfl fun c _ =>
            massReading_eq_weight_mul_kappaReading direction mass weight
              (fun d => ne_of_gt (hweight d)) probe c
      _ < ∑ c, weight c * (mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) := by
          refine Finset.sum_lt_sum (fun c _ =>
            mul_le_mul_of_nonneg_left (hmax c) (le_of_lt (hweight c)))
            ⟨label, mem_univ label, ?_⟩
          exact mul_lt_mul_of_pos_left hlt (hweight label)
      _ = mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
          rw [← Finset.sum_mul, hsum, one_mul]
  linarith [heq]

/-- **The nonnegative reading.**  A selection through a maximal label reads
nonnegatively at the probe. -/
theorem dotProduct_directionChartGap_nonneg_of_max_mem (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 ≤ mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (probe : Fin 3 → ℝ) {selected : Finset (Fin size)} {good : Fin size}
    (hmem : good ∈ selected)
    (hmax : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) :
    0 ≤ probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  have hkappaNonneg : ∀ label, 0 ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    fun label => mul_nonneg (div_nonneg (hmass label) (le_of_lt (hweight label))) (sq_nonneg _)
  have hsingle : mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum (fun label _ => hkappaNonneg label) hmem
  have hmean := massReading_le_kappaReading direction mass weight hweight hsum probe hmax
  linarith

/-- **The pointwise strictness law.**  With positive masses, a selection of two
or more labels through a maximal label reads STRICTLY positively at every probe
at which some direction reads nonzero. -/
theorem dotProduct_directionChartGap_pos_of_max_mem (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (probe : Fin 3 → ℝ) {selected : Finset (Fin size)} {good : Fin size}
    (hmem : good ∈ selected) (hcard : 2 ≤ selected.card)
    (hmax : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2)
    {readLabel : Fin size} (hread : direction readLabel ⬝ᵥ probe ≠ 0) :
    0 < probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  have hkappaNonneg : ∀ label, 0 ≤ mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
    fun label => mul_nonneg
      (div_nonneg (le_of_lt (hmass label)) (le_of_lt (hweight label))) (sq_nonneg _)
  have hgoodPos : 0 < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
    have hreadPos : 0 < mass readLabel / weight readLabel
        * (direction readLabel ⬝ᵥ probe) ^ 2 :=
      mul_pos (div_pos (hmass readLabel) (hweight readLabel))
        (by positivity)
    exact lt_of_lt_of_le hreadPos (hmax readLabel)
  have hmean := massReading_le_kappaReading direction mass weight hweight hsum probe hmax
  by_cases hflat : ∀ label, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
      = mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
  · have herase : (selected.erase good).Nonempty := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hmem]; omega)
    obtain ⟨other, hotherErase⟩ := herase
    obtain ⟨hotherNe', hotherMem⟩ := Finset.mem_erase.mp hotherErase
    have hotherNe : good ≠ other := Ne.symm hotherNe'
    have htwo : mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
          + mass other / weight other * (direction other ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
      have hpair : ({good, other} : Finset (Fin size)) ⊆ selected := by
        intro label hlabel
        rcases Finset.mem_insert.mp hlabel with hcase | hcase
        · exact hcase ▸ hmem
        · exact (Finset.mem_singleton.mp hcase) ▸ hotherMem
      calc mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
            + mass other / weight other * (direction other ⬝ᵥ probe) ^ 2
          = ∑ label ∈ ({good, other} : Finset (Fin size)),
              mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 := by
            rw [Finset.sum_insert (Finset.notMem_singleton.mpr hotherNe),
              Finset.sum_singleton]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpair
              fun label _ _ => hkappaNonneg label
    have hother := hflat other
    linarith [hmean, htwo, hgoodPos]
  · push Not at hflat
    obtain ⟨lowLabel, hlow⟩ := hflat
    have hstrict : (∑ label, mass label * (direction label ⬝ᵥ probe) ^ 2)
        < mass good / weight good * (direction good ⬝ᵥ probe) ^ 2 := by
      rcases lt_or_eq_of_le hmean with hcase | hcase
      · exact hcase
      · exact absurd (kappaReading_flat_of_massReading_eq direction mass weight hweight hsum
          probe hmax hcase lowLabel) hlow
    have hsingle : mass good / weight good * (direction good ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ selected, mass label / weight label * (direction label ⬝ᵥ probe) ^ 2 :=
      Finset.single_le_sum (fun label _ => hkappaNonneg label) hmem
    linarith

/-- **THE COVERING CRITERION.**  A selection of two or more labels that reaches
the maximal kappa reading at every probe is positive definite, for any spanning
direction family. -/
theorem posDef_directionChartGap_of_readingCover (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0)
    {selected : Finset (Fin size)} (hcard : 2 ≤ selected.card)
    (hcover : ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
      mass label / weight label * (direction label ⬝ᵥ probe) ^ 2
        ≤ mass good / weight good * (direction good ⬝ᵥ probe) ^ 2) :
    (directionChartGap direction mass weight selected).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose direction mass weight selected)
  · rw [star_trivial]
    obtain ⟨good, hgoodMem, hgoodMax⟩ := hcover probe
    have hread : ∃ readLabel, direction readLabel ⬝ᵥ probe ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (hspan probe hall)
    obtain ⟨readLabel, hreadNe⟩ := hread
    exact dotProduct_directionChartGap_pos_of_max_mem direction mass weight hmass hweight
      hsum probe hgoodMem hcard hgoodMax hreadNe

/-! ## The three-lines instance -/

/-- The three-lines directions span, at every slide: the three vertex
directions are the coordinate axes. -/
theorem threeLinesDirection_span (slide : ℝ) (probe : Fin 3 → ℝ)
    (hzero : ∀ label, threeLinesDirection slide label ⬝ᵥ probe = 0) : probe = 0 := by
  have hfirst := hzero 0
  have hsecond := hzero 1
  have hthird := hzero 3
  simp [threeLinesDirection_zero, threeLinesDirection_one, threeLinesDirection_three,
    dotProduct, Fin.sum_univ_three] at hfirst hsecond hthird
  funext coordIndex
  fin_cases coordIndex
  · simpa using hfirst
  · simpa using hsecond
  · simpa using hthird

/-- **The covering criterion on the three-lines chart.**  At any chart point, a
card-three selection whose labels reach the maximal kappa reading at every
probe is strictly dominating. -/
theorem posDef_directionChartGap_threeLines_of_readingCover (slide : ℝ)
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcard : selected.card = 3)
    (hcover : ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight selected).PosDef :=
  posDef_directionChartGap_of_readingCover (threeLinesDirection slide) point.mass point.weight
    point.mass_pos point.weight_pos point.weight_sum_one (threeLinesDirection_span slide)
    (by omega) hcover

/-- **The chart obligation from covering selections.**  If every chart point
admits a card-three covering selection, the three-lines chart has a strict
triple everywhere — with no antecedent. -/
theorem directionChartHasStrictTriple_threeLines_of_cover (slide : ℝ)
    (hselect : ∀ point : DirectionChartPoint 6, ∃ selected : Finset (Fin 6),
      selected.card = 3 ∧ ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
        point.mass label / point.weight label
            * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
          ≤ point.mass good / point.weight good
            * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2) :
    DirectionChartHasStrictTriple (threeLinesDirection slide) := by
  intro point
  obtain ⟨selected, hcard, hcover⟩ := hselect point
  exact ⟨selected, hcard,
    posDef_directionChartGap_threeLines_of_readingCover slide point hcard hcover⟩

/-- **No probe is negative for every selection.**  At any chart point of any
spanning family of size at least three, every probe has a card-three selection
reading nonnegatively at it. -/
theorem exists_selection_nonneg_reading (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 ≤ mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hthree : 3 ≤ size) (probe : Fin 3 → ℝ) :
    ∃ selected : Finset (Fin size), selected.card = 3 ∧
      0 ≤ probe ⬝ᵥ (directionChartGap direction mass weight selected *ᵥ probe) := by
  have hnonempty : (Finset.univ : Finset (Fin size)).Nonempty :=
    ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨good, _, hgoodMax⟩ := Finset.exists_max_image Finset.univ
    (fun label => mass label / weight label * (direction label ⬝ᵥ probe) ^ 2) hnonempty
  obtain ⟨selected, hsubset, hcard⟩ := Finset.exists_superset_card_eq
    (s := ({good} : Finset (Fin size))) (n := 3) (by simp) (by simpa using hthree)
  refine ⟨selected, hcard, ?_⟩
  exact dotProduct_directionChartGap_nonneg_of_max_mem direction mass weight hmass hweight
    hsum probe (hsubset (Finset.mem_singleton_self good))
    fun label => hgoodMax label (mem_univ label)

end Gtz
