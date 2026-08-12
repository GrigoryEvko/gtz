import Gtz.Wave.AssemblyMinimalSupport
import Gtz.Quantitative.AssemblyRankSplit
import Gtz.Quantitative.StrongStationarityIndexFloor
import Gtz.Reduction.Crystallization

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The support cap — `2 |S| ≤ r (r + 1)` at a support-minimal datum

The positive tight directions of a stationary datum span EXACTLY the assembly's
range: one inclusion is the landed span bound, and the other is the
positive-semidefinite kernel argument — a kernel vector of `Ξ` annihilates
every positively weighted tight direction, so each such direction lies in the
orthogonal complement of the kernel, which for a symmetric matrix IS the range.

The constraint columns `q_C q_Cᵀ` of the positive support therefore live in the
span of the symmetrised pair products of any basis of `range Ξ` — a space with
`r (r + 1) / 2` generators.  At a support-minimal datum the columns are
independent, so the support size obeys `2 |S| ≤ r (r + 1)`.  Against the rank
survivor list this reads: at most TEN positive blocks at assembly rank four,
FIFTEEN at rank five, TWENTY-ONE at rank six — against the count ladder's
ceiling of twenty at every rank.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.dotProduct_tightDir_eq_zero_of_multiplier_mulVec_eq_zero` — a kernel
  vector of the assembly annihilates every positively weighted tight direction.
* `Gtz.tightDir_mem_range_multiplier_of_pos` — **THE RANGE MEMBERSHIP.**  A
  positively weighted tight direction lies in `range Ξ`.  New: the landed facts
  ran only in the other direction.
* `Gtz.range_multiplier_eq_span_positive_tightDir` — **THE EXACT SPAN LAW.**
  `range Ξ` EQUALS the span of the positive tight directions.
* `Gtz.atomMatrix_sum_smul` and `Gtz.atomMatrix_mem_span_symPair` — the
  symmetrised decomposition of a spanned atom matrix.
* `Gtz.two_mul_card_le_of_independent_atomMatrix_of_mem_span` — the generic
  count: independent atom matrices drawn from a `dimension`-spanned family
  number at most `dimension * (dimension + 1) / 2`.
* `Gtz.two_mul_card_positiveActiveSet_le_of_independent` — the datum form of
  the cap, at every `(size, rank)`.
* `Gtz.SixThreeCrux.exists_multiplier_independent_two_mul_card_le` and
  `Gtz.SixThreeCrux.exists_multiplier_card_positiveActiveSet_le_twentyOne` —
  the crux packaging: a `(6,3)` counterexample carries a support-minimal datum
  whose positive support obeys the cap, hence has at most twenty-one members.

## Vacuity

The crux corollaries are vacuous if `Gtz.GtzWeighted 6 3` holds.  The generic
theorems are not: they hold at every stationary datum.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-! ## The kernel annihilation and the range membership -/

/-- A kernel vector of the assembly annihilates every positively weighted tight
direction: the quadratic form of `Ξ` at the vector is the multiplier-weighted
sum of squared pairings, and every summand is nonnegative. -/
theorem dotProduct_tightDir_eq_zero_of_multiplier_mulVec_eq_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {direction : Fin size → ℝ}
    (hkernel : chartMultiplierAssembly activeSet activeWeight tightDir *ᵥ direction = 0)
    {index : activeIndex} (hmem : index ∈ activeSet) (hpos : 0 < activeWeight index) :
    tightDir index ⬝ᵥ direction = 0 := by
  have hquadZero : direction ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
      *ᵥ direction) = 0 := by
    rw [hkernel, dotProduct_zero]
  have hexpand : direction ⬝ᵥ (chartMultiplierAssembly activeSet activeWeight tightDir
        *ᵥ direction)
      = ∑ label ∈ activeSet, activeWeight label * (tightDir label ⬝ᵥ direction) ^ 2 := by
    rw [chartMultiplierAssembly, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, dotProduct_comm direction (tightDir label)]
    ring
  rw [hexpand] at hquadZero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun label hlabelMem =>
    mul_nonneg (hdata.activeWeight_nonneg label hlabelMem) (sq_nonneg _)).mp
    hquadZero index hmem
  rcases mul_eq_zero.mp hterm with hzero | hzero
  · exact absurd hzero (ne_of_gt hpos)
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero

/-- **THE RANGE MEMBERSHIP.**  A positively weighted tight direction lies in
the range of the assembly.  The assembly is symmetric, so the orthogonal
complement of its kernel is its range, and the kernel annihilation puts the
direction there. -/
theorem tightDir_mem_range_multiplier_of_pos
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {index : activeIndex} (hmem : index ∈ activeSet) (hpos : 0 < activeWeight index) :
    tightDir index ∈ LinearMap.range (Matrix.toLin'
      (chartMultiplierAssembly activeSet activeWeight tightDir)) := by
  classical
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hsymm : assemblyᵀ = assembly :=
    transpose_chartMultiplierAssembly_of_isChartStationaryData hdata
  let B : LinearMap.BilinForm ℝ (Fin size → ℝ) := dotProductBilin ℝ ℝ
  let rangeSpace := LinearMap.range (Matrix.toLin' assembly)
  show tightDir index ∈ rangeSpace
  rw [← B.orthogonal_orthogonal dotProductBilin_nondegenerate dotProductBilin_isRefl
    rangeSpace, LinearMap.BilinForm.mem_orthogonal_iff]
  intro direction hdirection
  have hkernelVec : assembly *ᵥ direction = 0 := by
    funext coordinate
    have hrangeMem : Matrix.toLin' assembly (Pi.single coordinate 1) ∈ rangeSpace :=
      LinearMap.mem_range.mpr ⟨Pi.single coordinate 1, rfl⟩
    have hzero := LinearMap.BilinForm.mem_orthogonal_iff.mp hdirection _ hrangeMem
    have hzeroDot : (assembly *ᵥ Pi.single coordinate 1) ⬝ᵥ direction = 0 := by
      have hunfold : B (Matrix.toLin' assembly (Pi.single coordinate 1)) direction
          = (assembly *ᵥ Pi.single coordinate 1) ⬝ᵥ direction := by
        simp only [B, dotProductBilin_apply_apply, Matrix.toLin'_apply]
      rw [← hunfold]
      exact hzero
    have hentry : (assembly *ᵥ direction) coordinate
        = (assembly *ᵥ Pi.single coordinate 1) ⬝ᵥ direction := by
      calc (assembly *ᵥ direction) coordinate
          = (assembly *ᵥ direction) ⬝ᵥ Pi.single coordinate 1 := by
            rw [dotProduct_single, mul_one]
        _ = Pi.single coordinate 1 ⬝ᵥ (assembly *ᵥ direction) := dotProduct_comm _ _
        _ = (Pi.single coordinate 1 ᵥ* assembly) ⬝ᵥ direction :=
            Matrix.dotProduct_mulVec _ _ _
        _ = (assemblyᵀ *ᵥ Pi.single coordinate 1) ⬝ᵥ direction := by
            rw [Matrix.mulVec_transpose]
        _ = (assembly *ᵥ Pi.single coordinate 1) ⬝ᵥ direction := by rw [hsymm]
    rw [Pi.zero_apply, hentry]
    exact hzeroDot
  have hannihilate : B direction (tightDir index) = 0 := by
    simp only [B, dotProductBilin_apply_apply]
    rw [dotProduct_comm]
    exact dotProduct_tightDir_eq_zero_of_multiplier_mulVec_eq_zero hdata hkernelVec hmem hpos
  exact hannihilate

/-- **THE EXACT SPAN LAW.**  The assembly's range equals the span of the
positively weighted tight directions.  The landed
`Gtz.range_multiplier_le_span_positive_tightDir` is one inclusion, and the
range membership is the other. -/
theorem range_multiplier_eq_span_positive_tightDir
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    LinearMap.range (Matrix.toLin' (chartMultiplierAssembly activeSet activeWeight tightDir))
      = Submodule.span ℝ (↑((positiveActiveSet activeSet activeWeight).image tightDir)
          : Set (Fin size → ℝ)) := by
  classical
  apply le_antisymm
  · have hfilterEq : activeSet.filter (fun label => activeWeight label ≠ 0)
        = positiveActiveSet activeSet activeWeight := by
      rw [positiveActiveSet]
      refine Finset.filter_congr fun label hmem => ?_
      constructor
      · intro hne
        exact lt_of_le_of_ne (hdata.activeWeight_nonneg label hmem) (Ne.symm hne)
      · intro hpos
        exact ne_of_gt hpos
    have hlanded := range_multiplier_le_span_positive_tightDir activeSet activeWeight tightDir
    rw [hfilterEq] at hlanded
    exact hlanded
  · rw [Submodule.span_le]
    intro vec hvec
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hvec
    obtain ⟨label, hlabelMem, rfl⟩ := hvec
    obtain ⟨hlabelActive, hlabelPos⟩ := mem_positiveActiveSet.mp hlabelMem
    exact tightDir_mem_range_multiplier_of_pos hdata hlabelActive hlabelPos

/-! ## The symmetrised decomposition -/

/-- The atom matrix of a combination expands as the coefficient-weighted double
sum of pair products. -/
theorem atomMatrix_sum_smul {size dimension : ℕ}
    (base : Fin dimension → (Fin size → ℝ)) (coeff : Fin dimension → ℝ) :
    atomMatrix (∑ basisIndex, coeff basisIndex • base basisIndex)
      = ∑ leftIndex, ∑ rightIndex, (coeff leftIndex * coeff rightIndex)
          • Matrix.vecMulVec (base leftIndex) (base rightIndex) := by
  ext row col
  simp only [atomMatrix, Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun leftIndex _ => Finset.sum_congr rfl fun rightIndex _ => ?_
  ring

/-- **THE SYMMETRISED MEMBERSHIP.**  The atom matrix of a vector inside a span
lies in the span of the symmetrised pair products of the spanning family: pair
each term of the double sum with its transpose partner. -/
theorem atomMatrix_mem_span_symPair {size dimension : ℕ}
    (base : Fin dimension → (Fin size → ℝ)) (vec : Fin size → ℝ)
    (hmem : vec ∈ Submodule.span ℝ (Set.range base)) :
    atomMatrix vec ∈ Submodule.span ℝ (Set.range
      fun pair : {p : Fin dimension × Fin dimension // p.1 ≤ p.2} =>
        Matrix.vecMulVec (base pair.1.1) (base pair.1.2)
          + Matrix.vecMulVec (base pair.1.2) (base pair.1.1)) := by
  classical
  obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hproduct : atomMatrix vec
      = ∑ pair : Fin dimension × Fin dimension,
          (coeff pair.1 * coeff pair.2)
            • Matrix.vecMulVec (base pair.1) (base pair.2) := by
    rw [← hcoeff, atomMatrix_sum_smul]
    exact (Fintype.sum_prod_type (f := fun pair : Fin dimension × Fin dimension =>
      (coeff pair.1 * coeff pair.2)
        • Matrix.vecMulVec (base pair.1) (base pair.2))).symm
  have hswap : ∑ pair : Fin dimension × Fin dimension,
        (coeff pair.1 * coeff pair.2) • Matrix.vecMulVec (base pair.1) (base pair.2)
      = ∑ pair : Fin dimension × Fin dimension,
          (coeff pair.1 * coeff pair.2) • Matrix.vecMulVec (base pair.2) (base pair.1) := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin dimension) (Fin dimension)) _ _ ?_
    intro pair
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [mul_comm]
  have hcombine : ∑ pair : Fin dimension × Fin dimension,
        ((coeff pair.1 * coeff pair.2) / 2)
          • (Matrix.vecMulVec (base pair.1) (base pair.2)
            + Matrix.vecMulVec (base pair.2) (base pair.1))
      = ∑ pair : Fin dimension × Fin dimension,
          (coeff pair.1 * coeff pair.2)
            • Matrix.vecMulVec (base pair.1) (base pair.2) := by
    have hterm : ∀ pair : Fin dimension × Fin dimension,
        ((coeff pair.1 * coeff pair.2) / 2)
            • (Matrix.vecMulVec (base pair.1) (base pair.2)
              + Matrix.vecMulVec (base pair.2) (base pair.1))
          = (2⁻¹ : ℝ) • ((coeff pair.1 * coeff pair.2)
                • Matrix.vecMulVec (base pair.1) (base pair.2))
            + (2⁻¹ : ℝ) • ((coeff pair.1 * coeff pair.2)
                • Matrix.vecMulVec (base pair.2) (base pair.1)) := by
      intro pair
      rw [smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [Finset.sum_congr rfl fun pair _ => hterm pair, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← Finset.smul_sum, ← hswap, ← add_smul,
      show (2⁻¹ + 2⁻¹ : ℝ) = 1 from by norm_num, one_smul]
  rw [hproduct, ← hcombine]
  refine Submodule.sum_mem _ fun pair _ => Submodule.smul_mem _ _ ?_
  rcases le_total pair.1 pair.2 with hle | hle
  · exact Submodule.subset_span ⟨⟨pair, hle⟩, rfl⟩
  · rw [add_comm]
    exact Submodule.subset_span ⟨⟨(pair.2, pair.1), hle⟩, rfl⟩

/-- **THE GENERIC COUNT.**  Independent atom matrices drawn from a family
spanned by `dimension` vectors number at most `dimension * (dimension + 1) / 2`,
stated multiplication-side to keep the arithmetic in `ℕ` exact. -/
theorem two_mul_card_le_of_independent_atomMatrix_of_mem_span
    {size dimension : ℕ} {label : Type*}
    (base : Fin dimension → (Fin size → ℝ)) (vec : label → (Fin size → ℝ))
    (support : Finset label)
    (hspan : ∀ index ∈ support, vec index ∈ Submodule.span ℝ (Set.range base))
    (hindependent : LinearIndependent ℝ
      (fun index : {index // index ∈ support} => atomMatrix (vec index.1))) :
    2 * support.card ≤ dimension * (dimension + 1) := by
  classical
  have hcardEq : support.card = Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun index : {index // index ∈ support} => atomMatrix (vec index.1))) := by
    rw [finrank_span_eq_card hindependent, Fintype.card_coe]
  have hspanLe : Submodule.span ℝ
        (Set.range fun index : {index // index ∈ support} => atomMatrix (vec index.1))
      ≤ Submodule.span ℝ (Set.range
          fun pair : {p : Fin dimension × Fin dimension // p.1 ≤ p.2} =>
            Matrix.vecMulVec (base pair.1.1) (base pair.1.2)
              + Matrix.vecMulVec (base pair.1.2) (base pair.1.1)) := by
    rw [Submodule.span_le]
    rintro matrix ⟨index, rfl⟩
    exact atomMatrix_mem_span_symPair base (vec index.1) (hspan index.1 index.2)
  have hgeneratorCount : Module.finrank ℝ (Submodule.span ℝ (Set.range
        fun pair : {p : Fin dimension × Fin dimension // p.1 ≤ p.2} =>
          Matrix.vecMulVec (base pair.1.1) (base pair.1.2)
            + Matrix.vecMulVec (base pair.1.2) (base pair.1.1)))
      ≤ dimension * (dimension + 1) / 2 := by
    have hrangeEq : (Set.range
          fun pair : {p : Fin dimension × Fin dimension // p.1 ≤ p.2} =>
            Matrix.vecMulVec (base pair.1.1) (base pair.1.2)
              + Matrix.vecMulVec (base pair.1.2) (base pair.1.1))
        = ↑(Finset.univ.image
            fun pair : {p : Fin dimension × Fin dimension // p.1 ≤ p.2} =>
              Matrix.vecMulVec (base pair.1.1) (base pair.1.2)
                + Matrix.vecMulVec (base pair.1.2) (base pair.1.1)) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hrangeEq]
    refine le_trans (finrank_span_finset_le_card (R := ℝ) _) ?_
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_univ, card_orderedPairs]
  have hcardLe : support.card ≤ dimension * (dimension + 1) / 2 := by
    rw [hcardEq]
    exact (Submodule.finrank_mono hspanLe).trans hgeneratorCount
  have heven : dimension * (dimension + 1) / 2 * 2 = dimension * (dimension + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self dimension).two_dvd
  omega

/-! ## The datum form of the cap -/

/-- **THE SUPPORT CAP.**  At a stationary datum whose positive constraint
columns are independent, twice the positive support size is at most
`r (r + 1)`, for `r` the assembly rank.  The columns live in the symmetrised
pair span of a basis of `range Ξ`, because every positive tight direction lies
in `range Ξ`. -/
theorem two_mul_card_positiveActiveSet_le_of_independent
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (hindependent : LinearIndependent ℝ
      (fun index : {index // index ∈ positiveActiveSet activeSet activeWeight} =>
        atomMatrix (tightDir index.1))) :
    2 * (positiveActiveSet activeSet activeWeight).card
      ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir)))
        * (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
            (chartMultiplierAssembly activeSet activeWeight tightDir))) + 1) := by
  classical
  set rangeSpace := LinearMap.range (Matrix.toLin'
    (chartMultiplierAssembly activeSet activeWeight tightDir)) with hrangeDef
  set base : Fin (Module.finrank ℝ rangeSpace) → (Fin size → ℝ) :=
    fun basisIndex => ((Module.finBasis ℝ rangeSpace basisIndex : rangeSpace) : Fin size → ℝ)
    with hbaseDef
  have hbaseSpan : Submodule.span ℝ (Set.range base) = rangeSpace := by
    have hcompose : Set.range base
        = rangeSpace.subtype '' Set.range (Module.finBasis ℝ rangeSpace) := by
      rw [← Set.range_comp]
      refine congrArg Set.range ?_
      funext basisIndex
      simp [hbaseDef, Function.comp, Submodule.subtype_apply]
    rw [hcompose, Submodule.span_image, Module.Basis.span_eq, Submodule.map_subtype_top]
  refine two_mul_card_le_of_independent_atomMatrix_of_mem_span base tightDir
    (positiveActiveSet activeSet activeWeight) ?_ hindependent
  intro index hmemPositive
  rw [hbaseSpan]
  obtain ⟨hactive, hpos⟩ := mem_positiveActiveSet.mp hmemPositive
  exact tightDir_mem_range_multiplier_of_pos hdata hactive hpos

/-! ## The crux packaging -/

/-- **THE CRUX CARRIES A CAPPED DATUM.**  A `(6,3)` counterexample carries a
stationary datum at its argmax family whose positive support obeys
`2 |S| ≤ r (r + 1)` for `r` its assembly rank. -/
theorem SixThreeCrux.exists_multiplier_independent_two_mul_card_le
    (crux : SixThreeCrux) :
    ∃ (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection
      ∧ 2 * (positiveActiveSet (chartArgmaxFamily (chartPointOfDesign crux.design))
            multiplier).card
          ≤ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly (chartArgmaxFamily (chartPointOfDesign crux.design))
                  multiplier selection)))
            * (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
                (chartMultiplierAssembly (chartArgmaxFamily (chartPointOfDesign crux.design))
                  multiplier selection))) + 1) := by
  obtain ⟨multiplier, selection, hdata, hindependent⟩ :=
    crux.exists_multiplier_isChartStationaryData_independent_positive_support
  exact ⟨multiplier, selection, hdata,
    two_mul_card_positiveActiveSet_le_of_independent hdata hindependent⟩

/-- **THE TWENTY-ONE CAP.**  A `(6,3)` counterexample carries a stationary
datum with at most twenty-one positive blocks: the assembly rank is four, five
or six by the survivor list, and the cap reads ten, fifteen or twenty-one. -/
theorem SixThreeCrux.exists_multiplier_card_positiveActiveSet_le_twentyOne
    (crux : SixThreeCrux) :
    ∃ (multiplier : Finset (Fin 6) → ℝ) (selection : Finset (Fin 6) → (Fin 6 → ℝ)),
      IsChartStationaryData 3 (chartPointOfDesign crux.design).chart
        (chartPointOfDesign crux.design).weight
        (chartObjective (chartPointOfDesign crux.design))
        (chartArgmaxFamily (chartPointOfDesign crux.design))
        (id : Finset (Fin 6) → Finset (Fin 6)) multiplier selection
      ∧ (positiveActiveSet (chartArgmaxFamily (chartPointOfDesign crux.design))
          multiplier).card ≤ 21 := by
  obtain ⟨multiplier, selection, hdata, hcap⟩ :=
    crux.exists_multiplier_independent_two_mul_card_le
  refine ⟨multiplier, selection, hdata, ?_⟩
  rcases crux.finrank_range_multiplier_eq_four_or_five_or_six hdata with
    hrank | hrank | hrank <;>
  · rw [hrank] at hcap
    omega

end Gtz
