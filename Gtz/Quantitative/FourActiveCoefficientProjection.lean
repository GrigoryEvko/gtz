import Mathlib
import Gtz.Quantitative.AssemblyRankFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The four-active coefficient projection — the trace-two matrix under the leaf census

At a `(6,3)` crux with exactly four active blocks, pack the four tight directions
into the multiplier-weighted column matrix `B` (columns `sqrt(mu) * u`).  Then
`B Bᵀ` is the stationary assembly, the four columns are independent (the landed
rank floor), and the chart's commutation with the assembly descends to a
coefficient matrix `M` with `P B = B M`.  A left inverse of `B` transports the
chart's symmetry, idempotence and captured rank to `M`:

    `Mᵀ = M`,  `M² = M`,  `tr M = 2`.

This is the complete algebraic interface the four-active leaf exits consume — the
tightness rows of `B`, the coefficient projection `M`, and its trace — now with
every input drawn from the landed floor: multiplier positivity and the `(2,2)`
captured ranks are DERIVED from `Gtz.Quantitative.AssemblyRankFloor`, not
hypothesised.

The first half of the file is generic left-inverse algebra over an arbitrary
ambient type: existence of a matrix left inverse for four independent columns,
the explicit coefficient representation `M = Bᵀ P Lᵀ` under Gram commutation, and
the transports of idempotence, rank and symmetry through the left inverse.
-/

namespace Gtz

open Matrix

/-! ## Trace and rank of idempotents -/

/-- Exact trace/range identity for a real idempotent matrix. -/
theorem trace_eq_finrank_range_of_idempotent
    {dimension : ℕ} (M : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hidempotent : M * M = M) :
    Matrix.trace M =
      (Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) : ℝ) := by
  have hendoIdem : IsIdempotentElem (Matrix.toLin' M) := by
    show Matrix.toLin' M * Matrix.toLin' M = Matrix.toLin' M
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hidempotent]
  rw [← Matrix.trace_toLin'_eq M]
  exact (LinearMap.isProj_range_iff_isIdempotentElem _ |>.2 hendoIdem).trace

/-- An idempotent with two-dimensional range has trace two. -/
theorem trace_eq_two_of_idempotent_of_range_finrank_eq_two
    {dimension : ℕ} (M : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hidempotent : M * M = M)
    (hrank : Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = 2) :
    Matrix.trace M = 2 := by
  rw [trace_eq_finrank_range_of_idempotent M hidempotent, hrank]
  norm_num

/-! ## The generic left-inverse layer -/

variable {ambient rowCount : Type*}
  [Fintype ambient]
  [Fintype rowCount] [DecidableEq rowCount]

/-- Four independent columns in a real ambient space admit a matrix left
inverse — the bridge from the four-dimensional positive tight-row span to
coefficient coordinates. -/
theorem exists_matrix_leftInverse_of_finrank_range_eq_four
    (B : Matrix ambient (Fin 4) ℝ)
    (hrange : Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' B)) = 4) :
    ∃ L : Matrix (Fin 4) ambient ℝ, L * B = 1 := by
  classical
  let columnMap : (Fin 4 → ℝ) →ₗ[ℝ] (ambient → ℝ) := Matrix.toLin' B
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker columnMap
  have hdomain : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
    simp
  have hkernelRank : Module.finrank ℝ (LinearMap.ker columnMap) = 0 := by
    change Module.finrank ℝ (LinearMap.range (Matrix.toLin' B))
        + Module.finrank ℝ (LinearMap.ker columnMap) =
      Module.finrank ℝ (Fin 4 → ℝ) at hrankNullity
    omega
  have hkernel : LinearMap.ker columnMap = ⊥ := Submodule.finrank_eq_zero.mp hkernelRank
  obtain ⟨leftInverse, hleftInverse⟩ := columnMap.exists_leftInverse_of_injective hkernel
  refine ⟨LinearMap.toMatrix' leftInverse, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  simpa only [columnMap, Matrix.toLin'_one] using hleftInverse

/-- For a commuting Gram assembly the coefficient matrix is explicit:
`M = Bᵀ P Lᵀ`. -/
theorem commutingAssembly_coefficient_representation
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (hleft : L * B = 1)
    (hcommutes : P * (B * B.transpose) = (B * B.transpose) * P) :
    P * B = B * (B.transpose * P * L.transpose) := by
  have hright : B.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  calc
    P * B = (P * B) * (1 : Matrix rowCount rowCount ℝ) := by
      rw [Matrix.mul_one]
    _ = (P * B) * (B.transpose * L.transpose) := by rw [hright]
    _ = (P * (B * B.transpose)) * L.transpose := by
      simp only [Matrix.mul_assoc]
    _ = ((B * B.transpose) * P) * L.transpose := by rw [hcommutes]
    _ = B * (B.transpose * P * L.transpose) := by
      simp only [Matrix.mul_assoc]

/-- A left inverse transports idempotence of an ambient operator to its
coefficient matrix on an invariant family of columns. -/
theorem coefficient_idempotent_of_leftInverse
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (M : Matrix rowCount rowCount ℝ)
    (hleft : L * B = 1)
    (hprojection : P * P = P)
    (hrepresentation : P * B = B * M) :
    M * M = M := by
  calc
    M * M = (L * B) * (M * M) := by rw [hleft, Matrix.one_mul]
    _ = L * ((B * M) * M) := by simp only [Matrix.mul_assoc]
    _ = L * ((P * B) * M) := by rw [hrepresentation]
    _ = L * (P * (B * M)) := by simp only [Matrix.mul_assoc]
    _ = L * (P * (P * B)) := by rw [hrepresentation]
    _ = L * ((P * P) * B) := by simp only [Matrix.mul_assoc]
    _ = L * (P * B) := by rw [hprojection]
    _ = L * (B * M) := by rw [hrepresentation]
    _ = (L * B) * M := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hleft, Matrix.one_mul]

/-- A left inverse identifies the rank of the coefficient matrix with the rank
of the ambient operator restricted to its invariant columns. -/
theorem coefficient_rank_eq_of_leftInverse
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (M : Matrix rowCount rowCount ℝ)
    (hleft : L * B = 1)
    (hrepresentation : P * B = B * M) :
    M.rank = (P * B).rank := by
  apply le_antisymm
  · have hrecover : M = L * (P * B) := by
      calc
        M = (L * B) * M := by rw [hleft, Matrix.one_mul]
        _ = L * (B * M) := by simp only [Matrix.mul_assoc]
        _ = L * (P * B) := by rw [hrepresentation]
    rw [hrecover]
    exact Matrix.rank_mul_le_right L (P * B)
  · rw [hrepresentation]
    exact Matrix.rank_mul_le_right B M

/-- If `L` is a left inverse for `B`, multiplication by `Bᵀ` cannot lower the
rank of an ambient image `P B`. -/
theorem projectedAssembly_rank_eq_projectedColumns_of_leftInverse
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (hleft : L * B = 1) :
    (P * (B * B.transpose)).rank = (P * B).rank := by
  have hright : B.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  apply le_antisymm
  · rw [← Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left (P * B) B.transpose
  · have hrecover : P * B = (P * (B * B.transpose)) * L.transpose := by
      calc
        P * B = (P * B) * (1 : Matrix rowCount rowCount ℝ) := by
          rw [Matrix.mul_one]
        _ = (P * B) * (B.transpose * L.transpose) := by rw [hright]
        _ = (P * (B * B.transpose)) * L.transpose := by
          simp only [Matrix.mul_assoc]
    rw [hrecover]
    exact Matrix.rank_mul_le_left (P * (B * B.transpose)) L.transpose

/-- Commutation of `P` with `B Bᵀ`, together with self-adjointness of `P`,
makes the coefficient matrix symmetric in the weighted-row basis. -/
theorem coefficient_symmetric_of_commutes_of_leftInverse
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient rowCount ℝ)
    (L : Matrix rowCount ambient ℝ)
    (M : Matrix rowCount rowCount ℝ)
    (hleft : L * B = 1)
    (hsymmetric : P.transpose = P)
    (hcommutes : P * (B * B.transpose) = (B * B.transpose) * P)
    (hrepresentation : P * B = B * M) :
    M.transpose = M := by
  have hright : B.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  have htransposeRepresentation : B.transpose * P = M.transpose * B.transpose := by
    have htransposed := congrArg Matrix.transpose hrepresentation
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hsymmetric] at htransposed
    exact htransposed
  have hmiddle : B * M * B.transpose = B * M.transpose * B.transpose := by
    calc
      B * M * B.transpose = P * (B * B.transpose) := by
        rw [← hrepresentation]
        simp only [Matrix.mul_assoc]
      _ = (B * B.transpose) * P := hcommutes
      _ = B * (M.transpose * B.transpose) := by
        rw [← htransposeRepresentation]
        simp only [Matrix.mul_assoc]
      _ = B * M.transpose * B.transpose := by simp only [Matrix.mul_assoc]
  calc
    M.transpose = (L * B) * M.transpose * (B.transpose * L.transpose) := by
      rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
    _ = L * (B * M.transpose * B.transpose) * L.transpose := by
      simp only [Matrix.mul_assoc]
    _ = L * (B * M * B.transpose) * L.transpose := by rw [hmiddle]
    _ = (L * B) * M * (B.transpose * L.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = M := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

/-- The coefficient matrix of a rank-two captured stationary assembly is a
symmetric rank-two projection, hence has trace two. -/
theorem coefficient_projection_trace_eq_two
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient (Fin 4) ℝ)
    (L : Matrix (Fin 4) ambient ℝ)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hleft : L * B = 1)
    (hsymmetric : P.transpose = P)
    (hprojection : P * P = P)
    (hcommutes : P * (B * B.transpose) = (B * B.transpose) * P)
    (hrepresentation : P * B = B * M)
    (hrank : (P * (B * B.transpose)).rank = 2) :
    M.transpose = M ∧ M * M = M ∧ Matrix.trace M = 2 := by
  have hsymm := coefficient_symmetric_of_commutes_of_leftInverse
    P B L M hleft hsymmetric hcommutes hrepresentation
  have hidem := coefficient_idempotent_of_leftInverse
    P B L M hleft hprojection hrepresentation
  have hcoeffRank : M.rank = 2 := by
    rw [coefficient_rank_eq_of_leftInverse P B L M hleft hrepresentation,
      ← projectedAssembly_rank_eq_projectedColumns_of_leftInverse P B L hleft,
      hrank]
  have hfinrank :
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' M)) = 2 := by
    rw [Matrix.toLin'_apply']
    simpa only [Matrix.rank] using hcoeffRank
  exact ⟨hsymm, hidem,
    trace_eq_two_of_idempotent_of_range_finrank_eq_two M hidem hfinrank⟩

/-- Turn a full-rank four-column Gram factor of a commuting rank-two captured
assembly directly into a symmetric idempotent coefficient projection. -/
theorem exists_coefficient_projection_trace_eq_two_of_commutingGram
    (P : Matrix ambient ambient ℝ)
    (B : Matrix ambient (Fin 4) ℝ)
    (L : Matrix (Fin 4) ambient ℝ)
    (hleft : L * B = 1)
    (hsymmetric : P.transpose = P)
    (hprojection : P * P = P)
    (hcommutes : P * (B * B.transpose) = (B * B.transpose) * P)
    (hrank : (P * (B * B.transpose)).rank = 2) :
    ∃ M : Matrix (Fin 4) (Fin 4) ℝ,
      P * B = B * M ∧ M.transpose = M ∧ M * M = M
        ∧ Matrix.trace M = 2 := by
  let M := B.transpose * P * L.transpose
  have hrepresentation : P * B = B * M := by
    simpa only [M] using
      commutingAssembly_coefficient_representation P B L hleft hcommutes
  obtain ⟨hsymm, hidem, htrace⟩ := coefficient_projection_trace_eq_two
    P B L M hleft hsymmetric hprojection hcommutes hrepresentation hrank
  exact ⟨M, hrepresentation, hsymm, hidem, htrace⟩

/-! ## The weighted tight columns of a four-block family -/

/-- Multiplier-weighted tight columns for any injectively enumerated four-block
active family: column `c` is `sqrt(mu (label c)) * tightDir (label c)`. -/
noncomputable def fourFamilyWeightedTightColumns
    (label : Fin 4 → Finset (Fin 6))
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ) :
    Matrix (Fin 6) (Fin 4) ℝ :=
  fun atomIndex column =>
    Real.sqrt (multiplier (label column)) * tightDir (label column) atomIndex

/-- The weighted columns' Gram recovers the stationary assembly. -/
theorem fourFamilyWeightedTightColumns_mul_transpose
    (family : Finset (Finset (Fin 6)))
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = family)
    (hinjective : Function.Injective label)
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hnonneg : ∀ selected ∈ family, 0 ≤ multiplier selected) :
    fourFamilyWeightedTightColumns label multiplier tightDir
        * (fourFamilyWeightedTightColumns label multiplier tightDir).transpose
      = chartMultiplierAssembly family multiplier tightDir := by
  ext rowIndex colIndex
  rw [Matrix.mul_apply, chartMultiplierAssembly_apply, ← hrange,
    Finset.sum_image]
  apply Finset.sum_congr rfl
  intro column _
  have hlabelMem : label column ∈ family := by
    rw [← hrange]
    exact Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩
  have hroot := Real.sq_sqrt (hnonneg (label column) hlabelMem)
  simp only [fourFamilyWeightedTightColumns, Matrix.transpose_apply]
  calc
    Real.sqrt (multiplier (label column)) * tightDir (label column) rowIndex *
          (Real.sqrt (multiplier (label column)) * tightDir (label column) colIndex)
        = (Real.sqrt (multiplier (label column))) ^ 2 *
            (tightDir (label column) rowIndex * tightDir (label column) colIndex) := by ring
    _ = multiplier (label column) *
            (tightDir (label column) rowIndex * tightDir (label column) colIndex) := by
      rw [hroot]
  exact hinjective.injOn

/-- With positive multipliers the weighted columns span exactly the span of the
family's tight directions. -/
theorem fourFamilyWeightedTightColumns_span_eq
    (family : Finset (Finset (Fin 6)))
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = family)
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hpositive : ∀ selected ∈ family, 0 < multiplier selected) :
    Submodule.span ℝ
        (Set.range (fourFamilyWeightedTightColumns label multiplier tightDir).col)
      = Submodule.span ℝ (↑(family.image tightDir) : Set (Fin 6 → ℝ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro vector hvector
    rcases hvector with ⟨column, rfl⟩
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Finset.mem_coe, Finset.mem_image]
    refine ⟨label column, ?_, rfl⟩
    rw [← hrange]
    exact Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩
  · rw [Submodule.span_le]
    intro vector hvector
    simp only [Finset.mem_coe, Finset.mem_image] at hvector
    rcases hvector with ⟨selected, hselected, rfl⟩
    have hselectedRange : selected ∈ Finset.univ.image label := by
      rw [hrange]
      exact hselected
    rcases Finset.mem_image.mp hselectedRange with ⟨column, _, hlabel⟩
    have hroot : Real.sqrt (multiplier selected) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hpositive selected hselected))
    have hrecover : tightDir selected =
        (Real.sqrt (multiplier selected))⁻¹ •
          (fourFamilyWeightedTightColumns label multiplier tightDir).col column := by
      funext atomIndex
      simp [fourFamilyWeightedTightColumns, hlabel, hroot]
    rw [hrecover]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨column, rfl⟩

/-- A four-dimensional tight-direction span makes the weighted columns
independent. -/
theorem fourFamilyWeightedTightColumns_finrank_range
    (family : Finset (Finset (Fin 6)))
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = family)
    (multiplier : Finset (Fin 6) → ℝ)
    (tightDir : Finset (Fin 6) → Fin 6 → ℝ)
    (hpositive : ∀ selected ∈ family, 0 < multiplier selected)
    (hspan : Module.finrank ℝ
      (Submodule.span ℝ (↑(family.image tightDir) : Set (Fin 6 → ℝ))) = 4) :
    Module.finrank ℝ (LinearMap.range
      (Matrix.toLin' (fourFamilyWeightedTightColumns label multiplier tightDir))) = 4 := by
  rw [Matrix.range_toLin', fourFamilyWeightedTightColumns_span_eq
    family label hrange multiplier tightDir hpositive, hspan]

/-! ## The crux-level producer -/

/-- **THE FOUR-ACTIVE COEFFICIENT PROJECTION.**  At a `(6,3)` crux whose argmax
family has exactly the four enumerated blocks, the weighted tight columns admit
a left inverse and carry a coefficient matrix `M` with `P B = B M`, symmetric,
idempotent, of trace two.  Multiplier positivity and the `(2,2)` captured ranks
come from the landed assembly rank floor — nothing here is hypothesised beyond
the stationarity bundle and the family identification. -/
theorem SixThreeCrux.exists_fourFamily_coefficientProjection
    (crux : SixThreeCrux)
    (family : Finset (Finset (Fin 6)))
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = family)
    (hinjective : Function.Injective label)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) = family)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir) :
    let B := fourFamilyWeightedTightColumns label multiplier tightDir
    let P := (chartPointOfDesign crux.design).chart
    ∃ (L : Matrix (Fin 4) (Fin 6) ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ),
      L * B = 1 ∧ P * B = B * M ∧ M.transpose = M
        ∧ M * M = M ∧ Matrix.trace M = 2 := by
  classical
  let B := fourFamilyWeightedTightColumns label multiplier tightDir
  let P := (chartPointOfDesign crux.design).chart
  have hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily, ← hrange, Finset.card_image_iff.mpr hinjective.injOn]
    decide
  have hpositive : ∀ selected ∈
      chartArgmaxFamily (chartPointOfDesign crux.design), 0 < multiplier selected :=
    crux.activeWeight_pos_of_card_eq_four hdata hfamilyCard
  have hpositiveFamily : ∀ selected ∈ family, 0 < multiplier selected := by
    intro selected hselected
    apply hpositive selected
    rwa [hfamily]
  obtain ⟨hspan, hcaptured, _⟩ :=
    crux.fourRowSpan_and_capturedRanks_of_card_eq_four hdata hfamilyCard
  rw [hfamily] at hspan hcaptured
  have hBRange : Module.finrank ℝ (LinearMap.range (Matrix.toLin' B)) = 4 := by
    simpa only [B] using fourFamilyWeightedTightColumns_finrank_range
      family label hrange multiplier tightDir hpositiveFamily hspan
  obtain ⟨L, hleft⟩ := exists_matrix_leftInverse_of_finrank_range_eq_four B hBRange
  have hgram : B * B.transpose = chartMultiplierAssembly family multiplier tightDir := by
    simpa only [B] using fourFamilyWeightedTightColumns_mul_transpose
      family label hrange hinjective multiplier tightDir
        (fun selected hselected => le_of_lt (hpositiveFamily selected hselected))
  have hcommutes : P * (B * B.transpose) = (B * B.transpose) * P := by
    rw [hgram]
    simpa only [P, hfamily] using hdata.assembly_commutes
  have hcapturedGram : Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (P * (B * B.transpose)))) = 2 := by
    rw [hgram]
    simpa only [P] using hcaptured
  have hrank : (P * (B * B.transpose)).rank = 2 := by
    change Module.finrank ℝ
      (LinearMap.range (Matrix.toLin' (P * (B * B.transpose)))) = 2
    exact hcapturedGram
  obtain ⟨M, hrepresentation, hsymm, hidem, htrace⟩ :=
    exists_coefficient_projection_trace_eq_two_of_commutingGram
      P B L hleft (by simpa only [P] using hdata.isSymmetric)
      (by simpa only [P] using hdata.isIdempotent) hcommutes hrank
  exact ⟨L, M, hleft, hrepresentation, hsymm, hidem, htrace⟩

end Gtz
