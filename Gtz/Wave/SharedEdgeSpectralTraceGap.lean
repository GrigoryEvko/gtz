import Gtz.Wave.SharedEdgePathSpectrum
import Gtz.Design.TwoFamilyTightFrame
import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- Polynomial form of the path spectrum: `H^2-H` is the positive rank-one
form on the eigenvalue-two direction. -/
theorem sharedEdgePath_square_sub_self_eq {x y : ℝ}
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    sharedEdgePathMatrix x y * sharedEdgePathMatrix x y
        - sharedEdgePathMatrix x y =
      atomMatrix (sharedEdgeLargeVector x y) := by
  have hx := congrArg (fun value : ℝ => value * x) hcircle
  have hy := congrArg (fun value : ℝ => value * y) hcircle
  ring_nf at hx hy
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex
  all_goals simp [sharedEdgePathMatrix, sharedEdgeLargeVector, atomMatrix,
    Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf
  all_goals nlinarith

/-- After scaling the path matrix by `1/6`, its square has spectral floor
`1/6` on its range. -/
theorem sharedEdgePath_scaled_square_floor_posSemidef {x y : ℝ}
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    (((1 / 6 : ℝ) • sharedEdgePathMatrix x y)
          * ((1 / 6 : ℝ) • sharedEdgePathMatrix x y)
        - (1 / 6 : ℝ) • ((1 / 6 : ℝ) • sharedEdgePathMatrix x y)).PosSemidef := by
  have heq :
      ((1 / 6 : ℝ) • sharedEdgePathMatrix x y)
            * ((1 / 6 : ℝ) • sharedEdgePathMatrix x y)
          - (1 / 6 : ℝ) • ((1 / 6 : ℝ) • sharedEdgePathMatrix x y) =
        (1 / 36 : ℝ) • atomMatrix (sharedEdgeLargeVector x y) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
    rw [smul_smul]
    norm_num
    rw [← smul_sub, sharedEdgePath_square_sub_self_eq hcircle]
  rw [heq]
  exact (posSemidef_atomMatrix (sharedEdgeLargeVector x y)).smul (by norm_num)

/-- Canonical two-row path block.  The first row misses coordinate `2`, the
second misses coordinate `0`; unit norms, total multiplier `1/2`, and constant
diagonal `1/6` force the exact path circle relation. -/
theorem twoAtom_path_square_floor_posSemidef
    (first second : Fin 3 → ℝ) (firstWeight secondWeight : ℝ)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (hfirstMissing : first 2 = 0) (hsecondMissing : second 0 = 0)
    (hweightSum : firstWeight + secondWeight = 1 / 2)
    (hdiagonal : ∀ coordinate : Fin 3,
      (firstWeight • atomMatrix first + secondWeight • atomMatrix second)
        coordinate coordinate = 1 / 6) :
    let assembly := firstWeight • atomMatrix first + secondWeight • atomMatrix second
    (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef := by
  dsimp only
  let assembly := firstWeight • atomMatrix first + secondWeight • atomMatrix second
  change (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef
  let x : ℝ := 6 * assembly 0 1
  let y : ℝ := 6 * assembly 1 2
  have hdiagZero := hdiagonal 0
  have hdiagOne := hdiagonal 1
  have hdiagTwo := hdiagonal 2
  have hdiagZero' : firstWeight * (first 0 * first 0) = 1 / 6 := by
    simpa [Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, hsecondMissing] using hdiagZero
  have hdiagTwo' : secondWeight * (second 2 * second 2) = 1 / 6 := by
    simpa [Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, hfirstMissing] using hdiagTwo
  have hfirstWeightedUnit := congrArg (fun value : ℝ => firstWeight * value) hfirstUnit
  have hsecondWeightedUnit := congrArg (fun value : ℝ => secondWeight * value) hsecondUnit
  simp only [dotProduct, Fin.sum_univ_three] at hfirstWeightedUnit hsecondWeightedUnit
  have hfirstMiddle : firstWeight * first 1 * first 1 = firstWeight - 1 / 6 := by
    rw [hfirstMissing] at hfirstWeightedUnit
    norm_num at hfirstWeightedUnit
    nlinarith [hdiagZero']
  have hsecondMiddle : secondWeight * second 1 * second 1 = secondWeight - 1 / 6 := by
    rw [hsecondMissing] at hsecondWeightedUnit
    norm_num at hsecondWeightedUnit
    nlinarith [hdiagTwo']
  have hxSquare : (assembly 0 1) ^ 2 = (1 / 6) * (firstWeight - 1 / 6) := by
    have hassemblyZeroOne : assembly 0 1 = firstWeight * first 0 * first 1 := by
      simp [assembly, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
        Matrix.vecMulVec_apply, hsecondMissing]
      ring
    rw [hassemblyZeroOne]
    calc
      (firstWeight * first 0 * first 1) ^ 2 =
          (firstWeight * (first 0 * first 0)) *
            (firstWeight * first 1 * first 1) := by ring
      _ = (1 / 6) * (firstWeight - 1 / 6) := by
        rw [hdiagZero', hfirstMiddle]
  have hySquare : (assembly 1 2) ^ 2 = (1 / 6) * (secondWeight - 1 / 6) := by
    have hassemblyOneTwo : assembly 1 2 = secondWeight * second 1 * second 2 := by
      simp [assembly, Matrix.add_apply, Matrix.smul_apply, atomMatrix,
        Matrix.vecMulVec_apply, hfirstMissing]
      ring
    rw [hassemblyOneTwo]
    calc
      (secondWeight * second 1 * second 2) ^ 2 =
          (secondWeight * second 1 * second 1) *
            (secondWeight * (second 2 * second 2)) := by ring
      _ = (1 / 6) * (secondWeight - 1 / 6) := by
        rw [hsecondMiddle, hdiagTwo']
        ring
  have hcircle : x ^ 2 + y ^ 2 = 1 := by
    dsimp only [x, y]
    nlinarith
  have hassembly : assembly = (1 / 6 : ℝ) • sharedEdgePathMatrix x y := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex
    · simpa [assembly, sharedEdgePathMatrix] using hdiagZero
    · simp [x, sharedEdgePathMatrix]
    · simp [assembly, sharedEdgePathMatrix, Matrix.add_apply, Matrix.smul_apply,
        atomMatrix, Matrix.vecMulVec_apply, hfirstMissing, hsecondMissing]
    · simp [x, assembly, sharedEdgePathMatrix, Matrix.add_apply, Matrix.smul_apply,
        atomMatrix, Matrix.vecMulVec_apply]
      ring
    · simpa [assembly, sharedEdgePathMatrix] using hdiagOne
    · simp [y, sharedEdgePathMatrix]
    · simp [assembly, sharedEdgePathMatrix, Matrix.add_apply, Matrix.smul_apply,
        atomMatrix, Matrix.vecMulVec_apply, hfirstMissing, hsecondMissing]
    · simp [y, assembly, sharedEdgePathMatrix, Matrix.add_apply, Matrix.smul_apply,
        atomMatrix, Matrix.vecMulVec_apply]
      ring
    · simpa [assembly, sharedEdgePathMatrix] using hdiagTwo
  rw [hassembly]
  exact sharedEdgePath_scaled_square_floor_posSemidef hcircle

/-- Coordinate-free form of the path certificate, with an explicit reindexing
that sends coordinate `2` to the first row's missing coordinate and coordinate
`0` to the second row's missing coordinate. -/
theorem twoAtom_square_floor_posSemidef_of_pathEquiv
    (first second : Fin 3 → ℝ) (firstWeight secondWeight : ℝ)
    (reindex : Fin 3 ≃ Fin 3)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (hfirstMissing : first (reindex 2) = 0)
    (hsecondMissing : second (reindex 0) = 0)
    (hweightSum : firstWeight + secondWeight = 1 / 2)
    (hdiagonal : ∀ coordinate : Fin 3,
      (firstWeight • atomMatrix first + secondWeight • atomMatrix second)
        coordinate coordinate = 1 / 6) :
    let assembly := firstWeight • atomMatrix first + secondWeight • atomMatrix second
    (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef := by
  dsimp only
  let assembly := firstWeight • atomMatrix first + secondWeight • atomMatrix second
  let firstReindexed : Fin 3 → ℝ := first ∘ reindex
  let secondReindexed : Fin 3 → ℝ := second ∘ reindex
  have hfirstReindexedUnit : firstReindexed ⬝ᵥ firstReindexed = 1 := by
    change (first ∘ reindex) ⬝ᵥ (first ∘ reindex) = 1
    rw [comp_equiv_dotProduct_comp_equiv, hfirstUnit]
  have hsecondReindexedUnit : secondReindexed ⬝ᵥ secondReindexed = 1 := by
    change (second ∘ reindex) ⬝ᵥ (second ∘ reindex) = 1
    rw [comp_equiv_dotProduct_comp_equiv, hsecondUnit]
  have hfirstReindexedMissing : firstReindexed 2 = 0 := hfirstMissing
  have hsecondReindexedMissing : secondReindexed 0 = 0 := hsecondMissing
  have hdiagonalReindexed : ∀ coordinate : Fin 3,
      (firstWeight • atomMatrix firstReindexed
          + secondWeight • atomMatrix secondReindexed) coordinate coordinate = 1 / 6 := by
    intro coordinate
    simpa [firstReindexed, secondReindexed, Matrix.add_apply, Matrix.smul_apply,
      atomMatrix, Matrix.vecMulVec_apply] using hdiagonal (reindex coordinate)
  have hcanonical := twoAtom_path_square_floor_posSemidef firstReindexed
    secondReindexed firstWeight secondWeight hfirstReindexedUnit
    hsecondReindexedUnit hfirstReindexedMissing hsecondReindexedMissing
    hweightSum hdiagonalReindexed
  dsimp only at hcanonical
  have hassemblyReindexed :
      firstWeight • atomMatrix firstReindexed
          + secondWeight • atomMatrix secondReindexed =
        assembly.submatrix reindex reindex := by
    ext rowIndex colIndex
    rfl
  rw [hassemblyReindexed] at hcanonical
  have hreindexedFloor :
      (assembly * assembly - (1 / 6 : ℝ) • assembly).submatrix reindex reindex =
        assembly.submatrix reindex reindex * assembly.submatrix reindex reindex
          - (1 / 6 : ℝ) • assembly.submatrix reindex reindex := by
    calc
      (assembly * assembly - (1 / 6 : ℝ) • assembly).submatrix reindex reindex =
          (assembly * assembly).submatrix reindex reindex
            - (1 / 6 : ℝ) • assembly.submatrix reindex reindex := by rfl
      _ = assembly.submatrix reindex reindex * assembly.submatrix reindex reindex
            - (1 / 6 : ℝ) • assembly.submatrix reindex reindex := by
        rw [Matrix.submatrix_mul_equiv]
  rw [← hreindexedFloor] at hcanonical
  have hback := hcanonical.submatrix reindex.symm
  have hback' : (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef := by
    simp only [Matrix.submatrix_submatrix, Function.comp_def,
      Equiv.apply_symm_apply] at hback
    have hid :
        (assembly * assembly - (1 / 6 : ℝ) • assembly).submatrix
            (fun coordinate => coordinate) (fun coordinate => coordinate) =
          assembly * assembly - (1 / 6 : ℝ) • assembly := by
      rfl
    rw [hid] at hback
    exact hback
  simpa only [assembly] using hback'

/-- Canonical permutation putting the second row's missing coordinate first and
the first row's missing coordinate last. -/
def twoRowPathReindex (firstMissing secondMissing : Fin 3) : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 0 secondMissing).trans
    (Equiv.swap ((Equiv.swap 0 secondMissing) 2) firstMissing)

theorem twoRowPathReindex_zero (firstMissing secondMissing : Fin 3)
    (hne : firstMissing ≠ secondMissing) :
    twoRowPathReindex firstMissing secondMissing 0 = secondMissing := by
  fin_cases firstMissing <;> fin_cases secondMissing <;>
    simp_all [twoRowPathReindex, Equiv.swap_apply_def]

theorem twoRowPathReindex_two (firstMissing secondMissing : Fin 3)
    (hne : firstMissing ≠ secondMissing) :
    twoRowPathReindex firstMissing secondMissing 2 = firstMissing := by
  fin_cases firstMissing <;> fin_cases secondMissing <;>
    simp_all [twoRowPathReindex, Equiv.swap_apply_def]

/-- Fully coordinate-free two-row path certificate. -/
theorem twoAtom_square_floor_posSemidef_of_distinct_missing
    (first second : Fin 3 → ℝ) (firstWeight secondWeight : ℝ)
    (firstMissing secondMissing : Fin 3)
    (hmissingDistinct : firstMissing ≠ secondMissing)
    (hfirstUnit : first ⬝ᵥ first = 1)
    (hsecondUnit : second ⬝ᵥ second = 1)
    (hfirstMissing : first firstMissing = 0)
    (hsecondMissing : second secondMissing = 0)
    (hweightSum : firstWeight + secondWeight = 1 / 2)
    (hdiagonal : ∀ coordinate : Fin 3,
      (firstWeight • atomMatrix first + secondWeight • atomMatrix second)
        coordinate coordinate = 1 / 6) :
    let assembly := firstWeight • atomMatrix first + secondWeight • atomMatrix second
    (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef := by
  apply twoAtom_square_floor_posSemidef_of_pathEquiv first second firstWeight
    secondWeight (twoRowPathReindex firstMissing secondMissing) hfirstUnit
    hsecondUnit
  · rwa [twoRowPathReindex_two firstMissing secondMissing hmissingDistinct]
  · rwa [twoRowPathReindex_zero firstMissing secondMissing hmissingDistinct]
  · exact hweightSum
  · exact hdiagonal

/-- A polynomial spectral floor converts commutation with an orthogonal
projection into a trace gap.  This avoids eigenvalue APIs: compare
`tr((PA)^2)` below by the floor certificate and above by positivity. -/
theorem sixth_le_trace_projection_mul_of_square_floor
    {dimension : ℕ}
    (projection assembly : Matrix (Fin dimension) (Fin dimension) ℝ)
    (hprojectionPsd : projection.PosSemidef)
    (hprojectionIdempotent : projection * projection = projection)
    (hcommutes : projection * assembly = assembly * projection)
    (hproductPsd : (projection * assembly).PosSemidef)
    (hfloor : (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef)
    (htracePositive : 0 < Matrix.trace (projection * assembly)) :
    1 / 6 ≤ Matrix.trace (projection * assembly) := by
  let product := projection * assembly
  have hsquare : product * product = projection * (assembly * assembly) := by
    dsimp only [product]
    calc
      (projection * assembly) * (projection * assembly) =
          projection * (assembly * projection) * assembly := by
        simp only [Matrix.mul_assoc]
      _ = projection * (projection * assembly) * assembly := by rw [← hcommutes]
      _ = (projection * projection) * (assembly * assembly) := by
        simp only [Matrix.mul_assoc]
      _ = projection * (assembly * assembly) := by rw [hprojectionIdempotent]
  have hfloorProduct :
      projection * (assembly * assembly - (1 / 6 : ℝ) • assembly) =
        product * product - (1 / 6 : ℝ) • product := by
    rw [Matrix.mul_sub, Matrix.mul_smul, ← hsquare]
  have hlowerTrace := trace_mul_nonneg_of_posSemidef hprojectionPsd hfloor
  rw [hfloorProduct, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hlowerTrace
  have hproductSymmetric : ∀ rowIndex colIndex : Fin dimension,
      product colIndex rowIndex = product rowIndex colIndex := by
    intro rowIndex colIndex
    have hhermitian := hproductPsd.isHermitian.apply rowIndex colIndex
    simpa using hhermitian
  have hupperTrace :
      Matrix.trace (product * product) ≤ (Matrix.trace product) ^ 2 := by
    have hexpand : Matrix.trace (product * product) =
        ∑ rowIndex : Fin dimension, ∑ colIndex : Fin dimension,
          product rowIndex colIndex * product colIndex rowIndex :=
      Finset.sum_congr rfl fun rowIndex _ => by
        rw [Matrix.diag_apply, Matrix.mul_apply]
    have hsquareTrace : (Matrix.trace product) ^ 2 =
        ∑ rowIndex : Fin dimension, ∑ colIndex : Fin dimension,
          product rowIndex rowIndex * product colIndex colIndex := by
      rw [Matrix.trace, pow_two, Finset.sum_mul_sum]
      rfl
    rw [hexpand, hsquareTrace]
    refine Finset.sum_le_sum fun rowIndex _ => Finset.sum_le_sum fun colIndex _ => ?_
    rw [hproductSymmetric rowIndex colIndex, ← pow_two]
    exact sq_le_mul_diag_of_posSemidef hproductPsd rowIndex colIndex
  change 0 < Matrix.trace product at htracePositive
  have hchain : (1 / 6 : ℝ) * Matrix.trace product ≤
      Matrix.trace product * Matrix.trace product := by
    have hlower : (1 / 6 : ℝ) * Matrix.trace product ≤
        Matrix.trace (product * product) := by
      linarith
    rw [← pow_two]
    exact hlower.trans hupperTrace
  nlinarith

/-- The coordinate-selection injection is an isometry when its pick is
injective. -/
theorem transpose_selectionInjection_mul_self
    {small large : ℕ} (pick : Fin small → Fin large)
    (hinjective : Function.Injective pick) :
    (selectionInjection pick)ᵀ * selectionInjection pick = 1 := by
  ext firstIndex secondIndex
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectionInjection,
    Matrix.of_apply, Matrix.one_apply]
  by_cases heq : firstIndex = secondIndex
  · subst secondIndex
    rw [Finset.sum_eq_single (pick firstIndex)]
    · simp
    · intro otherIndex _ hother
      rw [if_neg (fun hpick => hother hpick.symm), zero_mul]
    · exact fun hnotMem => (hnotMem (Finset.mem_univ _)).elim
  · have hpickNe : pick firstIndex ≠ pick secondIndex :=
      fun hpick => heq (hinjective hpick)
    rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro otherIndex _
    by_cases hfirst : pick firstIndex = otherIndex
    · rw [if_pos hfirst,
        if_neg (fun hsecond => hpickNe (hfirst.trans hsecond.symm))]
      norm_num
    · rw [if_neg hfirst, zero_mul]

/-- Lift a square-floor certificate through a coordinate injection. -/
theorem embedded_square_floor_posSemidef
    {small large : ℕ} (pick : Fin small → Fin large)
    (hinjective : Function.Injective pick)
    (localAssembly : Matrix (Fin small) (Fin small) ℝ)
    (hlocalFloor :
      (localAssembly * localAssembly - (1 / 6 : ℝ) • localAssembly).PosSemidef) :
    let embedded := selectionInjection pick * localAssembly * (selectionInjection pick)ᵀ
    (embedded * embedded - (1 / 6 : ℝ) • embedded).PosSemidef := by
  dsimp only
  let injection := selectionInjection pick
  let embedded := injection * localAssembly * injectionᵀ
  change (embedded * embedded - (1 / 6 : ℝ) • embedded).PosSemidef
  have hinjectionOrthogonal : injectionᵀ * injection = 1 := by
    exact transpose_selectionInjection_mul_self pick hinjective
  have hembeddedSquare :
      embedded * embedded = injection * (localAssembly * localAssembly) * injectionᵀ := by
    dsimp only [embedded]
    calc
      (injection * localAssembly * injectionᵀ) *
          (injection * localAssembly * injectionᵀ) =
        (((injection * localAssembly) * (injectionᵀ * injection)) *
          localAssembly) * injectionᵀ := by simp only [Matrix.mul_assoc]
      _ = (((injection * localAssembly) *
          (1 : Matrix (Fin small) (Fin small) ℝ)) * localAssembly) * injectionᵀ := by
        rw [hinjectionOrthogonal]
      _ = injection * (localAssembly * localAssembly) * injectionᵀ := by
        simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hscaledEmbedded :
      (1 / 6 : ℝ) • embedded =
        injection * ((1 / 6 : ℝ) • localAssembly) * injectionᵀ := by
    dsimp only [embedded]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hfloorEq :
      embedded * embedded - (1 / 6 : ℝ) • embedded =
        injection *
          (localAssembly * localAssembly - (1 / 6 : ℝ) • localAssembly) *
            injectionᵀ := by
    rw [hembeddedSquare, hscaledEmbedded, Matrix.mul_sub, Matrix.sub_mul]
  rw [hfloorEq]
  have hcongruence := hlocalFloor.mul_mul_conjTranspose_same injection
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hcongruence

/-- Congruence of a rank-one atom matrix through a rectangular coordinate
injection. -/
theorem selectionInjection_mul_atomMatrix_mul_transpose
    {small large : ℕ} (pick : Fin small → Fin large)
    (vector : Fin small → ℝ) :
    selectionInjection pick * atomMatrix vector * (selectionInjection pick)ᵀ =
      atomMatrix (selectionInjection pick *ᵥ vector) := by
  rw [atomMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]
  rfl

/-- A block-orthogonal unit rank-one summand of weight `1/2` preserves the
`1/6` polynomial spectral floor. -/
theorem add_half_atomMatrix_square_floor_posSemidef
    {dimension : ℕ} (assembly : Matrix (Fin dimension) (Fin dimension) ℝ)
    (direction : Fin dimension → ℝ)
    (hassemblyFloor :
      (assembly * assembly - (1 / 6 : ℝ) • assembly).PosSemidef)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (hcrossRight : assembly * atomMatrix direction = 0)
    (hcrossLeft : atomMatrix direction * assembly = 0) :
    let total := assembly + (1 / 2 : ℝ) • atomMatrix direction
    (total * total - (1 / 6 : ℝ) • total).PosSemidef := by
  dsimp only
  let complement := (1 / 2 : ℝ) • atomMatrix direction
  have hatomSquare : atomMatrix direction * atomMatrix direction =
      atomMatrix direction := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply]
    simp only [atomMatrix, Matrix.vecMulVec_apply]
    calc
      ∑ middleIndex, direction rowIndex * direction middleIndex
            * (direction middleIndex * direction colIndex) =
          direction rowIndex *
              (∑ middleIndex, direction middleIndex * direction middleIndex) *
            direction colIndex := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun middleIndex _ => by ring
      _ = direction rowIndex * direction colIndex := by
        rw [← dotProduct, hdirectionUnit]
        ring
  have hcomplementSquare : complement * complement =
      (1 / 4 : ℝ) • atomMatrix direction := by
    dsimp only [complement]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hatomSquare]
    norm_num
  have hcomplementFloor :
      (complement * complement - (1 / 6 : ℝ) • complement).PosSemidef := by
    have heq : complement * complement - (1 / 6 : ℝ) • complement =
        (1 / 6 : ℝ) • atomMatrix direction := by
      rw [hcomplementSquare]
      dsimp only [complement]
      rw [smul_smul]
      ext rowIndex colIndex
      simp only [Matrix.sub_apply, Matrix.smul_apply]
      ring
    rw [heq]
    exact (posSemidef_atomMatrix direction).smul (by norm_num)
  have hassemblyComplement : assembly * complement = 0 := by
    dsimp only [complement]
    rw [Matrix.mul_smul, hcrossRight, smul_zero]
  have hcomplementAssembly : complement * assembly = 0 := by
    dsimp only [complement]
    rw [Matrix.smul_mul, hcrossLeft, smul_zero]
  have hsplit :
      (assembly + complement) * (assembly + complement)
          - (1 / 6 : ℝ) • (assembly + complement) =
        (assembly * assembly - (1 / 6 : ℝ) • assembly)
          + (complement * complement - (1 / 6 : ℝ) • complement) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      hassemblyComplement, hcomplementAssembly, add_zero, zero_add, smul_add]
    abel
  rw [hsplit]
  exact hassemblyFloor.add hcomplementFloor


end Gtz
