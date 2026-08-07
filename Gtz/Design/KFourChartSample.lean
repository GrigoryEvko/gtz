import Gtz.Design.RigidityBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The K4 chart at the tetrahedron's image: the first Road-A sample point

The coordinate-diagonal design (`Gtz.coordinateDiagonalDesign`, the regular
tetrahedron's six edge directions) realizes the `M(K4)` pattern, so by the
covering (`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`) it sits on
the K4 chart.  Its chart image is FULLY RATIONAL: the covering's per-atom gauge
absorbs the `sqrt(3/2)` scale (`scale^2 = 3/2`), leaving mass
`(1/6)*(3/2) = 1/4` and weight `1/6` at every label.

At that point the coordinate-axis triple `{3, 4, 5}` has chart gap
`(3/2)*I - (1/4)*(4*I - J) = (1/2)*I + (1/4)*J`, positive definite with margin
`1/2` — quadratic form `(1/2)*|x|^2 + (1/4)*(x0+x1+x2)^2`.  So the chart
obligation `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` holds at the one
chart point the stress-free stratum's known inhabitant occupies, by rational
arithmetic alone.  Every Road-A certificate takes this shape: explicit
rational chart data, an explicit triple, Sylvester-style positivity.
-/

namespace Gtz

open Matrix

/-- The K4 chart point under the tetrahedron: every mass `1/4`, every
weight `1/6`. -/
noncomputable def tetrahedronChartPoint : DirectionChartPoint 6 where
  mass := fun _ => 1 / 4
  weight := fun _ => 1 / 6
  mass_pos := fun _ => by norm_num
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num

/-- The `{3,4,5}` chart gap at the tetrahedron point, entry by entry:
`(1/2)*I + (1/4)*J`. -/
theorem tetrahedron_gap_eq :
    directionChartGap kFourDirection tetrahedronChartPoint.mass
        tetrahedronChartPoint.weight {3, 4, 5}
      = Matrix.of ![![3/4, 1/4, 1/4], ![1/4, 3/4, 1/4], ![1/4, 1/4, 3/4]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [tetrahedronChartPoint, kFourDirection, atomMatrix,
      Matrix.sub_apply] <;>
    norm_num

/-- **The strict triple at the tetrahedron's chart image.**  The gap of the
coordinate-axis triple is positive definite: its quadratic form is
`(1/2)*|x|^2 + (1/4)*(x0+x1+x2)^2`. -/
theorem tetrahedron_gap_posDef :
    (directionChartGap kFourDirection tetrahedronChartPoint.mass
      tetrahedronChartPoint.weight {3, 4, 5}).PosDef := by
  rw [tetrahedron_gap_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · have hnormPos : (0 : ℝ) < vecArg ⬝ᵥ vecArg := by
      obtain ⟨badIndex, hbadRaw⟩ := Function.ne_iff.mp hne
      have hbad : vecArg badIndex ≠ 0 := by simpa using hbadRaw
      exact Finset.sum_pos' (fun index _ => mul_self_nonneg (vecArg index))
        ⟨badIndex, Finset.mem_univ _,
          lt_of_le_of_ne (mul_self_nonneg _) (Ne.symm (mul_ne_zero hbad hbad))⟩
    rw [star_trivial]
    have hform : vecArg ⬝ᵥ ((Matrix.of ![![3/4, 1/4, 1/4], ![1/4, 3/4, 1/4],
          ![1/4, 1/4, 3/4]] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = 1/2 * (vecArg ⬝ᵥ vecArg)
          + 1/4 * (vecArg 0 + vecArg 1 + vecArg 2) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    nlinarith [sq_nonneg (vecArg 0 + vecArg 1 + vecArg 2), hnormPos]

/-- The Road-A sample: at the tetrahedron's chart image SOME triple is
strictly dominating — the chart obligation's conclusion holds there
unconditionally, weak antecedent not even needed. -/
theorem tetrahedronChartPoint_hasStrictTriple :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection tetrahedronChartPoint.mass
        tetrahedronChartPoint.weight selected).PosDef :=
  ⟨{3, 4, 5}, by decide, tetrahedron_gap_posDef⟩

end Gtz
