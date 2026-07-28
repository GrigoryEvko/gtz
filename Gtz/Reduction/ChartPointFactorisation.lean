/-
# The chart-to-design factorisation: `Gtz.ChartPointHasDesign`, DISCHARGED

`Gtz/Reduction/CompactnessReduction.lean` closes with an explicitly named unproved
leaf.  `Gtz.ChartPointHasDesign` (that file, line 1527) asks that every point of the
closed chart domain whose weights are all STRICTLY POSITIVE be the chart of an
honest `Gtz.WeightedDesign`, and `Gtz.chartGtzInterior_of_gtzWeighted` takes it as a
hypothesis.  Its header calls it "the SOLE obstruction to feeding the already
kernel-checked small rungs into any chart-side assembly" and records it as "TRUE
(spectral theorem) and not vacuous, merely unmechanized".

This file mechanizes it.  `Gtz.chartPointHasDesign` is unconditional at EVERY size
and EVERY rank, so `Gtz.chartGtzInterior_of_gtzWeighted_unconditional` drops the
hypothesis and `Gtz.chartGtzInterior_iff_gtzWeighted` and
`Gtz.chartGtz_iff_gtzWeighted` become plain equivalences.

## WHAT IS ACTUALLY PROVED, and what it is worth

ENGINEERING, not research.  The mathematical content is the spectral theorem for
real symmetric matrices, which Mathlib carries
(`Matrix.IsHermitian.spectral_theorem`), plus the observation that an idempotent's
eigenvalues lie in `{0, 1}` and that the trace counts the ones.  Nothing here bears
on `Gtz.GtzWeighted 6 3` or `Gtz.GtzWeighted 7 3`; what it removes is a scaffolding
gap, and it must be reported as exactly that.  The residue of the compactness
reduction is unchanged and is still `Gtz.ChartGtzInterior`, which that file's LEAD 1
shows is not weaker than the target.

## THE TWO STEPS, AND THE ONE THAT WAS ALREADY SHIPPED

0. The real spectral theorem in transpose form -- `A = Q diag(e) Qᵀ` with `Qᵀ Q = 1`
   and `Q Qᵀ = 1`, i.e. Mathlib's `Matrix.IsHermitian.spectral_theorem` with the
   `RCLike.ofReal` coercion and the `star`-versus-transpose dictionary discharged --
   IS ALREADY IN THE KERNEL and is NOT re-derived here.  It is
   `Gtz.eq_eigenvectorUnitary_mul_diagonal_mul_transpose` with
   `Gtz.transpose_mul_eigenvectorUnitary_self` and
   `Gtz.eigenvectorUnitary_mul_transpose_self`, all three in
   `Gtz/Quantitative/TwoBlockEliminationCertificate.lean`, which is why this
   `Gtz/Reduction/` module imports a `Gtz/Quantitative/` one.  LAYERING DEBT,
   recorded rather than repaired: that triple is generic linear algebra with no
   two-block content and belongs in `Gtz/LinAlg/`, and until it moves every consumer
   must reach across the directory boundary for it.
1. `Gtz.exists_orthonormalFrame_of_symmetric_idempotent` -- the factorisation
   proper: `Pᵀ = P`, `P * P = P`, `trace P = rank` give `V` of shape
   `size x rank` with `Vᵀ V = 1` and `V Vᵀ = P`.  Idempotency forces `D * D = D`
   by conjugating, hence `e_i * e_i = e_i` entrywise, hence `e_i` is `0` or `1`;
   the trace then says exactly `rank` of them are `1`, and `V` is the corresponding
   block of columns of `Q`, enumerated by `Finset.orderEmbOfFin`.  NO rank theory
   and NO eigenvector reasoning is used -- only that conjugating by an orthogonal
   matrix is injective.
2. `Gtz.designOfOrthonormalFrame` -- the design.  Its atoms are the frame's rows
   divided by the square roots of the weights, which is the inverse of
   `Gtz.scaledAtomRows`; Parseval is exactly `Vᵀ V = 1` after the weights cancel.
   THE POSITIVITY OF THE WEIGHTS ENTERS HERE AND ONLY HERE, in the single division
   by `sqrt (weight c)`, which is why the discharged statement is the INTERIOR one
   and nothing broader is claimed.  The restriction is not an artifact of the proof:
   `Gtz.not_exists_design_of_weight_eq_zero` shows a boundary chart point is the
   chart of NO weighted design whatever, since `Gtz.WeightedDesign` carries
   `weight_pos`.  So the boundary version of the leaf is FALSE, not open.
   `Gtz.rowDesign` (`Gtz/Reduction/Reductions.lean`) is the `weight = 1/n` slice of
   this constructor and is not generalised in place.

## A SECOND HONESTY CLAIM DISCHARGED, for free

`Gtz/LinAlg/ProjectionForm.lean` states of `Gtz.gtzOriginal_of_projectionCovering`
that it runs "one direction only: `A |-> A Aᵀ` lands inside the symmetric
idempotents of trace `k`, but its surjectivity onto them is the spectral
factorization this repo does not have".  Step 1 IS that surjectivity, so
`Gtz.projectionCovering_iff_frameProjectionCovering` and
`Gtz.gtzOriginal_iff_projectionCovering` land with it.

## WHAT IS NOT TOUCHED

`Gtz.ChartGtzInterior` stays an unproved leaf and is not weakened here.  Nothing in
this file says a chart point IS a minimiser, IS admissible, or carries any
stationarity data; the equivalences below are between two statements that were
already known to be equivalent MODULO this leaf, and all that changes is that the
modulo is gone.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.TwoBlockEliminationCertificate
import Gtz.Reduction.CompactnessReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The factorisation of a symmetric idempotent -/

/-- **THE FACTORISATION.**  A real symmetric idempotent of trace `rank` on
`size` indices is `V Vᵀ` for a `size x rank` matrix `V` with orthonormal columns.

This is the surjectivity of `V |-> V Vᵀ` onto the symmetric idempotents of trace
`rank` that `Gtz/LinAlg/ProjectionForm.lean` records as absent, and the content of
the leaf `Gtz.ChartPointHasDesign` that `Gtz/Reduction/CompactnessReduction.lean`
records as absent.

The proof is three moves.  Conjugating `P * P = P` by the orthogonal diagonaliser
gives `D * D = D`, so every eigenvalue satisfies `e * e = e` and is `0` or `1`.
The trace is the sum of the eigenvalues, so exactly `rank` of them are `1`.  `V` is
the block of columns of the diagonaliser at those indices, enumerated in order by
`Finset.orderEmbOfFin`; orthonormality of its columns is orthonormality of the
diagonaliser's, and `V Vᵀ` reassembles `P` because the eigenvalues it drops are
exactly the vanishing ones.  No rank theory and no eigenvector appears. -/
theorem exists_orthonormalFrame_of_symmetric_idempotent {size rank : ℕ}
    (projection : Matrix (Fin size) (Fin size) ℝ) (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htrace : Matrix.trace projection = (rank : ℝ)) :
    ∃ frame : Matrix (Fin size) (Fin rank) ℝ,
      frameᵀ * frame = 1 ∧ frame * frameᵀ = projection := by
  classical
  have hhermitian : projection.IsHermitian := isHermitian_of_transpose_eq hsymmetric
  obtain ⟨basisMatrix, eigenvalueVector, hleftInverse, hspectral⟩ :
      ∃ (basisMatrix : Matrix (Fin size) (Fin size) ℝ) (eigenvalueVector : Fin size → ℝ),
        basisMatrixᵀ * basisMatrix = 1 ∧
          projection = basisMatrix * Matrix.diagonal eigenvalueVector * basisMatrixᵀ :=
    ⟨(hhermitian.eigenvectorUnitary : Matrix (Fin size) (Fin size) ℝ), hhermitian.eigenvalues,
      transpose_mul_eigenvectorUnitary_self hhermitian,
      eq_eigenvectorUnitary_mul_diagonal_mul_transpose hhermitian⟩
  -- conjugating by the orthogonal diagonaliser is injective
  have hsandwich : ∀ middle : Matrix (Fin size) (Fin size) ℝ,
      basisMatrixᵀ * (basisMatrix * middle * basisMatrixᵀ) * basisMatrix = middle := by
    intro middle
    simp only [Matrix.mul_assoc]
    rw [hleftInverse, Matrix.mul_one, ← Matrix.mul_assoc, hleftInverse, Matrix.one_mul]
  -- idempotency descends to the diagonal factor
  have hdiagonalIdempotent :
      Matrix.diagonal eigenvalueVector * Matrix.diagonal eigenvalueVector
        = Matrix.diagonal eigenvalueVector := by
    have hexpand : basisMatrix
          * (Matrix.diagonal eigenvalueVector * Matrix.diagonal eigenvalueVector) * basisMatrixᵀ
        = (basisMatrix * Matrix.diagonal eigenvalueVector * basisMatrixᵀ)
            * (basisMatrix * Matrix.diagonal eigenvalueVector * basisMatrixᵀ) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc basisMatrixᵀ basisMatrix, hleftInverse, Matrix.one_mul]
    have hstep : basisMatrix
          * (Matrix.diagonal eigenvalueVector * Matrix.diagonal eigenvalueVector) * basisMatrixᵀ
        = basisMatrix * Matrix.diagonal eigenvalueVector * basisMatrixᵀ := by
      rw [hexpand, ← hspectral, hidempotent, hspectral]
    calc Matrix.diagonal eigenvalueVector * Matrix.diagonal eigenvalueVector
        = basisMatrixᵀ * (basisMatrix
            * (Matrix.diagonal eigenvalueVector * Matrix.diagonal eigenvalueVector)
            * basisMatrixᵀ) * basisMatrix := (hsandwich _).symm
      _ = basisMatrixᵀ * (basisMatrix * Matrix.diagonal eigenvalueVector * basisMatrixᵀ)
            * basisMatrix := by rw [hstep]
      _ = Matrix.diagonal eigenvalueVector := hsandwich _
  have hentrywiseIdempotent : ∀ coordIndex : Fin size,
      eigenvalueVector coordIndex * eigenvalueVector coordIndex
        = eigenvalueVector coordIndex := by
    have hvector : (fun coordIndex => eigenvalueVector coordIndex * eigenvalueVector coordIndex)
        = eigenvalueVector :=
      Matrix.diagonal_injective (by
        rw [← Matrix.diagonal_mul_diagonal]; exact hdiagonalIdempotent)
    exact fun coordIndex => congrFun hvector coordIndex
  have hbinary : ∀ coordIndex : Fin size,
      eigenvalueVector coordIndex = 0 ∨ eigenvalueVector coordIndex = 1 := by
    intro coordIndex
    have hfactored : eigenvalueVector coordIndex * (eigenvalueVector coordIndex - 1) = 0 := by
      have := hentrywiseIdempotent coordIndex
      nlinarith [this]
    rcases mul_eq_zero.mp hfactored with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (by linarith)
  -- the trace counts the eigenvalues equal to one
  set activeSet : Finset (Fin size) :=
    Finset.univ.filter (fun coordIndex => eigenvalueVector coordIndex = 1) with hactiveSet
  have hmemberIff : ∀ coordIndex : Fin size,
      coordIndex ∈ activeSet ↔ eigenvalueVector coordIndex = 1 := by
    intro coordIndex
    rw [hactiveSet, Finset.mem_filter]
    exact ⟨fun hpair => hpair.2, fun hvalue => ⟨Finset.mem_univ _, hvalue⟩⟩
  have htraceSum : Matrix.trace projection = ∑ coordIndex, eigenvalueVector coordIndex := by
    rw [hspectral, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hleftInverse, Matrix.one_mul,
      Matrix.trace_diagonal]
  have hactiveSum : ∑ coordIndex ∈ activeSet, eigenvalueVector coordIndex
      = (activeSet.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun coordIndex hmember => (hmemberIff coordIndex).mp hmember),
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hinactiveSum : ∑ coordIndex ∈ Finset.univ.filter
      (fun coordIndex => ¬ eigenvalueVector coordIndex = 1), eigenvalueVector coordIndex = 0 :=
    Finset.sum_eq_zero fun coordIndex hmember =>
      (hbinary coordIndex).resolve_right (Finset.mem_filter.mp hmember).2
  have hcardCast : (activeSet.card : ℝ) = (rank : ℝ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun coordIndex => eigenvalueVector coordIndex = 1) eigenvalueVector
    rw [← hactiveSet] at hsplit
    rw [hactiveSum, hinactiveSum, add_zero] at hsplit
    rw [hsplit, ← htraceSum]
    exact htrace
  have hcard : activeSet.card = rank := Nat.cast_injective hcardCast
  -- the surviving columns
  set pickIndex : Fin rank ↪o Fin size := activeSet.orderEmbOfFin hcard with hpickIndex
  have hpickInjective : Function.Injective pickIndex := pickIndex.injective
  have hpickImage : Finset.univ.image pickIndex = activeSet := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hpickIndex,
      Finset.range_orderEmbOfFin]
  refine ⟨Matrix.of fun rowIndex frameIndex => basisMatrix rowIndex (pickIndex frameIndex),
    ?_, ?_⟩
  · ext leftIndex rightIndex
    have hcolumns : ∑ rowIndex, basisMatrix rowIndex (pickIndex leftIndex)
        * basisMatrix rowIndex (pickIndex rightIndex)
          = (basisMatrixᵀ * basisMatrix) (pickIndex leftIndex) (pickIndex rightIndex) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [hcolumns, hleftInverse, Matrix.one_apply, Matrix.one_apply]
    by_cases hequal : leftIndex = rightIndex
    · rw [if_pos hequal, if_pos (congrArg pickIndex hequal)]
    · rw [if_neg hequal, if_neg fun habsurd => hequal (hpickInjective habsurd)]
  · ext rowIndex colIndex
    have hprojectionEntry : projection rowIndex colIndex
        = ∑ coordIndex, basisMatrix rowIndex coordIndex * eigenvalueVector coordIndex
            * basisMatrix colIndex coordIndex := by
      rw [hspectral, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun coordIndex _ => ?_
      rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    have hdropZero : ∑ coordIndex, basisMatrix rowIndex coordIndex * eigenvalueVector coordIndex
          * basisMatrix colIndex coordIndex
        = ∑ coordIndex ∈ activeSet,
            basisMatrix rowIndex coordIndex * basisMatrix colIndex coordIndex := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun coordIndex => eigenvalueVector coordIndex = 1)
        (fun coordIndex => basisMatrix rowIndex coordIndex * eigenvalueVector coordIndex
          * basisMatrix colIndex coordIndex)
      have hactivePart : ∑ coordIndex ∈ activeSet,
            basisMatrix rowIndex coordIndex * eigenvalueVector coordIndex
              * basisMatrix colIndex coordIndex
          = ∑ coordIndex ∈ activeSet,
              basisMatrix rowIndex coordIndex * basisMatrix colIndex coordIndex :=
        Finset.sum_congr rfl fun coordIndex hmember => by
          rw [(hmemberIff coordIndex).mp hmember, mul_one]
      have hinactivePart : ∑ coordIndex ∈ Finset.univ.filter
            (fun coordIndex => ¬ eigenvalueVector coordIndex = 1),
              basisMatrix rowIndex coordIndex * eigenvalueVector coordIndex
                * basisMatrix colIndex coordIndex = 0 :=
        Finset.sum_eq_zero fun coordIndex hmember => by
          rw [(hbinary coordIndex).resolve_right (Finset.mem_filter.mp hmember).2, mul_zero,
            zero_mul]
      rw [← hactiveSet] at hsplit
      rw [← hsplit, hactivePart, hinactivePart, add_zero]
    have hreindex : ∑ coordIndex ∈ activeSet,
          basisMatrix rowIndex coordIndex * basisMatrix colIndex coordIndex
        = ∑ frameIndex : Fin rank, basisMatrix rowIndex (pickIndex frameIndex)
            * basisMatrix colIndex (pickIndex frameIndex) := by
      rw [← hpickImage,
        Finset.sum_image fun left _ right _ hvalue => hpickInjective hvalue]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [hprojectionEntry, hdropZero, hreindex]

/-! ## From an orthonormal frame and positive weights to a weighted design -/

/-- **The design of an orthonormal frame.**  The atom at an index is the frame's row
there divided by the square root of the weight, which inverts `Gtz.scaledAtomRows`.

Parseval is exactly `frameᵀ frame = 1`: the weight multiplies the two halves of
`(sqrt t)⁻¹` back to one and nothing else survives.  POSITIVITY of the weight is
what makes the division legal, and it is the only place the interior hypothesis of
`Gtz.ChartPointHasDesign` is spent. -/
noncomputable def designOfOrthonormalFrame {size rank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    (weight : Fin size → ℝ) (hweightPos : ∀ atomIndex, 0 < weight atomIndex)
    (hweightSum : ∑ atomIndex, weight atomIndex = 1) : WeightedDesign size rank where
  atom atomIndex := fun coord => (Real.sqrt (weight atomIndex))⁻¹ * frame atomIndex coord
  weight := weight
  weight_pos := hweightPos
  weight_sum_one := hweightSum
  isParseval := by
    ext leftCoord rightCoord
    have hterm : ∀ atomIndex : Fin size,
        (weight atomIndex • atomMatrix
            (fun coord => (Real.sqrt (weight atomIndex))⁻¹ * frame atomIndex coord))
              leftCoord rightCoord
          = frame atomIndex leftCoord * frame atomIndex rightCoord := by
      intro atomIndex
      have hroot : Real.sqrt (weight atomIndex) * Real.sqrt (weight atomIndex)
          = weight atomIndex := Real.mul_self_sqrt (hweightPos atomIndex).le
      have hinverseSquare : (Real.sqrt (weight atomIndex))⁻¹ * (Real.sqrt (weight atomIndex))⁻¹
          = (weight atomIndex)⁻¹ := by rw [← mul_inv, hroot]
      simp only [Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
      calc weight atomIndex * ((Real.sqrt (weight atomIndex))⁻¹ * frame atomIndex leftCoord
              * ((Real.sqrt (weight atomIndex))⁻¹ * frame atomIndex rightCoord))
          = weight atomIndex
              * ((Real.sqrt (weight atomIndex))⁻¹ * (Real.sqrt (weight atomIndex))⁻¹)
              * (frame atomIndex leftCoord * frame atomIndex rightCoord) := by ring
        _ = weight atomIndex * (weight atomIndex)⁻¹
              * (frame atomIndex leftCoord * frame atomIndex rightCoord) := by
            rw [hinverseSquare]
        _ = frame atomIndex leftCoord * frame atomIndex rightCoord := by
            rw [mul_inv_cancel₀ (hweightPos atomIndex).ne', one_mul]
    have hgram : ∑ atomIndex, frame atomIndex leftCoord * frame atomIndex rightCoord
        = (frameᵀ * frame) leftCoord rightCoord := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Matrix.sum_apply, Finset.sum_congr rfl fun atomIndex _ => hterm atomIndex, hgram,
      hortho]

/-- The scaled frame of the design of a frame is that frame: the square roots
cancel.  This is the sense in which `Gtz.designOfOrthonormalFrame` inverts
`Gtz.scaledAtomRows`. -/
theorem scaledAtomRows_designOfOrthonormalFrame {size rank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    (weight : Fin size → ℝ) (hweightPos : ∀ atomIndex, 0 < weight atomIndex)
    (hweightSum : ∑ atomIndex, weight atomIndex = 1) :
    scaledAtomRows (designOfOrthonormalFrame frame hortho weight hweightPos hweightSum)
      = frame := by
  ext atomIndex coord
  show Real.sqrt (weight atomIndex)
      * ((Real.sqrt (weight atomIndex))⁻¹ * frame atomIndex coord) = frame atomIndex coord
  rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hweightPos atomIndex)).ne', one_mul]

/-- The projection chart of the design of a frame is `frame frameᵀ`. -/
theorem projectionOfDesign_designOfOrthonormalFrame {size rank : ℕ}
    (frame : Matrix (Fin size) (Fin rank) ℝ) (hortho : frameᵀ * frame = 1)
    (weight : Fin size → ℝ) (hweightPos : ∀ atomIndex, 0 < weight atomIndex)
    (hweightSum : ∑ atomIndex, weight atomIndex = 1) :
    projectionOfDesign (designOfOrthonormalFrame frame hortho weight hweightPos hweightSum)
      = frame * frameᵀ := by
  rw [projectionOfDesign, scaledAtomRows_designOfOrthonormalFrame]

/-! ## The leaf -/

/-- Two chart points agreeing on the chart and on the weights are equal: every
remaining field is a proof. -/
theorem chartPoint_eq_of_chart_eq_of_weight_eq {size rank : ℕ}
    (leftPoint rightPoint : ChartPoint size rank)
    (hchart : leftPoint.chart = rightPoint.chart)
    (hweight : leftPoint.weight = rightPoint.weight) : leftPoint = rightPoint := by
  obtain ⟨leftChart, leftWeight, _, _, _, _, _⟩ := leftPoint
  obtain ⟨rightChart, rightWeight, _, _, _, _, _⟩ := rightPoint
  have hchartField : leftChart = rightChart := hchart
  have hweightField : leftWeight = rightWeight := hweight
  subst hchartField
  subst hweightField
  rfl

/-- **THE LEAF, DISCHARGED, at every size and every rank.**  A chart point whose
weights are all strictly positive is the chart of a weighted design.

`Gtz/Reduction/CompactnessReduction.lean` names this as its unproved leaf number 2
and the sole obstruction to feeding the kernel-checked small rungs into the chart
side.  The interior hypothesis is genuinely consumed: it is what makes the division
by `sqrt (weight c)` in `Gtz.designOfOrthonormalFrame` legal, and no statement about
boundary chart points is claimed or provable this way. -/
theorem chartPointHasDesign (size rank : ℕ) : ChartPointHasDesign size rank := by
  intro point hpositive
  obtain ⟨frame, hortho, hframe⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent point.chart point.isSymmetric
      point.isIdempotent point.hasTraceRank
  refine ⟨designOfOrthonormalFrame frame hortho point.weight hpositive point.weight_sum_one, ?_⟩
  refine chartPoint_eq_of_chart_eq_of_weight_eq _ _ ?_ rfl
  show projectionOfDesign
      (designOfOrthonormalFrame frame hortho point.weight hpositive point.weight_sum_one)
    = point.chart
  rw [projectionOfDesign_designOfOrthonormalFrame, hframe]

/-- **THE INTERIOR HYPOTHESIS IS NOT REMOVABLE, and the boundary version is FALSE.**
A chart point with a vanishing weight is the chart of NO weighted design at all --
`Gtz.WeightedDesign` carries `weight_pos`, so the weights of a design's chart are
strictly positive by construction.

So `Gtz.ChartPointHasDesign` is stated at exactly the right generality: the
positivity in its antecedent is not a convenience of the proof above, and no
strengthening of that proof could drop it. -/
theorem not_exists_design_of_weight_eq_zero {size rank : ℕ} (point : ChartPoint size rank)
    {atomIndex : Fin size} (hvanishes : point.weight atomIndex = 0) :
    ¬ ∃ design : WeightedDesign size rank, chartPointOfDesign design = point := by
  rintro ⟨design, hdesign⟩
  have hweight : design.weight atomIndex = point.weight atomIndex :=
    congrArg (fun somePoint => ChartPoint.weight somePoint atomIndex) hdesign
  rw [hvanishes] at hweight
  exact absurd hweight (design.weight_pos atomIndex).ne'

/-! ## What the discharge buys, stated as plain equivalences -/

/-- `Gtz.chartGtzInterior_of_gtzWeighted` with its hypothesis removed. -/
theorem chartGtzInterior_of_gtzWeighted_unconditional {atoms rankValue : ℕ}
    (hweighted : GtzWeighted atoms rankValue) : ChartGtzInterior atoms rankValue :=
  chartGtzInterior_of_gtzWeighted (chartPointHasDesign atoms rankValue) hweighted

/-- **The interior chart obligation IS the weighted statement**, at the same size,
with no leaf on either side.  The forward direction is the density-free
`Gtz.gtzWeighted_of_chartGtzInterior`; the backward direction is the factorisation.

This is the equivalence `Gtz/Reduction/CompactnessReduction.lean`'s circularity
firewall states "with the factorisation leaf the implication reverses ... so the two
are equivalent" -- now without the modulo. -/
theorem chartGtzInterior_iff_gtzWeighted (atoms rankValue : ℕ) :
    ChartGtzInterior atoms rankValue ↔ GtzWeighted atoms rankValue :=
  ⟨gtzWeighted_of_chartGtzInterior, chartGtzInterior_of_gtzWeighted_unconditional⟩

/-- **The CLOSED chart statement is the weighted statement too.**  The boundary of
the compactification costs nothing: `Gtz.chartGtz_of_chartGtzInterior` mixes the
weights toward uniform, and the factorisation supplies the interior obligation from
the weighted one.

So `Gtz.ChartGtz` is not, after all, "strictly stronger as a hypothesis" than
`Gtz.GtzWeighted`, which is what its own docstring conjectured before the leaf was
discharged. -/
theorem chartGtz_iff_gtzWeighted (atoms rankValue : ℕ) :
    ChartGtz atoms rankValue ↔ GtzWeighted atoms rankValue :=
  ⟨gtzWeighted_of_chartGtz, fun hweighted =>
    chartGtz_of_chartGtzInterior (chartGtzInterior_of_gtzWeighted_unconditional hweighted)⟩

/-! ## The projection-covering reformulation, both directions -/

/-- The frame form of the covering statement implies the intrinsic form: every
symmetric idempotent of trace `rank` IS `frame frameᵀ` for an orthonormal-column
frame.  This is the direction `Gtz/LinAlg/ProjectionForm.lean` records as needing
"the spectral factorization this repo does not have". -/
theorem projectionCovering_of_frameProjectionCovering (atoms rankValue : ℕ)
    (hframeCovering : FrameProjectionCovering atoms rankValue) :
    ProjectionCovering atoms rankValue := by
  intro projection hsymmetric hidempotent htrace
  obtain ⟨frame, hortho, hframe⟩ :=
    exists_orthonormalFrame_of_symmetric_idempotent projection hsymmetric hidempotent htrace
  obtain ⟨rowPick, hinjective, hpsd⟩ := hframeCovering frame hortho
  exact ⟨rowPick, hinjective, by rwa [hframe] at hpsd⟩

/-- The two projection-covering statements agree. -/
theorem projectionCovering_iff_frameProjectionCovering (atoms rankValue : ℕ) :
    ProjectionCovering atoms rankValue ↔ FrameProjectionCovering atoms rankValue :=
  ⟨fun hcovering frame hortho =>
      hcovering (frame * frameᵀ) (mul_transpose_transpose frame)
        (mul_transpose_mul_self frame hortho) (trace_mul_transpose frame hortho),
    projectionCovering_of_frameProjectionCovering atoms rankValue⟩

/-- **Classical GTZ IS the intrinsic projection-covering statement** -- an iff, where
`Gtz.gtzOriginal_of_projectionCovering` had only the one direction. -/
theorem gtzOriginal_iff_projectionCovering (atoms rankValue : ℕ) (hatoms : 0 < atoms) :
    GtzOriginal atoms rankValue ↔ ProjectionCovering atoms rankValue :=
  (gtzOriginal_iff_frameProjectionCovering atoms hatoms).trans
    (projectionCovering_iff_frameProjectionCovering atoms rankValue).symm

end Gtz
