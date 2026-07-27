/-
# The MULTIPLIER SPLIT of the chart stationarity system — and the bridge to the design side

The companion of `Gtz.Quantitative.ChartStationary`, which bundles the first-order
data of the chart objective

    G(P, t) = max_{|C| = rank} lambda_min(W[C]),   W = P - diag t,

and derives the forced diagonal `(P Xi)_cc = (value + t_c)/size`.  That identity
is a statement about the AMBIENT `size x size` assembly.  This file resolves the
assembly into its two natural blocks — one on the range of the chart, one on its
kernel — and shows that the whole of the chart system is carried by the two
blocks and by nothing else.

## The frame pair

Everything below is stated against an explicit pair of isometries

    `rangeFrame : size x rank`   with  `Vᵀ V = 1` and `V Vᵀ = P` ,
    `kernelFrame : size x corank` with  `Zᵀ Z = 1` and `Z Zᵀ = 1 - P` ,

bundled as `IsChartFramePair`.  Note at once that this is STRICTLY MORE than the
chart-point conditions: `projection_transpose_of_isChartFramePair` and
`projection_mul_self_of_isChartFramePair` recover symmetry and idempotence from
the frame, and `trace_projection_of_isChartFramePair` recovers the trace, so a
frame determines a chart point but not conversely — see the honesty section.

## The two blocks, and what they carry (L5)

`chartRangeMultiplier V Xi = Vᵀ Xi V` and `chartKernelMultiplier Z Xi = Zᵀ Xi Z`
are the compressions of the assembly to the two subspaces.  Given
`IsChartStationaryData`:

* `posSemidef_chartRangeMultiplier`, `posSemidef_chartKernelMultiplier` — both
  blocks are positive semidefinite.  ONE LINE each, by compression: `M = Vᵀ Xi V`
  is a congruence of `Xi`.  Record this at its true size — the positive
  semidefiniteness of the two blocks carries NO information beyond that of `Xi`,
  so a "primal and dual multiplier conditions" reading of the split is empty in
  the forward direction.  All the content is in the equalities below and in the
  converse.
* `chartMultiplierAssembly_eq_frameSplit_of_isChartStationaryData` — **THE
  SPLIT**: `Xi = V M Vᵀ + Z N Zᵀ`.  Commutation makes the two off-diagonal blocks
  `P Xi (1 - P)` and `(1 - P) Xi P` vanish, and the two spanning identities turn
  the surviving corners into the two compressions.
* `rangeForm_chartRangeMultiplier_of_isChartStationaryData` — **the primal law**
  `v_cᵀ M v_c = (value + t_c)/size` at every atom, where `v_c` is the `c`-th ROW
  of `V`.  This is the forced diagonal of `Gtz.ChartStationary` read through the
  congruence.
* `kernelForm_chartKernelMultiplier_of_isChartStationaryData` — **the dual law**
  `z_cᵀ N z_c = (1 - value - t_c)/size`, the same argument run on the
  complementary projection.
* `trace_chartRangeMultiplier_of_isChartStationaryData`,
  `trace_chartKernelMultiplier_of_isChartStationaryData` — `tr M = value + 1/size`
  and `tr N = 1 - value - 1/size`, which add to `tr Xi = 1`.
* `exists_chartMultiplierSplit_of_isChartStationaryData` — the six facts above in
  the existential shape the campaign brief states them in.

## The CONVERSE, which is what an application invokes

`chartAssembledMultiplier V Z M N = V M Vᵀ + Z N Zᵀ` runs the construction
backwards, and the two stationarity conditions come out for free:

* `diagonal_chartAssembledMultiplier_eq_inv_size` — the constant diagonal `1/size`
  follows from the TWO LAWS ALONE.  No frame, no positive semidefiniteness: the
  two right-hand sides were built to add to `1/size` and that is the entire proof.
* `commutes_chartAssembledMultiplier_of_isChartFramePair` — the commutation
  follows from the FRAME ALONE, with neither law and neither positivity, because
  `P` fixes the range block and kills the kernel block on both sides.
* `posSemidef_chartAssembledMultiplier` — positive semidefiniteness follows from
  the two blocks' positive semidefiniteness alone.
* `isChartStationaryAssembly_of_chartMultiplierSplit` — the packaged converse,
  the only statement here that consumes all four inputs.

The three ingredients are stated separately BECAUSE each uses strictly less than
the packaged form, and an unused hypothesis in this repository is a defect.

**What this converse is NOT.**  It is the last clause of the brief's (E8) — "given
such `M` and `N`, (CS2) and (CS3) hold automatically" — and nothing more.  It is
NOT the brief's (E9), the claim that at `(6,3)` the six atom moments are a basis
of `Sym_3` so that `M` is the unique solution of a square system.  That claim is
FALSE exactly where a proof would need it: the moment-map rank is `4` of `6` at
the split tetrahedron, the split seven and near-pencil six, and `3` of `6` at the
octahedron, so the ENTIRE known `(6,3)` extremal locus is degenerate for it
[EXACT rational arithmetic, outside Lean, not mechanized].  Nothing below solves
a square system or claims uniqueness of either block.

## THE BRIDGE (L6) — why this is an extension and not a parallel development

At chart value ZERO the primal law becomes `t_c * (g_cᵀ M g_c) = t_c/size`, so
`Lambda := size * M` — `chartQuadricMultiplier` — satisfies

    `g_cᵀ Lambda g_c = 1` at every atom,   `tr Lambda = 1` ,

which is exactly the pair of conclusions
`Gtz.quadricLaw_of_isQuadricStationaryData` and
`Gtz.trace_multiplierMatrix_of_isQuadricStationaryData` produce at design value
ONE.  So the chart system, restricted to the extremal locus, MANUFACTURES a
design-side quadric multiplier out of chart data:

* `quadricLaw_of_chartQuadricMultiplier_of_value_zero`,
  `trace_chartQuadricMultiplier_of_value_zero`,
  `posSemidef_chartQuadricMultiplier` — the three properties.
* `quadricForm_chartQuadricMultiplier_eq_of_isQuadricStationaryData_value_one`
  and its trace twin — the CONNECTING theorems, stated against
  `Gtz.IsQuadricStationaryData` itself.
* `leverage_eq_rank_of_isotropic_chartQuadricMultiplier` — the chart mirror of
  `Gtz.leverage_eq_rank_of_isotropicMultiplier`, obtained by feeding the bridge
  into `Gtz.isotropicQuadric_iff_leverage_eq_rank`.
* `trace_mul_gap_of_chartQuadricMultiplier` — the gap-trace law
  `tr(Lambda (S_C - 1)) = rank - 1` at EVERY `rank`-subset, via
  `Gtz.trace_mul_gap_of_quadricLaw`.

**Read the bridge at exactly its size.**  Three separate warnings, all of them
recorded elsewhere in the repository and all of them live here.

* It is agreement of the LAWS at `value = 0`, not agreement of the two systems'
  MINIMISERS.  `Gtz.Reduction.CompactnessReduction`'s "THE OBJECTIVE MISMATCH"
  note stands unchanged: the congruence `diag(sqrt t_C)` rescales non-uniformly,
  so a critical point of one objective is not a critical point of the other.
* It does not say the two multipliers COINCIDE.  The quadric equations are `size`
  affine conditions on the `rank(rank+1)/2` independent entries of a symmetric
  multiplier and generally underdetermine it — at the tetrahedron the affine
  solution family is two-dimensional, as
  `Gtz.isotropicQuadric_iff_leverage_eq_rank`'s own docstring records.  The
  connecting theorems therefore state EQUALITY OF THE QUADRATIC FORMS on the
  atoms, which is what is true, and not equality of the matrices, which is not.
* It is not a transport.  The design-side multipliers of
  `Gtz.splitSevenDesign_isQuadricStationaryData` do NOT push forward: the naive
  transport leaves exact residuals `1/140` on the constant diagonal, `1/1280` on
  the commutation and `1/560` on the forced diagonal, and the chart system at
  that point is satisfied by a DIFFERENT multiplier vector [EXACT, outside Lean].
  Nothing below is obtained by transporting a theorem across.

Off the extremal locus the bridge FAILS, and audibly: with `Lambda = size * M` the
deviation `max_c |g_cᵀ Lambda g_c - 1|` is `0.500` at the `D3` root design, `0.658`
at the icosahedron, `1.000` at the reach witness and `2.000` at the octahedron
[EXACT/numeric, outside Lean, not mechanized].  The `value = 0` hypothesis is
load-bearing and is not decoration.

## THE WITNESS — the tetrahedron, reproducing the hand computation

`chartSplitTetraIsChartFramePair` exhibits the frame pair at `(4,3)`:
`V = Gtz.scaledAtomRows Gtz.tetraDesign` and `Z` the single normalised all-ones
column.  Against the tetrahedron datum of `Gtz.ChartStationary`, whose assembly is
`Xi = I_4/12 + J_4/6`, the two blocks come out as

    `M = I_3/12` ,   `N = 3/4` (a scalar, the kernel is a line) ,
    `Lambda = size * M = I_3/3` ,

which are the hand-computed reference values of the campaign brief, on the nose.
`exists_isChartStationaryData_value_zero_chartQuadricMultiplier_eq` packages the
inhabitation and the value together, so the bridge is not a statement about an
empty class.

## HONESTY — the frame hypothesis IS the unproved leaf

`IsChartFramePair` is a HYPOTHESIS everywhere below, exactly as
`IsChartStationaryData` is in the companion file.  Producing one from a bare chart
point requires factoring a symmetric idempotent of trace `rank` as `V Vᵀ` with
`Vᵀ V = 1`, which is the spectral factorisation this repository does not carry —
`Gtz.LinAlg.ProjectionForm`'s header says so in its own words ("a spectral
factorization that neither this file nor the repo has"), and it is the same
content as `Gtz.ChartPointHasDesign`.  So the split is available for free at a
chart point that ARRIVES with a frame (a design's chart always does, via
`Gtz.scaledAtomRows`) and is unavailable at an abstract chart point.  This is the
same leaf `Gtz.Quantitative.ChartStationary` records under its honesty item (d),
and it does not drop out here either.

Two smaller disclosures.  The `corank` is carried as a free natural number rather
than as `size - rank`, because the bundle already pins it —
`corank_cast_eq_of_isChartFramePair` proves `corank = size - rank` as reals — so
a truncated natural subtraction would cost something and buy nothing.  And
nothing below asserts that the split is UNIQUE: it is, given the frame, since
`M` and `N` are literally compressions of `Xi`, but the frame itself is unique
only up to an orthogonal change of basis in each block, and nothing here needs
or claims otherwise.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.ChartStationary
import Gtz.Quantitative.CriticalQuadric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank corank : ℕ} {activeIndex : Type*}

/-! ## A design-free bracket -/

/-- **The diagonal of a congruence is a row quadratic form.**  `(A B Aᵀ)_cc` is the
`c`-th row of `A` paired with itself through `B`.  This is the single computation
that turns every block statement below into a statement about atoms. -/
theorem diagonal_frameCongruence_eq_rowForm {dim : ℕ} (frame : Matrix (Fin size) (Fin dim) ℝ)
    (block : Matrix (Fin dim) (Fin dim) ℝ) (atomIndex : Fin size) :
    (frame * block * frameᵀ) atomIndex atomIndex
      = frame atomIndex ⬝ᵥ (block *ᵥ frame atomIndex) := by
  have hleft : (frame * block * frameᵀ) atomIndex atomIndex
      = ∑ colDim : Fin dim,
          (∑ rowDim : Fin dim, frame atomIndex rowDim * block rowDim colDim)
            * frame atomIndex colDim := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hright : frame atomIndex ⬝ᵥ (block *ᵥ frame atomIndex)
      = ∑ rowDim : Fin dim, frame atomIndex rowDim
          * ∑ colDim : Fin dim, block rowDim colDim * frame atomIndex colDim := by
    simp only [dotProduct, Matrix.mulVec]
  rw [hleft, hright]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ## The frame pair -/

/-- **A CHART FRAME PAIR**: an isometry whose columns span the range of the chart,
together with one whose columns span its kernel.

This is a HYPOTHESIS.  Every symmetric idempotent admits one, but producing it is
the spectral factorisation the repository does not carry; see the honesty section
of the file header.  A design's chart arrives with its range frame already built —
`Gtz.scaledAtomRows` — which is why the bridge below is stated for designs. -/
structure IsChartFramePair (projection : Matrix (Fin size) (Fin size) ℝ)
    (rangeFrame : Matrix (Fin size) (Fin rank) ℝ)
    (kernelFrame : Matrix (Fin size) (Fin corank) ℝ) : Prop where
  /-- The range frame's columns are orthonormal. -/
  rangeFrame_isIsometry : rangeFrameᵀ * rangeFrame = 1
  /-- The range frame's columns span the chart. -/
  rangeFrame_spansRange : rangeFrame * rangeFrameᵀ = projection
  /-- The kernel frame's columns are orthonormal. -/
  kernelFrame_isIsometry : kernelFrameᵀ * kernelFrame = 1
  /-- The kernel frame's columns span the complementary chart. -/
  kernelFrame_spansKernel : kernelFrame * kernelFrameᵀ = 1 - projection

variable {projection : Matrix (Fin size) (Fin size) ℝ}
  {rangeFrame : Matrix (Fin size) (Fin rank) ℝ}
  {kernelFrame : Matrix (Fin size) (Fin corank) ℝ}

/-- A framed chart is symmetric. -/
theorem projection_transpose_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    projectionᵀ = projection := by
  rw [← hframe.rangeFrame_spansRange, Matrix.transpose_mul, Matrix.transpose_transpose]

/-- A framed chart is idempotent — this step, and only this step, consumes the
range isometry. -/
theorem projection_mul_self_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    projection * projection = projection := by
  rw [← hframe.rangeFrame_spansRange, Matrix.mul_assoc, ← Matrix.mul_assoc rangeFrameᵀ,
    hframe.rangeFrame_isIsometry, Matrix.one_mul]

/-- A framed chart has trace exactly `rank`, so the column count of the range
frame is not free: it is determined by the chart. -/
theorem trace_projection_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    Matrix.trace projection = (rank : ℝ) := by
  rw [← hframe.rangeFrame_spansRange, Matrix.trace_mul_comm, hframe.rangeFrame_isIsometry,
    Matrix.trace_one, Fintype.card_fin]

/-- **The corank is not free either**: the kernel frame's column count is forced
to `size - rank`, as reals.  Its trace is read twice, once through `Zᵀ Z = 1` and
once through `Z Zᵀ = 1 - P`.

This is why `corank` enters below as a plain natural number and never as a
truncated natural subtraction: the bundle already pins it, so writing
`size - rank` would add a truncation and buy nothing. -/
theorem corank_cast_eq_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    (corank : ℝ) = (size : ℝ) - (rank : ℝ) := by
  have hkernelTrace : Matrix.trace (kernelFrame * kernelFrameᵀ) = (corank : ℝ) := by
    rw [Matrix.trace_mul_comm, hframe.kernelFrame_isIsometry, Matrix.trace_one, Fintype.card_fin]
  rw [hframe.kernelFrame_spansKernel, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    trace_projection_of_isChartFramePair hframe] at hkernelTrace
  exact hkernelTrace.symm

/-- **The two frames are orthogonal to each other.**  `P (1 - P) = 0` sandwiched
between the two isometries collapses to `Vᵀ Z = 0`. -/
theorem transpose_rangeFrame_mul_kernelFrame_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    rangeFrameᵀ * kernelFrame = 0 := by
  have hortho : rangeFrame * rangeFrameᵀ * (kernelFrame * kernelFrameᵀ) = 0 := by
    rw [hframe.rangeFrame_spansRange, hframe.kernelFrame_spansKernel, Matrix.mul_sub,
      Matrix.mul_one, projection_mul_self_of_isChartFramePair hframe, sub_self]
  have hexpand : rangeFrameᵀ * (rangeFrame * rangeFrameᵀ * (kernelFrame * kernelFrameᵀ))
        * kernelFrame
      = rangeFrameᵀ * rangeFrame * (rangeFrameᵀ * kernelFrame)
        * (kernelFrameᵀ * kernelFrame) := by
    simp only [Matrix.mul_assoc]
  rw [hortho, Matrix.mul_zero, Matrix.zero_mul, hframe.rangeFrame_isIsometry,
    hframe.kernelFrame_isIsometry, Matrix.one_mul, Matrix.mul_one] at hexpand
  exact hexpand.symm

/-- The transposed reading of the orthogonality. -/
theorem transpose_kernelFrame_mul_rangeFrame_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    kernelFrameᵀ * rangeFrame = 0 := by
  have hflipped :=
    congrArg Matrix.transpose (transpose_rangeFrame_mul_kernelFrame_of_isChartFramePair hframe)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at hflipped

/-- The chart fixes its own range frame. -/
theorem projection_mul_rangeFrame_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    projection * rangeFrame = rangeFrame := by
  rw [← hframe.rangeFrame_spansRange, Matrix.mul_assoc, hframe.rangeFrame_isIsometry,
    Matrix.mul_one]

/-- The chart annihilates its own kernel frame. -/
theorem projection_mul_kernelFrame_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame) :
    projection * kernelFrame = 0 := by
  rw [← hframe.rangeFrame_spansRange, Matrix.mul_assoc,
    transpose_rangeFrame_mul_kernelFrame_of_isChartFramePair hframe, Matrix.mul_zero]

/-! ## The two blocks -/

/-- **The RANGE block** `M = Vᵀ Xi V`, the compression of the assembly to the
chart's range. -/
def chartRangeMultiplier (rangeFrame : Matrix (Fin size) (Fin rank) ℝ)
    (assembly : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin rank) (Fin rank) ℝ :=
  rangeFrameᵀ * assembly * rangeFrame

/-- **The KERNEL block** `N = Zᵀ Xi Z`, the compression of the assembly to the
chart's kernel — the Naimark mirror of the range block. -/
def chartKernelMultiplier (kernelFrame : Matrix (Fin size) (Fin corank) ℝ)
    (assembly : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin corank) (Fin corank) ℝ :=
  kernelFrameᵀ * assembly * kernelFrame

/-- **The range block is positive semidefinite**, by compression, in one line.

DISCLOSURE, so the reach is not overstated: this needs nothing of the chart, the
frame or the laws — only that `Xi` is positive semidefinite, which the companion
file proves from nonnegative multipliers alone.  The primal half of a "primal and
Naimark-dual multiplier conditions" reading of the split is therefore EMPTY in
the forward direction, and the same holds for the dual half below.  What carries
content is the pair of EQUALITIES, and the converse. -/
theorem posSemidef_chartRangeMultiplier {assembly : Matrix (Fin size) (Fin size) ℝ}
    (hassembly : assembly.PosSemidef) (rangeFrame : Matrix (Fin size) (Fin rank) ℝ) :
    (chartRangeMultiplier rangeFrame assembly).PosSemidef := by
  have hcongruence := hassembly.mul_mul_conjTranspose_same rangeFrameᵀ
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at hcongruence

/-- **The kernel block is positive semidefinite**, by the same one-line
compression.  See the disclosure on the range block. -/
theorem posSemidef_chartKernelMultiplier {assembly : Matrix (Fin size) (Fin size) ℝ}
    (hassembly : assembly.PosSemidef) (kernelFrame : Matrix (Fin size) (Fin corank) ℝ) :
    (chartKernelMultiplier kernelFrame assembly).PosSemidef := by
  have hcongruence := hassembly.mul_mul_conjTranspose_same kernelFrameᵀ
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at hcongruence

/-- Re-expanding the range block into the chart: `V M Vᵀ = P Xi P`. -/
theorem rangeFrame_mul_chartRangeMultiplier_mul_transpose
    (hspan : rangeFrame * rangeFrameᵀ = projection)
    (assembly : Matrix (Fin size) (Fin size) ℝ) :
    rangeFrame * chartRangeMultiplier rangeFrame assembly * rangeFrameᵀ
      = projection * assembly * projection := by
  rw [chartRangeMultiplier, ← hspan]
  simp only [Matrix.mul_assoc]

/-- Re-expanding the kernel block: `Z N Zᵀ = (1 - P) Xi (1 - P)`. -/
theorem kernelFrame_mul_chartKernelMultiplier_mul_transpose
    (hspan : kernelFrame * kernelFrameᵀ = 1 - projection)
    (assembly : Matrix (Fin size) (Fin size) ℝ) :
    kernelFrame * chartKernelMultiplier kernelFrame assembly * kernelFrameᵀ
      = (1 - projection) * assembly * (1 - projection) := by
  rw [chartKernelMultiplier, ← hspan]
  simp only [Matrix.mul_assoc]

/-! ## L5: what the blocks carry, given chart stationarity data -/

variable {weight : Fin size → ℝ} {value : ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin size)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin size → ℝ)}

/-- **The complementary congruence.**  `(1 - P) Xi = (1 - P) Xi (1 - P)`, the
Naimark mirror of `Gtz.projection_mul_multiplier_eq_sandwich_of_isChartStationaryData`.
The complementary projection is again a symmetric idempotent commuting with the
assembly, so the one-sided product is already two-sided. -/
theorem complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
      = (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
        * (1 - projection) := by
  have hcomplementIdempotent :
      (1 - projection) * (1 - projection)
        = (1 - projection : Matrix (Fin size) (Fin size) ℝ) := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.isIdempotent, sub_self, sub_zero]
  have hcomplementCommutes :
      (1 - projection) * chartMultiplierAssembly activeSet activeWeight tightDir
        = chartMultiplierAssembly activeSet activeWeight tightDir * (1 - projection) := by
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hdata.assembly_commutes]
  rw [Matrix.mul_assoc, ← hcomplementCommutes, ← Matrix.mul_assoc, hcomplementIdempotent]

/-- **THE PRIMAL LAW (E8).**  At every atom,

    `v_cᵀ M v_c = (value + t_c) / size` ,

with `v_c` the `c`-th ROW of the range frame.  The forced diagonal of the
companion file, read through the congruence `V M Vᵀ = P Xi P = P Xi`.

Only the SPANNING identity `V Vᵀ = P` is used; the isometry is not. -/
theorem rangeForm_chartRangeMultiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hspan : rangeFrame * rangeFrameᵀ = projection)
    (atomIndex : Fin size) :
    rangeFrame atomIndex
        ⬝ᵥ (chartRangeMultiplier rangeFrame
              (chartMultiplierAssembly activeSet activeWeight tightDir)
            *ᵥ rangeFrame atomIndex)
      = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
  rw [← diagonal_frameCongruence_eq_rowForm,
    rangeFrame_mul_chartRangeMultiplier_mul_transpose hspan,
    ← projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex]

/-- **THE DUAL LAW (E8).**  At every atom,

    `z_cᵀ N z_c = (1 - value - t_c) / size` ,

with `z_c` the `c`-th ROW of the kernel frame.  The complementary congruence
`Z N Zᵀ = (1 - P) Xi` has diagonal `Xi_cc - (P Xi)_cc`, and the constant diagonal
of the assembly supplies the first term.

This is the one condition of the chart system with no design-side analogue. -/
theorem kernelForm_chartKernelMultiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hspan : kernelFrame * kernelFrameᵀ = 1 - projection)
    (atomIndex : Fin size) :
    kernelFrame atomIndex
        ⬝ᵥ (chartKernelMultiplier kernelFrame
              (chartMultiplierAssembly activeSet activeWeight tightDir)
            *ᵥ kernelFrame atomIndex)
      = (1 - value - weight atomIndex) * ((size : ℝ))⁻¹ := by
  rw [← diagonal_frameCongruence_eq_rowForm,
    kernelFrame_mul_chartKernelMultiplier_mul_transpose hspan,
    ← complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
    Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hdata.assembly_diagonal atomIndex,
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex]
  ring

/-- **The range block's trace**: `tr M = value + 1/size`, the trace form of the
forced diagonal moved across the congruence. -/
theorem trace_chartRangeMultiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hspan : rangeFrame * rangeFrameᵀ = projection) :
    Matrix.trace (chartRangeMultiplier rangeFrame
        (chartMultiplierAssembly activeSet activeWeight tightDir))
      = value + ((size : ℝ))⁻¹ := by
  rw [chartRangeMultiplier, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hspan]
  exact trace_projection_mul_multiplier_of_isChartStationaryData hdata

/-- **The kernel block's trace**: `tr N = 1 - value - 1/size`.  The two traces add
to `tr Xi = 1`, which is the trace form of the constant diagonal. -/
theorem trace_chartKernelMultiplier_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hspan : kernelFrame * kernelFrameᵀ = 1 - projection) :
    Matrix.trace (chartKernelMultiplier kernelFrame
        (chartMultiplierAssembly activeSet activeWeight tightDir))
      = 1 - value - ((size : ℝ))⁻¹ := by
  rw [chartKernelMultiplier, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hspan, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_sub, trace_chartMultiplierAssembly_of_isChartStationaryData hdata,
    trace_projection_mul_multiplier_of_isChartStationaryData hdata]
  ring

/-- **THE SPLIT.**  `Xi = V M Vᵀ + Z N Zᵀ`.

Commutation makes `P Xi P = Xi P` and `(1 - P) Xi (1 - P) = Xi - Xi P`, so the two
corners already exhaust the assembly and the two off-diagonal blocks are zero.
Only the two SPANNING identities are used. -/
theorem chartMultiplierAssembly_eq_frameSplit_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hrangeSpan : rangeFrame * rangeFrameᵀ = projection)
    (hkernelSpan : kernelFrame * kernelFrameᵀ = 1 - projection) :
    chartMultiplierAssembly activeSet activeWeight tightDir
      = rangeFrame * chartRangeMultiplier rangeFrame
            (chartMultiplierAssembly activeSet activeWeight tightDir) * rangeFrameᵀ
        + kernelFrame * chartKernelMultiplier kernelFrame
            (chartMultiplierAssembly activeSet activeWeight tightDir) * kernelFrameᵀ := by
  rw [rangeFrame_mul_chartRangeMultiplier_mul_transpose hrangeSpan,
    kernelFrame_mul_chartKernelMultiplier_mul_transpose hkernelSpan,
    ← projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
    ← complementProjection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata,
    Matrix.sub_mul, Matrix.one_mul]
  abel

/-- **(E8) IN THE SHAPE THE CAMPAIGN BRIEF STATES IT**: there exist symmetric
positive semidefinite blocks `M` and `N` splitting the assembly and obeying the
two quadric laws and the two trace laws.

The named theorems above are strictly more informative — they exhibit the two
blocks as the compressions `Vᵀ Xi V` and `Zᵀ Xi Z` rather than merely asserting
existence — and are what the converse and the bridge consume.  This packaging is
here so that the brief's statement is literally present. -/
theorem exists_chartMultiplierSplit_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hrangeSpan : rangeFrame * rangeFrameᵀ = projection)
    (hkernelSpan : kernelFrame * kernelFrameᵀ = 1 - projection) :
    ∃ (rangeBlock : Matrix (Fin rank) (Fin rank) ℝ)
      (kernelBlock : Matrix (Fin corank) (Fin corank) ℝ),
      rangeBlock.PosSemidef ∧ kernelBlock.PosSemidef
        ∧ chartMultiplierAssembly activeSet activeWeight tightDir
            = rangeFrame * rangeBlock * rangeFrameᵀ + kernelFrame * kernelBlock * kernelFrameᵀ
        ∧ (∀ atomIndex : Fin size, rangeFrame atomIndex ⬝ᵥ (rangeBlock *ᵥ rangeFrame atomIndex)
            = (value + weight atomIndex) * ((size : ℝ))⁻¹)
        ∧ (∀ atomIndex : Fin size, kernelFrame atomIndex ⬝ᵥ (kernelBlock *ᵥ kernelFrame atomIndex)
            = (1 - value - weight atomIndex) * ((size : ℝ))⁻¹)
        ∧ Matrix.trace rangeBlock = value + ((size : ℝ))⁻¹
        ∧ Matrix.trace kernelBlock = 1 - value - ((size : ℝ))⁻¹ :=
  ⟨chartRangeMultiplier rangeFrame (chartMultiplierAssembly activeSet activeWeight tightDir),
    chartKernelMultiplier kernelFrame (chartMultiplierAssembly activeSet activeWeight tightDir),
    posSemidef_chartRangeMultiplier
      (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata) rangeFrame,
    posSemidef_chartKernelMultiplier
      (posSemidef_chartMultiplierAssembly_of_isChartStationaryData hdata) kernelFrame,
    chartMultiplierAssembly_eq_frameSplit_of_isChartStationaryData hdata hrangeSpan hkernelSpan,
    fun atomIndex =>
      rangeForm_chartRangeMultiplier_of_isChartStationaryData hdata hrangeSpan atomIndex,
    fun atomIndex =>
      kernelForm_chartKernelMultiplier_of_isChartStationaryData hdata hkernelSpan atomIndex,
    trace_chartRangeMultiplier_of_isChartStationaryData hdata hrangeSpan,
    trace_chartKernelMultiplier_of_isChartStationaryData hdata hkernelSpan⟩

/-! ## The converse -/

/-- **The assembly built from two blocks**, `Xi = V M Vᵀ + Z N Zᵀ`. -/
def chartAssembledMultiplier (rangeFrame : Matrix (Fin size) (Fin rank) ℝ)
    (kernelFrame : Matrix (Fin size) (Fin corank) ℝ)
    (rangeBlock : Matrix (Fin rank) (Fin rank) ℝ)
    (kernelBlock : Matrix (Fin corank) (Fin corank) ℝ) : Matrix (Fin size) (Fin size) ℝ :=
  rangeFrame * rangeBlock * rangeFrameᵀ + kernelFrame * kernelBlock * kernelFrameᵀ

/-- **The two stationarity conditions on an assembly** — the constant diagonal
`1/size` from varying the SIMPLEX and the commutation with the chart from varying
the GRASSMANNIAN.  These are exactly the last two fields of
`Gtz.IsChartStationaryData`, named here so the converse has something to conclude. -/
def IsChartStationaryAssembly (projection : Matrix (Fin size) (Fin size) ℝ)
    (assembly : Matrix (Fin size) (Fin size) ℝ) : Prop :=
  (∀ atomIndex : Fin size, assembly atomIndex atomIndex = ((size : ℝ))⁻¹)
    ∧ projection * assembly = assembly * projection

/-- The naming is faithful: a chart stationarity datum's assembly is a chart
stationary assembly, by the two fields and nothing else. -/
theorem isChartStationaryAssembly_of_isChartStationaryData
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    IsChartStationaryAssembly projection
      (chartMultiplierAssembly activeSet activeWeight tightDir) :=
  ⟨hdata.assembly_diagonal, hdata.assembly_commutes⟩

variable {rangeBlock : Matrix (Fin rank) (Fin rank) ℝ}
  {kernelBlock : Matrix (Fin corank) (Fin corank) ℝ}

/-- **THE CONSTANT DIAGONAL, from the two laws alone.**  Neither the frame nor
any positivity enters: the two right-hand sides `(value + t_c)/size` and
`(1 - value - t_c)/size` were built to add to `1/size`, and that is the whole
proof. -/
theorem diagonal_chartAssembledMultiplier_eq_inv_size
    (hrangeLaw : ∀ atomIndex : Fin size,
      rangeFrame atomIndex ⬝ᵥ (rangeBlock *ᵥ rangeFrame atomIndex)
        = (value + weight atomIndex) * ((size : ℝ))⁻¹)
    (hkernelLaw : ∀ atomIndex : Fin size,
      kernelFrame atomIndex ⬝ᵥ (kernelBlock *ᵥ kernelFrame atomIndex)
        = (1 - value - weight atomIndex) * ((size : ℝ))⁻¹)
    (atomIndex : Fin size) :
    chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock atomIndex atomIndex
      = ((size : ℝ))⁻¹ := by
  rw [chartAssembledMultiplier, Matrix.add_apply, diagonal_frameCongruence_eq_rowForm,
    diagonal_frameCongruence_eq_rowForm, hrangeLaw, hkernelLaw]
  ring

/-- The chart acting on the assembled multiplier from the left keeps the range
block and kills the kernel block. -/
theorem projection_mul_chartAssembledMultiplier_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame)
    (rangeBlock : Matrix (Fin rank) (Fin rank) ℝ)
    (kernelBlock : Matrix (Fin corank) (Fin corank) ℝ) :
    projection * chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock
      = rangeFrame * rangeBlock * rangeFrameᵀ := by
  rw [chartAssembledMultiplier, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [projection_mul_rangeFrame_of_isChartFramePair hframe,
    projection_mul_kernelFrame_of_isChartFramePair hframe, Matrix.zero_mul, Matrix.zero_mul,
    add_zero]

/-- The same from the right, by the transposed orthogonality. -/
theorem chartAssembledMultiplier_mul_projection_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame)
    (rangeBlock : Matrix (Fin rank) (Fin rank) ℝ)
    (kernelBlock : Matrix (Fin corank) (Fin corank) ℝ) :
    chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock * projection
      = rangeFrame * rangeBlock * rangeFrameᵀ := by
  have hrangeFix : rangeFrameᵀ * projection = rangeFrameᵀ := by
    rw [← hframe.rangeFrame_spansRange, ← Matrix.mul_assoc, hframe.rangeFrame_isIsometry,
      Matrix.one_mul]
  have hkernelKill : kernelFrameᵀ * projection = 0 := by
    rw [← hframe.rangeFrame_spansRange, ← Matrix.mul_assoc,
      transpose_kernelFrame_mul_rangeFrame_of_isChartFramePair hframe, Matrix.zero_mul]
  rw [chartAssembledMultiplier, Matrix.add_mul]
  simp only [Matrix.mul_assoc]
  rw [hrangeFix, hkernelKill, Matrix.mul_zero, Matrix.mul_zero, add_zero]

/-- **THE COMMUTATION, from the frame alone.**  Neither law and neither positivity
enters: both products equal the range block re-expanded. -/
theorem commutes_chartAssembledMultiplier_of_isChartFramePair
    (hframe : IsChartFramePair projection rangeFrame kernelFrame)
    (rangeBlock : Matrix (Fin rank) (Fin rank) ℝ)
    (kernelBlock : Matrix (Fin corank) (Fin corank) ℝ) :
    projection * chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock
      = chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock * projection := by
  rw [projection_mul_chartAssembledMultiplier_of_isChartFramePair hframe,
    chartAssembledMultiplier_mul_projection_of_isChartFramePair hframe]

/-- **Positive semidefiniteness, from the two blocks alone** — a sum of two
congruences.  This is the direction in which positivity of the blocks has
content; the forward compressions above give it for free. -/
theorem posSemidef_chartAssembledMultiplier
    (hrangeBlock : rangeBlock.PosSemidef) (hkernelBlock : kernelBlock.PosSemidef)
    (rangeFrame : Matrix (Fin size) (Fin rank) ℝ)
    (kernelFrame : Matrix (Fin size) (Fin corank) ℝ) :
    (chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock).PosSemidef := by
  have hrangeCongruence := hrangeBlock.mul_mul_conjTranspose_same rangeFrame
  have hkernelCongruence := hkernelBlock.mul_mul_conjTranspose_same kernelFrame
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hrangeCongruence hkernelCongruence
  exact hrangeCongruence.add hkernelCongruence

/-- **THE CONVERSE, packaged** — the statement an application invokes.  Given a
frame pair and two positive semidefinite blocks obeying the two quadric laws, the
assembled `Xi` is positive semidefinite AND satisfies both stationarity
conditions, with no further work.

What this does NOT supply, and what a full instantiation of
`Gtz.IsChartStationaryData` would still need: a presentation of `Xi` as a
NONNEGATIVE COMBINATION OF RANK-ONE PROJECTORS ONTO TIGHT DIRECTIONS.  Re-expressing
a positive semidefinite matrix that way is a spectral decomposition, which this
repository does not carry, and tightness is genuinely extra information about the
chart gap.  So the converse closes the multiplier algebra and not the bundle. -/
theorem isChartStationaryAssembly_of_chartMultiplierSplit
    (hframe : IsChartFramePair projection rangeFrame kernelFrame)
    (hrangeLaw : ∀ atomIndex : Fin size,
      rangeFrame atomIndex ⬝ᵥ (rangeBlock *ᵥ rangeFrame atomIndex)
        = (value + weight atomIndex) * ((size : ℝ))⁻¹)
    (hkernelLaw : ∀ atomIndex : Fin size,
      kernelFrame atomIndex ⬝ᵥ (kernelBlock *ᵥ kernelFrame atomIndex)
        = (1 - value - weight atomIndex) * ((size : ℝ))⁻¹) :
    IsChartStationaryAssembly projection
      (chartAssembledMultiplier rangeFrame kernelFrame rangeBlock kernelBlock) :=
  ⟨fun atomIndex =>
      diagonal_chartAssembledMultiplier_eq_inv_size hrangeLaw hkernelLaw atomIndex,
    commutes_chartAssembledMultiplier_of_isChartFramePair hframe rangeBlock kernelBlock⟩

/-! ## L6: the bridge to the design-side quadric law -/

/-- **The design-side multiplier the chart manufactures**: `Lambda = size * M`.
At chart value zero this is the object that satisfies
`Gtz.quadricLaw_of_isQuadricStationaryData` at design value ONE. -/
def chartQuadricMultiplier (rangeFrame : Matrix (Fin size) (Fin rank) ℝ)
    (assembly : Matrix (Fin size) (Fin size) ℝ) : Matrix (Fin rank) (Fin rank) ℝ :=
  ((size : ℝ)) • chartRangeMultiplier rangeFrame assembly

/-- **A design's chart arrives with its range frame already built.**  The scaled
Parseval frame of `Gtz.LinAlg.ProjectionForm` spans the design's chart by
definition, so no spectral factorisation is needed at a design. -/
theorem scaledAtomRows_mul_transpose (design : WeightedDesign size rank) :
    scaledAtomRows design * (scaledAtomRows design)ᵀ = projectionOfDesign design := rfl

/-- **THE BRIDGE (E11), the quadric half.**  At chart value ZERO every atom of the
design lies on the central quadric of `Lambda = size * M` at level exactly ONE:

    `g_cᵀ Lambda g_c = 1`   at every atom `c` .

The primal law reads `t_c * (g_cᵀ M g_c) = t_c / size` because the `c`-th row of
the scaled frame is `sqrt(t_c) * g_c`; the strictly positive weight cancels, and
rescaling by `size` lands on one.

This is the conclusion of `Gtz.quadricLaw_of_isQuadricStationaryData` at
`value = 1`, produced from CHART data.  The `value = 0` hypothesis is load-bearing:
off the extremal locus the deviation is order one — `2.000` at the octahedron
[numeric, outside Lean, not mechanized]. -/
theorem quadricLaw_of_chartQuadricMultiplier_of_value_zero
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hweight : weight = design.weight)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (atomLabel : Fin size) :
    design.atom atomLabel
        ⬝ᵥ (chartQuadricMultiplier (scaledAtomRows design)
              (chartMultiplierAssembly activeSet activeWeight tightDir)
            *ᵥ design.atom atomLabel)
      = 1 := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
  have hspan : scaledAtomRows design * (scaledAtomRows design)ᵀ = projection := by
    rw [hchart]; exact scaledAtomRows_mul_transpose design
  have hprimal :=
    rangeForm_chartRangeMultiplier_of_isChartStationaryData hdata hspan atomLabel
  rw [hweight] at hprimal
  -- the row of the scaled frame is the atom rescaled by the square root of its weight
  have hrow : scaledAtomRows design atomLabel
      = Real.sqrt (design.weight atomLabel) • design.atom atomLabel := scaledAtomRows_row _ _
  have hscaled : scaledAtomRows design atomLabel
      ⬝ᵥ (chartRangeMultiplier (scaledAtomRows design)
            (chartMultiplierAssembly activeSet activeWeight tightDir)
          *ᵥ scaledAtomRows design atomLabel)
      = design.weight atomLabel
        * (design.atom atomLabel
            ⬝ᵥ (chartRangeMultiplier (scaledAtomRows design)
                  (chartMultiplierAssembly activeSet activeWeight tightDir)
                *ᵥ design.atom atomLabel)) := by
    rw [hrow, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Real.mul_self_sqrt (design.weight_pos atomLabel).le]
  rw [hscaled, zero_add] at hprimal
  have hunscaled : design.atom atomLabel
      ⬝ᵥ (chartRangeMultiplier (scaledAtomRows design)
            (chartMultiplierAssembly activeSet activeWeight tightDir)
          *ᵥ design.atom atomLabel)
      = ((size : ℝ))⁻¹ :=
    mul_left_cancel₀ (ne_of_gt (design.weight_pos atomLabel)) hprimal
  rw [chartQuadricMultiplier, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hunscaled,
    mul_inv_cancel₀ hsizeNe]

/-- **THE BRIDGE (E11), the trace half.**  `tr Lambda = 1` — the conclusion of
`Gtz.trace_multiplierMatrix_of_isQuadricStationaryData` at `value = 1`, again
produced from chart data.  The range block's trace is `0 + 1/size` at chart value
zero, and `Lambda` rescales it by `size`. -/
theorem trace_chartQuadricMultiplier_of_value_zero
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) :
    Matrix.trace (chartQuadricMultiplier (scaledAtomRows design)
        (chartMultiplierAssembly activeSet activeWeight tightDir))
      = 1 := by
  have hsizeNe : ((size : ℝ)) ≠ 0 := ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
  have hspan : scaledAtomRows design * (scaledAtomRows design)ᵀ = projection := by
    rw [hchart]; exact scaledAtomRows_mul_transpose design
  rw [chartQuadricMultiplier, Matrix.trace_smul,
    trace_chartRangeMultiplier_of_isChartStationaryData hdata hspan, zero_add, smul_eq_mul,
    mul_inv_cancel₀ hsizeNe]

/-- `Lambda` is positive semidefinite, the range block rescaled by a nonnegative
number. -/
theorem posSemidef_chartQuadricMultiplier {assembly : Matrix (Fin size) (Fin size) ℝ}
    (hassembly : assembly.PosSemidef) (rangeFrame : Matrix (Fin size) (Fin rank) ℝ) :
    (chartQuadricMultiplier rangeFrame assembly).PosSemidef :=
  (posSemidef_chartRangeMultiplier hassembly rangeFrame).smul (Nat.cast_nonneg size)

/-- **THE CONNECTING THEOREM.**  A chart stationarity datum at value ZERO and a
design stationarity datum at value ONE, on the SAME design, induce the SAME
quadratic form on every atom:

    `g_cᵀ Lambda_chart g_c = g_cᵀ Lambda_design g_c`   at every atom .

Both sides are `1` — the left by the bridge, the right by
`Gtz.quadricLaw_of_isQuadricStationaryData`.  This is what makes the chart
development an EXTENSION of `Gtz.Quantitative.CriticalQuadric` rather than a
parallel one: on the extremal locus the chart system lands inside the design
system's quadric law, and the corrections `value/(size * t_c)` and the dual
condition on `N` are what it adds off that locus.

READ IT AT ITS SIZE.  It does NOT say the two multipliers are equal.  The quadric
equations are `size` affine conditions on the `rank(rank+1)/2` entries of a
symmetric multiplier and generally underdetermine it — at the tetrahedron the
affine solution family is two-dimensional, as
`Gtz.isotropicQuadric_iff_leverage_eq_rank`'s docstring records.  Equality of the
forms on the atoms is what is true; equality of the matrices is not.

It also does NOT say the two systems have the same minimisers.  The threshold and
the law agree at `value = 0`; the MINIMISERS do not, because the congruence
`diag(sqrt t_C)` rescales non-uniformly, and
`Gtz.Reduction.CompactnessReduction`'s objective-mismatch note stands. -/
theorem quadricForm_chartQuadricMultiplier_eq_of_isQuadricStationaryData_value_one
    {designIndex : Type*} (design : WeightedDesign size rank)
    (hchart : projection = projectionOfDesign design) (hweight : weight = design.weight)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir)
    {designMultiplier : Matrix (Fin rank) (Fin rank) ℝ} {designActiveSet : Finset designIndex}
    {designActiveSubset : designIndex → Finset (Fin size)} {designActiveWeight : designIndex → ℝ}
    {designTightDir : designIndex → (Fin rank → ℝ)}
    (hdesignData : IsQuadricStationaryData design 1 designMultiplier designActiveSet
      designActiveSubset designActiveWeight designTightDir) (atomLabel : Fin size) :
    design.atom atomLabel
        ⬝ᵥ (chartQuadricMultiplier (scaledAtomRows design)
              (chartMultiplierAssembly activeSet activeWeight tightDir)
            *ᵥ design.atom atomLabel)
      = design.atom atomLabel ⬝ᵥ (designMultiplier *ᵥ design.atom atomLabel) := by
  rw [quadricLaw_of_chartQuadricMultiplier_of_value_zero design hchart hweight hdata atomLabel,
    quadricLaw_of_isQuadricStationaryData hdesignData atomLabel]

/-- The trace twin of the connecting theorem: both multipliers have trace one. -/
theorem trace_chartQuadricMultiplier_eq_of_isQuadricStationaryData_value_one
    {designIndex : Type*} (design : WeightedDesign size rank)
    (hchart : projection = projectionOfDesign design)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir)
    {designMultiplier : Matrix (Fin rank) (Fin rank) ℝ} {designActiveSet : Finset designIndex}
    {designActiveSubset : designIndex → Finset (Fin size)} {designActiveWeight : designIndex → ℝ}
    {designTightDir : designIndex → (Fin rank → ℝ)}
    (hdesignData : IsQuadricStationaryData design 1 designMultiplier designActiveSet
      designActiveSubset designActiveWeight designTightDir) :
    Matrix.trace (chartQuadricMultiplier (scaledAtomRows design)
        (chartMultiplierAssembly activeSet activeWeight tightDir))
      = Matrix.trace designMultiplier := by
  rw [trace_chartQuadricMultiplier_of_value_zero design hchart hdata,
    trace_multiplierMatrix_of_isQuadricStationaryData hdesignData]

/-- **The chart mirror of `Gtz.leverage_eq_rank_of_isotropicMultiplier`.**  If the
multiplier the chart manufactures happens to be scalar, every atom of the design
has leverage exactly `rank`.  Fed straight into
`Gtz.isotropicQuadric_iff_leverage_eq_rank`, whose hypothesis is the quadric law
the bridge supplies. -/
theorem leverage_eq_rank_of_isotropic_chartQuadricMultiplier
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hweight : weight = design.weight)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (hrankNe : rank ≠ 0)
    (hisotropic : chartQuadricMultiplier (scaledAtomRows design)
        (chartMultiplierAssembly activeSet activeWeight tightDir)
      = ((1 : ℝ) / (rank : ℝ)) • (1 : Matrix (Fin rank) (Fin rank) ℝ))
    (atomLabel : Fin size) :
    leverageOf (design.atom atomLabel) = (rank : ℝ) := by
  refine (isotropicQuadric_iff_leverage_eq_rank design one_ne_zero hrankNe).mp
    (fun atomIndex => ?_) atomLabel
  rw [← hisotropic]
  exact quadricLaw_of_chartQuadricMultiplier_of_value_zero design hchart hweight hdata atomIndex

/-- **The gap-trace law for the manufactured multiplier**: at EVERY `rank`-subset,
active or not,

    `tr(Lambda (S_C - 1)) = rank - 1` .

The subset never enters, only its cardinality — this is
`Gtz.trace_mul_gap_of_quadricLaw` applied to the two halves of the bridge.

A DISCLOSURE, not a new exclusion: the consequence "no chart-manufactured `Lambda`
annihilates the gap of a `rank`-subset when `2 <= rank`" is already unconditional
through `Gtz.not_isCriticalMultiplierAt`, which needs no stationarity data at all. -/
theorem trace_mul_gap_of_chartQuadricMultiplier
    (design : WeightedDesign size rank) (hchart : projection = projectionOfDesign design)
    (hweight : weight = design.weight)
    (hdata : IsChartStationaryData rank projection weight 0 activeSet activeSubset
      activeWeight tightDir) (chosenSubset : Finset (Fin size))
    (hcard : chosenSubset.card = rank) :
    Matrix.trace (chartQuadricMultiplier (scaledAtomRows design)
        (chartMultiplierAssembly activeSet activeWeight tightDir)
      * (subsetSum design chosenSubset - 1))
      = (rank : ℝ) - 1 :=
  trace_mul_gap_of_quadricLaw design chosenSubset hcard _
    (trace_chartQuadricMultiplier_of_value_zero design hchart hdata)
    fun atomIndex =>
      quadricLaw_of_chartQuadricMultiplier_of_value_zero design hchart hweight hdata atomIndex

/-! ## The witness — the tetrahedron at `(4,3)`, reproducing the hand computation

Four atoms of leverage three at uniform weight `1/4`.  The scaled Parseval frame
`V = Gtz.scaledAtomRows Gtz.tetraDesign` has rows `(1/2) * g_c`, and the kernel is
the single line spanned by the normalised all-ones vector, so `Z` is the `4 x 1`
column with every entry `1/2`.

Against the tetrahedron chart datum of `Gtz.Quantitative.ChartStationary`, whose
assembly is `Xi = I_4/12 + J_4/6`, the two compressions come out as

    `M = Vᵀ Xi V = I_3/12` ,   `N = Zᵀ Xi Z = 3/4` ,

because `Gᵀ G = 4 I` (Parseval at uniform weight) while `Gᵀ J G = 0` (the four
tetrahedron directions sum to zero), and because the entries of `Xi` sum to
`4 * (1/4) + 12 * (1/6) = 3`.  Rescaling by `size = 4` gives

    `Lambda = 4 * M = I_3/3` ,

and every one of those is the hand-computed reference value of the campaign brief,
on the nose. -/

/-- The tetrahedron's kernel frame: the single normalised all-ones column. -/
noncomputable def chartSplitTetraKernelFrame : Matrix (Fin 4) (Fin 1) ℝ :=
  Matrix.of fun _ _ => (2 : ℝ)⁻¹

/-- The tetrahedron's uniform weight has square root `1/2`. -/
theorem sqrt_tetraDesign_weight (atomIndex : Fin 4) :
    Real.sqrt (tetraDesign.weight atomIndex) = (2 : ℝ)⁻¹ := by
  show Real.sqrt ((1 : ℝ) / 4) = (2 : ℝ)⁻¹
  rw [show (1 : ℝ) / 4 = ((2 : ℝ)⁻¹) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The rows of the tetrahedron's range frame: the directions halved. -/
theorem scaledAtomRows_tetraDesign_apply (atomIndex : Fin 4) (coord : Fin 3) :
    scaledAtomRows tetraDesign atomIndex coord = (2 : ℝ)⁻¹ * tetraAtom atomIndex coord := by
  rw [scaledAtomRows, Matrix.of_apply, sqrt_tetraDesign_weight]
  rfl

/-- **The tetrahedron's chart is the hand value** `I - J/4`: `3/4` on the diagonal
and `-1/4` off it, matching `Gtz.chartTetraProjection`. -/
theorem projectionOfDesign_tetraDesign_eq :
    projectionOfDesign tetraDesign = chartTetraProjection := by
  ext rowIndex colIndex
  rw [projectionOfDesign_apply, sqrt_tetraDesign_weight, sqrt_tetraDesign_weight,
    chartTetraProjection, Matrix.of_apply]
  by_cases hequal : rowIndex = colIndex
  · rw [if_pos hequal, hequal]
    show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ * (tetraDesign.atom colIndex ⬝ᵥ tetraDesign.atom colIndex) = 3 / 4
    rw [show tetraDesign.atom = tetraAtom from rfl, tetraAtom_dot_self]
    norm_num
  · rw [if_neg hequal]
    show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ * (tetraDesign.atom rowIndex ⬝ᵥ tetraDesign.atom colIndex)
      = -(1 / 4)
    rw [show tetraDesign.atom = tetraAtom from rfl, tetraAtom_dot_of_ne hequal]
    norm_num

/-- The tetrahedron's weight vector, in the companion file's spelling. -/
theorem tetraDesign_weight_eq : tetraDesign.weight = chartTetraWeight := by
  funext atomIndex
  show (1 : ℝ) / 4 = (4 : ℝ)⁻¹
  norm_num

/-- **The tetrahedron carries a frame pair**, with the scaled Parseval frame on the
range and the normalised all-ones column on the kernel. -/
theorem chartSplitTetraIsChartFramePair :
    IsChartFramePair chartTetraProjection (scaledAtomRows tetraDesign)
      chartSplitTetraKernelFrame where
  rangeFrame_isIsometry := transpose_mul_scaledAtomRows tetraDesign
  rangeFrame_spansRange := by
    rw [scaledAtomRows_mul_transpose, projectionOfDesign_tetraDesign_eq]
  kernelFrame_isIsometry := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases rowIndex
    fin_cases colIndex
    norm_num [chartSplitTetraKernelFrame, Matrix.transpose_apply, Matrix.one_apply]
  kernelFrame_spansKernel := by
    ext rowIndex colIndex
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [chartSplitTetraKernelFrame, Matrix.transpose_apply, Matrix.one_apply,
        chartTetraProjection, Matrix.sub_apply, Fin.ext_iff]

/-- **THE RANGE BLOCK AT THE TETRAHEDRON**: `M = I_3/12`, the brief's hand value. -/
theorem chartSplitTetraRangeMultiplier_eq :
    chartRangeMultiplier (scaledAtomRows tetraDesign) chartTetraMultiplier
      = ((12 : ℝ))⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowCoord colCoord
  rw [chartRangeMultiplier, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, scaledAtomRows_tetraDesign_apply,
    chartTetraMultiplier, Matrix.of_apply, Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  fin_cases rowCoord <;> fin_cases colCoord <;>
    norm_num [tetraAtom, Fin.ext_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- **THE KERNEL BLOCK AT THE TETRAHEDRON**: `N = 3/4`, a scalar because the
kernel is a line — the brief's hand value. -/
theorem chartSplitTetraKernelMultiplier_eq :
    chartKernelMultiplier chartSplitTetraKernelFrame chartTetraMultiplier
      = ((3 : ℝ) / 4) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext rowIndex colIndex
  rw [chartKernelMultiplier, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, chartSplitTetraKernelFrame,
    chartTetraMultiplier, Matrix.of_apply, Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  fin_cases rowIndex
  fin_cases colIndex
  norm_num [Fin.ext_iff]

/-- **THE MANUFACTURED MULTIPLIER AT THE TETRAHEDRON**: `Lambda = 4 * M = I_3/3`,
the brief's hand value, and the isotropic point of the tetrahedron's quadric
family. -/
theorem chartSplitTetraQuadricMultiplier_eq :
    chartQuadricMultiplier (scaledAtomRows tetraDesign) chartTetraMultiplier
      = ((3 : ℝ))⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [chartQuadricMultiplier, chartSplitTetraRangeMultiplier_eq, smul_smul]
  norm_num

/-- **The bridge is inhabited, and it reproduces the hand computation.**  There is
a design whose chart carries a chart stationarity datum at value ZERO, and the
multiplier the bridge manufactures from it is exactly `I_3/3`.

So `quadricLaw_of_chartQuadricMultiplier_of_value_zero` and its companions are not
statements about an empty class, and the object they produce is the one the
campaign brief computed by hand. -/
theorem exists_isChartStationaryData_value_zero_chartQuadricMultiplier_eq :
    ∃ (design : WeightedDesign 4 3) (activeSubset : Fin 4 → Finset (Fin 4))
      (activeWeight : Fin 4 → ℝ) (tightDir : Fin 4 → (Fin 4 → ℝ)),
      IsChartStationaryData 3 (projectionOfDesign design) design.weight 0
          (Finset.univ : Finset (Fin 4)) activeSubset activeWeight tightDir
        ∧ chartQuadricMultiplier (scaledAtomRows design)
            (chartMultiplierAssembly (Finset.univ : Finset (Fin 4)) activeWeight tightDir)
          = ((3 : ℝ))⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine ⟨tetraDesign, chartTetraSubset, chartTetraMultiplierWeight, chartTetraTightDir, ?_, ?_⟩
  · rw [projectionOfDesign_tetraDesign_eq, tetraDesign_weight_eq]
    exact chartTetraProjection_isChartStationaryData
  · rw [chartTetraMultiplierAssembly_eq]
    exact chartSplitTetraQuadricMultiplier_eq

end Gtz
