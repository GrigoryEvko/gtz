/-
# The null frame of the diamond and of the split diamond, exactly

The corank-one arm needs its boundary fixtures with their null data IN KERNEL:
the `(5,3)` diamond primitive and the `(6,3)` split diamond are the inhabited
boundary that every closing law of the arm must respect, and until now their
gap corank, null direction and reading profile were only measured.  This
module lands them exactly, together with the graphic-frame transport that
makes any graphic fixture's null data computable.

## The transport

A graphic design's gap is the whitened Laplacian gap, so its quadratic form at
a probe IS the potential form at the whitened image
(`Gtz.graphicDesign_gap_form`).  Three consequences, all at any graph:

* a potential null LINE transports to a design `Gtz.GapNullLine` along the
  inverse whitener (`Gtz.gapNullLine_graphicDesign_of_potential`);
* readings against the transported vector are conductance-scaled potential
  drops, whitener-free (`Gtz.graphicAtom_dotProduct_whitenerInv`):
  `g_e ⬝ᵥ (W⁻¹ y) = √(c_e/t_e) · (b_e ⬝ᵥ y)`;
* pairings of transported vectors are Laplacian pairings
  (`Gtz.whitenerInv_pairing`), so norms are Dirichlet energies.

The whitener is a `Classical.choose`; every statement below is nonetheless
EXACT because the three transports eliminate it.

## The diamond's null frame

At the spine dominator `{0,1,2}` the potential gap form is the closed
polynomial `8(y₀−y₁)² + 12(y₀−y₂)² + 12y₀² − 3(y₁−y₂)² − 3y₁²`, whose double
is the exact sum of squares `(−8y₀+2y₁+3y₂)² + 9y₂²`.  The null line is the
potential `(1,4,0)`, transported to `Gtz.diamondNullVector`:

* `Gtz.gapNullLine_diamondDesign_spine` — the spine gap has corank exactly one;
* squared readings `(90, 15, 15, 240, 240)` against norm `120`
  (`Gtz.diamondNull_reading_sq_values`, `Gtz.diamondNullVector_normSq`) — the
  unit-normalized profile is `β² = (3/4, 1/8, 1/8)` inside and `(2, 2)`
  outside, the exact table of `scratchpad/corank1/fix.jl`;
* all three inside readings nonzero
  (`Gtz.diamondNull_spine_readings_ne_zero`) — the diamond sits in the
  ALL-NONZERO stratum, so the two-zero budget
  (`Gtz.isTie_iff_avoidingRefusals_of_twoZeroReadings`) is diamond-safe.

## The split diamond inherits the frame verbatim

The split copies the spine atom, so the spine dominator's subset sum is THE
SAME MATRIX upstairs (`Gtz.subsetSum_sixSplit_spine`), the null line
transports unchanged (`Gtz.gapNullLine_sixSplitDiamondDesign_spine`), and the
parallel pair reads the null direction identically
(`Gtz.sixSplit_atom_copy`).  The `(6,3)` fixture therefore carries, in kernel:
a tie (`Gtz.sixSplitDiamondDesign_isTie`, landed), a parallel pair (landed), a
corank-one weak dominator with explicit null data (here), and an all-nonzero
reading profile (here).  Its copy-for-spine exchange is `w`-flat
(`Gtz.sixSplit_copySwap_wform_zero`): the census sees the parallel pair as a
ZERO of the swap `w`-form, the degeneration signature the arm's closing laws
must reproduce.
-/
import Gtz.Wave.CorankOneGramMirror
import Gtz.Quantitative.ExtremalBasisActivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! ## 1. The graphic transport -/

/-- **The gap form of a graphic design is the potential form at the whitened
image.**  The whitener never appears on the right through its own entries —
only through the image vector. -/
theorem graphicDesign_gap_form {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (edgeSet : Finset (Fin edgeCount))
    (probe : Fin vertexRank → ℝ) :
    probe ⬝ᵥ ((subsetSum (graphicDesign data) edgeSet - 1) *ᵥ probe)
      = (data.whitener *ᵥ probe) ⬝ᵥ
          ((data.selectedLaplacian edgeSet - data.fullLaplacian)
            *ᵥ (data.whitener *ᵥ probe)) := by
  have hgap : subsetSum (graphicDesign data) edgeSet - 1
      = (data.whitener)ᵀ * (data.selectedLaplacian edgeSet - data.fullLaplacian)
          * data.whitener := by
    rw [graphicDesign_subsetSum, Matrix.mul_sub, Matrix.sub_mul, data.whitener_spec]
  rw [hgap, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec probe ((data.whitener)ᵀ)
      ((data.selectedLaplacian edgeSet - data.fullLaplacian)
        *ᵥ (data.whitener *ᵥ probe)),
    Matrix.vecMul_transpose]

/-- **A potential null line transports to a design null line.**  The inverse
whitener carries the potential kernel of the Laplacian gap to the
`Gtz.GapNullLine` of the graphic design. -/
theorem gapNullLine_graphicDesign_of_potential {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (edgeSet : Finset (Fin edgeCount))
    {nullPotential : Fin vertexRank → ℝ} (hne : nullPotential ≠ 0)
    (hnull : nullPotential ⬝ᵥ ((data.selectedLaplacian edgeSet - data.fullLaplacian)
        *ᵥ nullPotential) = 0)
    (hline : ∀ y : Fin vertexRank → ℝ,
        y ⬝ᵥ ((data.selectedLaplacian edgeSet - data.fullLaplacian) *ᵥ y) = 0 →
        ∃ s : ℝ, y = s • nullPotential) :
    GapNullLine (graphicDesign data) edgeSet ((data.whitener)⁻¹ *ᵥ nullPotential) := by
  have hback : data.whitener *ᵥ ((data.whitener)⁻¹ *ᵥ nullPotential) = nullPotential := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ data.whitener_isUnit,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    rw [hzero, Matrix.mulVec_zero] at hback
    exact hne hback.symm
  · rw [graphicDesign_gap_form, hback]
    exact hnull
  · intro probe hprobe
    rw [graphicDesign_gap_form] at hprobe
    obtain ⟨s, hs⟩ := hline (data.whitener *ᵥ probe) hprobe
    refine ⟨s, ?_⟩
    have hinv : (data.whitener)⁻¹ *ᵥ (data.whitener *ᵥ probe) = probe := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ data.whitener_isUnit,
        Matrix.one_mulVec]
    rw [← hinv, hs, Matrix.mulVec_smul]

/-- **The reading transport.**  Against an inverse-whitened vector, a graphic
atom reads the conductance-scaled potential drop — the whitener cancels. -/
theorem graphicAtom_dotProduct_whitenerInv {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (edge : Fin edgeCount)
    (y : Fin vertexRank → ℝ) :
    (graphicDesign data).atom edge ⬝ᵥ ((data.whitener)⁻¹ *ᵥ y)
      = Real.sqrt (data.conductance edge / data.weight edge)
        * (data.graph.edgeVector edge ⬝ᵥ y) := by
  show data.graphicAtom edge ⬝ᵥ _ = _
  rw [GraphDesignData.graphicAtom, smul_dotProduct, smul_eq_mul]
  congr 1
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ data.whitener_isUnit, Matrix.one_mulVec]

/-- **The pairing transport.**  Inverse-whitened vectors pair through the full
Laplacian: norms of transported null vectors are Dirichlet energies. -/
theorem whitenerInv_pairing {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (a b : Fin vertexRank → ℝ) :
    ((data.whitener)⁻¹ *ᵥ a) ⬝ᵥ ((data.whitener)⁻¹ *ᵥ b)
      = a ⬝ᵥ (data.fullLaplacian *ᵥ b) := by
  have hWTdet : IsUnit ((data.whitener)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact data.whitener_isUnit
  have hL : data.fullLaplacian = ((data.whitener)⁻¹)ᵀ * (data.whitener)⁻¹ := by
    calc data.fullLaplacian
        = ((data.whitener)ᵀ)⁻¹
            * ((data.whitener)ᵀ * data.fullLaplacian * data.whitener)
            * (data.whitener)⁻¹ := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
            Matrix.nonsing_inv_mul _ hWTdet, Matrix.one_mul, Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ data.whitener_isUnit, Matrix.mul_one]
      _ = ((data.whitener)ᵀ)⁻¹ * 1 * (data.whitener)⁻¹ := by
          rw [data.whitener_spec]
      _ = ((data.whitener)⁻¹)ᵀ * (data.whitener)⁻¹ := by
          rw [Matrix.mul_one, Matrix.transpose_nonsing_inv]
  rw [hL, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec a (((data.whitener)⁻¹)ᵀ) ((data.whitener)⁻¹ *ᵥ b),
    Matrix.vecMul_transpose]

/-! ## 2. The diamond's null frame -/

/-- The spine gap of the diamond, as one closed polynomial in the reduced
potentials. -/
theorem diamondSpineGap_potentialForm (y : Fin 3 → ℝ) :
    y ⬝ᵥ ((diamondData.selectedLaplacian ({0, 1, 2} : Finset (Fin 5))
        - diamondData.fullLaplacian) *ᵥ y)
      = 8 * (y 0 - y 1) ^ 2 + 12 * (y 0 - y 2) ^ 2 + 12 * (y 0) ^ 2
        - 3 * (y 1 - y 2) ^ 2 - 3 * (y 1) ^ 2 := by
  rw [diamondGap_form_indicator]
  norm_num +decide [diamondData, diamondDrop, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Matrix.cons_val, Finset.mem_insert, Finset.mem_singleton]
  ring

/-- **The spine's potential null line.**  The gap form vanishes exactly on the
potential line through `(1, 4, 0)`: twice the form is the sum of squares
`(−8y₀ + 2y₁ + 3y₂)² + 9y₂²`. -/
theorem diamondSpine_potential_line {y : Fin 3 → ℝ}
    (hzero : y ⬝ᵥ ((diamondData.selectedLaplacian ({0, 1, 2} : Finset (Fin 5))
        - diamondData.fullLaplacian) *ᵥ y) = 0) :
    ∃ s : ℝ, y = s • ![1, 4, 0] := by
  rw [diamondSpineGap_potentialForm] at hzero
  have hsos : (-8 * y 0 + 2 * y 1 + 3 * y 2) ^ 2 + 9 * (y 2) ^ 2 = 0 := by
    linear_combination 2 * hzero
  have hy2sq : (y 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (-8 * y 0 + 2 * y 1 + 3 * y 2), sq_nonneg (y 2)]
  have hy2 : y 2 = 0 := by
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hy2sq
  have hlead : (-8 * y 0 + 2 * y 1 + 3 * y 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (-8 * y 0 + 2 * y 1 + 3 * y 2)]
  have hy1 : y 1 = 4 * y 0 := by
    have h0 : -8 * y 0 + 2 * y 1 + 3 * y 2 = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.mp hlead
    rw [hy2] at h0
    linarith
  refine ⟨y 0, ?_⟩
  funext i
  fin_cases i <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hy1, hy2] <;>
    ring

/-- The potential `(1, 4, 0)` really is null for the spine gap. -/
theorem diamondSpine_potential_null :
    (![1, 4, 0] : Fin 3 → ℝ) ⬝ᵥ
      ((diamondData.selectedLaplacian ({0, 1, 2} : Finset (Fin 5))
        - diamondData.fullLaplacian) *ᵥ ![1, 4, 0]) = 0 := by
  rw [diamondSpineGap_potentialForm]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **The diamond's null vector**, the inverse-whitened image of the potential
`(1, 4, 0)`.  Squared norm `120`; squared readings `(90, 15, 15, 240, 240)`. -/
noncomputable def diamondNullVector : Fin 3 → ℝ :=
  (diamondData.whitener)⁻¹ *ᵥ ![1, 4, 0]

/-- **The diamond's spine gap has corank exactly one**, with the explicit null
vector `Gtz.diamondNullVector`.  The `(5,3)` primitive inhabits the corank-one
arm in kernel. -/
theorem gapNullLine_diamondDesign_spine :
    GapNullLine diamondDesign ({0, 1, 2} : Finset (Fin 5)) diamondNullVector := by
  refine gapNullLine_graphicDesign_of_potential diamondData ({0, 1, 2} : Finset (Fin 5))
    ?_ diamondSpine_potential_null (fun y hy => diamondSpine_potential_line hy)
  intro hzero
  have h0 := congrFun hzero 0
  norm_num at h0

/-- The squared reading of every diamond atom against the null vector, as the
conductance-scaled squared drop. -/
theorem diamondNull_reading_sq (edge : Fin 5) :
    (diamondDesign.atom edge ⬝ᵥ diamondNullVector) ^ 2
      = (diamondData.conductance edge / diamondData.weight edge)
        * (diamondData.graph.edgeVector edge ⬝ᵥ ![1, 4, 0]) ^ 2 := by
  rw [show diamondDesign = graphicDesign diamondData from rfl, diamondNullVector,
    graphicAtom_dotProduct_whitenerInv, mul_pow,
    Real.sq_sqrt (div_nonneg (diamondData.conductance_pos edge).le
      (diamondData.weight_pos edge).le)]

/-- The five drops of the null potential `(1, 4, 0)`: `(−3, 1, 1, 4, 4)`. -/
theorem diamondNull_drops :
    diamondData.graph.edgeVector 0 ⬝ᵥ ![1, 4, 0] = -3
    ∧ diamondData.graph.edgeVector 1 ⬝ᵥ ![1, 4, 0] = 1
    ∧ diamondData.graph.edgeVector 2 ⬝ᵥ ![1, 4, 0] = 1
    ∧ diamondData.graph.edgeVector 3 ⬝ᵥ ![1, 4, 0] = 4
    ∧ diamondData.graph.edgeVector 4 ⬝ᵥ ![1, 4, 0] = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num +decide [MultigraphOnGround.edgeVector, dotProduct, Fin.sum_univ_three,
      diamondData, diamondGraph, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val]

/-- **The exact squared reading profile** `(90, 15, 15, 240, 240)` of the
diamond against its spine null vector.  Against the norm `120` this is
`β² = (3/4, 1/8, 1/8)` inside and `(2, 2)` outside — the measured table,
now kernel. -/
theorem diamondNull_reading_sq_values :
    (diamondDesign.atom 0 ⬝ᵥ diamondNullVector) ^ 2 = 90
    ∧ (diamondDesign.atom 1 ⬝ᵥ diamondNullVector) ^ 2 = 15
    ∧ (diamondDesign.atom 2 ⬝ᵥ diamondNullVector) ^ 2 = 15
    ∧ (diamondDesign.atom 3 ⬝ᵥ diamondNullVector) ^ 2 = 240
    ∧ (diamondDesign.atom 4 ⬝ᵥ diamondNullVector) ^ 2 = 240 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := diamondNull_drops
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [diamondNull_reading_sq] <;>
    first
      | (rw [h0]; norm_num [diamondData, Matrix.cons_val_zero])
      | (rw [h1]; norm_num [diamondData, Matrix.cons_val_one, Matrix.head_cons])
      | (rw [h2]; norm_num [diamondData, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons])
      | (rw [h3]; norm_num [diamondData, Matrix.cons_val_three, Matrix.tail_cons,
          Matrix.head_cons])
      | (rw [h4]; norm_num [diamondData, Matrix.cons_val_four, Matrix.tail_cons,
          Matrix.head_cons])

/-- The null vector's squared norm is the Dirichlet energy `120` of the null
potential. -/
theorem diamondNullVector_normSq :
    diamondNullVector ⬝ᵥ diamondNullVector = 120 := by
  rw [diamondNullVector, whitenerInv_pairing]
  rw [show diamondData.fullLaplacian
      = laplacianOn diamondData.graph diamondData.conductance Finset.univ from rfl,
    laplacianOn_form]
  have hdrop : ∀ edge : Fin 5,
      groundedPotential (![1, 4, 0] : Fin 3 → ℝ) (diamondData.graph.edgeTail edge)
        - groundedPotential (![1, 4, 0] : Fin 3 → ℝ) (diamondData.graph.edgeHead edge)
      = diamondData.graph.edgeVector edge ⬝ᵥ ![1, 4, 0] := by
    intro edge
    rw [edgeVector_dotProduct]
  simp only [hdrop]
  obtain ⟨h0, h1, h2, h3, h4⟩ := diamondNull_drops
  rw [Fin.sum_univ_five, h0, h1, h2, h3, h4]
  norm_num [diamondData, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]

/-- **The diamond sits in the all-nonzero stratum**: no inside reading of the
spine dominator vanishes.  Every kill of the two-zero (or one-zero) stratum is
therefore diamond-safe, in kernel and not only by measurement. -/
theorem diamondNull_spine_readings_ne_zero :
    diamondDesign.atom 0 ⬝ᵥ diamondNullVector ≠ 0
    ∧ diamondDesign.atom 1 ⬝ᵥ diamondNullVector ≠ 0
    ∧ diamondDesign.atom 2 ⬝ᵥ diamondNullVector ≠ 0 := by
  obtain ⟨h0, h1, h2, _, _⟩ := diamondNull_reading_sq_values
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at h0; norm_num at h0
  · rw [h] at h1; norm_num at h1
  · rw [h] at h2; norm_num at h2

/-! ## 3. The split diamond inherits the frame -/

/-- The split diamond's spine subset sum IS the diamond's spine subset sum: the
class map is injective on `{0,1,2}` with image `{0,1,2}`. -/
theorem subsetSum_sixSplit_spine :
    subsetSum sixSplitDiamondDesign ({0, 1, 2} : Finset (Fin 6))
      = subsetSum diamondDesign ({0, 1, 2} : Finset (Fin 5)) := by
  rw [sixSplitDiamondDesign, subsetSum_parallelSplitDesign_of_injOn diamondDesign
    sixIntoFiveDiamond sixSplitDiamondWeight sixSplitDiamond_isParallelSplitting
    (by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | rfl
          | (exact absurd hab (by decide)))]
  congr 1 <;> decide

/-- **The split diamond's spine dominator has the SAME corank-one null line.**
The `(6,3)` fixture now carries in kernel: a tie, a parallel pair, and a
corank-one weak dominator with explicit null data. -/
theorem gapNullLine_sixSplitDiamondDesign_spine :
    GapNullLine sixSplitDiamondDesign ({0, 1, 2} : Finset (Fin 6)) diamondNullVector := by
  obtain ⟨hne, hform, hline⟩ := gapNullLine_diamondDesign_spine
  exact ⟨hne, by rw [subsetSum_sixSplit_spine]; exact hform,
    fun probe hp => hline probe (by rw [← subsetSum_sixSplit_spine]; exact hp)⟩

/-- The split copy IS the spine atom: the parallel pair of the fixture is a
pair of equal vectors. -/
theorem sixSplit_atom_copy :
    sixSplitDiamondDesign.atom 5 = sixSplitDiamondDesign.atom 0 := rfl

/-- The three inside atoms of the split diamond's spine dominator are the
diamond's, on the nose. -/
theorem sixSplit_spine_atoms :
    sixSplitDiamondDesign.atom 0 = diamondDesign.atom 0
    ∧ sixSplitDiamondDesign.atom 1 = diamondDesign.atom 1
    ∧ sixSplitDiamondDesign.atom 2 = diamondDesign.atom 2 := ⟨rfl, rfl, rfl⟩

/-- **The split diamond sits in the all-nonzero stratum too**: same readings,
same verdict. -/
theorem sixSplit_spine_readings_ne_zero :
    sixSplitDiamondDesign.atom 0 ⬝ᵥ diamondNullVector ≠ 0
    ∧ sixSplitDiamondDesign.atom 1 ⬝ᵥ diamondNullVector ≠ 0
    ∧ sixSplitDiamondDesign.atom 2 ⬝ᵥ diamondNullVector ≠ 0 := by
  obtain ⟨h0, h1, h2⟩ := diamondNull_spine_readings_ne_zero
  exact ⟨h0, h1, h2⟩

/-- **The census sees the parallel pair as a `w`-flat swap.**  Exchanging the
spine atom for its copy leaves the null form at zero exactly — the degeneration
signature of the doubled family inside the null census. -/
theorem sixSplit_copySwap_wform_zero :
    diamondNullVector ⬝ᵥ
      ((subsetSum sixSplitDiamondDesign
          (insert 5 (({0, 1, 2} : Finset (Fin 6)).erase 0)) - 1) *ᵥ diamondNullVector)
      = 0 := by
  have hform := gapNullLine_sixSplitDiamondDesign_spine.2.1
  rw [swapGapForm_at_nullDir sixSplitDiamondDesign ({0, 1, 2} : Finset (Fin 6)) hform
    (by decide) (by decide), sixSplit_atom_copy]
  ring

end Gtz
