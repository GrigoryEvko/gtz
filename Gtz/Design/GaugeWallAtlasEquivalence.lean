import Gtz.Design.ChartReadingLaw
import Gtz.Design.PivotArmClosure
import Gtz.Design.StallTypeSplit
import Gtz.Wave.KFourGaugeStarTransportWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The gauge wall admits only the atlas

The canonical gauge wall is the chart locus where the star `{3, 4, 5}` carries a
positive semidefinite gap of corank two.  The corank data supplies two kernel
vectors of that gap which are not collinear.

The three triangle directions `kFourDirection 0`, `1` and `2` span a plane, and
the three star directions are the coordinate axes.  Write the gap of any
selection against the star gap:

```
gap S = gap {3,4,5} + ∑_{c ∈ S ∩ {0,1,2}} kappa c • atom c
                    - ∑_{c ∈ {3,4,5} \ S} kappa c • atom c
```

A probe in the kernel of the star gap reads the first term as zero.  One more
linear condition still leaves a nonzero probe inside a two dimensional kernel.
Choose that condition to kill the triangle labels of `S`.  The reading of `gap S`
at that probe is then a sum of nonpositive terms.

**A selection that meets the triangle `{0, 1, 2}` in at most one label is never
positive definite on the gauge wall.**  For a spanning tree this says the tree
meets the star `{3, 4, 5}` exactly once, which is exactly the nine atlas cells.
The other seven spanning trees are dead, in one theorem rather than seven.

The same bound applies to a card-four stall, so the gauge wall consumes a stall
escape only at the shapes it permits.
-/

namespace Gtz

open Matrix

/-! ## A kernel probe orthogonal to one more direction -/

/-- Two non-collinear kernel vectors leave a nonzero kernel vector orthogonal to
any single reader.  This is the two dimensional kernel used one dimension at a
time, with no rank theory. -/
theorem exists_kernel_dotProduct_zero {dim : ℕ}
    (target : Matrix (Fin dim) (Fin dim) ℝ)
    (tight second reader : Fin dim → ℝ) (htightNe : tight ≠ 0)
    (htightKernel : target *ᵥ tight = 0)
    (hsecondKernel : target *ᵥ second = 0)
    (hnotCollinear : ¬ ∃ scale : ℝ, second = scale • tight) :
    ∃ probe : Fin dim → ℝ,
      probe ≠ 0 ∧ target *ᵥ probe = 0 ∧ reader ⬝ᵥ probe = 0 := by
  by_cases hread : reader ⬝ᵥ tight = 0
  · exact ⟨tight, htightNe, htightKernel, hread⟩
  refine ⟨(reader ⬝ᵥ tight) • second - (reader ⬝ᵥ second) • tight, ?_, ?_, ?_⟩
  · intro hzero
    refine hnotCollinear ⟨(reader ⬝ᵥ second) / (reader ⬝ᵥ tight), ?_⟩
    funext index
    have hpoint := congrFun (sub_eq_zero.mp hzero) index
    simp only [Pi.smul_apply, smul_eq_mul] at hpoint ⊢
    field_simp
    linarith [hpoint]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      htightKernel, hsecondKernel, smul_zero, smul_zero, sub_zero]
  · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring

/-! ## The wall reading -/

/-- A probe in the kernel of the star gap which is blind to the triangle labels
of a selection reads that selection nonpositively.

The star gap contributes zero.  Every surviving term is a star label outside the
selection, and its coefficient is negative. -/
theorem kFourGaugeWall_quadForm_nonpos (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (probe : Fin 3 → ℝ)
    (hkernel : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ probe = 0)
    (hblind : ∀ label ∈ selected ∩ ({0, 1, 2} : Finset (Fin 6)),
      kFourDirection label ⬝ᵥ probe = 0) :
    probe ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight selected
      *ᵥ probe) ≤ 0 := by
  have hnonneg : ∀ label : Fin 6,
      0 ≤ point.mass label / point.weight label
        * (kFourDirection label ⬝ᵥ probe) ^ 2 := by
    intro label
    exact mul_nonneg
      (div_nonneg (point.mass_pos label).le (point.weight_pos label).le)
      (sq_nonneg _)
  have hstar : probe ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ probe) = 0 := by
    rw [hkernel, dotProduct_zero]
  rw [dotProduct_directionChartGap_mulVec_eq] at hstar
  rw [dotProduct_directionChartGap_mulVec_eq]
  have hsplit : ∀ label : Fin 6, label ∉ ({3, 4, 5} : Finset (Fin 6)) →
      label ∈ ({0, 1, 2} : Finset (Fin 6)) := by decide
  have hrestrict : ∑ label ∈ selected,
        point.mass label / point.weight label
          * (kFourDirection label ⬝ᵥ probe) ^ 2
      = ∑ label ∈ selected ∩ ({3, 4, 5} : Finset (Fin 6)),
        point.mass label / point.weight label
          * (kFourDirection label ⬝ᵥ probe) ^ 2 := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro label hmem hnot
    have hstarNot : label ∉ ({3, 4, 5} : Finset (Fin 6)) := fun hc =>
      hnot (Finset.mem_inter.mpr ⟨hmem, hc⟩)
    rw [hblind label (Finset.mem_inter.mpr ⟨hmem, hsplit label hstarNot⟩)]
    ring
  have hbound : ∑ label ∈ selected ∩ ({3, 4, 5} : Finset (Fin 6)),
        point.mass label / point.weight label
          * (kFourDirection label ⬝ᵥ probe) ^ 2
      ≤ ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
        point.mass label / point.weight label
          * (kFourDirection label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun label _ _ => hnonneg label)
  rw [hrestrict]
  linarith

/-! ## The rank obstruction -/

/-- **THE GAUGE-WALL RANK OBSTRUCTION.**  On the canonical gauge wall a
selection which meets the triangle `{0, 1, 2}` in at most one label is never
positive definite.

The star gap is rank one there, so the positive part of any such selection has
rank at most two and cannot dominate. -/
theorem kFourGaugeWall_not_posDef_of_triangle_card_le_one
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (tight second : Fin 3 → ℝ) (htightNe : tight ≠ 0)
    (htightKernel : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ tight = 0)
    (hsecondKernel : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ second = 0)
    (hnotCollinear : ¬ ∃ scale : ℝ, second = scale • tight)
    (hcard : (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card ≤ 1) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef := by
  obtain ⟨corner, hcorner⟩ :
      ∃ corner : Fin 6,
        selected ∩ ({0, 1, 2} : Finset (Fin 6)) ⊆ {corner} := by
    rcases Finset.eq_empty_or_nonempty
      (selected ∩ ({0, 1, 2} : Finset (Fin 6))) with hempty | ⟨corner, hmem⟩
    · exact ⟨0, by rw [hempty]; exact Finset.empty_subset _⟩
    · refine ⟨corner, fun other hother => ?_⟩
      rw [Finset.mem_singleton]
      exact Finset.card_le_one.mp hcard other hother corner hmem
  obtain ⟨probe, hprobeNe, hprobeKernel, hprobeRead⟩ :=
    exists_kernel_dotProduct_zero _ tight second (kFourDirection corner)
      htightNe htightKernel hsecondKernel hnotCollinear
  have hblind : ∀ label ∈ selected ∩ ({0, 1, 2} : Finset (Fin 6)),
      kFourDirection label ⬝ᵥ probe = 0 := by
    intro label hlabel
    rw [Finset.mem_singleton.mp (hcorner hlabel)]
    exact hprobeRead
  intro hposDef
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial] at hpos
  have hnonpos :=
    kFourGaugeWall_quadForm_nonpos point selected probe hprobeKernel hblind
  linarith

/-- The contrapositive: a positive definite selection on the gauge wall carries
at least two triangle labels. -/
theorem kFourGaugeWall_two_le_triangle_card_of_posDef
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (tight second : Fin 3 → ℝ) (htightNe : tight ≠ 0)
    (htightKernel : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ tight = 0)
    (hsecondKernel : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) *ᵥ second = 0)
    (hnotCollinear : ¬ ∃ scale : ℝ, second = scale • tight)
    (hposDef : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    2 ≤ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card := by
  by_contra hlt
  push Not at hlt
  exact kFourGaugeWall_not_posDef_of_triangle_card_le_one point selected tight
    second htightNe htightKernel hsecondKernel hnotCollinear
    (Nat.lt_succ_iff.mp hlt) hposDef

/-- The same bound, read straight off the packaged corank-two wall data. -/
theorem kFourGaugeWall_two_le_triangle_card_of_corank
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcorank : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)))
    (hposDef : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    2 ≤ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card := by
  obtain ⟨tight, second, _pointer, htightNe, _hpointerOut, htightKernel,
    _hswap, _hsecondNe, hsecondKernel, _hperp, hnotCollinear⟩ := hcorank
  exact kFourGaugeWall_two_le_triangle_card_of_posDef point selected tight second
    htightNe htightKernel hsecondKernel hnotCollinear hposDef

/-! ## The atlas -/

/-- The nine atlas cells of the gauge wall: two triangle labels and one star
label.  These are exactly the spanning trees meeting `{3, 4, 5}` once. -/
def kFourGaugeAtlasList : List (Finset (Fin 6)) :=
  [{0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 2, 5},
   {1, 2, 3}, {1, 2, 4}, {1, 2, 5}]

/-- Every atlas cell is a spanning tree. -/
theorem kFourGaugeAtlasList_subset_treeList :
    ∀ cell ∈ kFourGaugeAtlasList, cell ∈ kFourSpanningTreeList := by decide

/-- A spanning tree with two triangle labels is an atlas cell. -/
theorem kFourTree_mem_gaugeAtlasList_of_triangle_card (tree : Finset (Fin 6))
    (htree : tree ∈ kFourSpanningTreeList)
    (hcard : 2 ≤ (tree ∩ ({0, 1, 2} : Finset (Fin 6))).card) :
    tree ∈ kFourGaugeAtlasList := by
  revert htree hcard
  revert tree
  decide

/-- **THE ATLAS EQUIVALENCE.**  On the canonical gauge wall a positive definite
spanning tree is one of the nine atlas cells.  The remaining seven spanning
trees are dead there, and no case tree over the wall coordinates is used. -/
theorem kFourGaugeWall_posDef_tree_mem_atlas (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) (htree : tree ∈ kFourSpanningTreeList)
    (hcorank : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)))
    (hposDef : (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef) :
    tree ∈ kFourGaugeAtlasList :=
  kFourTree_mem_gaugeAtlasList_of_triangle_card tree htree
    (kFourGaugeWall_two_le_triangle_card_of_corank point tree hcorank hposDef)

/-- The seven spanning trees outside the atlas are never positive definite on
the canonical gauge wall. -/
theorem kFourGaugeWall_not_posDef_of_notMem_atlas
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (htree : tree ∈ kFourSpanningTreeList)
    (hnotMem : tree ∉ kFourGaugeAtlasList)
    (hcorank : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6))) :
    ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef :=
  fun hposDef =>
    hnotMem (kFourGaugeWall_posDef_tree_mem_atlas point tree htree hcorank hposDef)

/-! ## The gauge wall consumes a shaped stall escape -/

/-- Card-four stall escape, restricted to the shapes the gauge wall permits: at
least two of the four labels are triangle labels.  Three of the fifteen
card-four selections are removed outright, namely those containing the whole
star `{3, 4, 5}`. -/
def KFourShapedCardFourStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (selected : Finset (Fin 6)),
    selected.card = 4 →
    2 ≤ (selected ∩ ({0, 1, 2} : Finset (Fin 6))).card →
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef →
    (∀ label ∈ selected, 1 ≤ chartLadderPivot kFourDirection point.mass
      point.weight selected label) →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- **THE GAUGE-WALL REDUCTION.**  The canonical gauge wall needs no atlas
covering argument and no wall-coordinate case tree.  A stall escape at the
shapes the wall permits closes it, through the landed descent dichotomy. -/
theorem kFourGaugeStarCorankWallClosure_of_shapedStallClosure
    (hclose : KFourShapedCardFourStallClosure) :
    KFourGaugeStarCorankWallClosure := by
  intro point _hpsd hcorank
  rcases kFour_strictTree_or_cardFour_stall point with
    hstrict | ⟨selected, hcard, hposDef, hstall⟩
  · exact hstrict
  · exact hclose point selected hcard
      (kFourGaugeWall_two_le_triangle_card_of_corank point selected hcorank
        hposDef) hposDef hstall

/-- The unrestricted stall escape closes the gauge wall a fortiori. -/
theorem kFourGaugeStarCorankWallClosure_of_cardFourStallClosure
    (hclose : ∀ (point : DirectionChartPoint 6) (selected : Finset (Fin 6)),
      selected.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef →
      (∀ label ∈ selected, 1 ≤ chartLadderPivot kFourDirection point.mass
        point.weight selected label) →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef) :
    KFourGaugeStarCorankWallClosure :=
  kFourGaugeStarCorankWallClosure_of_shapedStallClosure
    (fun point selected hcard _hshape => hclose point selected hcard)

end Gtz
