/-
# The disjoint two-block branch, killed on the CHART side

`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily`: the argmax family of a `(6,3)`
crux has at least THREE distinct triples.  Together with
`Gtz.SevenThreeCrux.three_le_card_chartArgmaxFamily`, already shipped and free
because three does not divide seven, both crux cells now carry the same floor.

## THIS SUPERSEDES A STANDING OPENNESS CLAIM, and the claim was stale, not wrong

`Gtz.Quantitative.SixThreeCrux`'s header says, under "NOT PROVED here, and named",
that **the disjoint two-block branch is open on the chart side**, that the third
step is shipped only on the quadric side
(`Gtz.three_le_card_activeSubsetImage_sixThree`, from
`Gtz.IsQuadricStationaryData`, a datum no crux carries), and that closing the gap
needs "either a chart-side isolated-block theorem (the repository has none -- no
chart file mentions isolation or disjointness) or a bridge valid off the extremal
locus".  The same claim is repeated in the root module's `SixThreeCrux` cluster.

Both readings are correct about ISOLATION and both miss the actual route.  The
branch was already closed, by
`Gtz.not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue`
(`Gtz.Quantitative.TwoBlockEliminationCertificate`), which is phrased in terms of
TWO COMPLEMENTARY BLOCKS and never mentions disjointness or isolation -- so a
grep for either word misses it.  Its route is a trace argument on the range
projection of the assembled multiplier, with no localisation anywhere.  Nothing
below is a port of the quadric chain; every file cited here was already in the
tree.  What was missing was the WELD: the observation that at `size = 2 * rank` a
two-member argmax family IS a pair of complementary blocks, so the shipped
theorem applies verbatim.

## What is proved

* `not_isChartTwoBlockFamily_chartArgmaxFamily_of_isMin` -- at general
  `(size, rank)`: the argmax family of a strictly interior global minimiser of the
  chart objective whose chart is a DESIGN's, at a NEGATIVE value, is never
  contained in `{C, Cᶜ}` for any `C`.  This is the general statement; everything
  else is arithmetic on top of it.
* `three_le_card_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank` -- when
  `size = 2 * rank`, coverage gives two blocks and the theorem above kills them, so
  the family has at least three members.  `(6,3)` is the instance the campaign
  needs; `(4,2)`, `(8,4)` and `(10,5)` come free.
* `SixThreeCrux.three_le_card_chartArgmaxFamily` -- the crux reading, which
  collapses the shipped disjunction
  `Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily_or_disjoint_partition` onto its
  left branch.
* `not_isIsolatedActiveBlock_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank`
  -- the chart-side reading of `Gtz.IsIsolatedActiveBlock`, the predicate the
  quadric chain is built on.  At `size = 2 * rank` a block of `rank` atoms that is
  disjoint from every other member forces every other member to BE its complement,
  which is the two-block hypothesis again.  So the argmax family of a crux has no
  isolated block, and `SixThreeCrux.exists_notDisjoint_mem_chartArgmaxFamily` reads
  that as: every triple of `rank` atoms is MET by some argmax triple other than
  itself.
* The SATURATED-ATOM law, and it is an EQUATION, not a bound.  If an atom lies in
  every active subset then the corresponding row of the assembled multiplier is an
  eigenvector of the chart with eigenvalue `value + t_c`
  (`projection_mulVec_multiplierRow_of_saturatedAtom`); the chart is idempotent and
  that row is nonzero because its own diagonal entry is `1/size`, so the eigenvalue
  is `0` or `1` (`sq_value_add_weight_of_saturatedAtom`), and a negative value
  excludes `1`.  Hence `weight_eq_neg_value_of_saturatedAtom_of_negativeValue`:
  **a saturated atom's weight is exactly `-value`**, so by the shipped floor
  `Gtz.weight_ge_neg_value_of_isChartStationaryData` it sits at the MINIMUM weight
  (`weight_le_weight_of_saturatedAtom_of_negativeValue`).
* `four_le_card_chartArgmaxFamily_of_saturatedPair_sixThree` -- saturation is
  expensive in blocks.  The double count of `Gtz.Quantitative.ClassRouteCost` has
  only `rank * |family| - size` to spend above the coverage floor, so at `(6,3)`
  two saturated atoms force a FOURTH argmax triple; contrapositively a three-member
  argmax family carries at most one saturated atom.

## THE SATURATION LAW IS NOT AN EXCLUSION, and must not be cited as one

`Gtz.Quantitative.ClassRouteCost` records that no chart-side analogue of the
quadric `Gtz.one_le_value_of_saturatedAtom` is shipped.  The law above is the
analogue, and it is genuinely chart-side -- but it EXCLUDES NOTHING on its own.
`-value <= t_c` holds at every atom already, so pinning the saturated atom to the
floor is consistent with the six weights summing to one for every value in the
window.  What it buys is rigidity: a saturated atom fixes the value, so two
saturated atoms have equal weight, and any independent lower bound on a saturated
atom's weight becomes an upper bound on `-value`.  Whether saturation is
excludable at `(6,3)` is open here.

The dichotomy's OTHER root is attained, so the negativity hypothesis is not
decoration: `exists_isChartStationaryData_saturatedAtom_value_add_weight_eq_one`
is a genuine stationarity datum with a saturated atom at `value + t_c = 1`, where
the law's conclusion is false.

## ADMISSIBILITY IS LOAD-BEARING, and the witness is already mechanized

Every theorem below routes through `Gtz.IsChartArgmaxValue`.  It cannot be
dropped: `Gtz.chartTwoBlockUniformProjection_isChartStationaryData` is a `(4,2)`
chart stationarity datum with UNIFORM weights, a genuine two-block family, and
`value = -1/4 = -1/size`, which is NEGATIVE.  It is INADMISSIBLE, and that is the
only reason it does not refute the statements below.  A first-order bundle alone
does not close this branch at any size.

Independent confirmation of the same shape: expanding the constant diagonal at a
two-member family forces both multipliers to `1/2` and both tight directions to be
FLAT on their blocks; the commutation then makes their span chart-invariant, the
two-by-two compression of an idempotent is idempotent, and a negative value leaves
only the zero compression -- giving uniform weights `1/size` and `value = -1/size`.
That derivation was carried out independently of the shipped proof and predicts the
`(4,2)` witness exactly.  It is not reproved here: the shipped
`Gtz.value_eq_neg_inv_size_of_isChartTwoBlockFamily_of_negativeValue` reaches the
same conclusion by a shorter route.

## Inherited honesty

`Gtz.IsChartStationaryData` is a HYPOTHESIS everywhere in the chart development,
but not here: at a strictly interior global minimiser it is DERIVED, by
`Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin`, and a crux
carries global minimality as a field.  So every crux statement below is free of
open hypotheses.  What none of them touch is the target: three argmax triples on
six atoms is a floor, not a contradiction, and the covering census at `(6,3)` has
2069 classes with two or more members.
-/
import Mathlib
import Gtz.Quantitative.ClassRouteCost
import Gtz.Quantitative.IsolatedBlockExclusion
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.TwoBlockEliminationCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The general kill

The argmax family of an admissible design-carried minimiser at a negative value is
never a two-block family.  Everything else in this file is arithmetic on top of
this one theorem plus counting. -/

/-- **THE ARGMAX FAMILY IS NEVER TWO COMPLEMENTARY BLOCKS.**  At a strictly
interior global minimiser of the chart objective whose chart is a design's, at a
strictly negative value, no subset `chosenSubset` has every argmax block equal to
`chosenSubset` or to its complement.

Both hypotheses of the shipped exclusion are supplied by the minimiser: the
stationarity datum and the argmax field come together out of
`Gtz.exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin`, and strict
interiority is `WeightedDesign.weight_pos`, free from the carrier. -/
theorem not_isChartTwoBlockFamily_chartArgmaxFamily_of_isMin [Nonempty (Fin rank)]
    (design : WeightedDesign size rank)
    (hmin : ∀ point : ChartPoint size rank,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point)
    (hnegative : chartObjective (chartPointOfDesign design) < 0)
    (chosenSubset : Finset (Fin size)) :
    ¬ IsChartTwoBlockFamily (chartArgmaxFamily (chartPointOfDesign design))
        (id : Finset (Fin size) → Finset (Fin size)) chosenSubset := by
  intro hfamily
  have hweightPos : ∀ atomIndex : Fin size, 0 < (chartPointOfDesign design).weight atomIndex :=
    fun atomIndex => design.weight_pos atomIndex
  obtain ⟨multiplier, selection, hdata⟩ :=
    (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ hweightPos hmin).1
  have hargmax := (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin
    (chartPointOfDesign design) hweightPos hmin).2
  exact absurd hdata
    (not_isChartStationaryData_of_isChartTwoBlockFamily_of_design_of_negativeValue
      design rfl hargmax hfamily hnegative)

/-! ## Two blocks that cover are complementary

The counting that turns "the family has two members" into the shipped hypothesis.
Nothing here is about charts: it is inclusion-exclusion at `size = 2 * rank`. -/

/-- Two disjoint subsets whose cardinalities exhaust the index type are
complementary. -/
theorem eq_compl_of_disjoint_of_card_add_card_eq_size {firstBlock secondBlock : Finset (Fin size)}
    (hdisjoint : Disjoint firstBlock secondBlock)
    (hcard : firstBlock.card + secondBlock.card = size) :
    secondBlock = firstBlockᶜ := by
  refine Finset.eq_of_subset_of_card_le (fun atomIndex hmem => ?_) ?_
  · exact Finset.mem_compl.mpr fun hfirst => (Finset.disjoint_left.mp hdisjoint hfirst) hmem
  · rw [Finset.card_compl, Fintype.card_fin]
    omega

/-- **A TWO-MEMBER ARGMAX FAMILY AT `size = 2 * rank` IS A COMPLEMENTARY PAIR.**
Coverage forces the two blocks to exhaust the atoms, `rank + rank = size` forces
them disjoint, and disjoint blocks that exhaust are complements.  This is the
general-size form of the shipped `(6,3)` classification
`Gtz.disjoint_partition_of_card_chartArgmaxFamily_eq_two_sixThree`, restated as the
hypothesis the elimination certificate consumes. -/
theorem exists_isChartTwoBlockFamily_of_card_chartArgmaxFamily_eq_two [Nonempty (Fin rank)]
    (minimiser : ChartPoint size rank) (hsize : size = 2 * rank)
    (hweightPos : ∀ atomIndex : Fin size, 0 < minimiser.weight atomIndex)
    (hmin : ∀ point : ChartPoint size rank, chartObjective minimiser ≤ chartObjective point)
    (hcard : (chartArgmaxFamily minimiser).card = 2) :
    ∃ chosenSubset : Finset (Fin size),
      IsChartTwoBlockFamily (chartArgmaxFamily minimiser)
        (id : Finset (Fin size) → Finset (Fin size)) chosenSubset := by
  classical
  obtain ⟨firstBlock, secondBlock, -, hpair⟩ := Finset.card_eq_two.mp hcard
  have hfirstMem : firstBlock ∈ chartArgmaxFamily minimiser := by
    rw [hpair]; exact Finset.mem_insert_self _ _
  have hsecondMem : secondBlock ∈ chartArgmaxFamily minimiser := by
    rw [hpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hfirstCard : firstBlock.card = rank :=
    ((mem_chartArgmaxFamily_iff minimiser firstBlock).mp hfirstMem).1
  have hsecondCard : secondBlock.card = rank :=
    ((mem_chartArgmaxFamily_iff minimiser secondBlock).mp hsecondMem).1
  have hcovered : (Finset.univ : Finset (Fin size)) ⊆ firstBlock ∪ secondBlock := by
    intro atomIndex _
    obtain ⟨block, hblockMem, hatomMem⟩ :=
      exists_mem_chartArgmaxFamily_of_isMin minimiser hweightPos hmin atomIndex
    rw [hpair] at hblockMem
    rcases Finset.mem_insert.mp hblockMem with hfirst | hsecond
    · exact Finset.mem_union_left _ (hfirst ▸ hatomMem)
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mp hsecond ▸ hatomMem)
  have hunionCard : (firstBlock ∪ secondBlock).card = size := by
    rw [Finset.Subset.antisymm (Finset.subset_univ _) hcovered, Finset.card_univ, Fintype.card_fin]
  have hdisjoint : Disjoint firstBlock secondBlock := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    have hinclusionExclusion := Finset.card_union_add_card_inter firstBlock secondBlock
    omega
  refine ⟨firstBlock, fun activeLabel hmem => ?_⟩
  rw [hpair] at hmem
  rcases Finset.mem_insert.mp hmem with heq | heq
  · exact Or.inl heq
  · refine Or.inr ?_
    rw [id, Finset.mem_singleton.mp heq]
    exact eq_compl_of_disjoint_of_card_add_card_eq_size hdisjoint (by omega)

/-! ## The floor at `size = 2 * rank`, and at the crux -/

/-- **THREE ARGMAX BLOCKS WHEN `size = 2 * rank`.**  Coverage alone gives two; the
two-member case is a complementary pair, and a complementary pair at a negative
value is excluded.  `(6,3)` is the campaign's instance. -/
theorem three_le_card_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank [Nonempty (Fin rank)]
    (design : WeightedDesign size rank) (hsize : size = 2 * rank)
    (hmin : ∀ point : ChartPoint size rank,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point)
    (hnegative : chartObjective (chartPointOfDesign design) < 0) :
    3 ≤ (chartArgmaxFamily (chartPointOfDesign design)).card := by
  have hweightPos : ∀ atomIndex : Fin size, 0 < (chartPointOfDesign design).weight atomIndex :=
    fun atomIndex => design.weight_pos atomIndex
  have hrankPos : 0 < rank := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin rank)›
  have hcount := size_le_rank_mul_card_chartArgmaxFamily_of_isMin _ hweightPos hmin
  rcases Nat.lt_or_ge (chartArgmaxFamily (chartPointOfDesign design)).card 3 with hsmall | hlarge
  swap
  · exact hlarge
  have hcard : (chartArgmaxFamily (chartPointOfDesign design)).card = 2 := by
    rcases Nat.lt_or_ge (chartArgmaxFamily (chartPointOfDesign design)).card 2 with htiny | hpair
    · exfalso
      have hcollapse : rank * (chartArgmaxFamily (chartPointOfDesign design)).card ≤ rank * 1 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · omega
  obtain ⟨chosenSubset, hfamily⟩ :=
    exists_isChartTwoBlockFamily_of_card_chartArgmaxFamily_eq_two _ hsize hweightPos hmin hcard
  exact absurd hfamily
    (not_isChartTwoBlockFamily_chartArgmaxFamily_of_isMin design hmin hnegative chosenSubset)

/-- **THREE ARGMAX TRIPLES AT A `(6,3)` MINIMISER**, from the design and negativity
alone -- the crux's other six fields are not consulted. -/
theorem three_le_card_chartArgmaxFamily_sixThree_of_isMin (design : WeightedDesign 6 3)
    (hmin : ∀ point : ChartPoint 6 3,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point)
    (hnegative : chartObjective (chartPointOfDesign design) < 0) :
    3 ≤ (chartArgmaxFamily (chartPointOfDesign design)).card :=
  three_le_card_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank design (by norm_num) hmin
    hnegative

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **THREE ARGMAX TRIPLES AT A CRUX.**  The disjunction
`Gtz.SixThreeCrux.three_le_card_chartArgmaxFamily_or_disjoint_partition` collapses:
its right branch is empty, so its left branch holds outright.  The `(7,3)` twin
`Gtz.SevenThreeCrux.three_le_card_chartArgmaxFamily` was already free, by counting
alone, because three does not divide seven. -/
theorem three_le_card_chartArgmaxFamily :
    3 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card :=
  three_le_card_chartArgmaxFamily_sixThree_of_isMin crux.design crux.isChartMinimiser
    crux.hasNegativeChartValue

end SixThreeCrux

/-! ## The isolated block, on the chart side

`Gtz.IsIsolatedActiveBlock` is the predicate the quadric chain
(`Gtz.Quantitative.IsolatedBlockExclusion`) is built on.  At `size = 2 * rank` it
collapses onto the two-block hypothesis, so it needs no localisation machinery. -/

/-- **AN ISOLATED BLOCK IS A TWO-BLOCK FAMILY.**  When `size = 2 * rank`, a block
of `rank` atoms disjoint from every other argmax block forces every other argmax
block -- itself of `rank` atoms, inside the complement, which also has `rank` atoms
-- to BE the complement. -/
theorem isChartTwoBlockFamily_of_isIsolatedActiveBlock_of_size_eq_two_mul_rank
    [Nonempty (Fin rank)] (minimiser : ChartPoint size rank) (hsize : size = 2 * rank)
    {block : Finset (Fin size)} (hblockCard : block.card = rank)
    (hisolated : IsIsolatedActiveBlock (chartArgmaxFamily minimiser)
      (id : Finset (Fin size) → Finset (Fin size)) block) :
    IsChartTwoBlockFamily (chartArgmaxFamily minimiser)
      (id : Finset (Fin size) → Finset (Fin size)) block := by
  intro activeLabel hmem
  rcases eq_or_ne (id activeLabel) block with hblock | hblock
  · exact Or.inl hblock
  · refine Or.inr ?_
    have hdisjoint : Disjoint (id activeLabel) block := hisolated activeLabel hmem hblock
    have hcard : activeLabel.card = rank :=
      ((mem_chartArgmaxFamily_iff minimiser activeLabel).mp hmem).1
    refine Finset.eq_of_subset_of_card_le (fun atomIndex hmemAtom => ?_) ?_
    · exact Finset.mem_compl.mpr fun hin => (Finset.disjoint_left.mp hdisjoint hmemAtom) hin
    · rw [Finset.card_compl, Fintype.card_fin, hblockCard]
      show size - rank ≤ activeLabel.card
      rw [hcard]
      omega

/-- **NO ISOLATED BLOCK.**  The chart-side reading of the quadric chain's
hypothesis, at `size = 2 * rank` and with no localisation: no set of `rank` atoms
is disjoint from every argmax block other than itself. -/
theorem not_isIsolatedActiveBlock_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank
    [Nonempty (Fin rank)] (design : WeightedDesign size rank) (hsize : size = 2 * rank)
    (hmin : ∀ point : ChartPoint size rank,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point)
    (hnegative : chartObjective (chartPointOfDesign design) < 0)
    {block : Finset (Fin size)} (hblockCard : block.card = rank) :
    ¬ IsIsolatedActiveBlock (chartArgmaxFamily (chartPointOfDesign design))
        (id : Finset (Fin size) → Finset (Fin size)) block :=
  fun hisolated =>
    not_isChartTwoBlockFamily_chartArgmaxFamily_of_isMin design hmin hnegative block
      (isChartTwoBlockFamily_of_isIsolatedActiveBlock_of_size_eq_two_mul_rank _ hsize hblockCard
        hisolated)

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **EVERY TRIPLE IS MET BY AN ARGMAX TRIPLE OTHER THAN ITSELF.**  The readable
form of "no isolated block": for any three atoms whatever, some argmax triple
different from them overlaps them.  The block is NOT required to be an argmax
triple, so this also says that no argmax triple is isolated. -/
theorem exists_notDisjoint_mem_chartArgmaxFamily {block : Finset (Fin 6)}
    (hblockCard : block.card = 3) :
    ∃ other ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      other ≠ block ∧ ¬ Disjoint other block := by
  by_contra hnone
  refine not_isIsolatedActiveBlock_chartArgmaxFamily_of_isMin_of_size_eq_two_mul_rank
    crux.design (by norm_num) crux.isChartMinimiser crux.hasNegativeChartValue hblockCard
    fun activeLabel hmem hne => ?_
  by_contra hoverlap
  exact hnone ⟨activeLabel, hmem, hne, hoverlap⟩

end SixThreeCrux

/-! ## The saturated atom

An atom lying in EVERY active subset.  On the quadric side saturation forces
`1 <= value` (`Gtz.one_le_value_of_saturatedAtom`); the chart-side law below is an
exact equation instead, and is not an exclusion -- see the file header. -/

variable {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
variable {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- **A SATURATED ATOM'S MULTIPLIER ROW IS A CHART EIGENVECTOR**, with eigenvalue
`value + t_c`.

The shipped `Gtz.projection_mul_multiplier_apply_of_split` needs, at every active
index, either the ROW atom inside that index's subset or the tight direction
vanishing at the COLUMN atom; saturation supplies the first alternative outright,
for every column at once.  Commuting the assembly past the chart then reads the
same entry as a matrix-vector product against that row. -/
theorem projection_mulVec_multiplierRow_of_saturatedAtom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {atomLabel : Fin size}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    projection *ᵥ (fun colAtom =>
        chartMultiplierAssembly activeSet activeWeight tightDir atomLabel colAtom)
      = (value + weight atomLabel) •
          (fun colAtom =>
            chartMultiplierAssembly activeSet activeWeight tightDir atomLabel colAtom) := by
  funext colAtom
  have hentry : (chartMultiplierAssembly activeSet activeWeight tightDir * projection)
      atomLabel colAtom
      = (value + weight atomLabel)
        * chartMultiplierAssembly activeSet activeWeight tightDir atomLabel colAtom := by
    rw [← hdata.assembly_commutes]
    exact projection_mul_multiplier_apply_of_split hdata
      fun activeLabel hmem => Or.inl (hsaturated activeLabel hmem)
  have hswap : ∀ otherAtom : Fin size,
      projection colAtom otherAtom = projection otherAtom colAtom := by
    intro otherAtom
    have hentrySymmetric := congrFun (congrFun hdata.isSymmetric otherAtom) colAtom
    rwa [Matrix.transpose_apply] at hentrySymmetric
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [← hentry, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun otherAtom _ => by rw [hswap otherAtom, mul_comm]

/-- **THE EIGENVALUE OF A SATURATED ATOM IS IDEMPOTENT.**  The chart is idempotent
and the multiplier row is nonzero -- its own diagonal entry is the bundle's forced
`1/size` -- so `value + t_c` squares to itself, i.e. it is `0` or `1`. -/
theorem sq_value_add_weight_of_saturatedAtom
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) {atomLabel : Fin size}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    (value + weight atomLabel) ^ 2 = value + weight atomLabel := by
  have hsizeNe : ((size : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (size_cast_pos_of_isChartStationaryData hdata))
  have heigen := projection_mulVec_multiplierRow_of_saturatedAtom hdata hsaturated
  have hidempotent : projection *ᵥ (projection *ᵥ (fun colAtom =>
      chartMultiplierAssembly activeSet activeWeight tightDir atomLabel colAtom))
      = projection *ᵥ (fun colAtom =>
        chartMultiplierAssembly activeSet activeWeight tightDir atomLabel colAtom) := by
    rw [Matrix.mulVec_mulVec, hdata.isIdempotent]
  rw [heigen, Matrix.mulVec_smul, heigen, smul_smul] at hidempotent
  have hcoordinate := congrFun hidempotent atomLabel
  simp only [Pi.smul_apply, smul_eq_mul, hdata.assembly_diagonal atomLabel] at hcoordinate
  rw [pow_two]
  exact mul_right_cancel₀ hsizeNe hcoordinate

/-- **A SATURATED ATOM SITS AT THE WEIGHT FLOOR.**  Its weight is exactly `-value`.
The other root `value + t_c = 1` needs `t_c = 1 - value > 1` at a negative value,
and no weight exceeds one. -/
theorem weight_eq_neg_value_of_saturatedAtom_of_negativeValue
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0) {atomLabel : Fin size}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel) :
    weight atomLabel = -value := by
  have hsquare := sq_value_add_weight_of_saturatedAtom hdata hsaturated
  have hbound : weight atomLabel ≤ 1 :=
    weight_le_one_of_sum_one hdata.weight_sum_one (fun atomIndex => (hdata.weight_pos atomIndex).le)
      atomLabel
  have hfactor : (value + weight atomLabel) * (value + weight atomLabel - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · linarith
  · linarith

/-- **A SATURATED ATOM IS A LIGHTEST ATOM.**  Its weight is `-value`, and the
shipped `Gtz.weight_ge_neg_value_of_isChartStationaryData` says `-value` is a lower
bound on every weight. -/
theorem weight_le_weight_of_saturatedAtom_of_negativeValue
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) (hnegative : value < 0) {atomLabel : Fin size}
    (hsaturated : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel)
    (otherAtom : Fin size) :
    weight atomLabel ≤ weight otherAtom := by
  rw [weight_eq_neg_value_of_saturatedAtom_of_negativeValue hdata hnegative hsaturated]
  exact weight_ge_neg_value_of_isChartStationaryData hdata otherAtom

/-- **THE OTHER ROOT IS ATTAINED, so negativity is not decoration.**  The identity
chart on two atoms with uniform weights, one active label carrying the whole index
set and the flat tight direction, is a genuine stationarity datum at
`value = 1/2` in which BOTH atoms are saturated and `value + t_c = 1`.  There
`weight_eq_neg_value_of_saturatedAtom_of_negativeValue`'s conclusion is false, so
its hypothesis `value < 0` cannot be dropped.

The witness is the degenerate `rank = size` chart, and that is forced for a datum
in which EVERY atom is saturated: the constant diagonal makes every atom lie in
some active subset with a nonzero multiplier, so a single active subset containing
all atoms must have `rank` atoms and be everything.  Whether the root `1` is
attained with `rank < size` and only SOME atom saturated is not settled here. -/
theorem exists_isChartStationaryData_saturatedAtom_value_add_weight_eq_one :
    ∃ (projection : Matrix (Fin 2) (Fin 2) ℝ) (weight : Fin 2 → ℝ) (value : ℝ)
      (activeSet : Finset (Fin 1)) (activeSubset : Fin 1 → Finset (Fin 2))
      (activeWeight : Fin 1 → ℝ) (tightDir : Fin 1 → (Fin 2 → ℝ)) (atomLabel : Fin 2),
      IsChartStationaryData 2 projection weight value activeSet activeSubset activeWeight
          tightDir
        ∧ (∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel)
        ∧ value + weight atomLabel = 1
        ∧ weight atomLabel ≠ -value := by
  have hroot : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  refine ⟨1, fun _ => (2 : ℝ)⁻¹, (2 : ℝ)⁻¹, Finset.univ, fun _ => Finset.univ, fun _ => 1,
    fun _ _ => (Real.sqrt 2)⁻¹, 0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun _ _ => Finset.mem_univ _, by norm_num, by norm_num⟩
  · exact Matrix.transpose_one
  · exact one_mul 1
  · rw [Matrix.trace_one]; norm_num
  · intro _; norm_num
  · rw [Fin.sum_univ_two]; norm_num
  · intro _ _; norm_num
  · rw [Finset.sum_const, Finset.card_univ]; norm_num
  · intro _ _; rw [Finset.card_univ]; norm_num
  · intro _ _; rw [dotProduct, Fin.sum_univ_two, hroot]; norm_num
  · intro _ _ atomIndex hnotMem; exact absurd (Finset.mem_univ atomIndex) hnotMem
  · intro _ _ atomIndex _
    simp only [chartStationaryGap, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal]
    ring
  · intro atomIndex
    rw [chartMultiplierAssembly_diagonal, Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_fin, one_smul, one_mul, pow_two, hroot]
    norm_num
  · rw [one_mul, mul_one]

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- **AT A `(6,3)` CRUX A SATURATED ATOM WEIGHS `-chartObjective`.**  An atom in
every argmax triple has its weight pinned by the chart value, and is a lightest
atom of the design. -/
theorem weight_eq_neg_chartObjective_of_saturatedAtom {atomIndex : Fin 6}
    (hsaturated : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      atomIndex ∈ block) :
    crux.design.weight atomIndex = -chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  exact weight_eq_neg_value_of_saturatedAtom_of_negativeValue hdata crux.hasNegativeChartValue
    hsaturated

end SixThreeCrux

namespace SevenThreeCrux

variable (crux : SevenThreeCrux)

/-- The `(7,3)` twin of `Gtz.SixThreeCrux.weight_eq_neg_chartObjective_of_saturatedAtom`.
The saturation law is size-generic, so it costs nothing here. -/
theorem weight_eq_neg_chartObjective_of_saturatedAtom {atomIndex : Fin 7}
    (hsaturated : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      atomIndex ∈ block) :
    crux.design.weight atomIndex = -chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ :=
    (exists_isChartStationaryData_and_isChartArgmaxValue_of_isMin _ crux.weight_pos
      crux.isChartMinimiser).1
  exact weight_eq_neg_value_of_saturatedAtom_of_negativeValue hdata crux.hasNegativeChartValue
    hsaturated

end SevenThreeCrux

/-! ## Counting against saturation

Saturation is expensive in argmax blocks: a saturated atom uses up a full column of
the incidence count, and the double count `sum_c deg(c) = rank * |family|` of
`Gtz.Quantitative.ClassRouteCost` has only `rank * |family| - size` to spend above
the coverage floor.  At `(6,3)` two saturated atoms already need a fourth block. -/

/-- **TWO SATURATED ATOMS FORCE A FOURTH ARGMAX TRIPLE AT `(6,3)`.**  Each of the
two contributes its degree in full, the remaining four atoms contribute at least one
each by coverage, and the double count is `3 * |family|`; so
`3 |family| >= 2 |family| + 4`.

Contrapositively, an argmax family of exactly three triples has AT MOST ONE
saturated atom -- and by
`Gtz.SixThreeCrux.weight_eq_neg_chartObjective_of_saturatedAtom` that atom's weight
is then pinned to `-chartObjective`. -/
theorem four_le_card_chartArgmaxFamily_of_saturatedPair_sixThree (design : WeightedDesign 6 3)
    (hmin : ∀ point : ChartPoint 6 3,
      chartObjective (chartPointOfDesign design) ≤ chartObjective point)
    {firstAtom secondAtom : Fin 6} (hdistinct : firstAtom ≠ secondAtom)
    (hfirst : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign design), firstAtom ∈ block)
    (hsecond : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign design), secondAtom ∈ block) :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign design)).card := by
  classical
  set family := chartArgmaxFamily (chartPointOfDesign design) with hfamilyDef
  have hweightPos : ∀ atomIndex : Fin 6, 0 < (chartPointOfDesign design).weight atomIndex :=
    fun atomIndex => design.weight_pos atomIndex
  have hmemberCard : ∀ chosenSubset ∈ family, chosenSubset.card = 3 :=
    fun chosenSubset hmem =>
      ((mem_chartArgmaxFamily_iff (chartPointOfDesign design) chosenSubset).mp hmem).1
  have hdouble := sum_activeFamilyDegree_eq_rank_mul_card (rank := 3) family hmemberCard
  have hfullDegree : ∀ atomIndex : Fin 6,
      (∀ chosenSubset ∈ family, atomIndex ∈ chosenSubset) →
        activeFamilyDegree family atomIndex = family.card := by
    intro atomIndex hall
    rw [activeFamilyDegree, Finset.filter_true_of_mem hall]
  have hcovered : ∀ atomIndex : Fin 6, 1 ≤ activeFamilyDegree family atomIndex := by
    intro atomIndex
    obtain ⟨block, hblockMem, hatomMem⟩ :=
      exists_mem_chartArgmaxFamily_of_isMin (chartPointOfDesign design) hweightPos hmin atomIndex
    rw [activeFamilyDegree]
    exact Finset.card_pos.mpr ⟨block, Finset.mem_filter.mpr ⟨hblockMem, hatomMem⟩⟩
  have hpairSum : ∑ atomIndex ∈ ({firstAtom, secondAtom} : Finset (Fin 6)),
      activeFamilyDegree family atomIndex = 2 * family.card := by
    rw [Finset.sum_pair hdistinct, hfullDegree firstAtom hfirst, hfullDegree secondAtom hsecond]
    ring
  have hrestSum : 4 ≤ ∑ atomIndex ∈ ({firstAtom, secondAtom} : Finset (Fin 6))ᶜ,
      activeFamilyDegree family atomIndex := by
    have hcardCompl : (({firstAtom, secondAtom} : Finset (Fin 6))ᶜ).card = 4 := by
      rw [Finset.card_compl, Finset.card_pair hdistinct, Fintype.card_fin]
    calc 4 = (({firstAtom, secondAtom} : Finset (Fin 6))ᶜ).card := hcardCompl.symm
      _ = ∑ _atomIndex ∈ ({firstAtom, secondAtom} : Finset (Fin 6))ᶜ, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun atomIndex _ => hcovered atomIndex
  have hsplit := Finset.sum_add_sum_compl ({firstAtom, secondAtom} : Finset (Fin 6))
    fun atomIndex => activeFamilyDegree family atomIndex
  omega

namespace SixThreeCrux

variable (crux : SixThreeCrux)

/-- The crux reading: two atoms lying in every argmax triple force a fourth one. -/
theorem four_le_card_chartArgmaxFamily_of_saturatedPair {firstAtom secondAtom : Fin 6}
    (hdistinct : firstAtom ≠ secondAtom)
    (hfirst : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design), firstAtom ∈ block)
    (hsecond : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      secondAtom ∈ block) :
    4 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card :=
  four_le_card_chartArgmaxFamily_of_saturatedPair_sixThree crux.design crux.isChartMinimiser
    hdistinct hfirst hsecond

end SixThreeCrux

end Gtz
