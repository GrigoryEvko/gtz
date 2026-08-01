/-
# The collar lane at `(6,3)`: the tube slot is CIRCULAR, and the stress locus
# is the margin-independent replacement

Gap 3 of the campaign ledger reads "quantitative bridge, collar lane -- HALF-BUILT
... Open input: the modulus lower bound", with a measured warning that the collar
CONSTANT erodes as the weight floor falls.  This file says, in the kernel, that
neither half of that description is where the difficulty lies.

## 1.  The open input is not weaker than the target

`Gtz.collared_two_piece_law` (`Gtz/Quantitative/CollarRate.lean:212`) takes

  `htube : dist <= tubeRadius -> (rateConst / leverageCap) * dist <= phi`

for BARE REALS `phi` and `dist`: it carries no design, no class and no quantifier,
so the class quantification lives entirely at the -- absent -- call site.
`HasCollarTubeLawAtFloor` is that slot instantiated at the tree's own objects,
`phi := Gtz.designMargin`, `dist := Metric.infDist _ (Gtz.tieLocus ...)`,
class := `Gtz.collaredSet`, with the rate and radius EXISTENTIAL, i.e. the weakest
honest reading of "the tube law holds at this weight floor".

`exists_dominates_of_hasCollarTubeLawAtFloor` then proves that slot already forces
domination, and `gtzWeightedHeavy_of_forall_hasCollarTubeLaw` that the per-floor
family of slots gives `Gtz.GtzWeightedHeavy m k` outright -- at `(6,3)` the whole of
rank three, through the shipped `Gtz.rank_three_of_heavy_six_three`.

The mechanism is that `Gtz.tieLocus` is `{margin <= 0}` intersected with the
collared class, NOT `{margin = 0}`: `Gtz.mem_tieLocus_iff` says so.  At rank five the
two agree because `Gtz.gtzWeighted_of_le_five` forces `margin >= 0`, and rank five is
where the collar layer was calibrated (`Gtz/Quantitative/CollarExponent.lean:375`
prices the effective Lojasiewicz bound at `n = 5*3 + 5 = 20`).  At `(6,3)` that
forcing theorem is exactly what is open, so every counterexample lies IN the tie
locus, at distance zero from it, where the tube inequality degenerates to
`0 <= margin`.

## 2.  The erosion was never on the logical path

The collared class is compact only at a POSITIVE weight floor, and
`Gtz.exists_collared_minimiser_of_forall_not_dominates` shows each counterexample
supplies its own floor -- its smallest weight.  A consumer therefore needs the law
once PER FLOOR, never with a floor-uniform constant, whatever rate the constant
decays at as the floor tends to zero.  That is visible in the proof of
`gtzWeightedHeavy_of_forall_hasCollarTubeLaw`, which instantiates the hypothesis at
`Finset.univ.inf' _ D.weight` and nowhere needs uniformity.

## 3.  The leverage cap does not come back the other way

A weight floor IS a leverage cap: `leverageOf_le_inv_weightFloor_of_mem_collaredSet`
is the composite of `Gtz.leverage_le_inv_floor_of_parseval` with membership of the
collared class, which the tree proves inline inside `Gtz.isCompact_collaredSet` but
never states.  The converse fails, and `weight_mul_leverageCap_sub_le` says how:
from the trace identity `Gtz.sum_weight_mul_leverage` a cap `l_c <= cap` yields
`t_c (cap - l_c) <= cap - k`, an UPPER bound on the weight and no lower bound
anywhere.  So a cap on the leverages of a crux -- which is what would bound the
collar's `l` parameter -- cannot be manufactured from the funnel, and the collar's
`l` is `1 / weightFloor` by construction rather than the design's largest leverage.

## 4.  The repair, and what it costs

`stressLocus` replaces `Gtz.tieLocus` by the collared configurations carrying a
nonzero stress.  It is cut out without reference to the margin -- equivalently by
the single polynomial equation `(hadamardSquareGram design).det = 0`, through the
shipped Frobenius bridge `Gtz.hadamardSquareGram_mulVec_eq_zero_iff` -- and on it
`Gtz.exists_dominating_sixThree_of_stress` makes `margin >= 0` a THEOREM
(`designMargin_nonneg_of_mem_stressLocus`).  A tube analysis anchored here starts
from a discharged boundary condition instead of the open conjecture.

`neg_lipschitz_mul_infDist_le_margin` is the missing companion of the shipped
`Gtz.consumedModulus_le_lipschitzConstant`: that lemma caps the modulus from ABOVE
at a set where the margin VANISHES; this one runs the estimate the other way and
needs only NONNEGATIVITY on the reference set.  Composing the two gives
`designMargin_ge_neg_reach_of_stressLocus`, an unconditional a-priori value floor
from two inputs -- a Lipschitz constant for the margin on the collared class and a
REACH bound -- neither of which is a Lojasiewicz exponent, so the measured erosion
does not touch the chain.

## 5.  A hypothesis that had to be repaired before it could be landed

The natural way to write that assembly asks for `LipschitzWith lipschitzConstant
designMargin`, a GLOBAL constant.  That hypothesis is unsatisfiable, and
`not_lipschitzWith_designMargin_sixThree` proves it: `Gtz.atomMatrix g` is `g gᵀ`, so
the margin is quadratic in the atoms while the configuration space is unbounded, and
three orthogonal spikes of length `scale` reach margin about `scale ^ 2` at distance
`scale`.  An assembly resting on a global constant would therefore be VACUOUSLY TRUE
-- it would read as a quantitative theorem while asserting nothing.  Everything here
is stated with `LipschitzOnWith` on the collared class instead, where the class is
compact, the margin is continuous, and the open content is the constant's SIZE.

WHAT THIS DOES NOT DO, stated plainly.  It does not close `Gtz.GtzWeighted 6 3` and
it does not supply either quantitative input.  Even a correct Lipschitz constant on
the class is not obviously enough: the hand estimate `6 * sqrt 3 / sqrt weightFloor`
is about `29.4` at floor `1/8`, so the product beats even the trivial floor `-1` only
for a reach below about `0.034`, on a design manifold of diameter of order one.  That
hand estimate is NOT mechanized here and is quoted as arithmetic, not as a theorem.
The live question this file makes precise is whether a DIRECTIONAL estimate along a
path to the stress locus does better -- not whether the modulus at the margin's own
zero set can be bounded, which is the question that is circular.
-/
import Mathlib
import Gtz.Design.CollaredCompact
import Gtz.Quantitative.CollarExponent
import Gtz.Quantitative.HollowInvolution
import Gtz.Reduction.ChartAttainmentWeld
import Gtz.Reduction.StressConditionalWalk
import Gtz.Ties.SelectionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## 1.  The collar's leverage cap, and the direction it does not run -/

/-- **Collared implies leverage-capped.**  `Gtz.minWeight_ge_inv_leverageCap`
(`Gtz/Quantitative/CollarRate.lean:145`) proves `1/(1/weightFloor) <= minWeight` from
`hCap : leverageCap = 1/weightFloor`; leverage appears in that NAME only, and its whole
proof is `rw [hCap, one_div_one_div]`.  The geometric content is
`Gtz.leverage_le_inv_floor_of_parseval`, in a different file, and the composite with
`Gtz.collaredSet` -- the statement "a collared configuration has capped leverage" -- is
stated nowhere.  Here it is. -/
theorem leverageOf_le_inv_weightFloor_of_mem_collaredSet {m k : ℕ} {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)}
    (hmem : config ∈ collaredSet m k weightFloor) (chosen : Fin m) :
    leverageOf (config.1 chosen) ≤ 1 / weightFloor :=
  leverage_le_inv_floor_of_parseval hmem.1 hfloor hmem.2.2.1 chosen

/-- **And the converse fails: a leverage cap floors nothing.**  From the trace identity
`Gtz.sum_weight_mul_leverage`, a cap `l_c <= cap` yields `t_c (cap - l_c) <= cap - k`: an
UPPER bound on the weight at every atom whose leverage is strictly below the cap, and a
lower bound nowhere.  So "leverage cap" and "weight floor" are not interchangeable -- the
implication runs one way, weight floor to leverage cap -- and the collar's `l` band is
governed by the smallest weight, which at a `(6,3)` crux is not known to be bounded away
from zero. -/
theorem weight_mul_leverageCap_sub_le {m k : ℕ} (D : WeightedDesign m k) {cap : ℝ}
    (hcap : ∀ c, leverageOf (D.atom c) ≤ cap) (chosen : Fin m) :
    D.weight chosen * (cap - leverageOf (D.atom chosen)) ≤ cap - (k : ℝ) := by
  have htrace := sum_weight_mul_leverage D
  have hweightSplit := Finset.add_sum_erase Finset.univ D.weight (Finset.mem_univ chosen)
  have hproductSplit := Finset.add_sum_erase Finset.univ
    (fun c => D.weight c * leverageOf (D.atom c)) (Finset.mem_univ chosen)
  have hcapped : ∑ c ∈ Finset.univ.erase chosen, D.weight c * leverageOf (D.atom c)
      ≤ ∑ c ∈ Finset.univ.erase chosen, D.weight c * cap :=
    Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hcap c) (D.weight_pos c).le
  have hcollapse : ∑ c ∈ Finset.univ.erase chosen, D.weight c * cap
      = (1 - D.weight chosen) * cap := by
    rw [← Finset.sum_mul]
    have hrest : ∑ c ∈ Finset.univ.erase chosen, D.weight c = 1 - D.weight chosen := by
      have := D.weight_sum_one
      linarith [hweightSplit]
    rw [hrest]
  rw [hcollapse] at hcapped
  nlinarith [htrace, hproductSplit, hcapped]

/-! ## 2.  The tube slot at `Gtz.tieLocus`, and its circularity -/

section TubeSlot

variable {m k : ℕ} [Nonempty (Fin k)]

/-- **The `htube` slot of `Gtz.collared_two_piece_law`, instantiated.**  The margin is the
tree's own `Gtz.designMargin`, the distance is measured to the tree's own `Gtz.tieLocus`,
and the class is the tree's own `Gtz.collaredSet`.  Rate and radius are EXISTENTIAL, so
this is the weakest reading of "the tube law holds at this weight floor". -/
def HasCollarTubeLawAtFloor (hrank : k ≤ m) (weightFloor : ℝ) : Prop :=
  ∃ tubeRadius > (0 : ℝ), ∃ tubeRate > (0 : ℝ),
    ∀ config ∈ collaredSet m k weightFloor,
      Metric.infDist config (tieLocus m k weightFloor (chartCandidates m k)) ≤ tubeRadius →
        tubeRate * Metric.infDist config (tieLocus m k weightFloor (chartCandidates m k))
          ≤ designMargin hrank config

/-- **THE CIRCULARITY.**  The tube slot at `Gtz.tieLocus` already forces domination, with
no off-tube gap, no compactness, no rate law and no radius: a design failing to dominate
lies IN the tie locus, hence at distance zero from it, where the tube inequality
degenerates to `0 <= margin`.  Every hypothesis of `Gtz.collared_two_piece_law` beyond
`htube` is therefore decorative at the frontier, and the open input of the collar lane is
not weaker than the cell it was meant to attack. -/
theorem exists_dominates_of_hasCollarTubeLawAtFloor (hrank : k ≤ m) {weightFloor : ℝ}
    (hlaw : HasCollarTubeLawAtFloor hrank weightFloor) (D : WeightedDesign m k)
    (hheavy : ∀ c, 1 ≤ leverageOf (D.atom c)) (hfloorLe : ∀ c, weightFloor ≤ D.weight c) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C := by
  by_contra hno
  push Not at hno
  have hmemCollared : ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
      ∈ collaredSet m k weightFloor := design_mem_collaredSet D hfloorLe hheavy
  have hmemTie : ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
      ∈ tieLocus m k weightFloor (chartCandidates m k) := by
    refine ⟨hmemCollared, fun gate hgate hposDef => ?_⟩
    exact hno gate ((mem_chartCandidates_iff m k gate).mp hgate) hposDef.posSemidef
  obtain ⟨tubeRadius, hradiusPos, tubeRate, _hratePos, hbound⟩ := hlaw
  have hdistZero : Metric.infDist ((D.atom, D.weight) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
      (tieLocus m k weightFloor (chartCandidates m k)) = 0 :=
    Metric.infDist_zero_of_mem hmemTie
  have hnonneg := hbound _ hmemCollared (by rw [hdistZero]; exact hradiusPos.le)
  rw [hdistZero, mul_zero] at hnonneg
  exact absurd hnonneg (not_le.mpr (designMargin_neg_of_forall_not_dominates hrank D hno))

/-- **The circularity, at the level of the whole cell.**  A tube law at every positive
weight floor implies all-heavy weighted GTZ outright -- each counterexample carries its own
smallest weight as a floor, so no floor-uniform constant is ever consumed.  At
`(m,k) = (6,3)` this is `Gtz.GtzWeightedHeavy 6 3`, which by
`Gtz.rank_three_of_heavy_six_three` carries the whole of rank three. -/
theorem gtzWeightedHeavy_of_forall_hasCollarTubeLaw (hrank : k ≤ m)
    (hlaw : ∀ weightFloor : ℝ, 0 < weightFloor → HasCollarTubeLawAtFloor hrank weightFloor) :
    GtzWeightedHeavy m k := by
  intro D hheavy
  have hpositiveRank : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  have hpositiveSize : 0 < m := lt_of_lt_of_le hpositiveRank hrank
  have hindexNonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hpositiveSize
  set weightFloor : ℝ := Finset.univ.inf' hindexNonempty D.weight with hfloorDef
  have hfloorPositive : 0 < weightFloor := by
    rw [hfloorDef, Finset.lt_inf'_iff]
    exact fun c _ => D.weight_pos c
  exact exists_dominates_of_hasCollarTubeLawAtFloor hrank (hlaw weightFloor hfloorPositive) D
    (fun c => (hheavy c).le) (fun c => Finset.inf'_le D.weight (Finset.mem_univ c))

end TubeSlot

/-! ## 3.  The stress locus: a margin-independent reference variety at `(6,3)` -/

/-- **The stress locus of the collared class at `(6,3)`.**  Collared configurations whose
Veronese images are linearly DEPENDENT.  Unlike `Gtz.tieLocus` this is cut out without any
reference to the margin -- equivalently by the single polynomial equation
`(hadamardSquareGram design).det = 0`, via the shipped Frobenius bridge
`Gtz.hadamardSquareGram_mulVec_eq_zero_iff`. -/
def stressLocus (weightFloor : ℝ) : Set ((Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)) :=
  {config | config ∈ collaredSet 6 3 weightFloor ∧
    ∃ stress : Fin 6 → ℝ, stress ≠ 0 ∧ (∑ c, stress c • atomMatrix (config.1 c)) = 0}

theorem stressLocus_subset_collaredSet (weightFloor : ℝ) :
    stressLocus weightFloor ⊆ collaredSet 6 3 weightFloor := fun _ hmem => hmem.1

/-- **Lowering the floor enlarges the reference variety.**  The collar condition is a floor
on the weights, so it is antitone; the stress condition does not mention the floor at all.
A reach measured against a locus at a SMALLER floor is therefore a smaller number, and
`designMargin_ge_neg_reach_of_stressLocus` is stated with the two floors separate for
exactly that reason. -/
theorem stressLocus_mono {weightFloor smallerFloor : ℝ} (hle : smallerFloor ≤ weightFloor) :
    stressLocus weightFloor ⊆ stressLocus smallerFloor := by
  rintro config ⟨⟨hparseval, hsum, hfloor, hheavy⟩, hstress⟩
  exact ⟨⟨hparseval, hsum, fun c => hle.trans (hfloor c), hheavy⟩, hstress⟩

/-- **THE BOUNDARY CONDITION IS A THEOREM ON THE STRESS LOCUS.**  Whereas the tube slot at
`Gtz.tieLocus` degenerates at distance zero to the open conjecture, at the stress locus it
degenerates to `Gtz.exists_dominating_sixThree_of_stress`, which is proved.  So a tube
analysis anchored here starts from a discharged boundary condition -- the structural repair
the collar lane needs at the frontier cell. -/
theorem designMargin_nonneg_of_mem_stressLocus {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {config : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)} (hmem : config ∈ stressLocus weightFloor) :
    0 ≤ designMargin (show (3 : ℕ) ≤ 6 by norm_num) config := by
  obtain ⟨hcollared, stress, hnonzero, hstress⟩ := hmem
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominating_sixThree_of_stress (designOfCollared hfloor hcollared) hnonzero hstress
  have hmember : selected ∈ chartCandidates 6 3 :=
    (mem_chartCandidates_iff 6 3 selected).mpr hcard
  have hone : (1 : ℝ) ≤ lambdaMinMat (subsetSumRaw config selected) :=
    (dominates_iff_one_le_lambdaMinMat (designOfCollared hfloor hcollared) selected).mp hdominates
  have hsup : lambdaMinMat (subsetSumRaw config selected)
      ≤ (chartCandidates 6 3).sup' (chartCandidates_nonempty (show (3 : ℕ) ≤ 6 by norm_num))
        fun candidate => lambdaMinMat (subsetSumRaw config candidate) :=
    Finset.le_sup' (f := fun candidate => lambdaMinMat (subsetSumRaw config candidate)) hmember
  rw [designMargin]
  linarith

/-! ### Populating the locus -/

/-- **A parallel pair IS a stress, in the positive direction.**  The tree ships only the
contrapositive, `Gtz.not_hasParallelPair_of_no_stress`, whose proof builds the annihilating
combination `e_dropLabel - ratio^2 * e_keptLabel` and then discards it into a negation.
This recovers the witness, so no second construction of it is needed anywhere. -/
theorem exists_stress_of_hasParallelPair (design : WeightedDesign 6 3)
    (hparallel : HasParallelPair design) :
    ∃ stress : Fin 6 → ℝ, stress ≠ 0 ∧ (∑ c, stress c • atomMatrix (design.atom c)) = 0 := by
  by_contra hno
  push Not at hno
  refine not_hasParallelPair_of_no_stress design (fun stress hsum => ?_) hparallel
  by_contra hne
  exact hno stress hne hsum

/-- **The parallel-pair stratum lies in the stress locus.**  General in the ratio, so it
covers the merged, the doubled and the antipodal pairs alike. -/
theorem mem_stressLocus_of_parallel_atoms {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {config : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)}
    (hcollared : config ∈ collaredSet 6 3 weightFloor)
    {keptLabel dropLabel : Fin 6} {ratio : ℝ} (hdistinct : keptLabel ≠ dropLabel)
    (hparallel : config.1 dropLabel = ratio • config.1 keptLabel) :
    config ∈ stressLocus weightFloor := by
  obtain ⟨stress, hnonzero, hsum⟩ :=
    exists_stress_of_hasParallelPair (designOfCollared hfloor hcollared)
      ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  exact ⟨hcollared, stress, hnonzero, hsum⟩

/-- The repeated-atom case, `ratio = 1`. -/
theorem mem_stressLocus_of_repeated_atom {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {config : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)}
    (hcollared : config ∈ collaredSet 6 3 weightFloor)
    {first second : Fin 6} (hne : first ≠ second) (heq : config.1 second = config.1 first) :
    config ∈ stressLocus weightFloor :=
  mem_stressLocus_of_parallel_atoms hfloor hcollared (ratio := 1) hne (by rw [heq, one_smul])

/-- **THE STRESS LOCUS IS NONEMPTY, AT A SHIPPED WITNESS.**  The doubled tetrahedron
`Gtz.doubledTetrahedronDesign` has atoms `0` and `1` equal, every leverage `3`, and every
weight at least `1/8`, so its configuration is collared at floor `1/8` and lies in the
stress locus.  This discharges the `hNonempty` slot of
`designMargin_ge_neg_reach_of_stressLocus`: the arc below is not vacuous, and the reach
bound has a concrete anchor to be measured from. -/
theorem doubledTetrahedron_mem_stressLocus :
    ((doubledTetrahedronDesign.atom, doubledTetrahedronDesign.weight) :
        (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ))
      ∈ stressLocus (1 / 8) := by
  have hweights : ∀ c, (1 : ℝ) / 8 ≤ doubledTetrahedronDesign.weight c := by
    intro c
    fin_cases c <;> norm_num [doubledTetrahedronDesign]
  have hthird : ∀ first second third : ℝ, (![first, second, third] : Fin 3 → ℝ) 2 = third :=
    fun _ _ _ => rfl
  have hheavy : ∀ c, (1 : ℝ) ≤ leverageOf (doubledTetrahedronDesign.atom c) := by
    intro c
    fin_cases c <;>
      norm_num [leverageOf, doubledTetrahedronDesign, doubledTetrahedronAtom,
        Fin.sum_univ_three, hthird]
  refine mem_stressLocus_of_repeated_atom (by norm_num)
    (design_mem_collaredSet doubledTetrahedronDesign hweights hheavy)
    (first := 0) (second := 1) (by decide) ?_
  simp only [doubledTetrahedronDesign, doubledTetrahedronAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem stressLocus_nonempty : (stressLocus (1 / 8)).Nonempty :=
  ⟨_, doubledTetrahedron_mem_stressLocus⟩

/-! ## 4.  A reference variety with a nonnegative margin gives a VALUE FLOOR

### 4a.  First, why the constant has to be a constant ON A SET

`Gtz.designMargin` is QUADRATIC in the atoms -- `Gtz.atomMatrix g` is `g gᵀ` -- and its
carrier is the whole unbounded configuration space, so it admits NO global Lipschitz
constant.  `not_lipschitzWith_designMargin_sixThree` proves that outright, by exhibiting
three orthogonal spikes of length `scale` whose margin grows like `scale ^ 2` at distance
`scale` from the origin.

This is not a technicality.  An assembled value floor stated with a `LipschitzWith`
hypothesis would be VACUOUSLY TRUE -- it would read like a quantitative theorem while
asserting nothing at all, since its hypothesis is unsatisfiable.  Every statement below
uses `LipschitzOnWith` on the collared class instead, where the hypothesis is genuinely
open: that class is compact and the margin is continuous on it. -/

/-- Three orthogonal spikes of length `scale`, three zero atoms, uniform weights.  This is a
CONFIGURATION and not a design -- Parseval fails at every `scale` -- which is exactly the
point: `Gtz.designMargin` is defined on raw configurations, so that is where its Lipschitz
constant would have to live. -/
noncomputable def spikeGrowthConfig (scale : ℝ) : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ) :=
  (fun atomIndex coordinate => if (atomIndex : ℕ) = (coordinate : ℕ) then scale else 0,
    fun _ => 1 / 6)

/-- The first three spikes sum to `scale ^ 2` times the identity. -/
theorem subsetSumRaw_spikeGrowthConfig (scale : ℝ) :
    subsetSumRaw (spikeGrowthConfig scale) {0, 1, 2}
      = (scale ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext rowIndex columnIndex
  fin_cases rowIndex <;> fin_cases columnIndex <;>
    simp [subsetSumRaw, spikeGrowthConfig, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.sum_apply, Finset.sum_insert, Finset.mem_insert] <;> ring

/-- Hence the margin grows at least quadratically along the family. -/
theorem sq_sub_one_le_designMargin_spikeGrowthConfig (scale : ℝ) :
    scale ^ 2 - 1
      ≤ designMargin (show (3 : ℕ) ≤ 6 by norm_num) (spikeGrowthConfig scale) := by
  have hmember : ({0, 1, 2} : Finset (Fin 6)) ∈ chartCandidates 6 3 :=
    (mem_chartCandidates_iff 6 3 _).mpr (by decide)
  have hsymmetric : (subsetSumRaw (spikeGrowthConfig scale) {0, 1, 2})ᵀ
      = subsetSumRaw (spikeGrowthConfig scale) {0, 1, 2} := by
    rw [subsetSumRaw_spikeGrowthConfig, Matrix.transpose_smul, Matrix.transpose_one]
  have hlower : scale ^ 2
      ≤ lambdaMinMat (subsetSumRaw (spikeGrowthConfig scale) {0, 1, 2}) := by
    rw [le_lambdaMinMat_iff_posSemidef_sub_smul_one _ hsymmetric,
      subsetSumRaw_spikeGrowthConfig, sub_self]
    exact Matrix.PosSemidef.zero
  have hsup := Finset.le_sup'
    (f := fun candidate => lambdaMinMat (subsetSumRaw (spikeGrowthConfig scale) candidate))
    hmember
  rw [designMargin]
  linarith

/-- While the family stays at distance at most `scale` from its own base point. -/
theorem dist_spikeGrowthConfig_le {scale : ℝ} (hscale : 0 ≤ scale) :
    dist (spikeGrowthConfig scale) (spikeGrowthConfig 0) ≤ scale := by
  rw [Prod.dist_eq]
  refine max_le ((dist_pi_le_iff hscale).mpr fun atomIndex => ?_) ?_
  · refine (dist_pi_le_iff hscale).mpr fun coordinate => ?_
    simp only [spikeGrowthConfig, Real.dist_eq]
    by_cases hdiagonal : (atomIndex : ℕ) = (coordinate : ℕ)
    · simp [hdiagonal, abs_of_nonneg hscale]
    · simp [hdiagonal]
      linarith
  · simp only [spikeGrowthConfig, dist_self]
    exact hscale

/-- **NO GLOBAL LIPSCHITZ CONSTANT EXISTS FOR THE `(6,3)` DESIGN MARGIN.**  Quadratic growth
at linear distance defeats every candidate constant: at `scale = lipschitzConstant +
|baseValue| + 2` the margin has already outrun `lipschitzConstant * scale`.

The consequence for this file is stated at `designMargin_ge_neg_reach_of_stressLocus`, and
the consequence for anyone else is general: a quantitative statement about the design margin
must name the SET its constant is taken over, or it says nothing. -/
theorem not_lipschitzWith_designMargin_sixThree (lipschitzConstant : NNReal) :
    ¬ LipschitzWith lipschitzConstant
      (designMargin (m := 6) (k := 3) (show (3 : ℕ) ≤ 6 by norm_num)) := by
  intro hLipschitz
  set baseValue : ℝ :=
    designMargin (show (3 : ℕ) ≤ 6 by norm_num) (spikeGrowthConfig 0) with hbaseValue
  set scale : ℝ := (lipschitzConstant : ℝ) + |baseValue| + 2 with hscaleDef
  have hConstNonneg : (0 : ℝ) ≤ (lipschitzConstant : ℝ) := lipschitzConstant.coe_nonneg
  have hAbsNonneg : (0 : ℝ) ≤ |baseValue| := abs_nonneg _
  have hScaleTwo : (2 : ℝ) ≤ scale := by rw [hscaleDef]; linarith
  have hScaleNonneg : (0 : ℝ) ≤ scale := by linarith
  have hdist := hLipschitz.dist_le_mul (spikeGrowthConfig scale) (spikeGrowthConfig 0)
  rw [Real.dist_eq] at hdist
  have hupper := (abs_le.mp hdist).2
  have hshort : (lipschitzConstant : ℝ) * dist (spikeGrowthConfig scale) (spikeGrowthConfig 0)
      ≤ (lipschitzConstant : ℝ) * scale :=
    mul_le_mul_of_nonneg_left (dist_spikeGrowthConfig_le hScaleNonneg) hConstNonneg
  have hlower := sq_sub_one_le_designMargin_spikeGrowthConfig scale
  have hbase : baseValue ≤ |baseValue| := le_abs_self _
  have hproduct : 0 ≤ |baseValue| * (scale - 1) :=
    mul_nonneg hAbsNonneg (by linarith)
  nlinarith [hlower, hupper, hshort, hbase, hproduct, hscaleDef]

/-! ### 4b.  The transport lemmas -/

/-- **The missing companion of `Gtz.consumedModulus_le_lipschitzConstant`.**  That lemma
caps the collar modulus from ABOVE by the margin's Lipschitz constant, and asks the
reference set to be a set where the margin VANISHES.  This one runs the estimate the other
way and asks only that the margin be NONNEGATIVE there: a reference set on which it is
nonnegative floors the margin everywhere by `-lipschitzConstant * dist(-, reference)`.

The weaker hypothesis is the whole point.  `margin = 0` on the reference set is, at the
frontier cell, a statement nobody can supply without the conjecture; `0 <= margin` on the
stress locus is `designMargin_nonneg_of_mem_stressLocus`. -/
theorem neg_lipschitz_mul_infDist_le_margin {carrier : Type*} [MetricSpace carrier]
    {margin : carrier → ℝ} {lipschitzConstant : NNReal}
    (hLipschitz : LipschitzWith lipschitzConstant margin)
    {reference : Set carrier} (hNonempty : reference.Nonempty)
    (hNonneg : ∀ anchor ∈ reference, 0 ≤ margin anchor) (point : carrier) :
    -((lipschitzConstant : ℝ) * Metric.infDist point reference) ≤ margin point := by
  have hCoeNonneg : (0 : ℝ) ≤ (lipschitzConstant : ℝ) := lipschitzConstant.coe_nonneg
  have hkey : ∀ anchor ∈ reference,
      -margin point ≤ (lipschitzConstant : ℝ) * dist point anchor := by
    intro anchor hanchor
    have hdist := hLipschitz.dist_le_mul point anchor
    rw [Real.dist_eq] at hdist
    have habs := abs_le.mp hdist
    linarith [hNonneg anchor hanchor, habs.1]
  rcases eq_or_lt_of_le hCoeNonneg with hzeroConst | hposConst
  · obtain ⟨anchor, hanchor⟩ := hNonempty
    have hstep := hkey anchor hanchor
    rw [← hzeroConst] at hstep ⊢
    simp only [zero_mul, neg_zero] at hstep ⊢
    linarith
  · have hquotient : -margin point / (lipschitzConstant : ℝ)
        ≤ Metric.infDist point reference := by
      refine (Metric.le_infDist hNonempty).mpr fun anchor hanchor => ?_
      rw [div_le_iff₀ hposConst]
      linarith [hkey anchor hanchor]
    have hscaled : -margin point
        ≤ (lipschitzConstant : ℝ) * Metric.infDist point reference := by
      calc -margin point
          = -margin point / (lipschitzConstant : ℝ) * (lipschitzConstant : ℝ) := by field_simp
        _ ≤ Metric.infDist point reference * (lipschitzConstant : ℝ) := by gcongr
        _ = (lipschitzConstant : ℝ) * Metric.infDist point reference := mul_comm _ _
    linarith

/-- **The same estimate under Lipschitz control ON A SET, which is the form the frontier
can actually supply.**  The global version above is useless at `(6,3)`: the design margin is
QUADRATIC in the atoms, so it is not globally Lipschitz on the unbounded configuration
space -- `not_lipschitzWith_designMargin_sixThree` proves that, and an assembly stated with
a global constant would be vacuously true.  Lipschitz control on the COMPACT collared class
is a different matter, and it is what `designMargin_ge_neg_reach_of_stressLocus` asks for. -/
theorem neg_lipschitzOn_mul_infDist_le_margin {carrier : Type*} [MetricSpace carrier]
    {margin : carrier → ℝ} {lipschitzConstant : NNReal} {ambient : Set carrier}
    (hLipschitz : LipschitzOnWith lipschitzConstant margin ambient)
    {reference : Set carrier} (hsubset : reference ⊆ ambient) (hNonempty : reference.Nonempty)
    (hNonneg : ∀ anchor ∈ reference, 0 ≤ margin anchor)
    {point : carrier} (hpoint : point ∈ ambient) :
    -((lipschitzConstant : ℝ) * Metric.infDist point reference) ≤ margin point := by
  have hCoeNonneg : (0 : ℝ) ≤ (lipschitzConstant : ℝ) := lipschitzConstant.coe_nonneg
  have hkey : ∀ anchor ∈ reference,
      -margin point ≤ (lipschitzConstant : ℝ) * dist point anchor := by
    intro anchor hanchor
    have hdist := hLipschitz.dist_le_mul point hpoint anchor (hsubset hanchor)
    rw [Real.dist_eq] at hdist
    have habs := abs_le.mp hdist
    linarith [hNonneg anchor hanchor, habs.1]
  rcases eq_or_lt_of_le hCoeNonneg with hzeroConst | hposConst
  · obtain ⟨anchor, hanchor⟩ := hNonempty
    have hstep := hkey anchor hanchor
    rw [← hzeroConst] at hstep ⊢
    simp only [zero_mul, neg_zero] at hstep ⊢
    linarith
  · have hquotient : -margin point / (lipschitzConstant : ℝ)
        ≤ Metric.infDist point reference := by
      refine (Metric.le_infDist hNonempty).mpr fun anchor hanchor => ?_
      rw [div_le_iff₀ hposConst]
      linarith [hkey anchor hanchor]
    have hscaled : -margin point
        ≤ (lipschitzConstant : ℝ) * Metric.infDist point reference := by
      calc -margin point
          = -margin point / (lipschitzConstant : ℝ) * (lipschitzConstant : ℝ) := by field_simp
        _ ≤ Metric.infDist point reference * (lipschitzConstant : ℝ) := by gcongr
        _ = (lipschitzConstant : ℝ) * Metric.infDist point reference := mul_comm _ _
    linarith

/-- **THE ASSEMBLED A-PRIORI VALUE FLOOR AT `(6,3)`.**  Two quantitative inputs -- a
Lipschitz constant for the design margin ON THE COLLARED CLASS, and a REACH bound saying
every collared configuration lies within `reach` of the stress locus -- deliver an
unconditional lower bound `margin >= -lipschitzConstant * reach` at every collared
configuration.

This is the shape the value lane wants and never stated: not a modulus at the margin's own
zero set, which is circular by `exists_dominates_of_hasCollarTubeLawAtFloor`, but a
Lipschitz transport from a variety where nonnegativity is PROVED.  Both inputs are
finite-dimensional, exactly computable and falsifiable, and neither is a Lojasiewicz
exponent, so the measured erosion of the collar constant does not touch this chain.

THE LIPSCHITZ HYPOTHESIS IS `LipschitzOnWith` AND NOT `LipschitzWith`, AND THAT IS NOT
COSMETIC.  `not_lipschitzWith_designMargin_sixThree` proves no global constant exists, so
the same statement with a global hypothesis would be vacuously true -- it would look like an
assembled value floor while asserting nothing.  On the collared class the hypothesis is
instead genuinely open: the class is compact (`Gtz.isCompact_collaredSet`) and the margin is
continuous on it (`Gtz.continuous_designMargin`), so a constant exists on general grounds
and the content is its SIZE.

The reference variety and the ambient class carry the SAME floor, because the transport
needs the reference set inside the set the Lipschitz bound covers and `Gtz.collaredSet` is
antitone in the floor.  A user holding Lipschitz control on a larger class may enlarge the
reference variety by `stressLocus_mono` and shrink the reach accordingly. -/
theorem designMargin_ge_neg_reach_of_stressLocus {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {lipschitzConstant : NNReal}
    (hLipschitz : LipschitzOnWith lipschitzConstant
      (designMargin (m := 6) (k := 3) (show (3 : ℕ) ≤ 6 by norm_num))
      (collaredSet 6 3 weightFloor))
    (hNonempty : (stressLocus weightFloor).Nonempty) {reach : ℝ}
    (hReach : ∀ config ∈ collaredSet 6 3 weightFloor,
      Metric.infDist config (stressLocus weightFloor) ≤ reach)
    {config : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)}
    (hmem : config ∈ collaredSet 6 3 weightFloor) :
    -((lipschitzConstant : ℝ) * reach)
      ≤ designMargin (show (3 : ℕ) ≤ 6 by norm_num) config := by
  have hbase := neg_lipschitzOn_mul_infDist_le_margin hLipschitz
    (stressLocus_subset_collaredSet weightFloor) hNonempty
    (fun anchor hanchor => designMargin_nonneg_of_mem_stressLocus hfloor hanchor) hmem
  have hmono : (lipschitzConstant : ℝ) * Metric.infDist config (stressLocus weightFloor)
      ≤ (lipschitzConstant : ℝ) * reach :=
    mul_le_mul_of_nonneg_left (hReach config hmem) lipschitzConstant.coe_nonneg
  linarith

end Gtz
