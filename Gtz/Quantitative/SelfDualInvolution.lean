/-
# The `(6,3)` self-duality as an involution: what it preserves, and where it is free

`k * (k + 1) / 2 = 2 * k` holds only at `k = 3`, so `(6,3)` is the unique cell that is
simultaneously the Veronese top and Naimark self-dual.  This file asks what the
resulting involution actually does, and answers three questions the campaign left open.

## 1.  THE INVOLUTION HAS NO FIXED POINT, at any size and rank

`projectionOfDesign_ne_of_isChartDual`.  A design and its chart dual never share a
projection chart, so the involution is fixed-point free on designs-up-to-rotation.  The
proof is three lines of ring algebra on `Gtz.projectionOfDesign_mul_self` and needs no
hypothesis at all.  Consequence for a parity argument: the involution has no fixed
point to exclude, so any counting must come from a FINITE invariant it acts on.

## 2.  THE TWO DUALS COINCIDE AT A UNIFORM WEIGHT — the `D4` band, repaired

`Gtz/Quantitative/ChartDuality.lean` proves a NEGATIVE:
`Gtz.not_forall_dominates_chartDual_compl` exhibits a rational all-heavy `(6,3)` design
whose CHART dual fails the Loewner flip, and concludes that the ledger's D4 band — which
wanted the anti-parity law and the crux transport on ONE object — is unavailable.

That negative is sharp only OFF the uniform-weight slice.
`dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` proves the Loewner
flip FOR THE CHART DUAL whenever the weights are uniform, so on that slice the chart
dual IS a Naimark dual and every D1/D2/D3/D5 property holds simultaneously with the
crux transport.  The separating witness `Gtz.orthoSplitDesign` carries the weights
`1/6, 1/6, 2/5, 1/10, 1/12, 1/12`, which is exactly why it can separate them.

The proof is elementary and spectral-free: at a uniform weight the two selected Gram
matrices satisfy `N Nᵀ = weight⁻¹ • 1 − M Mᵀ`, and two applications of the shipped
transpose flips move the statement from `Cᶜ` on the dual to `C` on the primal.

## 3.  NO PARITY ARGUMENT CAN BITE AT THE SIGN LAYER

`sectorSurvives_compl_eq`.  The complement involution on two-graphs is `link ↦ 1023 −
link`, and `Gtz.sectorSurvives` is INVARIANT under it — not merely as a measured
coincidence but for every one of the 1024 patterns.  So "a pattern survives only if its
complement does" removes nothing, whether or not it is licensed.  Together with §2 this
closes the sign-layer parity route from both ends: on the uniform slice the filter is
licensed and void, off it the filter is unlicensed.

## 4.  A `decide`-BOUNDED GENERALITY DEFECT, REPAIRED

`Gtz.selfDual_eq_top_iff` is stated for `rank ≤ 40` and proved by `decide`.
`selfDual_eq_top_iff_of_pos` proves it at every rank, by the one-line argument
`2k = k(k+1)/2` with `k > 0` gives `4 = k + 1`.

## NOT PROVED here, and named

The Naimark dual of `Gtz.exists_naimarkDual_loewnerEquiv` is delivered existentially and
its projection chart is never exposed, so nothing below is a statement about THAT object
except through the shipped flip.  In particular "the Naimark involution is fixed-point
free" is NOT proved here; §1 is about the chart dual only.
-/
import Mathlib
import Gtz.Quantitative.ChartDuality
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.TwoGraphCollision
import Gtz.Reduction.RankFourLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k dualRank : ℕ}

/-! ## 1.  The chart-dual involution is fixed-point free -/

/-- **NO DESIGN IS ITS OWN CHART DUAL.**  The two projection charts are complementary,
and a projection cannot equal its own complement: `P + P = 1` multiplied by `P` and
folded through idempotence gives `P = 0`, whence `1 = 0`.

No hypothesis beyond a nonempty index set, so the involution is fixed-point free on the
whole design space at every size and rank, hence on every subset of it — the crux locus
included. -/
theorem projectionOfDesign_ne_of_isChartDual [Nonempty (Fin m)]
    {design : WeightedDesign m k} {dual : WeightedDesign m dualRank}
    (hdual : IsChartDual design dual) :
    projectionOfDesign dual ≠ projectionOfDesign design := by
  intro hsame
  have hself : projectionOfDesign design = 1 - projectionOfDesign design :=
    hsame.symm.trans hdual.chart_eq
  have hsum : projectionOfDesign design + projectionOfDesign design
      = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    nth_rewrite 1 [hself]
    abel
  have hidem := projectionOfDesign_mul_self design
  have hzero : projectionOfDesign design = 0 := by
    have hleft : projectionOfDesign design
        * (projectionOfDesign design + projectionOfDesign design)
          = projectionOfDesign design * 1 := by rw [hsum]
    rw [Matrix.mul_add, hidem, Matrix.mul_one] at hleft
    have := hleft
    linear_combination (norm := module) this
  rw [hzero, add_zero] at hsum
  obtain ⟨atomIndex⟩ := ‹Nonempty (Fin m)›
  have hentry := congrFun (congrFun hsum atomIndex) atomIndex
  rw [Matrix.zero_apply, Matrix.one_apply_eq] at hentry
  exact zero_ne_one hentry

/-! ## 2.  At a uniform weight the chart dual carries the Loewner flip -/

/-- The chart dual's Gram at a uniform weight: `g'_c ⬝ g'_d = weight⁻¹ δ_cd − g_c ⬝ g_d`.
`Gtz.dotProduct_chartDual_of_ne` is the off-diagonal half and
`Gtz.leverageOf_chartDual` the diagonal one; uniformity is what lets the two be written
as one formula. -/
theorem dotProduct_chartDual_of_uniformWeight
    {design : WeightedDesign m k} {dual : WeightedDesign m dualRank}
    (hdual : IsChartDual design dual) {weightValue : ℝ}
    (huniform : ∀ atomIndex, design.weight atomIndex = weightValue)
    (rowIndex colIndex : Fin m) :
    dual.atom rowIndex ⬝ᵥ dual.atom colIndex
      = weightValue⁻¹ * (1 : Matrix (Fin m) (Fin m) ℝ) rowIndex colIndex
        - design.atom rowIndex ⬝ᵥ design.atom colIndex := by
  rcases eq_or_ne rowIndex colIndex with rfl | hne
  · rw [Matrix.one_apply_eq, mul_one, dotProduct_self_eq_sum_sq, ← leverageOf,
      dotProduct_self_eq_sum_sq, ← leverageOf, leverageOf_chartDual hdual, huniform]
  · rw [Matrix.one_apply_ne hne, mul_zero, zero_sub, dotProduct_chartDual_of_ne hdual hne]

/-- The same identity on the selected-row matrices, which is the form the flip reads:
`N Nᵀ = weight⁻¹ • 1 − M Mᵀ` along any injective selection. -/
theorem selectedAtomRows_mul_transpose_chartDual_of_uniformWeight
    {design : WeightedDesign m k} {dual : WeightedDesign m dualRank}
    (hdual : IsChartDual design dual) {weightValue : ℝ}
    (huniform : ∀ atomIndex, design.weight atomIndex = weightValue)
    {size : ℕ} (pick : Fin size → Fin m) (hinj : Function.Injective pick) :
    selectedAtomRows dual pick * (selectedAtomRows dual pick)ᵀ
      = weightValue⁻¹ • (1 : Matrix (Fin size) (Fin size) ℝ)
        - selectedAtomRows design pick * (selectedAtomRows design pick)ᵀ := by
  ext rowIndex colIndex
  have hgram := dotProduct_chartDual_of_uniformWeight hdual huniform (pick rowIndex)
    (pick colIndex)
  have hone : (1 : Matrix (Fin m) (Fin m) ℝ) (pick rowIndex) (pick colIndex)
      = (1 : Matrix (Fin size) (Fin size) ℝ) rowIndex colIndex := by
    rcases eq_or_ne rowIndex colIndex with rfl | hne
    · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (fun hcontra => hne (hinj hcontra)), Matrix.one_apply_ne hne]
  rw [hone] at hgram
  simpa [Matrix.mul_apply, Matrix.transpose_apply, selectedAtomRows, dotProduct,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using hgram

/-- Positive scaling does not change semidefiniteness. -/
private theorem posSemidef_smul_iff_of_pos {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    {factor : ℝ} (hfactor : 0 < factor) :
    (factor • form).PosSemidef ↔ form.PosSemidef := by
  refine ⟨fun hscaled => ?_, fun hform => hform.smul hfactor.le⟩
  have hback := hscaled.smul (a := factor⁻¹) (inv_pos.mpr hfactor).le
  rwa [smul_smul, inv_mul_cancel₀ hfactor.ne', one_smul] at hback

/-- **THE LEVELLED CONTRACTION FLIP.**  `Gtz.posSemidef_one_sub_transpose_comm` at an
arbitrary positive level, obtained by rescaling the rectangular factor by
`(sqrt level)⁻¹`.  The shipped statement is the case `level = 1`. -/
theorem posSemidef_smul_one_sub_transpose_comm {leftDim rightDim : ℕ} {level : ℝ}
    (hlevel : 0 < level) (X : Matrix (Fin leftDim) (Fin rightDim) ℝ) :
    (level • (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - Xᵀ * X).PosSemidef
      ↔ (level • (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - X * Xᵀ).PosSemidef := by
  have hsqrt : (0 : ℝ) < Real.sqrt level := Real.sqrt_pos.mpr hlevel
  have hsquare : (Real.sqrt level)⁻¹ * (Real.sqrt level)⁻¹ = level⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hlevel.le]
  set scaled : Matrix (Fin leftDim) (Fin rightDim) ℝ := (Real.sqrt level)⁻¹ • X with hscaled
  have hright : (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - scaledᵀ * scaled
      = level⁻¹ • (level • (1 : Matrix (Fin rightDim) (Fin rightDim) ℝ) - Xᵀ * X) := by
    rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsquare,
      smul_sub, smul_smul, inv_mul_cancel₀ hlevel.ne', one_smul]
  have hleft : (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - scaled * scaledᵀ
      = level⁻¹ • (level • (1 : Matrix (Fin leftDim) (Fin leftDim) ℝ) - X * Xᵀ) := by
    rw [hscaled, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsquare,
      smul_sub, smul_smul, inv_mul_cancel₀ hlevel.ne', one_smul]
  have hbridge := posSemidef_one_sub_transpose_comm scaled
  rw [hright, hleft, posSemidef_smul_iff_of_pos (inv_pos.mpr hlevel),
    posSemidef_smul_iff_of_pos (inv_pos.mpr hlevel)] at hbridge
  exact hbridge

/-- **THE `D4` BAND, REPAIRED ON THE UNIFORM-WEIGHT SLICE.**  At a uniform weight the
CHART dual satisfies the Loewner flip: a triple dominates the design exactly when its
complement dominates the chart dual.

`Gtz.not_forall_dominates_chartDual_compl` shows this FAILS in general, and its witness
`Gtz.orthoSplitDesign` has weights `1/6, 1/6, 2/5, 1/10, 1/12, 1/12` — non-uniform,
which is exactly the room this theorem closes.  On the uniform slice the anti-parity law
`Gtz.tripleParity_chartDual` and the crux transport
`Gtz.SixThreeCrux.exists_naimarkDual_allHeavy_not_dominating` therefore hold on ONE
object, which is what the ledger's D4 band asked for. -/
theorem dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree
    {design dual : WeightedDesign 6 3} (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex, design.weight atomIndex = (6 : ℝ)⁻¹)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    Dominates design selected ↔ Dominates dual selectedᶜ := by
  classical
  have hcardCompl : (selectedᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  set pick : Fin 3 → Fin 6 := ⇑((selectedᶜ).orderEmbOfFin hcardCompl) with hpick
  have hinj : Function.Injective pick := ((selectedᶜ).orderEmbOfFin hcardCompl).injective
  have himage : Finset.image pick Finset.univ = selectedᶜ := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hpick, Finset.range_orderEmbOfFin]
  set primalRows := selectedAtomRows design pick with hprimalRows
  set dualRows := selectedAtomRows dual pick with hdualRows
  have hprimalSub : primalRowsᵀ * primalRows = subsetSum design selectedᶜ := by
    rw [hprimalRows, transpose_mul_selectedAtomRows design pick hinj, himage]
  have hdualSub : dualRowsᵀ * dualRows = subsetSum dual selectedᶜ := by
    rw [hdualRows, transpose_mul_selectedAtomRows dual pick hinj, himage]
  have hgram : dualRows * dualRowsᵀ
      = (6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - primalRows * primalRowsᵀ := by
    have hraw := selectedAtomRows_mul_transpose_chartDual_of_uniformWeight hdual huniform
      pick hinj
    rw [hprimalRows, hdualRows]
    simpa using hraw
  have hlevel : ((6 : ℝ)⁻¹⁻¹ - 1) = (5 : ℝ) := by norm_num
  rw [dominates_iff_posSemidef_smul_one_sub_subsetSum_compl design huniform selected, hlevel,
    ← hprimalSub, posSemidef_smul_one_sub_transpose_comm (by norm_num : (0 : ℝ) < 5) primalRows,
    Dominates, ← hdualSub, posSemidef_transpose_mul_sub_one_comm dualRows, hgram]
  refine Iff.of_eq (congrArg Matrix.PosSemidef ?_)
  rw [show ((5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = (6 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - 1 by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, add_smul, one_smul]; abel]
  abel

/-! ## 3.  What the involution does to the crux fields, on the uniform slice -/

/-- **THE CO-SINGLETON FIELD IS A LEVERAGE CEILING AT A UNIFORM WEIGHT.**  Strict
domination of every co-singleton says exactly `leverage < weight⁻¹ − 1`, which at
`(6,3)` with weight `1/6` reads `leverage < 5`.  Paired with `Gtz.AllHeavy` this pins a
doubly heavy design into the window `1 < leverage < 5`. -/
theorem leverageOf_lt_of_hasStrictlyDominatingCoSingletons_of_uniformWeight
    (design : WeightedDesign m k) {weightValue : ℝ}
    (huniform : ∀ atomIndex, design.weight atomIndex = weightValue)
    (hco : HasStrictlyDominatingCoSingletons design) (atomIndex : Fin m)
    (hpositive : 0 < leverageOf (design.atom atomIndex)) :
    leverageOf (design.atom atomIndex) < weightValue⁻¹ - 1 := by
  classical
  have hsplit := subsetSum_add_subsetSum_compl_of_uniformWeight design huniform
    ({atomIndex} : Finset (Fin m))
  have hsingle : subsetSum design ({atomIndex} : Finset (Fin m))
      = atomMatrix (design.atom atomIndex) := by
    rw [subsetSum, Finset.sum_singleton]
  have hcompl : subsetSum design ({atomIndex} : Finset (Fin m))ᶜ - 1
      = (weightValue⁻¹ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)
        - subsetSum design ({atomIndex} : Finset (Fin m)) := by
    have hrewrite : subsetSum design ({atomIndex} : Finset (Fin m))ᶜ
        = weightValue⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)
          - subsetSum design ({atomIndex} : Finset (Fin m)) := by
      rw [← hsplit]; abel
    rw [hrewrite, sub_smul, one_smul]
    abel
  have hposDef := hco atomIndex
  rw [hcompl] at hposDef
  have hne : design.atom atomIndex ≠ 0 := by
    intro hzero
    rw [hzero] at hpositive
    simp [leverageOf] at hpositive
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rw [star_trivial] at hform
  have hquad : design.atom atomIndex ⬝ᵥ
      (((weightValue⁻¹ - 1) • (1 : Matrix (Fin k) (Fin k) ℝ)
        - subsetSum design ({atomIndex} : Finset (Fin m))) *ᵥ design.atom atomIndex)
      = (weightValue⁻¹ - 1) * leverageOf (design.atom atomIndex)
        - leverageOf (design.atom atomIndex) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, dotProduct_self_eq_sum_sq, ← leverageOf,
      dotProduct_subsetSum_mulVec_of_finset, Finset.sum_singleton, dotProduct_self_eq_sum_sq,
      ← leverageOf]
  rw [hquad] at hform
  by_contra hcontra
  push Not at hcontra
  nlinarith [hform, hpositive, mul_le_mul_of_nonneg_left hcontra hpositive.le]

/-- **THE CHART DUAL OF A DOUBLY HEAVY UNIFORM DESIGN IS ALL-HEAVY.**  `l'_c = 6 − l_c`
and the co-singleton field is `l_c < 5`. -/
theorem allHeavy_chartDual_of_uniformWeight_sixThree
    {design dual : WeightedDesign 6 3} (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex, design.weight atomIndex = (6 : ℝ)⁻¹)
    (hheavy : AllHeavy design) (hco : HasStrictlyDominatingCoSingletons design) :
    AllHeavy dual := by
  intro atomIndex
  have hprimal := hheavy atomIndex
  have hceiling := leverageOf_lt_of_hasStrictlyDominatingCoSingletons_of_uniformWeight
    design huniform hco atomIndex (by linarith)
  rw [leverageOf_chartDual hdual, huniform]
  norm_num at hceiling ⊢
  linarith

/-- **THE SINGLE OBJECT THE `D4` BAND ASKED FOR.**  At a uniform-weight crux with no
vanishing pairing there is ONE partner design that is simultaneously the anti-parity
partner and the Naimark dual: same weights, all-heavy, no dominating triple, and every
triple parity reversed.

`Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates` shows no such object
exists in general; this is the slice where it does. -/
theorem SixThreeCrux.exists_selfDual_partner_of_uniformWeight (crux : SixThreeCrux)
    (huniform : ∀ atomIndex, crux.design.weight atomIndex = (6 : ℝ)⁻¹)
    (hnonzero : ∀ atomFirst atomSecond : Fin 6, atomFirst ≠ atomSecond →
      atomPairing crux.design atomFirst atomSecond ≠ 0) :
    ∃ partner : WeightedDesign 6 3,
      partner.weight = crux.design.weight
      ∧ AllHeavy partner
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates partner selected)
      ∧ (∀ first second third : Fin 6, first ≠ second → first ≠ third → second ≠ third →
          tripleParity partner first second third
            = -tripleParity crux.design first second third) := by
  obtain ⟨partner, hpartner⟩ := exists_isChartDual_sixThree crux.design
  refine ⟨partner, hpartner.weight_eq,
    allHeavy_chartDual_of_uniformWeight_sixThree hpartner huniform crux.isAllHeavy
      crux.hasStrictlyDominatingCoSingletons, ?_, ?_⟩
  · intro selected hcard hdominates
    have hcardCompl : (selectedᶜ : Finset (Fin 6)).card = 3 := by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
    refine crux.hasNoDominatingTriple selectedᶜ hcardCompl ?_
    refine (dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree hpartner huniform
      selectedᶜ hcardCompl).mpr ?_
    rwa [compl_compl]
  · intro first second third hfs hft hst
    exact tripleParity_chartDual hpartner hfs hft hst (hnonzero first second hfs)
      (hnonzero first third hft) (hnonzero second third hst)

/-! ## 4.  The complement involution on the sector table acts trivially -/

/-- **THE COMPLEMENT INVOLUTION FIXES THE SECTOR TABLE, PATTERN BY PATTERN.**  Two-graph
complementation flips every one of the twenty parities, which on the ten-bit link word
of `Gtz.linkWordOf` is `link ↦ 1023 − link`, and `Gtz.sectorSurvives` is invariant.

The consequence is the exact answer to "does a parity argument bite at the sign layer".
`Gtz/Quantitative/TwoGraphCollision.lean` declines to apply the complement filter because
it is unlicensed; this says that even LICENSED it removes nothing, because the filter is
implied by the table it would filter.  The three levers are already complement-symmetric
by construction: `Gtz.hasNoCoherentQuadruple` is `Gtz.hasNoIncoherentQuadruple` with the
parities reversed, and `Gtz.hasNoSaturatedMatching` tests each matching on both signs. -/
theorem sectorSurvives_compl_eq :
    ∀ link ∈ Finset.range 1024, sectorSurvives (1023 - link) = sectorSurvives link := by
  decide +kernel

/-- The residual sector set is closed under complementation. -/
theorem compl_mem_residualSectors {link : ℕ} (hmem : link ∈ residualSectors) :
    1023 - link ∈ residualSectors := by
  rw [mem_residualSectors_iff] at hmem ⊢
  refine ⟨by omega, ?_⟩
  rw [sectorSurvives_compl_eq link (Finset.mem_range.mpr hmem.1)]
  exact hmem.2

/-- The complement filter removes NOTHING: the residual set and its image under
complementation have the same cardinality, so no parity argument at the sign layer can
cut a single pattern. -/
theorem card_image_compl_residualSectors :
    (residualSectors.image fun link => 1023 - link).card = residualSectors.card := by
  decide +kernel

/-- **RUNNING A DOMINATION LEVER ON THE DUAL IS AN EXCLUSION ON THE PRIMAL.**  At a
uniform weight, a PARALLEL PAIR IN THE CHART DUAL already forces the design itself to
dominate: the pair merges the dual onto `(5,3)`, which is corank two, and the flip
carries the resulting dominating triple back across the complement.

This is the shape of every "must survive the involution" argument at this cell, and it
is worth stating once because it also settles the transport of the crux field
`hasNoParallelPair`: at a uniform-weight crux the dual CANNOT have a parallel pair, not
for a geometric reason but because the crux has no dominating triple. -/
theorem exists_dominates_of_hasParallelPair_chartDual_of_uniformWeight_sixThree
    {design dual : WeightedDesign 6 3} (hdual : IsChartDual design dual)
    (huniform : ∀ atomIndex, design.weight atomIndex = (6 : ℝ)⁻¹)
    (hparallel : HasParallelPair dual) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hpair⟩ := hparallel
  obtain ⟨dualPick, hdualCard, hdualDominates⟩ :=
    dominating_of_parallel_pair (m := 5) dual
      (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hdistinct hpair
  have hcompCard : (dualPickᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hdualCard]
  refine ⟨dualPickᶜ, hcompCard, ?_⟩
  refine (dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree hdual huniform
    dualPickᶜ hcompCard).mpr ?_
  rwa [compl_compl]

/-- **THE CRUX FIELD `hasNoParallelPair` TRANSPORTS, AND FOR THE OTHER REASON.**  At a
uniform-weight crux the chart dual is parallel-free — forced by
`hasNoDominatingTriple`, not by any geometric statement about the dual's atoms.  The
geometry does NOT transport: `Gtz.atomShare_add_atomShare_eq_one_of_pairGramMinor_eq_zero`
shows a dependent pair survives duality only on the `s_c + s_d = 1` locus. -/
theorem SixThreeCrux.hasNoParallelPair_chartDual_of_uniformWeight (crux : SixThreeCrux)
    {dual : WeightedDesign 6 3} (hdual : IsChartDual crux.design dual)
    (huniform : ∀ atomIndex, crux.design.weight atomIndex = (6 : ℝ)⁻¹) :
    ¬ HasParallelPair dual := by
  intro hparallel
  obtain ⟨selected, hcard, hdominates⟩ :=
    exists_dominates_of_hasParallelPair_chartDual_of_uniformWeight_sixThree hdual huniform
      hparallel
  exact crux.hasNoDominatingTriple selected hcard hdominates

/-! ### The `D4` band, as a filter on the sector table -/

/-- The ledger's D4 band at one base: at least two COHERENT and at least two
INCOHERENT triples through it. -/
def twoSidedBandAtBase (link : ℕ) (base first second third fourth fifth : Fin 6) : Bool :=
  let pairs : List (Fin 6 × Fin 6) :=
    [(first, second), (first, third), (first, fourth), (first, fifth),
     (second, third), (second, fourth), (second, fifth),
     (third, fourth), (third, fifth), (fourth, fifth)]
  Nat.ble 2 (pairs.filter fun pair => sectorIncoherent link base pair.1 pair.2).length
    && Nat.ble 2 (pairs.filter fun pair => !(sectorIncoherent link base pair.1 pair.2)).length

/-- **THE `D4` BAND.**  Every atom carries at least two coherent and at least two
incoherent triples.  The coherent half is `Gtz.two_le_card_coherentPairsThroughBase_sixThree`
and the incoherent half is the same statement read on the anti-parity partner. -/
def twoSidedBand (link : ℕ) : Bool :=
  twoSidedBandAtBase link 0 1 2 3 4 5
    && twoSidedBandAtBase link 1 0 2 3 4 5
    && twoSidedBandAtBase link 2 0 1 3 4 5
    && twoSidedBandAtBase link 3 0 1 2 4 5
    && twoSidedBandAtBase link 4 0 1 2 3 5
    && twoSidedBandAtBase link 5 0 1 2 3 4

/-- The band alone leaves 992 of the 1024 patterns. -/
theorem sectorCount_twoSidedBand : sectorCount twoSidedBand = 992 := by decide +kernel

/-- **THE `D4` BAND REMOVES NOTHING.**  Intersecting it with the residual table leaves
`Gtz.card_residualSectors` untouched: all 32 patterns the band excludes were already
excluded by the three levers.

So the band is void TWICE OVER.  Off the uniform-weight slice it is unlicensed, by
`Gtz.exists_naimarkDual_dominates_and_chartDual_not_dominates`; on the slice it is
licensed by `dominates_iff_dominates_chartDual_compl_of_uniformWeight_sixThree` and it
cuts zero patterns.  Together with `sectorSurvives_compl_eq` this closes the sign-layer
parity route completely. -/
theorem sectorCount_twoSidedBand_and_sectorSurvives :
    sectorCount (fun link => twoSidedBand link && sectorSurvives link) = 842 := by
  decide +kernel

/-! ## 5.  The self-dual cell is the Veronese top at every rank -/

/-- **`Gtz.selfDual_eq_top_iff`, WITHOUT THE `decide` BOUND.**  The shipped statement is
`∀ rank ≤ 40`; the bound is an artefact of the proof method.  `2k = k(k+1)/2` with
`k > 0` gives `4k = k(k+1)`, hence `k = 3`. -/
theorem selfDual_eq_top_iff_of_pos (rank : ℕ) (hrank : 1 ≤ rank) :
    2 * rank = rank * (rank + 1) / 2 ↔ rank = 3 := by
  constructor
  · intro hequal
    have hdvd : 2 ∣ rank * (rank + 1) := (Nat.even_mul_succ_self rank).two_dvd
    have hcancel : rank * (rank + 1) / 2 * 2 = rank * (rank + 1) := Nat.div_mul_cancel hdvd
    have hfour : rank * (rank + 1) = rank * 4 := by omega
    have hcancelLeft : rank + 1 = 4 := Nat.eq_of_mul_eq_mul_left (by omega) hfour
    omega
  · rintro rfl
    norm_num

/-- The rank-three coincidence, restated so that the two cells are visibly equal only
there: at every other positive rank the self-dual family `(2k, k)` and the Veronese top
`(N_k, k)` are different cells. -/
theorem selfDual_ne_top_of_ne_three (rank : ℕ) (hrank : 1 ≤ rank) (hne : rank ≠ 3) :
    2 * rank ≠ rank * (rank + 1) / 2 :=
  fun hcontra => hne ((selfDual_eq_top_iff_of_pos rank hrank).mp hcontra)

end Gtz
