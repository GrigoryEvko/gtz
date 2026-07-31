/-
# The concentrated tilt, and the circularity of the tilt family

`Gtz.EcpStar m k` asks, at every design of the cell, for a POSITIVE TILT whose
tilted mixture `Gtz.tiltedMixture` has no root strictly below one.  The shipped
`Gtz/Quantitative/ExpectedCharPolynomial.lean` records the question as open and
supplies one mechanized fragment, that the UNIFORM tilt fails at `(6,3)`.  This
file settles what a non-uniform tilt buys, and the answer is: nothing that was
not already there.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `exists_tilt_no_root_below_one_of_posDefGap` — a design carrying a STRICTLY
  dominating `rank`-subset admits a witness tilt.  The tilt is explicit: put a
  large scale on the strict dominator and one elsewhere.  Two regimes drive it.
  At or below zero every subset's `det(x·I − S_C)` is nonpositive at odd rank
  while a positively weighted one is strictly negative, so the mixture is
  negative for ANY positive tilt.  On `[0,1)` the dominator's term carries
  `scale ^ rank` while every other subset carries at most `scale ^ (rank − 1)`,
  two distinct subsets of equal size overlapping in fewer than that many
  elements, so a large enough scale outweighs a compact-interval bound on the
  rest.
* `ecpStar_of_forall_exists_posDefGap` — THE CIRCULARITY.  Strict GTZ at every
  design of a cell implies `EcpStar` at that cell.  The tilt family is a
  CONSEQUENCE of the conjecture it was introduced to attack, so proposing it as
  an attack route is refuted by this declaration.
* `exists_tilt_no_root_below_one_rootKillDesign` and
  `exists_tilt_no_root_below_one_axisKillDesign` — the two named designs at which
  the campaign refutes `Gtz.HasMixedRootAtLeastOne` do satisfy `EcpStar`'s
  witness shape, at `(6,3)` and at the target cell `(7,3)` respectively.  Both
  witnesses are manufactured from a triple that already dominated.
* `tiltedMixture_eval_neg_of_nonpos` — at odd rank every positive tilt is
  strictly negative on `(−∞, 0]`, for every design and with no hypothesis
  whatever.  So all the content of `EcpStar` lives on `(0, 1)`.
* `tiltedMixture_eval_one_eq_zero_of_totalTieSupported` — at a total tie every
  tilted mixture is pinned to zero at level one, so no tilt buys slack there.

## NOT proved here

Nothing about `EcpStar` at the tie locus, where no strict dominator exists by
definition.  The circularity theorem says precisely that the instrument is
silent exactly where the problem is.  `Gtz/Quantitative/TiltLevelOneSignLaw.lean`
carries the complementary sign law and the dichotomy that decides the lane.

Provenance: scratch report 06 (`mss-endpoint`).  The scratch file additionally
restated the shipped `Gtz.scalar_eq_smul_one`
(`Gtz/Reduction/ExchangeInvariant.lean`) and packaged an `And` of two shipped
theorems as `sqRankBound_saturated_on_allHeavy`; both are dropped.  The
observation the latter recorded is worth keeping in prose: the free Jensen leg
`Gtz.sq_rank_le_expectedElementary_one` is already TIGHT at the regular
tetrahedron (`Gtz.expectedElementary_one_tetraDesign`), which is all-heavy
(`Gtz.tetraDesign_allHeavy`), so all-heaviness cannot improve that leg by any
positive amount.
-/
import Mathlib
import Gtz.Quantitative.ExpectedCharPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Evaluation, and the sign of a single subset's contribution -/

/-- **The tilted mixture, evaluated**, in the shape `Gtz.mixedCharPoly_eval` uses. -/
theorem tiltedMixture_eval (D : WeightedDesign m k) (tilt : Fin m → ℝ) (level : ℝ) :
    (tiltedMixture D tilt).eval level
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, tilt atomIndex) * shadowDeterminant D selected
            * (subsetSum D selected).charpoly.eval level := by
  rw [tiltedMixture, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun selected _ => ?_
  rw [Polynomial.eval_smul, smul_eq_mul]

/-- **Below zero every subset contributes with the sign of the rank.**  At odd rank
`det(x·I − S_C) = −det(S_C + (−x)·I) ≤ 0`, because a positive-semidefinite matrix plus
a nonnegative multiple of the identity is positive semidefinite.  No design data beyond
positive-semidefiniteness of the atom sum is used. -/
theorem charpolyEval_nonpos_of_nonpos (D : WeightedDesign m k) (hodd : Odd k)
    (selected : Finset (Fin m)) {level : ℝ} (hlevel : level ≤ 0) :
    (subsetSum D selected).charpoly.eval level ≤ 0 := by
  rw [Matrix.eval_charpoly]
  have hshape : Matrix.scalar (Fin k) level - subsetSum D selected
      = -(subsetSum D selected + (-level) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [scalar_eq_smul_one]; module
  have hposSemidef : (subsetSum D selected
      + (-level) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    (posSemidef_subsetSum D selected).add (Matrix.PosSemidef.one.smul (by linarith))
  rw [hshape, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, neg_one_mul, neg_nonpos]
  exact hposSemidef.det_nonneg

/-- **A strict dominator contributes strictly negatively at every level at most one.**
`S_C − x·I = (S_C − I) + (1 − x)·I` is positive definite for `x ≤ 1`, so its determinant
is strictly positive and the odd-rank sign flip makes `det(x·I − S_C)` strictly
negative.  This is the uniform-in-`x` strengthening of
`Gtz.det_scalarOne_sub_subsetSum_neg_of_posDef`, which is stated only at `x = 1`. -/
theorem charpolyEval_neg_of_posDefGap (D : WeightedDesign m k) (hodd : Odd k)
    {selected : Finset (Fin m)} (hstrict : (subsetSum D selected - 1).PosDef)
    {level : ℝ} (hlevel : level ≤ 1) :
    (subsetSum D selected).charpoly.eval level < 0 := by
  rw [Matrix.eval_charpoly]
  have hshape : Matrix.scalar (Fin k) level - subsetSum D selected
      = -((subsetSum D selected - 1) + (1 - level) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [scalar_eq_smul_one]; module
  have hposDef : ((subsetSum D selected - 1)
      + (1 - level) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef :=
    hstrict.add_posSemidef (Matrix.PosSemidef.one.smul (by linarith))
  rw [hshape, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, neg_one_mul]
  linarith [hposDef.det_pos]

/-! ## Volume-sampling mass, and what it forces -/

/-- **A strict dominator carries strictly positive volume-sampling mass.**  Its atom sum
is positive definite, so both factors of
`Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum` are strictly positive. -/
theorem shadowDeterminant_pos_of_posDefGap (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hstrict : (subsetSum D selected - 1).PosDef) :
    0 < shadowDeterminant D selected := by
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum D hcard]
  refine mul_pos (Finset.prod_pos fun atomIndex _ => D.weight_pos atomIndex) ?_
  have hposDef : (subsetSum D selected).PosDef := by
    have hsplit : subsetSum D selected = (subsetSum D selected - 1) + 1 := by abel
    rw [hsplit]
    exact hstrict.add_posSemidef Matrix.PosSemidef.one
  exact hposDef.det_pos

/-- Positive volume-sampling mass forces a nonsingular atom sum. -/
theorem detSubsetSum_pos_of_shadowDeterminant_pos (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hmass : 0 < shadowDeterminant D selected) : 0 < (subsetSum D selected).det := by
  have hweights : (0 : ℝ) < ∏ atomIndex ∈ selected, D.weight atomIndex :=
    Finset.prod_pos fun atomIndex _ => D.weight_pos atomIndex
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum D hcard] at hmass
  by_contra hnonpos
  push Not at hnonpos
  nlinarith

/-- Positive volume-sampling mass upgrades the atom sum from positive semidefinite
to positive DEFINITE, since a positive-semidefinite matrix with nonzero determinant
has no null direction. -/
theorem posDef_subsetSum_of_shadowDeterminant_pos (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hmass : 0 < shadowDeterminant D selected) : (subsetSum D selected).PosDef :=
  (posSemidef_subsetSum D selected).posDef_iff_det_ne_zero.mpr
    (ne_of_gt (detSubsetSum_pos_of_shadowDeterminant_pos D hcard hmass))

/-- Some `rank`-subset always carries strictly positive volume-sampling mass, because
the masses are nonnegative and sum to one. -/
theorem exists_shadowDeterminant_pos (D : WeightedDesign m k) :
    ∃ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      0 < shadowDeterminant D selected := by
  by_contra hnone
  push Not at hnone
  have hzero : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      shadowDeterminant D selected = 0 :=
    Finset.sum_eq_zero fun selected hmem =>
      le_antisymm (hnone selected hmem)
        (shadowDeterminant_nonneg D (Finset.mem_powersetCard.mp hmem).2)
  rw [sum_shadowDeterminant_eq_one D] at hzero
  exact one_ne_zero hzero

/-! ## The concentrated tilt -/

/-- The tilt that puts `scale` on one distinguished subset and one everywhere else. -/
noncomputable def concentratedTilt (best : Finset (Fin m)) (scale : ℝ) : Fin m → ℝ :=
  fun atomIndex => if atomIndex ∈ best then scale else 1

theorem concentratedTilt_pos {best : Finset (Fin m)} {scale : ℝ} (hscale : 0 < scale)
    (atomIndex : Fin m) : 0 < concentratedTilt best scale atomIndex := by
  rw [concentratedTilt]
  by_cases hmem : atomIndex ∈ best
  · rw [if_pos hmem]; exact hscale
  · rw [if_neg hmem]; norm_num

/-- The tilt product over a subset is `scale` to the size of its overlap. -/
theorem prod_concentratedTilt (best selected : Finset (Fin m)) (scale : ℝ) :
    (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
      = scale ^ (selected ∩ best).card := by
  simp only [concentratedTilt]
  rw [Finset.prod_ite_mem selected best (fun _ => scale), Finset.prod_const]

theorem prod_concentratedTilt_self (best : Finset (Fin m)) (scale : ℝ) :
    (∏ atomIndex ∈ best, concentratedTilt best scale atomIndex) = scale ^ best.card := by
  rw [prod_concentratedTilt, Finset.inter_self]

/-- **Two distinct subsets of the same size overlap in fewer than that many elements.** -/
theorem card_inter_lt_of_ne {best selected : Finset (Fin m)}
    (hbest : best.card = k) (hselected : selected.card = k) (hne : selected ≠ best) :
    (selected ∩ best).card < k := by
  by_contra hnotLess
  push Not at hnotLess
  have hoverlapEqBest : selected ∩ best = best :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hbest]; exact hnotLess)
  have hbestSubset : best ⊆ selected := by
    rw [← hoverlapEqBest]; exact Finset.inter_subset_left
  exact hne (Finset.eq_of_subset_of_card_le hbestSubset (by rw [hselected, hbest])).symm

/-! ## The competing mass, bounded on the unit interval by compactness -/

/-- The total absolute contribution of every `rank`-subset OTHER than the distinguished
one, weighted by volume-sampling mass alone.  Bounding this on `[0,1]` is all the
control the concentrated tilt needs: the tilt itself is factored out. -/
noncomputable def competingMass (D : WeightedDesign m k) (best : Finset (Fin m))
    (level : ℝ) : ℝ :=
  ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase best,
    shadowDeterminant D selected * |(subsetSum D selected).charpoly.eval level|

theorem continuous_competingMass (D : WeightedDesign m k) (best : Finset (Fin m)) :
    Continuous (competingMass D best) := by
  unfold competingMass
  exact continuous_finsetSum _ fun selected _ =>
    continuous_const.mul ((subsetSum D selected).charpoly.continuous.abs)

theorem competingMass_nonneg (D : WeightedDesign m k) (best : Finset (Fin m)) (level : ℝ) :
    0 ≤ competingMass D best level := by
  refine Finset.sum_nonneg fun selected hselected => ?_
  exact mul_nonneg
    (shadowDeterminant_nonneg D
      (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2)
    (abs_nonneg _)

/-! ## The concentrated tilt kills every root below one, once a STRICT dominator exists -/

/-- **THE CONCENTRATION WITNESS.**  If a design has a STRICTLY dominating
`rank`-subset then a positive tilt exists whose tilted mixture has no root strictly
below one — so that design satisfies the `Gtz.EcpStar` condition.  The tilt is
explicit: put a large constant on the strict dominator and one elsewhere.

Mechanism, in two regimes.  Below zero every subset's `det(x·I − S_C)` is nonpositive
at odd rank (`charpolyEval_nonpos_of_nonpos`) while the dominator's is strictly
negative, so the mixture is negative for ANY positive tilt.  On `[0,1)` the dominator's
contribution carries `scale ^ rank` while every other subset carries at most
`scale ^ (rank − 1)` — two distinct subsets of the same size overlap in fewer than
that many elements (`card_inter_lt_of_ne`) — so a large enough scale makes the
dominator outweigh the compact-interval bound on all the rest.

Read the consequence exactly: the tilt must be BUILT FROM a subset already known to
dominate strictly.  The tilt family therefore reproduces GTZ wherever GTZ is easy and
supplies nothing where it is hard, namely on the tie locus, where no strict dominator
exists at all (`Gtz.IsTie`). -/
theorem exists_tilt_no_root_below_one_of_posDefGap
    (D : WeightedDesign m k) (hodd : Odd k)
    {best : Finset (Fin m)} (hcard : best.card = k)
    (hstrict : (subsetSum D best - 1).PosDef) :
    ∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
      ∀ level : ℝ, level < 1 → (tiltedMixture D tilt).eval level ≠ 0 := by
  classical
  have hrankPos : 0 < k := by
    obtain ⟨half, hhalf⟩ := hodd
    omega
  have hrankPred : k - 1 + 1 = k := by omega
  have hmass : 0 < shadowDeterminant D best := shadowDeterminant_pos_of_posDefGap D hcard hstrict
  have hbestMem : best ∈ (Finset.univ : Finset (Fin m)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  -- the compact bound on everything except the dominator
  obtain ⟨argCompeting, hargCompetingMem, hargCompetingMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
      (continuous_competingMass D best).continuousOn
  rw [isMaxOn_iff] at hargCompetingMax
  set bound := competingMass D best argCompeting with hboundDef
  have hboundNonneg : 0 ≤ bound := competingMass_nonneg D best argCompeting
  -- the compact bound on the dominator, strictly negative
  obtain ⟨argDominator, hargDominatorMem, hargDominatorMax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one)
      ((subsetSum D best).charpoly.continuous.continuousOn
        (s := Set.Icc (0 : ℝ) 1))
  rw [isMaxOn_iff] at hargDominatorMax
  set gap := -((subsetSum D best).charpoly.eval argDominator) with hgapDef
  have hgapPos : 0 < gap := by
    have hneg := charpolyEval_neg_of_posDefGap D hodd hstrict hargDominatorMem.2
    rw [hgapDef]; linarith
  -- the scale
  set scale := max 1 (bound / (shadowDeterminant D best * gap) + 1) with hscaleDef
  have hscaleOne : (1 : ℝ) ≤ scale := le_max_left _ _
  have hscalePos : (0 : ℝ) < scale := lt_of_lt_of_le one_pos hscaleOne
  have hscaleBig : bound < scale * (shadowDeterminant D best * gap) := by
    have hstep : bound / (shadowDeterminant D best * gap) < scale :=
      lt_of_lt_of_le (by linarith) (le_max_right _ _)
    exact (div_lt_iff₀ (mul_pos hmass hgapPos)).mp hstep
  refine ⟨concentratedTilt best scale, concentratedTilt_pos hscalePos, ?_⟩
  intro level hlevel
  -- the dominator's own term
  have hdominatorTerm :
      (∏ atomIndex ∈ best, concentratedTilt best scale atomIndex) * shadowDeterminant D best
          * (subsetSum D best).charpoly.eval level
        = scale ^ k * shadowDeterminant D best
          * (subsetSum D best).charpoly.eval level := by
    rw [prod_concentratedTilt_self, hcard]
  have hscalePowPos : (0 : ℝ) < scale ^ k := pow_pos hscalePos k
  have hscalePredPos : (0 : ℝ) < scale ^ (k - 1) := pow_pos hscalePos (k - 1)
  refine ne_of_lt ?_
  rw [tiltedMixture_eval, ← Finset.add_sum_erase _ _ hbestMem, hdominatorTerm]
  rcases le_or_gt level 0 with hlow | hhigh
  · -- below zero: every term is nonpositive and the dominator's is strictly negative
    have hdominatorNeg : scale ^ k * shadowDeterminant D best
        * (subsetSum D best).charpoly.eval level < 0 := by
      have hneg := charpolyEval_neg_of_posDefGap D hodd hstrict (le_trans hlow zero_le_one)
      have hfactor : 0 < scale ^ k * shadowDeterminant D best := mul_pos hscalePowPos hmass
      nlinarith
    have hrestNonpos : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase best,
        (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
          * shadowDeterminant D selected
          * (subsetSum D selected).charpoly.eval level ≤ 0 := by
      refine Finset.sum_nonpos fun selected hselected => ?_
      have hselectedCard : selected.card = k :=
        (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2
      have hprodNonneg : 0 ≤ ∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex :=
        Finset.prod_nonneg fun atomIndex _ => (concentratedTilt_pos hscalePos atomIndex).le
      have hshadowNonneg : 0 ≤ shadowDeterminant D selected :=
        shadowDeterminant_nonneg D hselectedCard
      have hevalNonpos := charpolyEval_nonpos_of_nonpos D hodd selected hlow
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hprodNonneg hshadowNonneg) hevalNonpos
    linarith
  · -- inside the unit interval: the scale gap decides
    have hlevelMem : level ∈ Set.Icc (0 : ℝ) 1 := ⟨hhigh.le, hlevel.le⟩
    have hdominatorBound : scale ^ k * shadowDeterminant D best
        * (subsetSum D best).charpoly.eval level
          ≤ -(scale ^ (k - 1) * scale * shadowDeterminant D best * gap) := by
      have hevalLe := hargDominatorMax level hlevelMem
      have hfactor : 0 < scale ^ k * shadowDeterminant D best := mul_pos hscalePowPos hmass
      have hpow : scale ^ k = scale ^ (k - 1) * scale := by
        rw [← pow_succ, hrankPred]
      have hvalueLe : (subsetSum D best).charpoly.eval level ≤ -gap := by
        rw [hgapDef]; linarith
      refine le_trans (mul_le_mul_of_nonneg_left hvalueLe hfactor.le) (le_of_eq ?_)
      rw [hpow]; ring
    have hrestBound : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase best,
        (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
          * shadowDeterminant D selected
          * (subsetSum D selected).charpoly.eval level
        ≤ scale ^ (k - 1) * bound := by
      refine le_trans (Finset.sum_le_sum (fun selected hselected => ?_))
        (le_trans (le_of_eq (Finset.mul_sum _ _ _).symm)
          (mul_le_mul_of_nonneg_left (hargCompetingMax level hlevelMem) hscalePredPos.le))
      have hselectedCard : selected.card = k :=
        (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2
      have hne : selected ≠ best := Finset.ne_of_mem_erase hselected
      have hoverlap : (selected ∩ best).card ≤ k - 1 := by
        have := card_inter_lt_of_ne hcard hselectedCard hne
        omega
      have hprodLe : (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
          ≤ scale ^ (k - 1) := by
        rw [prod_concentratedTilt]
        exact pow_le_pow_right₀ hscaleOne hoverlap
      have hprodNonneg : 0 ≤ ∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex :=
        Finset.prod_nonneg fun atomIndex _ => (concentratedTilt_pos hscalePos atomIndex).le
      have hshadowNonneg : 0 ≤ shadowDeterminant D selected :=
        shadowDeterminant_nonneg D hselectedCard
      have habs : (subsetSum D selected).charpoly.eval level
          ≤ |(subsetSum D selected).charpoly.eval level| := le_abs_self _
      have habsNonneg : 0 ≤ |(subsetSum D selected).charpoly.eval level| := abs_nonneg _
      have hraiseValue : (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
            * shadowDeterminant D selected * (subsetSum D selected).charpoly.eval level
          ≤ (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
            * shadowDeterminant D selected * |(subsetSum D selected).charpoly.eval level| :=
        mul_le_mul_of_nonneg_left habs (mul_nonneg hprodNonneg hshadowNonneg)
      have hraiseTilt : (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
            * (shadowDeterminant D selected * |(subsetSum D selected).charpoly.eval level|)
          ≤ scale ^ (k - 1)
            * (shadowDeterminant D selected * |(subsetSum D selected).charpoly.eval level|) :=
        mul_le_mul_of_nonneg_right hprodLe (mul_nonneg hshadowNonneg habsNonneg)
      have hassoc : (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
            * shadowDeterminant D selected * |(subsetSum D selected).charpoly.eval level|
          = (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
            * (shadowDeterminant D selected
              * |(subsetSum D selected).charpoly.eval level|) := by ring
      linarith
    have hfinal : scale ^ (k - 1) * bound
        < scale ^ (k - 1) * scale * shadowDeterminant D best * gap := by
      nlinarith [hscalePredPos, hscaleBig]
    linarith

/-! ## Where the tilt can and cannot have any content -/

/-- **AT AND BELOW ZERO THE TILT IS POWERLESS, AND SO IS THE DESIGN.**  At odd rank
every positive tilt makes the tilted mixture strictly negative on `(−∞, 0]`, for every
design whatsoever.  A subset carrying positive volume-sampling mass has a positive
DEFINITE atom sum (`posDef_subsetSum_of_shadowDeterminant_pos`), so adding the
nonnegative multiple `(−x)·I` keeps it positive definite and the odd-rank sign flip
makes its contribution strictly negative; every other contribution is nonpositive and
no cancellation is available.  Consequently all the content of `Gtz.EcpStar` — and of
`Gtz.HasMixedRootAtLeastOne` — lives on `(0, 1)`. -/
theorem tiltedMixture_eval_neg_of_nonpos (D : WeightedDesign m k) (hodd : Odd k)
    {tilt : Fin m → ℝ} (htilt : ∀ atomIndex, 0 < tilt atomIndex)
    {level : ℝ} (hlevel : level ≤ 0) :
    (tiltedMixture D tilt).eval level < 0 := by
  obtain ⟨witness, hwitnessMem, hwitnessMass⟩ := exists_shadowDeterminant_pos D
  have hwitnessCard : witness.card = k := (Finset.mem_powersetCard.mp hwitnessMem).2
  have hwitnessNeg : (∏ atomIndex ∈ witness, tilt atomIndex) * shadowDeterminant D witness
      * (subsetSum D witness).charpoly.eval level < 0 := by
    have hposDef : (subsetSum D witness
        + (-level) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef :=
      (posDef_subsetSum_of_shadowDeterminant_pos D hwitnessCard hwitnessMass).add_posSemidef
        (Matrix.PosSemidef.one.smul (by linarith))
    have hshape : Matrix.scalar (Fin k) level - subsetSum D witness
        = -(subsetSum D witness + (-level) • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
      rw [scalar_eq_smul_one]; module
    have hvalueNeg : (subsetSum D witness).charpoly.eval level < 0 := by
      rw [Matrix.eval_charpoly, hshape, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow,
        neg_one_mul]
      linarith [hposDef.det_pos]
    have hweightPos : 0 < (∏ atomIndex ∈ witness, tilt atomIndex)
        * shadowDeterminant D witness :=
      mul_pos (Finset.prod_pos fun atomIndex _ => htilt atomIndex) hwitnessMass
    exact mul_neg_of_pos_of_neg hweightPos hvalueNeg
  rw [tiltedMixture_eval, ← Finset.add_sum_erase _ _ hwitnessMem]
  have hrest : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase witness,
      (∏ atomIndex ∈ selected, tilt atomIndex) * shadowDeterminant D selected
        * (subsetSum D selected).charpoly.eval level ≤ 0 :=
    Finset.sum_nonpos fun selected hselected =>
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Finset.prod_nonneg fun atomIndex _ => (htilt atomIndex).le)
          (shadowDeterminant_nonneg D
            (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2))
        (charpolyEval_nonpos_of_nonpos D hodd selected hlevel)
  linarith

/-- The strictly-below-zero reading of `tiltedMixture_eval_neg_of_nonpos`. -/
theorem tiltedMixture_eval_neg_of_neg (D : WeightedDesign m k) (hodd : Odd k)
    {tilt : Fin m → ℝ} (htilt : ∀ atomIndex, 0 < tilt atomIndex)
    {level : ℝ} (hlevel : level < 0) :
    (tiltedMixture D tilt).eval level < 0 :=
  tiltedMixture_eval_neg_of_nonpos D hodd htilt hlevel.le

/-- **AT LEVEL ZERO EVERY POSITIVE TILT IS STRICTLY NEGATIVE.**  The endpoint reading
of `tiltedMixture_eval_neg_of_nonpos`, and the one that makes the intermediate value
theorem bite at level one. -/
theorem tiltedMixture_eval_zero_neg (D : WeightedDesign m k) (hodd : Odd k)
    {tilt : Fin m → ℝ} (htilt : ∀ atomIndex, 0 < tilt atomIndex) :
    (tiltedMixture D tilt).eval 0 < 0 :=
  tiltedMixture_eval_neg_of_nonpos D hodd htilt le_rfl

/-- **AT A TOTAL TIE THE WHOLE TILT FAMILY DEGENERATES.**
`Gtz.mixedCharPoly_eval_one_eq_zero_of_totalTieSupported` is measure-independent, so it
survives every tilt: at a total tie EVERY tilted mixture is rooted exactly at one, with
zero margin.  So no tilt buys any slack at the tie locus — the family is pinned to the
boundary there, whatever the tilt. -/
theorem tiltedMixture_eval_one_eq_zero_of_totalTieSupported (D : WeightedDesign m k)
    (htie : IsTotalTieSupported D) (tilt : Fin m → ℝ) :
    (tiltedMixture D tilt).eval 1 = 0 := by
  rw [tiltedMixture_eval]
  refine Finset.sum_eq_zero fun selected hmem => ?_
  rcases htie selected (Finset.mem_powersetCard.mp hmem).2 with hmass | hgap
  · rw [hmass, mul_zero, zero_mul]
  · rw [Matrix.eval_charpoly, hgap, mul_zero]

/-! ## The two refuting witnesses of `Gtz/Reduction/MixedCharPolynomial.lean`, retilted

At both designs the UNIFORM tilt has a root strictly inside `(0,1)` — that is the
campaign's own refutation of `Gtz.HasMixedRootAtLeastOne`.  Both nevertheless carry a
STRICTLY dominating triple, so the concentrated tilt applies and the `Gtz.EcpStar`
condition HOLDS at both.  The tilt therefore does exactly one thing: it reads off a
dominator that was already there. -/

/-- The `(6,3)` witness's triple `{0,2,4}` dominates STRICTLY: the gap is
`(1/2)·I + (3/2)·u uᵀ`, positive definite because of the `(1/2)·I`.  The decomposition
is the one `Gtz.rootKillDesign_hasDominatingSubset` uses; only the conclusion is
strengthened from positive semidefinite to positive definite. -/
theorem posDefGap_rootKillDesign_zeroTwoFour :
    (subsetSum rootKillDesign {0, 2, 4} - 1).PosDef := by
  have hdecomposition : subsetSum rootKillDesign {0, 2, 4} - 1
      = (1 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + (3 / 2 : ℝ) • atomMatrix rootKillWitnessAtom := by
    ext rowCoord colCoord
    by_cases hdiagonal : rowCoord = colCoord
    · subst hdiagonal
      simp only [Matrix.sub_apply, subsetSum_rootKillDesign_apply, rootKillGram_zeroTwoFour,
        Matrix.one_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        atomMatrix, Matrix.vecMulVec_apply, rootKillWitnessAtom]
      push_cast
      ring
    · simp only [Matrix.sub_apply, subsetSum_rootKillDesign_apply, rootKillGram_zeroTwoFour,
        if_neg hdiagonal, Matrix.one_apply_ne hdiagonal, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply, rootKillWitnessAtom]
      push_cast
      ring
  rw [hdecomposition]
  exact (Matrix.PosDef.one.smul (by norm_num)).add_posSemidef
    ((posSemidef_atomMatrix _).smul (by norm_num))

/-- **THE `(6,3)` TILT EXISTS.**  At the `D₃` root system — the design at which
`Gtz.not_uniformTilt_witnesses_ecpStar_sixThree` shows the uniform tilt FAILS — a
positive tilt does witness the `Gtz.EcpStar` condition.  So the `(6,3)` tilt question
is decided affirmatively, and the witness is manufactured from the triple `{0,2,4}`
that already dominated. -/
theorem exists_tilt_no_root_below_one_rootKillDesign :
    ∃ tilt : Fin 6 → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
      ∀ level : ℝ, level < 1 → (tiltedMixture rootKillDesign tilt).eval level ≠ 0 :=
  exists_tilt_no_root_below_one_of_posDefGap rootKillDesign (by decide) (by decide)
    posDefGap_rootKillDesign_zeroTwoFour

/-- The `(7,3)` witness's three doubled axes dominate STRICTLY: the gap is `(5/2)·I`.
Again the decomposition is `Gtz.axisKillDesign_hasDominatingSubset`'s, with the
conclusion strengthened. -/
theorem posDefGap_axisKillDesign_fourFiveSix :
    (subsetSum axisKillDesign {4, 5, 6} - 1).PosDef := by
  have hdecomposition : subsetSum axisKillDesign {4, 5, 6} - 1
      = (5 / 2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext rowCoord colCoord
    by_cases hdiagonal : rowCoord = colCoord
    · subst hdiagonal
      simp only [Matrix.sub_apply, subsetSum_axisKillDesign_apply, axisKillGram_fourFiveSix,
        Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
      norm_num
    · simp only [Matrix.sub_apply, subsetSum_axisKillDesign_apply, axisKillGram_fourFiveSix,
        if_neg hdiagonal, Matrix.one_apply_ne hdiagonal, Matrix.smul_apply, smul_eq_mul]
      norm_num
  rw [hdecomposition]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- **THE `(7,3)` TILT EXISTS — at the target cell.**  `Gtz.axisKillDesign` is the
all-heavy `(7,3)` design that refutes `Gtz.HasMixedRootAtLeastOne 7 3`; a positive tilt
nevertheless witnesses the `Gtz.EcpStar` condition there, built from the strictly
dominating triple `{4,5,6}`. -/
theorem exists_tilt_no_root_below_one_axisKillDesign :
    ∃ tilt : Fin 7 → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
      ∀ level : ℝ, level < 1 → (tiltedMixture axisKillDesign tilt).eval level ≠ 0 :=
  exists_tilt_no_root_below_one_of_posDefGap axisKillDesign (by decide) (by decide)
    posDefGap_axisKillDesign_fourFiveSix

/-! ## The circularity -/

/-- **EVERY-DESIGN-STRICTLY-DOMINATES IMPLIES `EcpStar`.**  If GTZ holds with strict
domination at every design of a cell, then the tilt existential holds at that cell.
Read with `Gtz.EcpStar`'s own scope note — the predicate implies nothing about GTZ on
its own — this is the exact sense in which the tilt family is circular: it is a
CONSEQUENCE of the conjecture it was introduced to attack.  Any campaign lane that
proposes the tilt as an attack route is refuted here. -/
theorem ecpStar_of_forall_exists_posDefGap (hodd : Odd k)
    (hstrictGtz : ∀ D : WeightedDesign m k, ∃ selected : Finset (Fin m),
      selected.card = k ∧ (subsetSum D selected - 1).PosDef) :
    EcpStar m k := by
  intro D
  obtain ⟨selected, hcard, hstrict⟩ := hstrictGtz D
  exact exists_tilt_no_root_below_one_of_posDefGap D hodd hcard hstrict

end Gtz
