/-
# The level-one sign law for the tilted volume-sampling mixture

`Gtz.EcpStar m k` asks, for every design, for a POSITIVE TILT whose tilted mixture
`Gtz.tiltedMixture` has no root strictly below one.
`Gtz/Quantitative/TiltConcentration.lean` shows the condition is a CONSEQUENCE of
strict GTZ, so it can only have content where strict domination fails.  This file
settles what remains, and shows the whole family is decided at the single level
`x = 1` by the SIGNS of the coefficients

    levelOneCoefficient D C  =  shadowDeterminant D C · det(1·I − S_C).

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `exists_tilt_eval_one_neg_iff_exists_levelOneCoefficient_neg` — the tilt buys
  EXACTLY one bit.  A positive tilt making the mixture negative at level one
  exists if and only if some `rank`-subset has a strictly negative level-one
  coefficient.  Forward by reading off a negative summand, backward by
  concentration.
* `exists_levelOneCoefficient_neg_or_isTotalTieSupported` — THE DICHOTOMY.  An
  `EcpStar` witness at a design forces that design into one of two classes: it
  has a negative level-one coefficient, or it is a TOTAL TIE
  (`Gtz.IsTotalTieSupported`), where every coefficient vanishes.  No third
  possibility.
* `not_ecpStar_of_levelOneCoefficient_nonneg` with
  `isTie_of_levelOneCoefficient_nonneg` and
  `not_isTotalTieSupported_of_levelOneCoefficient_pos` — `EcpStar m k` is FALSE
  as soon as some design has all level-one coefficients nonnegative and one
  positive, and such a design is necessarily a NON-TOTAL TIE.  So the fate of
  the tilt lane is the same question as the campaign's open "does a non-total
  tie exist", and cannot be settled without it.
* `exists_posSemidef_levelOneNegative_not_dominating` and
  `levelOneCoefficient_neg_and_not_dominates_decoyDesign` — the gap on the other
  side, abstractly and at an honest rational `(6,3)` design.  A negative
  level-one coefficient does NOT imply domination: at odd rank
  `det(1·I − S_C) < 0` means an EVEN number of eigenvalues of `S_C` lie below
  one, which at rank three is zero (a strict dominator) OR two (a doubly
  deficient subset).  The tilt family's only binding constraint is therefore
  strictly weaker than GTZ, and satisfying it proves nothing.

## NOT proved here

Whether `EcpStar` holds or fails at any cell.  The dichotomy reduces that to the
open non-total-tie question and stops; this file does not settle it, and the
lane is barred rather than advanced.

Provenance: scratch report 01 (`deepen-lit`).  Seven declarations the scratch
file shared verbatim with report 06 are consumed from
`Gtz/Quantitative/TiltConcentration.lean` instead of restated, and the scratch
`tiltedMixture_eval` is renamed `tiltedMixture_eval_det` and derived from the
canonical charpoly form there.
-/
import Mathlib
import Gtz.Quantitative.ExpectedCharPolynomial
import Gtz.Quantitative.TiltConcentration
import Gtz.Certificates.ResidueDissolution
import Gtz.Quantitative.RealnessEngine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Evaluation in determinant form -/

/-- The tilted mixture, evaluated with the characteristic polynomial expanded into
its determinant.  The charpoly form `Gtz.tiltedMixture_eval` is the primitive one;
this is the reading the level-one coefficient is stated in. -/
theorem tiltedMixture_eval_det (D : WeightedDesign m k) (tilt : Fin m → ℝ) (level : ℝ) :
    (tiltedMixture D tilt).eval level
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, tilt atomIndex) * shadowDeterminant D selected
            * (Matrix.scalar (Fin k) level - subsetSum D selected).det := by
  rw [tiltedMixture_eval]
  exact Finset.sum_congr rfl fun selected _ => by rw [Matrix.eval_charpoly]

/-- The odd-rank sign flip at level zero, in determinant form. -/
theorem det_scalarZero_sub_subsetSum (D : WeightedDesign m k) (hodd : Odd k)
    (selected : Finset (Fin m)) :
    (Matrix.scalar (Fin k) (0 : ℝ) - subsetSum D selected).det
      = -(subsetSum D selected).det := by
  have hzero : Matrix.scalar (Fin k) (0 : ℝ) = 0 := map_zero _
  rw [hzero, zero_sub, Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, neg_one_mul]

/-! ## The level-one coefficient -/

/-- The coefficient a `rank`-subset contributes to the tilted mixture AT LEVEL ONE:
its volume-sampling mass times `det(1·I − S_C)`.  Every tilt sees the same
coefficients; the tilt only reweights them multiaffinely. -/
noncomputable def levelOneCoefficient (D : WeightedDesign m k) (selected : Finset (Fin m)) : ℝ :=
  shadowDeterminant D selected * (Matrix.scalar (Fin k) (1 : ℝ) - subsetSum D selected).det

theorem tiltedMixture_eval_one (D : WeightedDesign m k) (tilt : Fin m → ℝ) :
    (tiltedMixture D tilt).eval 1
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (∏ atomIndex ∈ selected, tilt atomIndex) * levelOneCoefficient D selected := by
  rw [tiltedMixture_eval_det]
  exact Finset.sum_congr rfl fun selected _ => by rw [levelOneCoefficient, mul_assoc]

/-- **A TOTAL TIE IS EXACTLY "EVERY LEVEL-ONE COEFFICIENT VANISHES".**  The two
disjuncts of `Gtz.IsTotalTieSupported` are the two factors of the coefficient. -/
theorem isTotalTieSupported_iff_forall_levelOneCoefficient_eq_zero (D : WeightedDesign m k) :
    IsTotalTieSupported D
      ↔ ∀ selected : Finset (Fin m), selected.card = k → levelOneCoefficient D selected = 0 := by
  constructor
  · intro htie selected hcard
    exact mul_eq_zero.mpr (htie selected hcard)
  · intro hzero selected hcard
    exact mul_eq_zero.mp (hzero selected hcard)

/-- A negative level-one coefficient says exactly: positive volume-sampling mass
AND `det(1·I − S_C) < 0`. -/
theorem levelOneCoefficient_neg_iff (D : WeightedDesign m k) {selected : Finset (Fin m)}
    (hcard : selected.card = k) :
    levelOneCoefficient D selected < 0
      ↔ 0 < shadowDeterminant D selected
        ∧ (Matrix.scalar (Fin k) (1 : ℝ) - subsetSum D selected).det < 0 := by
  constructor
  · intro hneg
    rw [levelOneCoefficient] at hneg
    have hmassNonneg := shadowDeterminant_nonneg D hcard
    have hmassPos : 0 < shadowDeterminant D selected := by
      rcases hmassNonneg.lt_or_eq with hpos | hzero
      · exact hpos
      · rw [← hzero, zero_mul] at hneg
        exact absurd hneg (lt_irrefl 0)
    refine ⟨hmassPos, ?_⟩
    by_contra hnonneg
    push Not at hnonneg
    nlinarith
  · rintro ⟨hmass, hdet⟩
    exact mul_neg_of_pos_of_neg hmass hdet

/-- A strictly dominating subset has a strictly NEGATIVE level-one coefficient:
positive mass times `det(1·I − S_C) < 0`.  So the campaign's own strict-domination
hypothesis lands inside the negative-coefficient class — which is the reason
`Gtz.ecpStar_of_forall_exists_posDefGap` goes through. -/
theorem levelOneCoefficient_neg_of_posDef (D : WeightedDesign m k) (hodd : Odd k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hstrict : (subsetSum D selected - 1).PosDef) :
    levelOneCoefficient D selected < 0 := by
  rw [levelOneCoefficient]
  exact mul_neg_of_pos_of_neg (shadowDeterminant_pos_of_posDefGap D hcard hstrict)
    (det_scalarOne_sub_subsetSum_neg_of_posDef D hodd hstrict)

/-! ## The concentrated tilt realises a negative coefficient -/

/-- The total absolute level-one weight of every `rank`-subset other than the
distinguished one.  Unlike `Gtz.competingMass` this needs no continuity: it is a
finite sum of absolute coefficients at the single level one. -/
noncomputable def competingLevelOneMass (D : WeightedDesign m k) (best : Finset (Fin m)) : ℝ :=
  ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase best,
    |levelOneCoefficient D selected|

theorem competingLevelOneMass_nonneg (D : WeightedDesign m k) (best : Finset (Fin m)) :
    0 ≤ competingLevelOneMass D best :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **A NEGATIVE COEFFICIENT IS REALISABLE.**  If some `rank`-subset has a strictly
negative level-one coefficient then a positive tilt makes the tilted mixture
strictly negative at level one: concentrate a large scale on that subset, whose
weight is `scale ^ rank`, while every other `rank`-subset overlaps it in at most
`rank − 1` elements and so carries at most `scale ^ (rank − 1)`. -/
theorem exists_tilt_eval_one_neg_of_levelOneCoefficient_neg (D : WeightedDesign m k)
    (hrank : 0 < k) {best : Finset (Fin m)} (hcard : best.card = k)
    (hneg : levelOneCoefficient D best < 0) :
    ∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex)
      ∧ (tiltedMixture D tilt).eval 1 < 0 := by
  classical
  have hrankPred : k - 1 + 1 = k := by omega
  have hbestMem : best ∈ (Finset.univ : Finset (Fin m)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  set bound := competingLevelOneMass D best with hboundDef
  have hboundNonneg : 0 ≤ bound := competingLevelOneMass_nonneg D best
  set gap := -levelOneCoefficient D best with hgapDef
  have hgapPos : 0 < gap := by rw [hgapDef]; linarith
  set scale := max 1 (bound / gap + 1) with hscaleDef
  have hscaleOne : (1 : ℝ) ≤ scale := le_max_left _ _
  have hscalePos : (0 : ℝ) < scale := lt_of_lt_of_le one_pos hscaleOne
  have hscaleBig : bound < scale * gap := by
    have hstep : bound / gap < scale := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    exact (div_lt_iff₀ hgapPos).mp hstep
  have hscalePredPos : (0 : ℝ) < scale ^ (k - 1) := pow_pos hscalePos (k - 1)
  refine ⟨concentratedTilt best scale, concentratedTilt_pos hscalePos, ?_⟩
  rw [tiltedMixture_eval_one, ← Finset.add_sum_erase _ _ hbestMem, prod_concentratedTilt_self,
    hcard]
  have hbestTerm : scale ^ k * levelOneCoefficient D best
      = -(scale ^ (k - 1) * scale * gap) := by
    rw [hgapDef, ← pow_succ, hrankPred]
    ring
  have hrestBound : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase best,
      (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
        * levelOneCoefficient D selected ≤ scale ^ (k - 1) * bound := by
    rw [hboundDef, competingLevelOneMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun selected hselected => ?_
    have hselectedCard : selected.card = k :=
      (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2
    have hoverlap : (selected ∩ best).card ≤ k - 1 := by
      have := card_inter_lt_of_ne hcard hselectedCard (Finset.ne_of_mem_erase hselected)
      omega
    have hprodLe : (∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex)
        ≤ scale ^ (k - 1) := by
      rw [prod_concentratedTilt]
      exact pow_le_pow_right₀ hscaleOne hoverlap
    have hprodNonneg : 0 ≤ ∏ atomIndex ∈ selected, concentratedTilt best scale atomIndex :=
      Finset.prod_nonneg fun atomIndex _ => (concentratedTilt_pos hscalePos atomIndex).le
    have hvalueLe : levelOneCoefficient D selected ≤ |levelOneCoefficient D selected| :=
      le_abs_self _
    nlinarith [abs_nonneg (levelOneCoefficient D selected)]
  have hfinal : scale ^ (k - 1) * bound < scale ^ (k - 1) * scale * gap := by
    nlinarith [hscalePredPos, hscaleBig]
  rw [hbestTerm]
  linarith

/-! ## The level-one story, complete -/

/-- **THE TILT BUYS EXACTLY ONE BIT AT LEVEL ONE.**  A positive tilt driving the
tilted mixture below zero at level one exists if and only if some `rank`-subset has a
strictly negative level-one coefficient.  Both directions are constructive in
content: forward by reading off a negative summand, backward by concentration. -/
theorem exists_tilt_eval_one_neg_iff_exists_levelOneCoefficient_neg (D : WeightedDesign m k)
    (hrank : 0 < k) :
    (∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex)
        ∧ (tiltedMixture D tilt).eval 1 < 0)
      ↔ ∃ selected : Finset (Fin m), selected.card = k
          ∧ levelOneCoefficient D selected < 0 := by
  constructor
  · rintro ⟨tilt, htilt, hvalue⟩
    rw [tiltedMixture_eval_one] at hvalue
    have htotal : ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        (∏ atomIndex ∈ selected, tilt atomIndex) * levelOneCoefficient D selected
          < ∑ _selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k, (0 : ℝ) := by
      rw [Finset.sum_const_zero]
      exact hvalue
    obtain ⟨selected, hselected, hterm⟩ := Finset.exists_lt_of_sum_lt htotal
    refine ⟨selected, (Finset.mem_powersetCard.mp hselected).2, ?_⟩
    have hprodPos : 0 < ∏ atomIndex ∈ selected, tilt atomIndex :=
      Finset.prod_pos fun atomIndex _ => htilt atomIndex
    nlinarith
  · rintro ⟨selected, hcard, hneg⟩
    exact exists_tilt_eval_one_neg_of_levelOneCoefficient_neg D hrank hcard hneg

/-- **NECESSITY.**  A tilt witnessing `Gtz.EcpStar` at `D` forces the tilted
mixture to be NONPOSITIVE at level one.  Mechanism: at odd rank the mixture is
strictly negative at level zero for every positive tilt
(`Gtz.tiltedMixture_eval_zero_neg`), so a strictly positive value at level one
produces a root strictly inside `(0,1)`. -/
theorem tiltedMixture_eval_one_nonpos_of_witness (D : WeightedDesign m k) (hodd : Odd k)
    {tilt : Fin m → ℝ} (htilt : ∀ atomIndex, 0 < tilt atomIndex)
    (hnoRoot : ∀ level : ℝ, level < 1 → (tiltedMixture D tilt).eval level ≠ 0) :
    (tiltedMixture D tilt).eval 1 ≤ 0 := by
  by_contra hpositive
  push Not at hpositive
  have hbelow := tiltedMixture_eval_zero_neg D hodd htilt
  have hcontinuous : ContinuousOn (fun level : ℝ => (tiltedMixture D tilt).eval level)
      (Set.Icc 0 1) := (tiltedMixture D tilt).continuous_aeval.continuousOn
  have hmember : (0 : ℝ) ∈ Set.Icc ((tiltedMixture D tilt).eval 0)
      ((tiltedMixture D tilt).eval 1) := ⟨hbelow.le, hpositive.le⟩
  obtain ⟨level, hlevelMem, hlevelValue⟩ :=
    intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontinuous hmember
  have hvalue : (tiltedMixture D tilt).eval level = 0 := hlevelValue
  refine hnoRoot level ?_ hvalue
  rcases hlevelMem.2.lt_or_eq with hstrict | hone
  · exact hstrict
  · rw [hone] at hvalue
    rw [hvalue] at hpositive
    exact absurd hpositive (lt_irrefl 0)

/-- **THE OBSTRUCTION.**  If no `rank`-subset has a negative level-one coefficient and
some `rank`-subset has a strictly positive one, then NO positive tilt avoids a root
below one: the tilted mixture is strictly positive at level one for every tilt and
strictly negative at level zero, so every tilt has a root inside `(0,1)`. -/
theorem not_exists_witnessTilt_of_levelOneCoefficient_nonneg (D : WeightedDesign m k)
    (hodd : Odd k)
    (hnonneg : ∀ selected : Finset (Fin m), selected.card = k
      → 0 ≤ levelOneCoefficient D selected)
    {witness : Finset (Fin m)} (hcard : witness.card = k)
    (hwitnessPos : 0 < levelOneCoefficient D witness) :
    ¬ ∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
        ∀ level : ℝ, level < 1 → (tiltedMixture D tilt).eval level ≠ 0 := by
  rintro ⟨tilt, htilt, hnoRoot⟩
  have hnonpos := tiltedMixture_eval_one_nonpos_of_witness D hodd htilt hnoRoot
  have hmember : witness ∈ (Finset.univ : Finset (Fin m)).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hpositive : 0 < (tiltedMixture D tilt).eval 1 := by
    rw [tiltedMixture_eval_one, ← Finset.add_sum_erase _ _ hmember]
    have hwitnessTerm : 0 < (∏ atomIndex ∈ witness, tilt atomIndex)
        * levelOneCoefficient D witness :=
      mul_pos (Finset.prod_pos fun atomIndex _ => htilt atomIndex) hwitnessPos
    have hrest : 0 ≤ ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).erase witness,
        (∏ atomIndex ∈ selected, tilt atomIndex) * levelOneCoefficient D selected :=
      Finset.sum_nonneg fun selected hselected =>
        mul_nonneg (Finset.prod_nonneg fun atomIndex _ => (htilt atomIndex).le)
          (hnonneg selected (Finset.mem_powersetCard.mp (Finset.mem_of_mem_erase hselected)).2)
    linarith
  linarith

/-- **THE DICHOTOMY.**  At odd rank, a design admitting an `Gtz.EcpStar` witness tilt
either has a `rank`-subset with strictly negative level-one coefficient — a
positively weighted subset with `det(1·I − S_C) < 0` — or is a TOTAL TIE, where
every level-one coefficient vanishes and the mixture is pinned to zero at level
one for EVERY tilt.  There is no third possibility. -/
theorem exists_levelOneCoefficient_neg_or_isTotalTieSupported (D : WeightedDesign m k)
    (hodd : Odd k)
    (hwitness : ∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
        ∀ level : ℝ, level < 1 → (tiltedMixture D tilt).eval level ≠ 0) :
    (∃ selected : Finset (Fin m), selected.card = k ∧ levelOneCoefficient D selected < 0)
      ∨ IsTotalTieSupported D := by
  by_cases hnegative : ∃ selected : Finset (Fin m), selected.card = k
      ∧ levelOneCoefficient D selected < 0
  · exact Or.inl hnegative
  refine Or.inr ?_
  push Not at hnegative
  rw [isTotalTieSupported_iff_forall_levelOneCoefficient_eq_zero]
  intro selected hcard
  by_contra hne
  exact not_exists_witnessTilt_of_levelOneCoefficient_nonneg D hodd hnegative hcard
    (lt_of_le_of_ne (hnegative selected hcard) (Ne.symm hne)) hwitness

/-- The dichotomy at the cell level. -/
theorem forall_design_levelOneCoefficient_neg_or_isTotalTieSupported_of_ecpStar
    (hodd : Odd k) (hecp : EcpStar m k) (D : WeightedDesign m k) :
    (∃ selected : Finset (Fin m), selected.card = k ∧ levelOneCoefficient D selected < 0)
      ∨ IsTotalTieSupported D :=
  exists_levelOneCoefficient_neg_or_isTotalTieSupported D hodd (hecp D)

/-! ## What refutes `EcpStar`, and what such a refuting design must look like -/

/-- **A REFUTATION TEMPLATE.**  One design with all level-one coefficients
nonnegative and one strictly positive refutes `Gtz.EcpStar` at its whole cell. -/
theorem not_ecpStar_of_levelOneCoefficient_nonneg (D : WeightedDesign m k) (hodd : Odd k)
    (hnonneg : ∀ selected : Finset (Fin m), selected.card = k
      → 0 ≤ levelOneCoefficient D selected)
    {witness : Finset (Fin m)} (hcard : witness.card = k)
    (hwitnessPos : 0 < levelOneCoefficient D witness) :
    ¬ EcpStar m k := fun hecp =>
  not_exists_witnessTilt_of_levelOneCoefficient_nonneg D hodd hnonneg hcard hwitnessPos (hecp D)

/-- A design with no negative level-one coefficient has NO strictly dominating
`rank`-subset, by `levelOneCoefficient_neg_of_posDef`. -/
theorem not_posDef_gap_of_levelOneCoefficient_nonneg (D : WeightedDesign m k) (hodd : Odd k)
    (hnonneg : ∀ selected : Finset (Fin m), selected.card = k
      → 0 ≤ levelOneCoefficient D selected)
    (selected : Finset (Fin m)) (hcard : selected.card = k) :
    ¬ (subsetSum D selected - 1).PosDef := fun hstrict =>
  absurd (levelOneCoefficient_neg_of_posDef D hodd hcard hstrict)
    (not_lt.mpr (hnonneg selected hcard))

/-- **ANY REFUTING DESIGN IS A TIE.**  Combining the previous theorem with a
dominating subset — which GTZ supplies at every design — a design refuting
`Gtz.EcpStar` by the template is a `Gtz.IsTie`. -/
theorem isTie_of_levelOneCoefficient_nonneg (D : WeightedDesign m k) (hodd : Odd k)
    (hnonneg : ∀ selected : Finset (Fin m), selected.card = k
      → 0 ≤ levelOneCoefficient D selected)
    (hdominated : ∃ C : Finset (Fin m), C.card = k ∧ Dominates D C) :
    IsTie D :=
  ⟨hdominated, not_posDef_gap_of_levelOneCoefficient_nonneg D hodd hnonneg⟩

/-- **AND IT IS NOT A TOTAL TIE.**  A strictly positive level-one coefficient is
exactly a failure of `Gtz.IsTotalTieSupported`.  So the tilt lane's fate is the
campaign's OPEN non-total-tie question: `Gtz.EcpStar m k` fails at odd rank if and
only if some design has all level-one coefficients nonnegative with one positive,
and such a design is a NON-TOTAL TIE. -/
theorem not_isTotalTieSupported_of_levelOneCoefficient_pos (D : WeightedDesign m k)
    {witness : Finset (Fin m)} (hcard : witness.card = k)
    (hwitnessPos : 0 < levelOneCoefficient D witness) :
    ¬ IsTotalTieSupported D := by
  rw [isTotalTieSupported_iff_forall_levelOneCoefficient_eq_zero]
  intro hzero
  rw [hzero witness hcard] at hwitnessPos
  exact absurd hwitnessPos (lt_irrefl 0)

/-! ## The gap on the other side: the level-one test does not see domination -/

/-- **THE LEVEL-ONE TEST IS STRICTLY WEAKER THAN DOMINATION.**  At rank three
`det(1·I − S) < 0` says only that an EVEN number of eigenvalues of `S` lie below
one; zero of them is a strict dominator, but TWO of them is a doubly deficient
subset that dominates in no sense at all.  The witness `diag(1/2, 1/2, 3)` is
positive semidefinite, has `det(1·I − S) = −1/2 < 0`, and its gap is not even
positive semidefinite.  Consequently the only constraint the tilt family imposes
(`exists_tilt_eval_one_neg_iff_exists_levelOneCoefficient_neg`) can be satisfied
by a design with no dominating subset whatsoever, and satisfying it proves
nothing about GTZ. -/
theorem exists_posSemidef_levelOneNegative_not_dominating :
    ∃ atomSum : Matrix (Fin 3) (Fin 3) ℝ, atomSum.PosSemidef
      ∧ (Matrix.scalar (Fin 3) (1 : ℝ) - atomSum).det < 0
      ∧ ¬ (atomSum - 1).PosSemidef := by
  refine ⟨Matrix.diagonal ![1/2, 1/2, 3], ?_, ?_, ?_⟩
  · refine (Matrix.posSemidef_diagonal_iff).mpr fun index => ?_
    fin_cases index <;> norm_num
  · have hone : Matrix.scalar (Fin 3) (1 : ℝ) = 1 := map_one _
    have hdiagonalOne : (1 : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.diagonal (fun _ : Fin 3 => (1 : ℝ)) := Matrix.diagonal_one.symm
    rw [hone, hdiagonalOne, Matrix.diagonal_sub, Matrix.det_diagonal, Fin.prod_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · intro hposSemidef
    have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hposSemidef).2 ![1, 0, 0]
    rw [star_trivial] at hquad
    have hvalue : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ
        ((Matrix.diagonal ![1/2, 1/2, 3] - (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ ![1, 0, 0])
        = -(1/2) := by
      norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.diagonal_apply,
        Matrix.one_apply, Matrix.sub_apply, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
    rw [hvalue] at hquad
    norm_num at hquad

/-! ## The law has teeth at the target cell

`Gtz.axisKillDesign` is the all-heavy `(7,3)` design at which the campaign refutes
`Gtz.HasMixedRootAtLeastOne 7 3`: its UNIFORM mixture is strictly positive at level
one (`Gtz.mixedCharPoly_axisKillDesign_eval_one = 11/256`).  A tilt fixes that, and
the reason is visible in the sign law — the triple `{4,5,6}` of doubled axes has
gap `(5/2)·I` (`Gtz.posDefGap_axisKillDesign_fourFiveSix`), hence a strictly negative
level-one coefficient. -/

/-- **THE UNIFORM TILT IS ON THE WRONG SIDE AT `(7,3)`**: `11/256 > 0`. -/
theorem tiltedMixture_axisKillDesign_uniform_eval_one_pos :
    0 < (tiltedMixture axisKillDesign (fun _ => 1)).eval 1 := by
  rw [tiltedMixture_one, mixedCharPoly_axisKillDesign_eval_one]
  norm_num

/-- **AND A TILT REPAIRS IT.**  Concentrating on the strictly dominating triple
`{4,5,6}` drives the tilted mixture strictly below zero at level one.  So the tilt
is not powerless in general — it is powerless exactly against designs with no
negative level-one coefficient, which by `isTie_of_levelOneCoefficient_nonneg` are
ties, and by `not_isTotalTieSupported_of_levelOneCoefficient_pos` non-total ones. -/
theorem exists_tilt_eval_one_neg_axisKillDesign :
    ∃ tilt : Fin 7 → ℝ, (∀ atomIndex, 0 < tilt atomIndex)
      ∧ (tiltedMixture axisKillDesign tilt).eval 1 < 0 :=
  exists_tilt_eval_one_neg_of_levelOneCoefficient_neg axisKillDesign (by norm_num) (by decide)
    (levelOneCoefficient_neg_of_posDef axisKillDesign (by decide) (by decide)
      posDefGap_axisKillDesign_fourFiveSix)

/-- The same at the `(6,3)` refuting witness, via the icosahedron's shipped strict
dominator: `Gtz.icosaDesign` has `q(1) = 16/25 > 0` under the uniform tilt (the
campaign's own reading), yet its triple `{0,2,4}` dominates strictly, so a tilt
puts it on the good side of level one. -/
theorem exists_tilt_eval_one_neg_icosaDesign :
    ∃ tilt : Fin 6 → ℝ, (∀ atomIndex, 0 < tilt atomIndex)
      ∧ (tiltedMixture icosaDesign tilt).eval 1 < 0 :=
  exists_tilt_eval_one_neg_of_levelOneCoefficient_neg icosaDesign (by norm_num) (by decide)
    (levelOneCoefficient_neg_of_posDef icosaDesign (by decide) (by decide)
      icosaDesign_strictly_dominates)

/-! ## A design-level decoy: the level-one test does not find a dominating subset

The abstract witness above is realised by an honest, fully rational `(6,3)`
design.  Its triple `{0,1,2}` has atom sum `diag(1/4, 1/4, 4)`: TWO eigenvalues
below one and one above, so `det(1·I − S_C) = −27/16 < 0` and the level-one
coefficient is strictly negative — yet the triple does not dominate, not even
weakly.  A search that finds a negative level-one coefficient therefore returns
nothing usable for GTZ. -/

/-- Six axis-aligned integer directions: three short ones carrying the coordinate
frame at half scale and three long ones restoring Parseval. -/
def decoyVector : Fin 6 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 4], ![4, 0, 0], ![0, 4, 0], ![0, 0, 6]]

/-- Weight numerators over the common denominator `25`. -/
def decoyWeightNumerator : Fin 6 → ℤ := ![4, 4, 4, 6, 6, 1]

theorem decoyWeightNumerator_sum : ∑ atomIndex : Fin 6, decoyWeightNumerator atomIndex = 25 := by
  decide

/-- The integer Parseval identity `∑_c n_c v_c v_cᵀ = 100·I₃`. -/
theorem decoyVector_parseval (rowCoord colCoord : Fin 3) :
    ∑ atomIndex : Fin 6, decoyWeightNumerator atomIndex
        * (decoyVector atomIndex rowCoord * decoyVector atomIndex colCoord)
      = if rowCoord = colCoord then 100 else 0 := by
  revert rowCoord colCoord
  decide

/-- **A fully rational `(6,3)` design** whose triple `{0,1,2}` has atom sum
`diag(1/4, 1/4, 4)`. -/
noncomputable def decoyDesign : WeightedDesign 6 3 where
  atom := fun atomIndex coord => (1/2 : ℝ) * ((decoyVector atomIndex coord : ℤ) : ℝ)
  weight := fun atomIndex => ((decoyWeightNumerator atomIndex : ℤ) : ℝ) / 25
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex <;> norm_num [decoyWeightNumerator]
  weight_sum_one := by
    rw [← Finset.sum_div]
    have hnumerators : ∑ atomIndex : Fin 6, ((decoyWeightNumerator atomIndex : ℤ) : ℝ)
        = ((25 : ℤ) : ℝ) := by
      rw [← Int.cast_sum, decoyWeightNumerator_sum]
    rw [hnumerators]
    norm_num
  isParseval := by
    ext rowCoord colCoord
    rw [Matrix.sum_apply]
    have hterm : ∀ atomIndex : Fin 6,
        ((((decoyWeightNumerator atomIndex : ℤ) : ℝ) / 25)
            • atomMatrix (fun coord => (1/2 : ℝ) * ((decoyVector atomIndex coord : ℤ) : ℝ)))
          rowCoord colCoord
          = (1 / 100 : ℝ) * (((decoyWeightNumerator atomIndex
              * (decoyVector atomIndex rowCoord * decoyVector atomIndex colCoord) : ℤ) : ℝ)) := by
      intro atomIndex
      simp only [Matrix.smul_apply, smul_eq_mul, atomMatrix, Matrix.vecMulVec_apply]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hterm atomIndex,
      ← Finset.mul_sum, ← Int.cast_sum, decoyVector_parseval]
    by_cases hdiagonal : rowCoord = colCoord
    · rw [if_pos hdiagonal, hdiagonal, Matrix.one_apply_eq]
      norm_num
    · rw [if_neg hdiagonal, Matrix.one_apply_ne hdiagonal]
      norm_num

theorem decoyDesign_atom (atomIndex : Fin 6) (coord : Fin 3) :
    decoyDesign.atom atomIndex coord = (1/2 : ℝ) * ((decoyVector atomIndex coord : ℤ) : ℝ) := rfl

theorem decoyDesign_weight (atomIndex : Fin 6) :
    decoyDesign.weight atomIndex = ((decoyWeightNumerator atomIndex : ℤ) : ℝ) / 25 := rfl

/-- The integer Gram of a subset of directions. -/
def decoyGram (selected : Finset (Fin 6)) (rowCoord colCoord : Fin 3) : ℤ :=
  ∑ atomIndex ∈ selected, decoyVector atomIndex rowCoord * decoyVector atomIndex colCoord

theorem subsetSum_decoyDesign_apply (selected : Finset (Fin 6)) (rowCoord colCoord : Fin 3) :
    subsetSum decoyDesign selected rowCoord colCoord
      = (1 / 4 : ℝ) * ((decoyGram selected rowCoord colCoord : ℤ) : ℝ) := by
  rw [subsetSum_apply, decoyGram]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [decoyDesign_atom, decoyDesign_atom]
  ring

theorem decoyGram_zeroOneTwo (rowCoord colCoord : Fin 3) :
    decoyGram {0, 1, 2} rowCoord colCoord
      = if rowCoord = colCoord then (if rowCoord = 2 then 16 else 1) else 0 := by
  revert rowCoord colCoord
  decide

private theorem finThreeZero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem finThreeOne_ne_two : (1 : Fin 3) ≠ 2 := by decide
private theorem finThreeTwo_ne_zero : (2 : Fin 3) ≠ 0 := by decide
private theorem finThreeTwo_ne_one : (2 : Fin 3) ≠ 1 := by decide

theorem det_subsetSum_decoyDesign_zeroOneTwo :
    (subsetSum decoyDesign {0, 1, 2}).det = 1/4 := by
  rw [Matrix.det_fin_three]
  simp only [subsetSum_decoyDesign_apply, decoyGram_zeroOneTwo, finThreeZero_ne_two,
    finThreeOne_ne_two, finThreeTwo_ne_zero, finThreeTwo_ne_one, if_false, if_true]
  norm_num

theorem det_scalarOne_sub_subsetSum_decoyDesign_zeroOneTwo :
    (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum decoyDesign {0, 1, 2}).det = -(27/16) := by
  have hone : Matrix.scalar (Fin 3) (1 : ℝ) = 1 := map_one _
  rw [hone, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.one_apply, subsetSum_decoyDesign_apply,
    decoyGram_zeroOneTwo, finThreeZero_ne_two, finThreeOne_ne_two, finThreeTwo_ne_zero,
    finThreeTwo_ne_one, if_false, if_true]
  norm_num

theorem shadowDeterminant_decoyDesign_zeroOneTwo_pos :
    0 < shadowDeterminant decoyDesign {0, 1, 2} := by
  rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum decoyDesign (by decide),
    det_subsetSum_decoyDesign_zeroOneTwo]
  exact mul_pos (Finset.prod_pos fun atomIndex _ => decoyDesign.weight_pos atomIndex) (by norm_num)

theorem not_dominates_decoyDesign_zeroOneTwo : ¬ Dominates decoyDesign {0, 1, 2} := by
  intro hdominates
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 ![1, 0, 0]
  rw [star_trivial] at hquad
  have hvalue : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ
      ((subsetSum decoyDesign {0, 1, 2} - 1) *ᵥ ![1, 0, 0]) = -(3/4) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.sub_apply,
      subsetSum_decoyDesign_apply, decoyGram_zeroOneTwo, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, finThreeZero_ne_two, finThreeOne_ne_two, finThreeTwo_ne_zero,
      finThreeTwo_ne_one, if_false, if_true]
    norm_num
  rw [hvalue] at hquad
  norm_num at hquad

/-- **THE DESIGN-LEVEL FORM OF THE GAP.**  A genuine `(6,3)` design has a triple
with strictly negative level-one coefficient that does not dominate.  Combined
with `exists_tilt_eval_one_neg_iff_exists_levelOneCoefficient_neg`, this says the
tilt family's only binding constraint is met by data GTZ cannot use. -/
theorem levelOneCoefficient_neg_and_not_dominates_decoyDesign :
    levelOneCoefficient decoyDesign {0, 1, 2} < 0 ∧ ¬ Dominates decoyDesign {0, 1, 2} := by
  refine ⟨?_, not_dominates_decoyDesign_zeroOneTwo⟩
  rw [levelOneCoefficient, det_scalarOne_sub_subsetSum_decoyDesign_zeroOneTwo]
  exact mul_neg_of_pos_of_neg shadowDeterminant_decoyDesign_zeroOneTwo_pos (by norm_num)

end Gtz
