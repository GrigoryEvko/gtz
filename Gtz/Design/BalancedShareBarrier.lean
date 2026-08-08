import Gtz.Quantitative.TieRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! # The balanced-share barrier for the pair-conditioned tie average

`Gtz.sum_offPair_weight_mul_discriminantTie` reduces the pair-conditioned average
of the tie leg to the SURPLUS FORM

    u_b * shareSurplus a + u_a * shareSurplus b - 2 <g_a,g_b>^2 (t_a + t_b),

and `Gtz.exists_pos_discriminantTie_of_pos_surplusForm` turns a strictly positive
surplus form into a genuine completion with a positive tie leg.  This file records
the exact SHARE condition the form needs, and the size-six pigeonhole that denies
it at one atom of every design.

The reading: firing needs an atom of ABOVE-HALF leverage share, while
`Gtz.sum_atomShare_eq_rank` pins the shares to average `k/m`, which is exactly a
half at `(6,3)`.  So the balanced stratum -- the one the tie locus sits on -- is
where the pair-conditioned average is uniformly dead. -/

/-- The surplus form of a pair: the right-hand side of the honest off-pair law. -/
noncomputable def pairSurplusForm (D : WeightedDesign m 3) (pivot pairFirst : Fin m) : ℝ :=
  heavyExcess D pairFirst * shareSurplus D pivot
    + heavyExcess D pivot * shareSurplus D pairFirst
    - 2 * atomPairing D pivot pairFirst ^ 2 * (D.weight pivot + D.weight pairFirst)

/-- **THE BALANCED-SHARE BARRIER.**  A pair both of whose atoms carry at most half
the leverage share has a strictly negative surplus form, so the positive criterion
can never fire there.  Only `Gtz.AllHeavy` and the two share bounds are used. -/
theorem pairSurplusForm_neg_of_shares_le_half (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) (pivot pairFirst : Fin m)
    (hpivotShare : atomShare D pivot ≤ 1 / 2)
    (hpartnerShare : atomShare D pairFirst ≤ 1 / 2) :
    pairSurplusForm D pivot pairFirst < 0 := by
  have hpivotExcess : 0 < heavyExcess D pivot := by
    have := hheavy pivot; simp only [heavyExcess]; linarith
  have hpartnerExcess : 0 < heavyExcess D pairFirst := by
    have := hheavy pairFirst; simp only [heavyExcess]; linarith
  have hpivotSurplus : shareSurplus D pivot < 0 :=
    shareSurplus_neg_of_atomShare_le_half D hpivotShare
  have hpartnerSurplus : shareSurplus D pairFirst < 0 :=
    shareSurplus_neg_of_atomShare_le_half D hpartnerShare
  have hpairing : 0 ≤ 2 * atomPairing D pivot pairFirst ^ 2
      * (D.weight pivot + D.weight pairFirst) := by
    have hweights := add_pos (D.weight_pos pivot) (D.weight_pos pairFirst)
    positivity
  have hfirst : heavyExcess D pairFirst * shareSurplus D pivot < 0 :=
    mul_neg_of_pos_of_neg hpartnerExcess hpivotSurplus
  have hsecond : heavyExcess D pivot * shareSurplus D pairFirst < 0 :=
    mul_neg_of_pos_of_neg hpivotExcess hpartnerSurplus
  simp only [pairSurplusForm]
  linarith

/-- **What firing costs.**  A strictly positive surplus form forces one of the two
atoms to carry MORE than half the leverage share.  Contrapositive of the barrier. -/
theorem exists_atomShare_gt_half_of_pos_pairSurplusForm (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) (pivot pairFirst : Fin m)
    (hpositive : 0 < pairSurplusForm D pivot pairFirst) :
    1 / 2 < atomShare D pivot ∨ 1 / 2 < atomShare D pairFirst := by
  by_contra hneither
  push Not at hneither
  exact absurd hpositive
    (not_lt.mpr (pairSurplusForm_neg_of_shares_le_half D hheavy pivot pairFirst
      hneither.1 hneither.2).le)

/-- **THE BALANCED STRATUM IS UNIFORMLY DEAD.**  If no atom carries more than half
the leverage share then NO pair fires -- the pair-conditioned tie average is
strictly negative at every pair at once. -/
theorem pairSurplusForm_neg_of_balanced (D : WeightedDesign m 3) (hheavy : AllHeavy D)
    (hbalanced : ∀ atomIndex : Fin m, atomShare D atomIndex ≤ 1 / 2)
    (pivot pairFirst : Fin m) :
    pairSurplusForm D pivot pairFirst < 0 :=
  pairSurplusForm_neg_of_shares_le_half D hheavy pivot pairFirst
    (hbalanced pivot) (hbalanced pairFirst)

/-! ## Size six: one atom is always below the half -/

/-- At `(6,3)` the share average is exactly a half, so some atom sits at or below
it.  This is `Gtz.exists_atomShare_le_rank_div_size` with `k/m = 3/6`. -/
theorem exists_atomShare_le_half_sixThree (D : WeightedDesign 6 3) :
    ∃ atomIndex : Fin 6, atomShare D atomIndex ≤ 1 / 2 := by
  obtain ⟨atomIndex, hbound⟩ := exists_atomShare_le_rank_div_size D (by norm_num)
  refine ⟨atomIndex, ?_⟩
  norm_num at hbound
  linarith

/-- **THE SIZE-SIX OBSTRUCTION.**  Every `(6,3)` design carries an atom whose share
surplus is strictly negative, hence an atom that can only ever appear in a firing
pair alongside a partner of strictly above-half share. -/
theorem exists_shareSurplus_neg_sixThree (D : WeightedDesign 6 3) :
    ∃ atomIndex : Fin 6, shareSurplus D atomIndex < 0 := by
  obtain ⟨atomIndex, hshare⟩ := exists_atomShare_le_half_sixThree D
  exact ⟨atomIndex, shareSurplus_neg_of_atomShare_le_half D hshare⟩

/-- **The paired form of the obstruction.**  At `(6,3)` there is an atom every one
of whose pairs with a below-half partner is dead. -/
theorem exists_atom_deadAgainstBalancedPartners_sixThree (D : WeightedDesign 6 3)
    (hheavy : AllHeavy D) :
    ∃ deadAtom : Fin 6, ∀ partner : Fin 6,
      atomShare D partner ≤ 1 / 2 → pairSurplusForm D deadAtom partner < 0 := by
  obtain ⟨deadAtom, hshare⟩ := exists_atomShare_le_half_sixThree D
  exact ⟨deadAtom, fun partner hpartner =>
    pairSurplusForm_neg_of_shares_le_half D hheavy deadAtom partner hshare hpartner⟩

/-! ## The bridge to the landed off-pair law -/

/-- `pairSurplusForm` IS the right-hand side of `Gtz.sum_offPair_weight_mul_discriminantTie`. -/
theorem sum_offPair_weight_mul_discriminantTie_eq_pairSurplusForm (D : WeightedDesign m 3)
    {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex
      = pairSurplusForm D pivot pairFirst :=
  sum_offPair_weight_mul_discriminantTie D hdistinct

/-- **THE VERDICT, in the landed vocabulary.**  On a heavy design whose leverage
shares are all at most a half, the pair-conditioned average of the tie leg is
strictly negative at EVERY pair.  So no pair-conditioned averaging certificate can
produce a positive tie leg anywhere on the balanced stratum. -/
theorem sum_offPair_weight_mul_discriminantTie_neg_of_balanced (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) (hbalanced : ∀ atomIndex : Fin m, atomShare D atomIndex ≤ 1 / 2)
    {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex < 0 := by
  rw [sum_offPair_weight_mul_discriminantTie D hdistinct]
  simpa [pairSurplusForm] using pairSurplusForm_neg_of_balanced D hheavy hbalanced pivot pairFirst

end Gtz
