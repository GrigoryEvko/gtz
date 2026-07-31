/-
# The `e_3` PAIR ROW LAW, and why pair-conditioned averaging of the tie leg is dead

`Gtz/Quantitative/ChartHadamard.lean` carries the unconditional identities for the
FIRST and SECOND elementary symmetric functions of the chart gap `W = P - diag t`:
the row law `Gtz.sum_weight_mul_chartObstruction` and the total mass
`Gtz.sum_weight_mul_weight_mul_chartObstruction`.  Its own header records that the
`e_2` layer is vacuous exactly where the problem is and that the whole obstruction
is `e_3`.  No row law for `e_3` appears anywhere in the tree at general weights.

This file supplies it, and then shows the rung it opens is a BARRIER rather than a
route.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `sum_weight_mul_discriminantTie` — THE `e_3` PAIR ROW LAW.  For EVERY weighted
  `(m,3)` design, EVERY pair of atoms and EVERY weight vector,
  `sum_c t_c * det(Gram[{a,b,c}] - 1) = -((l_a - 1) + (l_b - 1))`.
  Three Parseval readings do all the work.  The pairing `<g_a,g_b>` enters twice
  with opposite signs and cancels EXACTLY at rank three, so the pair-conditioned
  average of the tie leg cannot see the correlation of the pair it is conditioned
  on at all.  It sees only the two leverages.
* `sum_offPair_weight_mul_discriminantTie` — the honest off-pair law, obtained by
  peeling the two degenerate completions.  It is the surplus form.
* `sum_offPair_weight_mul_discriminantTie_neg` — THE BARRIER.  One strictly
  negative share surplus at either atom makes the honest off-pair average
  strictly NEGATIVE under `Gtz.AllHeavy`, at any weights and any size.  So no
  averaging of the tie leg over the completions of a fixed pair can ever certify
  a dominating triple.  This is the `e_3` companion of the `e_2` positivity
  `Gtz.exists_pos_chartGapPairMinorSum_of_allHeavy`, and it points the other way:
  the ladder of averaged symmetric functions of the gap is POSITIVE at `e_2` and
  NEGATIVE at `e_3`, which is precisely the rung the covering needs.
* `sum_shareSurplus` — the surplus budget `2*rank - 1 - size`, which at rank three
  is `5 - m`.  Strictly negative from size six on, so both frontier cells `(6,3)`
  and `(7,3)` sit on the barrier's side of it.
* `sum_ordered_weight_mul_discriminantTie` — the ordered weighted triple aggregate
  is `-4` at every weight vector and every size.  The shipped
  `Gtz.sum_det_subsetSum_sub_one_uniform` is the FLAT sum over `rank`-subsets and
  needs a uniform-weight hypothesis, the flat sum being genuinely design-dependent
  without one; the ordered weighted aggregate has no such hypothesis.

## NOT proved here

Nothing about a positive rung.  `exists_pos_discriminantTie_of_pos_surplusForm` is
the only affirmative criterion, and `sum_shareSurplus` shows it cannot fire on
average at the frontier sizes.  The weak and strict barriers are kept as separate
statements deliberately: the strict form is FALSE when both surpluses vanish and
the pair is orthogonal, so they must not be merged.

Provenance: scratch report 10 (`deepen-alg`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Quantitative.ChartHadamard
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The row law -/

/-- Parseval's bilinear reading with BOTH pairings oriented away from the summation
index, which is the orientation the tie leg produces.  The shipped
`Gtz.sum_weight_mul_atomPairing_mul_atomPairing` carries the other orientation;
this stays private so the two never compete as public API. -/
private theorem sum_weight_mul_atomPairing_mul_atomPairing_right (D : WeightedDesign m 3)
    (pivot pairFirst : Fin m) :
    ∑ thirdIndex, D.weight thirdIndex
        * ((D.atom pivot ⬝ᵥ D.atom thirdIndex) * (D.atom pairFirst ⬝ᵥ D.atom thirdIndex))
      = D.atom pivot ⬝ᵥ D.atom pairFirst := by
  rw [← sum_weight_mul_atomPairing_mul_atomPairing D pivot pairFirst]
  exact Finset.sum_congr rfl fun thirdIndex _ => by
    rw [dotProduct_comm (D.atom pairFirst) (D.atom thirdIndex)]

/-- **THE `e_3` PAIR ROW LAW.**  Averaging the tie leg over the third atom against
the design's own weights returns MINUS the sum of the two heavy excesses of the
conditioning pair — for every design, every size and every weight vector.

The tie leg is `det(Gram - 1)` of the triple, so this is the third elementary
symmetric function's analogue of `Gtz.sum_weight_mul_chartObstruction`, which is
the second's.  Where that one carries the leverage of the row it is taken on, this
one carries NOTHING but the two excesses: the pairing `<g_a,g_b>` enters twice with
opposite signs — once through `sum_c t_c (l_c - 1) <g_a,g_b>^2` and once through
`2<g_a,g_b> sum_c t_c <g_a,g_c><g_b,g_c>` — and at rank three the two cancel
exactly. -/
theorem sum_weight_mul_discriminantTie (D : WeightedDesign m 3) (pivot pairFirst : Fin m) :
    ∑ thirdIndex, D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex
      = -(heavyExcess D pivot + heavyExcess D pairFirst) := by
  have hlinear : ∀ thirdIndex : Fin m,
      D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex
        = (heavyExcess D pivot * heavyExcess D pairFirst
              - atomPairing D pivot pairFirst ^ 2)
            * (D.weight thirdIndex * (leverageOf (D.atom thirdIndex) - 1))
          - heavyExcess D pivot
              * (D.weight thirdIndex * (D.atom pairFirst ⬝ᵥ D.atom thirdIndex) ^ 2)
          - heavyExcess D pairFirst
              * (D.weight thirdIndex * (D.atom pivot ⬝ᵥ D.atom thirdIndex) ^ 2)
          + 2 * atomPairing D pivot pairFirst
              * (D.weight thirdIndex
                  * ((D.atom pivot ⬝ᵥ D.atom thirdIndex)
                      * (D.atom pairFirst ⬝ᵥ D.atom thirdIndex))) := by
    intro thirdIndex
    simp only [discriminantTie, heavyExcess, atomPairing]
    ring
  rw [Finset.sum_congr rfl fun thirdIndex (_ : thirdIndex ∈ Finset.univ) => hlinear thirdIndex,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_weight_mul_leverage_sub_one D, sum_weight_mul_sq_atomPairing D pairFirst,
    sum_weight_mul_sq_atomPairing D pivot,
    sum_weight_mul_atomPairing_mul_atomPairing_right D pivot pairFirst]
  simp only [heavyExcess, atomPairing]
  norm_num
  ring

/-! ## The two degenerate completions, and the honest off-pair law -/

/-- The completion by the pivot itself. -/
theorem discriminantTie_self_pivot (D : WeightedDesign m 3) (pivot pairFirst : Fin m) :
    discriminantTie D pivot pairFirst pivot
      = -(heavyExcess D pairFirst * (2 * heavyExcess D pivot + 1))
        + 2 * atomPairing D pivot pairFirst ^ 2 := by
  simp only [discriminantTie, heavyExcess, atomPairing,
    dotProduct_comm (D.atom pairFirst) (D.atom pivot),
    dotProduct_self_eq_sum_sq (D.atom pivot), leverageOf]
  ring

/-- The completion by the pair partner itself. -/
theorem discriminantTie_self_pairFirst (D : WeightedDesign m 3) (pivot pairFirst : Fin m) :
    discriminantTie D pivot pairFirst pairFirst
      = -(heavyExcess D pivot * (2 * heavyExcess D pairFirst + 1))
        + 2 * atomPairing D pivot pairFirst ^ 2 := by
  simp only [discriminantTie, heavyExcess, atomPairing,
    dotProduct_self_eq_sum_sq (D.atom pairFirst), leverageOf]
  ring

/-- **The share surplus of an atom**, `2 s_c - t_c - 1`.  It is the exact amount by
which the atom's leverage score exceeds the half-way point between its weight and
one, and it is the ONLY design quantity the honest off-pair tie average sees
besides the two excesses and the pairing. -/
noncomputable def shareSurplus (D : WeightedDesign m 3) (atomIndex : Fin m) : ℝ :=
  2 * atomShare D atomIndex - D.weight atomIndex - 1

/-- **The surplus budget**: the share surpluses total `2*rank - 1 - size`.  At rank
three that is `5 - m`: strictly positive below size five, ZERO at size five,
strictly negative from size six on.  So on the `(6,3)` and `(7,3)` frontier cells
the surplus is negative on average, and the criterion below fires only on designs
that concentrate their leverage. -/
theorem sum_shareSurplus (D : WeightedDesign m 3) :
    ∑ atomIndex, shareSurplus D atomIndex = 5 - (m : ℝ) := by
  simp only [shareSurplus]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_atomShare_eq_rank D, D.weight_sum_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  norm_num

/-- **THE HONEST OFF-PAIR LAW.**  Dropping the two degenerate completions from the
row law leaves an average over the genuine completions only, and it is the surplus
form: excess times partner's surplus, twice, minus twice the squared pairing
against the pair's weight mass. -/
theorem sum_offPair_weight_mul_discriminantTie (D : WeightedDesign m 3)
    {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex
      = heavyExcess D pairFirst * shareSurplus D pivot
        + heavyExcess D pivot * shareSurplus D pairFirst
        - 2 * atomPairing D pivot pairFirst ^ 2 * (D.weight pivot + D.weight pairFirst) := by
  have hpivotMember : pivot ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ pivot
  have hpartnerMember : pairFirst ∈ Finset.univ.erase pivot :=
    Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ pairFirst⟩
  have hpeelPivot := Finset.add_sum_erase (Finset.univ : Finset (Fin m))
    (fun thirdIndex => D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex)
    hpivotMember
  have hpeelPartner := Finset.add_sum_erase (Finset.univ.erase pivot)
    (fun thirdIndex => D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex)
    hpartnerMember
  have hrow := sum_weight_mul_discriminantTie D pivot pairFirst
  rw [← hpeelPivot, ← hpeelPartner] at hrow
  have hsurplus : ∀ atomIndex : Fin m,
      D.weight atomIndex * (2 * heavyExcess D atomIndex + 1) = shareSurplus D atomIndex + 1 := by
    intro atomIndex
    simp only [shareSurplus, atomShare, heavyExcess]
    ring
  have hpivotTerm : D.weight pivot * discriminantTie D pivot pairFirst pivot
      = -(heavyExcess D pairFirst * (shareSurplus D pivot + 1))
        + 2 * atomPairing D pivot pairFirst ^ 2 * D.weight pivot := by
    rw [discriminantTie_self_pivot D pivot pairFirst, ← hsurplus pivot]
    ring
  have hpartnerTerm : D.weight pairFirst * discriminantTie D pivot pairFirst pairFirst
      = -(heavyExcess D pivot * (shareSurplus D pairFirst + 1))
        + 2 * atomPairing D pivot pairFirst ^ 2 * D.weight pairFirst := by
    rw [discriminantTie_self_pairFirst D pivot pairFirst, ← hsurplus pairFirst]
    ring
  rw [hpivotTerm, hpartnerTerm] at hrow
  linarith [hrow]

/-! ## What the law decides -/

/-- **THE POSITIVE CRITERION.**  A pair whose surplus form is strictly positive owns
a genuine completion at which the tie leg is strictly positive.  The form is
`u_b * surplus a + u_a * surplus b - 2 <g_a,g_b>^2 (t_a + t_b)`, so it fires exactly
on pairs of concentrated, weakly correlated atoms; `sum_shareSurplus` says that at
rank three this needs size at most five on average, and the frontier cells `(6,3)`
and `(7,3)` sit on the wrong side of it. -/
theorem exists_pos_discriminantTie_of_pos_surplusForm (D : WeightedDesign m 3)
    {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst)
    (hsurplus : 0 < heavyExcess D pairFirst * shareSurplus D pivot
      + heavyExcess D pivot * shareSurplus D pairFirst
      - 2 * atomPairing D pivot pairFirst ^ 2 * (D.weight pivot + D.weight pairFirst)) :
    ∃ thirdIndex : Fin m, thirdIndex ≠ pivot ∧ thirdIndex ≠ pairFirst
      ∧ 0 < discriminantTie D pivot pairFirst thirdIndex := by
  by_contra hnone
  have hnonpos : ∀ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
      D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex ≤ 0 := by
    intro thirdIndex hmember
    have hoffPartner : thirdIndex ≠ pairFirst := Finset.ne_of_mem_erase hmember
    have hoffPivot : thirdIndex ≠ pivot :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hmember)
    have htie : discriminantTie D pivot pairFirst thirdIndex ≤ 0 := by
      by_contra hpositive
      exact hnone ⟨thirdIndex, hoffPivot, hoffPartner, not_le.mp hpositive⟩
    exact mul_nonpos_of_nonneg_of_nonpos (D.weight_pos thirdIndex).le htie
  have hupper := Finset.sum_nonpos hnonpos
  rw [sum_offPair_weight_mul_discriminantTie D hdistinct] at hupper
  linarith

/-- An atom whose leverage score is at most a half has a strictly negative share
surplus: `2 s - t - 1 <= -t < 0`.  Every uniform-share cell with `2*rank <= size`
qualifies, `(7,3)` at `s = 3/7` among them. -/
theorem shareSurplus_neg_of_atomShare_le_half (D : WeightedDesign m 3) {atomIndex : Fin m}
    (hshare : atomShare D atomIndex ≤ 1 / 2) : shareSurplus D atomIndex < 0 := by
  have hweight := D.weight_pos atomIndex
  simp only [shareSurplus]
  linarith

/-- **THE BARRIER, weak form.**  Whenever neither atom of the pair has a positive
share surplus, the honest off-pair average of the tie leg is nonpositive under
`Gtz.AllHeavy` — at any weights and any size.  Kept separate from the strict form
below on purpose: the strict conclusion is FALSE when both surpluses vanish and the
pair is orthogonal, so the two must not be merged into one strict inequality. -/
theorem sum_offPair_weight_mul_discriminantTie_nonpos (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst)
    (hpivotSurplus : shareSurplus D pivot ≤ 0)
    (hpartnerSurplus : shareSurplus D pairFirst ≤ 0) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex ≤ 0 := by
  have hpivotExcess : 0 < heavyExcess D pivot := by
    have := hheavy pivot; simp only [heavyExcess]; linarith
  have hpartnerExcess : 0 < heavyExcess D pairFirst := by
    have := hheavy pairFirst; simp only [heavyExcess]; linarith
  have hpairing : 0 ≤ 2 * atomPairing D pivot pairFirst ^ 2
      * (D.weight pivot + D.weight pairFirst) := by
    have hweights := add_pos (D.weight_pos pivot) (D.weight_pos pairFirst)
    positivity
  have hfirstTerm : heavyExcess D pairFirst * shareSurplus D pivot ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpartnerExcess.le hpivotSurplus
  have hsecondTerm : heavyExcess D pivot * shareSurplus D pairFirst ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpivotExcess.le hpartnerSurplus
  rw [sum_offPair_weight_mul_discriminantTie D hdistinct]
  linarith

/-- **THE BARRIER.**  One strictly negative surplus at either atom of the pair makes
the honest off-pair average of the tie leg strictly NEGATIVE under `Gtz.AllHeavy` —
at any weights and any size.  So no averaging of the tie leg over the completions of
a fixed pair can ever certify a dominating triple.

This is the `e_3` companion of the `e_2` positivity
`Gtz.exists_pos_chartGapPairMinorSum_of_allHeavy`, and it points the other way: the
ladder of averaged symmetric functions of the gap is POSITIVE at `e_2` and NEGATIVE
at `e_3`, which is precisely the rung the covering needs. -/
theorem sum_offPair_weight_mul_discriminantTie_neg (D : WeightedDesign m 3)
    (hheavy : AllHeavy D) {pivot pairFirst : Fin m} (hdistinct : pivot ≠ pairFirst)
    (hpivotSurplus : shareSurplus D pivot < 0)
    (hpartnerSurplus : shareSurplus D pairFirst ≤ 0) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex < 0 := by
  have hpivotExcess : 0 < heavyExcess D pivot := by
    have := hheavy pivot; simp only [heavyExcess]; linarith
  have hpartnerExcess : 0 < heavyExcess D pairFirst := by
    have := hheavy pairFirst; simp only [heavyExcess]; linarith
  have hpairing : 0 ≤ 2 * atomPairing D pivot pairFirst ^ 2
      * (D.weight pivot + D.weight pairFirst) := by
    have hweights := add_pos (D.weight_pos pivot) (D.weight_pos pairFirst)
    positivity
  have hfirstTerm : heavyExcess D pairFirst * shareSurplus D pivot < 0 :=
    mul_neg_of_pos_of_neg hpartnerExcess hpivotSurplus
  have hsecondTerm : heavyExcess D pivot * shareSurplus D pairFirst ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpivotExcess.le hpartnerSurplus
  rw [sum_offPair_weight_mul_discriminantTie D hdistinct]
  linarith

/-- **THE BARRIER AT THE FRONTIER.**  On the `(7,3)` uniform-share stratum — the
cell `Gtz.discriminantCovering_seven_iff_rank_three` makes equivalent to the whole
of rank three — EVERY pair's five genuine completions carry a strictly negative
weighted total tie.  The surplus is `6/7 - t_c - 1 = -1/7 - t_c`, negative with no
hypothesis on the leverages at all. -/
theorem sum_offPair_weight_mul_discriminantTie_neg_uniformShareSeven
    (D : WeightedDesign 7 3) (hheavy : AllHeavy D)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pivot pairFirst : Fin 7} (hdistinct : pivot ≠ pairFirst) :
    ∑ thirdIndex ∈ (Finset.univ.erase pivot).erase pairFirst,
        D.weight thirdIndex * discriminantTie D pivot pairFirst thirdIndex < 0 := by
  refine sum_offPair_weight_mul_discriminantTie_neg D hheavy hdistinct ?_ ?_
  · exact shareSurplus_neg_of_atomShare_le_half D (by rw [huniform pivot]; norm_num)
  · exact (shareSurplus_neg_of_atomShare_le_half D (by rw [huniform pairFirst]; norm_num)).le

/-! ## The ordered aggregate at every weight vector -/

/-- **THE ORDERED WEIGHTED TRIPLE AGGREGATE IS `-4`.**  Averaging the tie leg over
ALL ordered triples against the design's own weights returns `-4` for every
weighted `(m,3)` design at every weight vector and every size.

`Gtz.sum_det_subsetSum_sub_one_uniform` is the tree's design-blindness statement for
the FLAT sum over `rank`-subsets, and it carries a UNIFORM-WEIGHT hypothesis because
the flat sum is genuinely design-dependent without one (the `(6,3)` split tetrahedron
gives `-64` against the uniform `-56`).  The ordered weighted aggregate has no such
hypothesis: it is `-2(rank - 1)` at rank three whatever the weights do. -/
theorem sum_ordered_weight_mul_discriminantTie (D : WeightedDesign m 3) :
    ∑ pivot, ∑ pairFirst, ∑ thirdIndex,
        D.weight pivot * D.weight pairFirst * D.weight thirdIndex
          * discriminantTie D pivot pairFirst thirdIndex
      = -4 := by
  have hexcessTotal : ∑ atomIndex, D.weight atomIndex * heavyExcess D atomIndex = 2 := by
    simp only [heavyExcess]
    rw [sum_weight_mul_leverage_sub_one D]
    norm_num
  have hinner : ∀ pivot pairFirst : Fin m,
      ∑ thirdIndex, D.weight pivot * D.weight pairFirst * D.weight thirdIndex
          * discriminantTie D pivot pairFirst thirdIndex
        = D.weight pivot * D.weight pairFirst
          * -(heavyExcess D pivot + heavyExcess D pairFirst) := by
    intro pivot pairFirst
    rw [← sum_weight_mul_discriminantTie D pivot pairFirst, Finset.mul_sum]
    exact Finset.sum_congr rfl fun thirdIndex _ => by ring
  have hmiddle : ∀ pivot : Fin m,
      ∑ pairFirst, D.weight pivot * D.weight pairFirst
          * -(heavyExcess D pivot + heavyExcess D pairFirst)
        = (-1 : ℝ) * (D.weight pivot * heavyExcess D pivot) - 2 * D.weight pivot := by
    intro pivot
    have hexpand : ∀ pairFirst : Fin m,
        D.weight pivot * D.weight pairFirst * -(heavyExcess D pivot + heavyExcess D pairFirst)
          = (-(D.weight pivot * heavyExcess D pivot)) * D.weight pairFirst
            - D.weight pivot * (D.weight pairFirst * heavyExcess D pairFirst) :=
      fun pairFirst => by ring
    rw [Finset.sum_congr rfl fun pairFirst (_ : pairFirst ∈ Finset.univ) => hexpand pairFirst,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, D.weight_sum_one, hexcessTotal]
    ring
  rw [Finset.sum_congr rfl fun pivot (_ : pivot ∈ Finset.univ) =>
      Finset.sum_congr rfl fun pairFirst (_ : pairFirst ∈ Finset.univ) => hinner pivot pairFirst,
    Finset.sum_congr rfl fun pivot (_ : pivot ∈ Finset.univ) => hmiddle pivot,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hexcessTotal, D.weight_sum_one]
  norm_num

end Gtz
