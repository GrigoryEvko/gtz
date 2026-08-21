/-
# The subset-determinant layer profile, at every subset size

`Gtz.sum_det_subsetSum_sub_one_eq` (Gtz/Quantitative/CauchyBinetLayerSum.lean) totals the
gap determinants over the `rank`-subsets and gets a weight-free expression in the
elementary symmetric functions of the UNWEIGHTED second moment `N = Σ_c g_c g_cᵀ`.  It is
stated at ONE subset size, `chosenCard = rank`, because that is the size the tie condition
reads.  The proof never uses that hypothesis.

This file removes it.  For EVERY subset size `r`,

    Σ_{|T| = r} det(S_T − 1)  =  Σ_j (−1)^{rank+j} · C(size − j, r − j) · e_j(N) ,

with the convention that the `j > r` terms drop out because a `j`-minor of an `r`-sized
Gram block does not exist.  The whole determinant profile of a design across all subset
sizes is therefore ONE polynomial, determined by the `rank` eigenvalues of `N` alone.

## Why the other sizes matter

The campaign reads three sizes and owns only one of them.

* `r = rank` is the tie aggregate, shipped.
* **`r = size − 1` is the five-set aggregate at `(6,3)`**, and "every five-set dominates
  strictly" is a standing hypothesis of the open `(6,3)` stratum.  This file computes it:
  `Σ_{|F| = 5} det(S_F − 1) = 3·det N − 4·e_2(N) + 5·tr N − 6` (`Gtz.sum_det_gap_fiveSets_sixThree`).
* **`r = 2` is the pair aggregate**, and `det(S_{ab} − 1) = −q_ab`, so the total of the
  fifteen pair minors is `e_2(N) − 5·tr N + 15` — a closed form for a quantity the campaign
  has only ever had a WEIGHTED version of (`Σ_{a,b} t_a t_b q_ab = k² − 3k + 1`).

## The generating function

In the eigenvalues `ν_1 … ν_rank` of `N − 1` the whole profile collapses:

    Σ_r z^r · Σ_{|T| = r} det(S_T − 1)  =  (−1)^rank · (1 + z)^{size − rank} · Π_i (1 − ν_i z) .

At `(6,3)`, writing `E_j` for the elementary symmetric functions of `ν`, the four readings
that carry a hypothesis are

    r = 6 :  E_3                          (always positive: `Gtz.posDef_subsetSum_univ_sub_one`)
    r = 5 :  3 E_3 − E_2                  (positive when every five-set dominates strictly)
    r = 4 :  3 E_3 − 3 E_2 + E_1
    r = 3 :  E_3 − 3 E_2 + 3 E_1 − 1      (nonpositive at a tie)

The `r = 5` reading is a second, independent proof of the sibling identity
`Σ_c totalGapReading = rank + tr((N − 1)⁻¹)` of Gtz/Wave/SharpFiveSetCriterion.lean, which
that file reaches through Parseval: the two agree because
`det(S_{univ \ c} − 1) = det(N − 1)·(1 − r_c)` and `E_2/E_3 = tr((N−1)⁻¹)`.  Cauchy–Binet
and Parseval meet here.

## What this buys on the open stratum, and what it does not

The residual `(6,3)` stratum is: all-heavy, every five-set strictly dominating, every
dominating triple of type K0.  The two aggregates above pin the spectrum of `N − 1` into an
explicit window (`Gtz.spectral_window_of_isTie_sixThree`).  In the reciprocal coordinates
`x_i = 1/ν_i` the window is

    σ_1(x) < 1              (five-sets strict, through the weighted reading)
    1 − 3σ_1 + 3σ_2 − σ_3 ≤ 0   (tie).

[MEASURED.  The window is NOT empty, so this reduction does not close the stratum and no
successor should expect it to.  At the split diamond — the `(5,3)` diamond with one atom
split in two, which lies in the residual stratum and carries a parallel pair — the spectrum
of `N − 1` is `(4,4,6)`, the triple total is `−55`, the five-set total is `+224`, and
`σ_1 = 2/3`.  Both conditions hold with wide slack.  A direct search confirms the same:
under a hard collinearity bound `cos² ≤ 1 − ε` the tie residual `|max_T λ_min|` stalls at
`3.2e−2`, `9.2e−3`, `2.4e−3`, `1.7e−3` for `ε = 0.30, 0.10, 0.03, 0.01`, with the
collinearity constraint INACTIVE at every optimum, while the same code run at `(5,3)` —
where the hinge is refuted — reaches `3.0e−7`.  Four to five orders of magnitude, and the
obstruction is not the constraint.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.CauchyBinetLayerSum
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Part 1 — the layer law at every subset size

The shipped `Gtz.sum_principalMinorTotal_subsetSum_eq` is this statement with
`chosenCard = k`.  Its proof uses Cauchy–Binet to move `e_level` off the `rank × rank` atom
sum and onto the `|T| × |T|` Gram block, reindexes the block's minors as the whole Gram's
minors over subsets of `T`, and double-counts.  Not one of the three steps knows the size
of `T`. -/

/-- **THE LAYER LAW AT EVERY SUBSET SIZE.**  Summing `e_level` of the selected atom sum over
all subsets of a FIXED size multiplies `e_level` of the whole unweighted moment by the
number of such subsets containing a given `level`-subset:

    `Σ_{|T| = r} e_level(S_T) = C(size − level, r − level) · e_level(N)` .

No design hypothesis and no weight: this holds for any `size` vectors in `ℝ^rank`. -/
theorem sum_principalMinorTotal_subsetSum_layer (D : WeightedDesign m k)
    (chosenCard level : ℕ) (hlevel : level ≤ chosenCard) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard chosenCard,
        principalMinorTotal (subsetSum D selected) level
      = (((m - level).choose (chosenCard - level) : ℕ) : ℝ)
        * principalMinorTotal (subsetSum D Finset.univ) level := by
  classical
  have hblock : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard chosenCard,
      principalMinorTotal (subsetSum D selected) level
        = ∑ inner ∈ selected.powersetCard level,
            ((atomGramMatrix D).submatrix
              (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)
              (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)).det := by
    intro selected _
    rw [← transpose_mul_selectedRowFrame D selected,
      ← sum_det_principalMinors_mul_transpose_comm (selectedRowFrame D selected) level,
      selectedRowFrame_mul_transpose]
    exact sum_det_principalSubmatrix_subtype (atomGramMatrix D) selected level
  have hmoment : principalMinorTotal (subsetSum D Finset.univ) level
      = principalMinorTotal (atomGramMatrix D) level := by
    rw [← transpose_mul_atomRowFrame D,
      ← sum_det_principalMinors_mul_transpose_comm (atomRowFrame D) level, atomGramMatrix]
  have hcount := sum_powersetCard_sum_powersetCard (indexType := Fin m) (baseRing := ℝ)
    chosenCard level hlevel (fun inner => ((atomGramMatrix D).submatrix
      (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)
      (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)).det)
  rw [Finset.sum_congr rfl hblock, hcount, hmoment, principalMinorTotal, Fintype.card_fin,
    nsmul_eq_mul]

/-- **ABOVE THE SUBSET SIZE THE LAYER VANISHES.**  A Gram block of size `r` carries no
minor of size above `r`, so the layer total is zero.  This is the branch the shipped
statement could not reach, and it is what lets the profile run BELOW the rank. -/
theorem sum_principalMinorTotal_subsetSum_layer_of_lt (D : WeightedDesign m k)
    {chosenCard level : ℕ} (hlt : chosenCard < level) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard chosenCard,
        principalMinorTotal (subsetSum D selected) level = 0 := by
  classical
  refine Finset.sum_eq_zero fun selected hselected => ?_
  have hcard : selected.card = chosenCard := (Finset.mem_powersetCard.mp hselected).2
  have hblock : principalMinorTotal (subsetSum D selected) level
      = ∑ inner ∈ selected.powersetCard level,
          ((atomGramMatrix D).submatrix
            (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)
            (Subtype.val : { atomIndex // atomIndex ∈ inner } → Fin m)).det := by
    rw [← transpose_mul_selectedRowFrame D selected,
      ← sum_det_principalMinors_mul_transpose_comm (selectedRowFrame D selected) level,
      selectedRowFrame_mul_transpose]
    exact sum_det_principalSubmatrix_subtype (atomGramMatrix D) selected level
  rw [hblock, Finset.powersetCard_eq_empty.mpr (by rw [hcard]; exact hlt), Finset.sum_empty]

/-- **THE SUBSET-DETERMINANT PROFILE, AT OR ABOVE THE RANK.**  For every subset size at
least the rank, the aggregate of the gap determinants is a fixed integral combination of
the elementary symmetric functions of the unweighted second moment.  Neither side mentions
a weight.  At `r = k` this is the shipped `Gtz.sum_det_subsetSum_sub_one_eq`. -/
theorem sum_det_subsetSum_sub_one_layer (D : WeightedDesign m k) {chosenCard : ℕ}
    (hcard : k ≤ chosenCard) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard chosenCard,
        (subsetSum D selected - 1).det
      = ∑ level ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ (k + level) * (((m - level).choose (chosenCard - level) : ℕ) : ℝ)
            * principalMinorTotal (subsetSum D Finset.univ) level := by
  have hexpand : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard chosenCard,
      (subsetSum D selected - 1).det
        = ∑ level ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ (k + level) * principalMinorTotal (subsetSum D selected) level := by
    intro selected _
    have hshifted := det_sub_one_eq_sum_signed_principalMinorTotal (subsetSum D selected)
    rwa [Fintype.card_fin] at hshifted
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun level hlevel => ?_
  rw [← Finset.mul_sum,
    sum_principalMinorTotal_subsetSum_layer D chosenCard level
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel)) hcard),
    ← mul_assoc]

/-! ## Part 1b — what the layers ARE

The layer `e_level(N)` is not an abstract invariant.  Cauchy–Binet identifies it with the
total of the `level`-sized Gram minors of the atoms, so `e_1` is the total leverage, `e_2`
the total squared pair area, and `e_3` the total squared triple volume.  Every reading below
can therefore be transcribed into the campaign's own pair and triple vocabulary. -/

/-- **THE LAYERS OF THE MOMENT ARE THE GRAM MINOR TOTALS.**  `e_level(N)` is the sum of the
`level`-sized principal minors of the ATOM GRAM, which for `level = 1, 2, 3` is the total
leverage, the total squared pair area `Σ_{a<b} w_ab`, and the total squared triple volume
`Σ_{|T| = 3} [T]²`. -/
theorem principalMinorTotal_subsetSum_univ_eq_gram (D : WeightedDesign m k) (level : ℕ) :
    principalMinorTotal (subsetSum D Finset.univ) level
      = principalMinorTotal (atomGramMatrix D) level := by
  rw [← transpose_mul_atomRowFrame D,
    ← sum_det_principalMinors_mul_transpose_comm (atomRowFrame D) level, atomGramMatrix]

/-- The first layer is the total leverage. -/
theorem trace_subsetSum_univ_eq_sum_leverage (D : WeightedDesign m k) :
    Matrix.trace (subsetSum D Finset.univ) = ∑ label, leverageOf (D.atom label) := by
  have hgram := principalMinorTotal_subsetSum_univ_eq_gram D 1
  rw [principalMinorTotal_one, principalMinorTotal_one] at hgram
  rw [hgram, Matrix.trace]
  refine Finset.sum_congr rfl fun label _ => ?_
  show atomGramMatrix D label label = leverageOf (D.atom label)
  rw [atomGramMatrix_apply, leverageOf_eq_dotProduct]

/-- **THE TOP LAYER IS THE WHOLE GAP.**  At subset size equal to the ground set there is a
single term, and the profile returns `det(N − 1)`.  Every layer count is one there, so this
is the consistency check on the whole law, at every cell. -/
theorem sum_det_gap_topLayer (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard m,
        (subsetSum D selected - 1).det
      = (subsetSum D Finset.univ - 1).det := by
  classical
  have hsingle : (Finset.univ : Finset (Fin m)).powersetCard m
      = {(Finset.univ : Finset (Fin m))} := by
    ext chosen
    simp only [Finset.mem_powersetCard, Finset.mem_singleton, Finset.subset_univ, true_and]
    constructor
    · intro hchosen
      exact Finset.eq_univ_of_card chosen (by rw [hchosen, Fintype.card_fin])
    · intro hchosen
      rw [hchosen, Finset.card_univ, Fintype.card_fin]
  rw [hsingle, Finset.sum_singleton]

/-! ## Part 2 — the four readings at `(6,3)`

The layer counts are the whole content.  A `j`-subset lies in `C(6 − j, r − j)` of the
`r`-subsets, and the sign is `(−1)^{3 + j}`. -/

section SixThree

variable (D : WeightedDesign 6 3)

/-- The determinant layer of the whole moment, named. -/
theorem principalMinorTotal_three_univ_sixThree :
    principalMinorTotal (subsetSum D Finset.univ) 3 = (subsetSum D Finset.univ).det := by
  have hcard := principalMinorTotal_card (subsetSum D Finset.univ)
  rwa [Fintype.card_fin] at hcard

/-- **THE FIVE-SET AGGREGATE AT `(6,3)`.**  The six five-sets total

    `Σ_{|F| = 5} det(S_F − 1) = 3·det N − 4·e_2(N) + 5·tr N − 6` ,

the layer counts being `C(3,2) = 3`, `C(4,3) = 4`, `C(5,4) = 5` and `C(6,5) = 6`.  This is
the size the open `(6,3)` stratum carries a hypothesis about, and no shipped statement
reaches it. -/
theorem sum_det_gap_fiveSets_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
        (subsetSum D selected - 1).det
      = 3 * (subsetSum D Finset.univ).det
        - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 5 * Matrix.trace (subsetSum D Finset.univ) - 6 := by
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 5) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    principalMinorTotal_three_univ_sixThree, principalMinorTotal_one, principalMinorTotal_zero]
    at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE FOUR-SET AGGREGATE AT `(6,3)`.**  The fifteen four-sets total

    `Σ_{|Q| = 4} det(S_Q − 1) = 3·det N − 6·e_2(N) + 10·tr N − 15` . -/
theorem sum_det_gap_fourSets_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 4,
        (subsetSum D selected - 1).det
      = 3 * (subsetSum D Finset.univ).det
        - 6 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 10 * Matrix.trace (subsetSum D Finset.univ) - 15 := by
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 4) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    principalMinorTotal_three_univ_sixThree, principalMinorTotal_one, principalMinorTotal_zero]
    at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE SIX-SET AGGREGATE IS THE WHOLE GAP.**  The profile at `r = size` must return
`det(N − 1)`, and it does: `det N − e_2(N) + tr N − 1`.  This is a consistency check on the
layer counts, all four of which are one at `r = 6`. -/
theorem sum_det_gap_sixSets_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 6,
        (subsetSum D selected - 1).det
      = (subsetSum D Finset.univ).det
        - principalMinorTotal (subsetSum D Finset.univ) 2
        + Matrix.trace (subsetSum D Finset.univ) - 1 := by
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 6) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    principalMinorTotal_three_univ_sixThree, principalMinorTotal_one, principalMinorTotal_zero]
    at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE PAIR AGGREGATE AT `(6,3)`.**  Below the rank the top layer drops out, and the
fifteen pairs total

    `Σ_{|T| = 2} det(S_T − 1) = −e_2(N) + 5·tr N − 15` .

Because `det(S_{ab} − 1) = −pairGapMinor(g_a, g_b)`
(`Gtz.det_subsetSum_pairGap_eq_neg_pairGapMinor`), the fifteen pair minors total
`e_2(N) − 5·tr N + 15`.  The campaign owns only the WEIGHTED pair-minor total
`Σ_{a,b} t_a t_b q_ab = k² − 3k + 1`; this is the unweighted one, and it is a spectral
invariant of `N`. -/
theorem sum_det_gap_pairs_sixThree :
    ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
        (subsetSum D selected - 1).det
      = - principalMinorTotal (subsetSum D Finset.univ) 2
        + 5 * Matrix.trace (subsetSum D Finset.univ) - 15 := by
  have hexpand : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
      (subsetSum D selected - 1).det
        = ∑ level ∈ Finset.range 4,
            (-1 : ℝ) ^ (3 + level) * principalMinorTotal (subsetSum D selected) level := by
    intro selected _
    have hshifted := det_sub_one_eq_sum_signed_principalMinorTotal (subsetSum D selected)
    rwa [Fintype.card_fin] at hshifted
  have hsplit : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
      (subsetSum D selected - 1).det
      = ∑ level ∈ Finset.range 4, (-1 : ℝ) ^ (3 + level)
          * ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
              principalMinorTotal (subsetSum D selected) level := by
    rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
    exact Finset.sum_congr rfl fun level _ => (Finset.mul_sum _ _ _).symm
  have htop : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2,
      principalMinorTotal (subsetSum D selected) 3 = 0 :=
    sum_principalMinorTotal_subsetSum_layer_of_lt D (by norm_num)
  have hzero := sum_principalMinorTotal_subsetSum_layer D 2 0 (by norm_num)
  have hone := sum_principalMinorTotal_subsetSum_layer D 2 1 (by norm_num)
  have htwo := sum_principalMinorTotal_subsetSum_layer D 2 2 (by norm_num)
  rw [principalMinorTotal_zero] at hzero
  rw [principalMinorTotal_one] at hone
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    htop, hzero, hone, htwo] at hsplit
  rw [hsplit]
  norm_num [Nat.choose]
  ring

end SixThree

/-! ## Part 2b — the other rank-three cells

The same four layer counts at `(5,3)` and `(7,3)`.  The `(5,3)` triple reading is the one
the diamond calibrates: at the diamond `N = 5·1`, so the reading is
`125 − 3·75 + 6·15 − 10 = −20`, and every one of its ten triples is a weak dominator with a
vanishing gap determinant except the two that are strictly refused. -/

/-- **THE TRIPLE AGGREGATE AT `(5,3)`.**  Ten triples, layer counts `C(5,3) = 10`,
`C(4,2) = 6`, `C(3,1) = 3`, `C(2,0) = 1`. -/
theorem sum_det_gap_triples_fiveThree (D : WeightedDesign 5 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3,
        (subsetSum D selected - 1).det
      = (subsetSum D Finset.univ).det
        - 3 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 6 * Matrix.trace (subsetSum D Finset.univ) - 10 := by
  have hcard : principalMinorTotal (subsetSum D Finset.univ) 3
      = (subsetSum D Finset.univ).det := by
    have h := principalMinorTotal_card (subsetSum D Finset.univ)
    rwa [Fintype.card_fin] at h
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hcard, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE CO-ATOM AGGREGATE AT `(5,3)`.**  The five four-sets. -/
theorem sum_det_gap_fourSets_fiveThree (D : WeightedDesign 5 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 5)).powersetCard 4,
        (subsetSum D selected - 1).det
      = 2 * (subsetSum D Finset.univ).det
        - 3 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 4 * Matrix.trace (subsetSum D Finset.univ) - 5 := by
  have hcard : principalMinorTotal (subsetSum D Finset.univ) 3
      = (subsetSum D Finset.univ).det := by
    have h := principalMinorTotal_card (subsetSum D Finset.univ)
    rwa [Fintype.card_fin] at h
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 4) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hcard, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE TRIPLE AGGREGATE AT `(7,3)`.**  Thirty-five triples, layer counts `C(7,3) = 35`,
`C(6,2) = 15`, `C(5,1) = 5`, `C(4,0) = 1`. -/
theorem sum_det_gap_triples_sevenThree (D : WeightedDesign 7 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 3,
        (subsetSum D selected - 1).det
      = (subsetSum D Finset.univ).det
        - 5 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 15 * Matrix.trace (subsetSum D Finset.univ) - 35 := by
  have hcard : principalMinorTotal (subsetSum D Finset.univ) 3
      = (subsetSum D Finset.univ).det := by
    have h := principalMinorTotal_card (subsetSum D Finset.univ)
    rwa [Fintype.card_fin] at h
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hcard, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-- **THE CO-ATOM AGGREGATE AT `(7,3)`.**  The seven six-sets. -/
theorem sum_det_gap_sixSets_sevenThree (D : WeightedDesign 7 3) :
    ∑ selected ∈ (Finset.univ : Finset (Fin 7)).powersetCard 6,
        (subsetSum D selected - 1).det
      = 4 * (subsetSum D Finset.univ).det
        - 5 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 6 * Matrix.trace (subsetSum D Finset.univ) - 7 := by
  have hcard : principalMinorTotal (subsetSum D Finset.univ) 3
      = (subsetSum D Finset.univ).det := by
    have h := principalMinorTotal_card (subsetSum D Finset.univ)
    rwa [Fintype.card_fin] at h
  have hexpanded := sum_det_subsetSum_sub_one_layer D (chosenCard := 6) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    hcard, principalMinorTotal_one, principalMinorTotal_zero] at hexpanded
  rw [hexpanded]
  norm_num [Nat.choose]
  ring

/-! ## Part 3 — the tie readings

Two hypotheses of the open `(6,3)` stratum become two scalar inequalities on the spectrum
of the unweighted moment. -/

/-- **A REFUSED TRIPLE OF AN ADMISSIBLE HEAVY PAIR HAS NONPOSITIVE GAP DETERMINANT.**  The
Sylvester chain decides strict domination by three signs, and two of them are the
hypotheses, so the third carries the refusal.  Without an admissible heavy pair a refused
triple can still have a positive determinant, with two of the three signs negative — which
is why this bridge is stated and not assumed. -/
theorem tripleGapDet_nonpos_of_not_posDef (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : 1 < leverageOf (D.atom x))
    (hadmissible : 0 < pairGapMinor (D.atom x) (D.atom y))
    (hrefused : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  by_contra hpositive
  push Not at hpositive
  exact hrefused ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mpr
    ⟨by linarith, hadmissible, hpositive⟩)

/-- **THE TIE BOUND ON THE MOMENT SPECTRUM.**  When no triple's gap determinant is
positive, the twenty-triple aggregate is nonpositive, and the shipped layer law reads that
as one inequality in the elementary symmetric functions of `N`:

    `det N − 4·e_2(N) + 10·tr N − 20 ≤ 0` .

In the eigenvalues `ν` of `N − 1` this is `E_3 − 3E_2 + 3E_1 − 1 ≤ 0`. -/
theorem moment_spectral_bound_of_forall_det_nonpos (D : WeightedDesign 6 3)
    (hnonpos : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0) :
    (subsetSum D Finset.univ).det
        - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 10 * Matrix.trace (subsetSum D Finset.univ) - 20 ≤ 0 := by
  have haggregate := sum_det_subsetSum_sub_one_sixThree_eq D
  have htotal : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0 := Finset.sum_nonpos hnonpos
  linarith [haggregate, htotal]

/-- **THE FIVE-SET BOUND ON THE MOMENT SPECTRUM.**  When every five-set dominates strictly,
the six-term aggregate is positive:

    `0 < 3·det N − 4·e_2(N) + 5·tr N − 6` ,

which in the eigenvalues `ν` of `N − 1` is `3E_3 > E_2`, that is `tr((N − 1)⁻¹) < 3`. -/
theorem moment_spectral_bound_of_forall_fiveSet_posDef (D : WeightedDesign 6 3)
    (hstrict : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
      (subsetSum D selected - 1).PosDef) :
    0 < 3 * (subsetSum D Finset.univ).det
        - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 5 * Matrix.trace (subsetSum D Finset.univ) - 6 := by
  classical
  have hnonempty : ((Finset.univ : Finset (Fin 6)).powersetCard 5).Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    rw [Finset.card_univ, Fintype.card_fin]
    norm_num
  have htotal : 0 < ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
      (subsetSum D selected - 1).det :=
    Finset.sum_pos (fun selected hselected => (hstrict selected hselected).det_pos) hnonempty
  have haggregate := sum_det_gap_fiveSets_sixThree D
  linarith [haggregate, htotal]

/-- **THE WINDOW.**  The two hypotheses of the open `(6,3)` stratum together confine the
unweighted moment to an explicit region of the three-dimensional space of its elementary
symmetric functions.  Both bounds are spectral: no weight and no atom survives.

This is a REDUCTION and not a closure.  The window is not empty — the split diamond sits in
it with wide slack — so no successor should route a kill through these two inequalities
alone. -/
theorem spectral_window_of_isTie_sixThree (D : WeightedDesign 6 3)
    (hnonpos : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0)
    (hstrict : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
      (subsetSum D selected - 1).PosDef) :
    (subsetSum D Finset.univ).det
          - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
          + 10 * Matrix.trace (subsetSum D Finset.univ) - 20 ≤ 0
      ∧ 0 < 3 * (subsetSum D Finset.univ).det
          - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
          + 5 * Matrix.trace (subsetSum D Finset.univ) - 6 :=
  ⟨moment_spectral_bound_of_forall_det_nonpos D hnonpos,
    moment_spectral_bound_of_forall_fiveSet_posDef D hstrict⟩

/-- **THE `e_2` LAYER CANCELS BETWEEN THE TWO BOUNDS.**  Both aggregates carry the same
coefficient `−4` on `e_2(N)`, so the difference of the two hypotheses is free of it:

    `−14 < 2·det N − 5·tr N` .

The `e_2` layer is the only place the PAIR geometry enters the profile, and it drops out of
the difference entirely.  That is the structural reason this pair of aggregates cannot
close the stratum: a parallel pair is a vanishing `2 × 2` Gram minor, and the two bounds
that the tie and the five-sets supply see that minor only through one shared coefficient. -/
theorem e_two_cancels_in_the_window (D : WeightedDesign 6 3)
    (hnonpos : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0)
    (hstrict : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 5,
      (subsetSum D selected - 1).PosDef) :
    -14 < 2 * (subsetSum D Finset.univ).det
      - 5 * Matrix.trace (subsetSum D Finset.univ) := by
  obtain ⟨hlow, hhigh⟩ := spectral_window_of_isTie_sixThree D hnonpos hstrict
  linarith

/-- **THE EQUALITY CASE IS TOTAL RIGIDITY.**  The triple aggregate is a sum of twenty
nonpositive terms, so it vanishes only when EVERY one of the twenty gap determinants
vanishes — every triple exactly on the boundary of strict domination at once.  So a design
saturating the spectral bound is pinned by twenty equations, and a design that refuses even
one triple strictly sits below the bound. -/
theorem forall_det_gap_eq_zero_of_moment_spectral_bound_eq (D : WeightedDesign 6 3)
    (hnonpos : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0)
    (hsaturate : (subsetSum D Finset.univ).det
      - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
      + 10 * Matrix.trace (subsetSum D Finset.univ) - 20 = 0) :
    ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det = 0 := by
  classical
  have haggregate := sum_det_subsetSum_sub_one_sixThree_eq D
  have htotal : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det = 0 := by rw [haggregate, hsaturate]
  have hnegNonneg : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      0 ≤ -(subsetSum D selected - 1).det :=
    fun selected hselected => neg_nonneg.mpr (hnonpos selected hselected)
  have hnegTotal : ∑ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      -(subsetSum D selected - 1).det = 0 := by
    rw [Finset.sum_neg_distrib, htotal, neg_zero]
  intro selected hselected
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnegNonneg).mp hnegTotal selected hselected
  linarith

/-- **A STRICTLY REFUSED TRIPLE PUSHES THE DESIGN OFF THE BOUND.**  The contrapositive
reading: one triple with a strictly negative gap determinant forces the spectral bound to
be strict. -/
theorem moment_spectral_bound_strict_of_exists_neg (D : WeightedDesign 6 3)
    (hnonpos : ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (subsetSum D selected - 1).det ≤ 0)
    {witness : Finset (Fin 6)} (hmem : witness ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3)
    (hneg : (subsetSum D witness - 1).det < 0) :
    (subsetSum D Finset.univ).det
        - 4 * principalMinorTotal (subsetSum D Finset.univ) 2
        + 10 * Matrix.trace (subsetSum D Finset.univ) - 20 < 0 := by
  rcases lt_or_eq_of_le (moment_spectral_bound_of_forall_det_nonpos D hnonpos) with hlt | heq
  · exact hlt
  · exact absurd (forall_det_gap_eq_zero_of_moment_spectral_bound_eq D hnonpos heq witness hmem)
      (ne_of_lt hneg)

end Gtz
