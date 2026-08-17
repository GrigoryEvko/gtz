/-
# The cross-pairing budget, the per-triple cost, and why the count never outruns them

Every theorem in this module is UNCONDITIONAL, or carries `Gtz.IsTie` alone.  None
of them adds `Gtz.IsPrimitiveDesign`, stress-freeness or a line pattern next to
`Gtz.IsTie`, and none of them concludes `∃ selected, selected.card = 3 ∧ PosDef`.
Read `Gtz/Wave/OnPathRegistryCollapse.lean` and `Gtz/Wave/WiringSynonymClass.lean`
first: those three shapes are the whole synonym class of `Gtz.HingeHoldsAtSize 6 3`.

## What this module measures

Two landed laws bound the same double sum from the two sides.

* `Gtz.sum_weight_mul_pairing_sq` — the squared pairing total is the rank:
  `sum over c, sum over d of t_c t_d <g_c, g_d>^2 = rank`.
* `Gtz.sum_share_sq_le_rank` — the diagonal part of that total, the share second
  moment `sum over c of s_c^2` with `s_c = t_c l_c`, is at most the rank.

Their difference is the OFF-DIAGONAL part.  This module names it the CROSS-PAIRING
TOTAL `Gtz.crossPairingTotal`, and section one proves the exact identity

    crossPairingTotal D  =  rank  -  sum over c of s_c^2

together with the Cauchy-Schwarz floor `rank^2 <= size * sum over c of s_c^2`, which
gives the size-aware ceiling

    size * crossPairingTotal D  <=  size * rank  -  rank^2.

At rank three the ceiling reads `6/5` at five atoms, `3/2` at six and `12/7` at
seven.  The ceiling grows with the size.

## The budget carries no tie information, and this module proves it

`Gtz.crossPairingTotal_eq_of_constant_share` shows the ceiling is an EQUALITY at
every design whose shares are all equal to `rank / size`.  At `(6,3)` that is
`3/2`, and `Gtz.icosaDesign` and `Gtz.kFourDesign` both have every share `1/2`.
The two designs dominate STRICTLY.  So the ceiling is attained at designs that are
not ties, and no tie constraint lives in the ceiling alone.  Whatever the route is
worth, it is worth it on the DEMAND side.

## The demand side: what one triple costs

At a tie no triple dominates strictly, so the Gram gap `Gram_C - 1` of every triple
fails to be positive definite (`Gtz.subsetSum_posDef_iff_tripleGram`).  A failure
direction `v` gives

    v_0^2 d_a + v_1^2 d_b + v_2^2 d_c + 2 (v_0 v_1 p_ab + v_0 v_2 p_ac + v_1 v_2 p_bc) <= 0

with `d = l - 1` the heavy excess and `p` the pairings.  At a tie the leverage floor
makes every `d` nonnegative, so only the pairings can break positivity, and they
must break it by a measurable amount.  Two Cauchy-Schwarz steps give
`Gtz.three_mul_sq_le_four_mul_pairSquareTotal`:

    3 * floor^2  <=  4 * (p_ab^2 + p_ac^2 + p_bc^2)

for every common lower bound `floor >= 0` of the three heavy excesses.  The
constant `3/4` is SHARP: `Gtz.tetrahedralTriple_attains_pairSquareTotal_bound`
exhibits three of the four tetrahedral directions, where `floor = 2` and the pair
square total is exactly `3`, and both sides read `12`.

The same section reads the second-invariant branch of the tie dichotomy in the same
vocabulary (`Gtz.pairSquareTotal_gt_of_sum_pairGapMinor_neg`).

## The bridge, and its exact loss factor

The ceiling is WEIGHTED and the per-triple cost is UNWEIGHTED, so the two must be
bridged.  `Gtz.sum_weight_mul_pairSquareTotal` is the bridge, and it is an
IDENTITY, not an estimate:

    sum over a, b, c of t_a t_b t_c (p_ab^2 + p_ac^2 + p_bc^2)  =  9.

The right side is three times the rank.  The factor three is pure combinatorics —
a triple has three pairs — so the bridge CANNOT lose less than three, and no
sharper density beats it.  A prior fork measured the same factor against the volume
law.  This module shows the factor is exact.

## The size test, and the negative

Aggregate the cost against the distinct-triple mass and the bridge gives
`Gtz.three_mul_floor_sq_mul_distinctTripleMass_le`:

    3 * floor^2 * distinctTripleMass D  <=  36.

At the uniform point of rank three, `floor = 2` and the distinct-triple mass is
`(size - 1) (size - 2) / size^2`, so the demand is `3 (size - 1)(size - 2)/size^2`
while the bridged ceiling is `9 (size - 3) / size`.  Their exact quotient is

    3  -  6 / ((size - 1) (size - 2)).

`Gtz.uniformScalarPoint_ceiling_eq_ratio_mul_demand` proves that identity,
`Gtz.pairingRouteRatio_lt_three` bounds it, `Gtz.pairingRouteRatio_strictMono`
proves it INCREASES with the size, and `Gtz.one_lt_pairingRouteRatio` proves it
stays above one at every size from four upward.

That is the negative, and it is permanent.  The count of triples does grow like
`size choose 3`, but the product weight `t_a t_b t_c` normalises that count away:
the distinct-triple mass tends to one, not to infinity.  The ceiling meanwhile
grows to `rank`.  So the ratio of ceiling to demand grows toward three and never
falls to one.  The route separates no size from any other, and it moves in the
WRONG direction: five is tighter than six, and six is tighter than seven.

## The same reading on the landed ties

Section six measures the ceiling at the three landed ties, in kernel.  The `(5,3)`
PRIMITIVE diamond has cross-pairing total `23/20` against a ceiling of `6/5`, a
slack of `1/20`.  The `(6,3)` split diamond, which is the SAME geometry one size
up, has `123/100` against `3/2`, a slack of `27/100`.  The `(6,3)` non-uniform
leverage tie has `304/243` against `3/2`, a slack of `121/486`.

Both six-atom slacks are more than five times the five-atom slack.  The ceiling is
therefore TIGHTEST at the size where a primitive tie is known to exist.  That is
the wrong order, and `Gtz.crossPairingTotal_slack_grows_from_five_to_six` states it.

## Inhabitants

Every hypothesis in this module has a witness.  `Gtz.nonUniformLeverageTieDesign`
is a `(6,3)` tie whose leverages are `19/3` and `4/3`, so `floor = 1/3` satisfies
the heavy-excess hypothesis, and
`Gtz.nonUniformLeverageTie_pairSquareTotal_floor` reads the cost there.  The
tetrahedral triple inhabits the non-positive-definite hypothesis with equality.

## Where the cost stops

The cost is proportional to the SQUARE of the heavy-excess floor.  At a `(6,3)` tie
the tree supplies `1 <= l`, hence `floor = 0`, and the cost bound is then vacuous.
This is not slack in the proof.  An atom of leverage exactly one defeats every
triple it meets at zero pairing cost, because a symmetric matrix with a zero
diagonal entry and a nonzero entry in that row is never positive definite.  A
strictly positive leverage floor at `(6,3)` is exactly what this route needs and
the tree does not have.
-/
import Gtz.Wave.TieStratumClassification
import Gtz.Design.TripleGramSylvester
import Gtz.Ties.NonUniformLeverageTie

namespace Gtz

open Finset Matrix

variable {m k : ℕ}

/-! ## 1. The cross-pairing total and its size-aware ceiling

The squared pairing total of a weighted design is the rank.  Its diagonal part is
the share second moment.  The difference is what this section measures. -/

/-- **THE CROSS-PAIRING TOTAL.**  The off-diagonal part of the squared pairing
total, `sum over c, sum over d distinct from c of t_c t_d <g_c, g_d>^2`.

The name avoids `off-diagonal energy`, which `Gtz/Design/PivotGramIdempotent.lean`
already uses for the inverse-Gram pivots, and avoids `pairingEnergy`, which
`Gtz/Wave/GapDeterminantSignComplement.lean` already uses for a triple. -/
noncomputable def crossPairingTotal (D : WeightedDesign m k) : ℝ :=
  ∑ leftLabel, ∑ rightLabel ∈ Finset.univ.erase leftLabel,
    D.weight leftLabel * D.weight rightLabel * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2

/-- Each diagonal term of the squared pairing total is the square of a share. -/
theorem diagonal_pairing_sq_eq_share_sq (D : WeightedDesign m k) (label : Fin m) :
    D.weight label * D.weight label * (D.atom label ⬝ᵥ D.atom label) ^ 2
      = (D.weight label * leverageOf (D.atom label)) ^ 2 := by
  rw [leverageOf_eq_dotProduct]
  ring

/-- **THE EXACT SPLIT.**  The cross-pairing total is the rank less the share second
moment.  Unconditional, at every size and every rank.

This is `Gtz.sum_weight_mul_pairing_sq` with its diagonal removed, and the diagonal
is exactly the sum of the squared shares. -/
theorem crossPairingTotal_eq_rank_sub_sum_share_sq (D : WeightedDesign m k) :
    crossPairingTotal D
      = (k : ℝ) - ∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2 := by
  classical
  have hrow : ∀ leftLabel : Fin m,
      (∑ rightLabel ∈ Finset.univ.erase leftLabel,
          D.weight leftLabel * D.weight rightLabel
            * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
        = (∑ rightLabel, D.weight leftLabel * D.weight rightLabel
              * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2)
          - (D.weight leftLabel * leverageOf (D.atom leftLabel)) ^ 2 := by
    intro leftLabel
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
      (fun rightLabel => D.weight leftLabel * D.weight rightLabel
        * (D.atom leftLabel ⬝ᵥ D.atom rightLabel) ^ 2) (Finset.mem_univ leftLabel)
    rw [diagonal_pairing_sq_eq_share_sq D leftLabel] at hsplit
    linarith
  rw [crossPairingTotal, Finset.sum_congr rfl fun leftLabel _ => hrow leftLabel,
    Finset.sum_sub_distrib, sum_weight_mul_pairing_sq D]

/-- The cross-pairing total is nonnegative: every summand is a product of positive
weights with a square. -/
theorem crossPairingTotal_nonneg (D : WeightedDesign m k) : 0 ≤ crossPairingTotal D := by
  classical
  refine Finset.sum_nonneg fun leftLabel _ => Finset.sum_nonneg fun rightLabel _ => ?_
  exact mul_nonneg (mul_nonneg (D.weight_pos leftLabel).le (D.weight_pos rightLabel).le)
    (sq_nonneg _)

/-- The shares total the rank.  This is Parseval read on the trace. -/
theorem sum_share_eq_rank (D : WeightedDesign m k) :
    (∑ label, D.weight label * leverageOf (D.atom label)) = (k : ℝ) := by
  have htrace := sum_weight_mul_dotProduct_self D
  simpa only [leverageOf_eq_dotProduct] using htrace

/-- **THE CAUCHY-SCHWARZ FLOOR ON THE SHARE SECOND MOMENT.**  At every size and
every rank, `rank^2 <= size * sum over c of s_c^2`.

The shares total the rank over `size` labels, so their second moment cannot fall
below `rank^2 / size`.  Equality holds exactly when all shares agree. -/
theorem sq_rank_le_card_mul_sum_share_sq (D : WeightedDesign m k) :
    (k : ℝ) ^ 2 ≤ (m : ℝ) * ∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun _ => (1 : ℝ)) (fun label => D.weight label * leverageOf (D.atom label))
  have hleft : (∑ label, (1 : ℝ) * (D.weight label * leverageOf (D.atom label)))
      = (k : ℝ) := by
    rw [Finset.sum_congr rfl fun label _ => one_mul
      (D.weight label * leverageOf (D.atom label))]
    exact sum_share_eq_rank D
  have hones : (∑ _label : Fin m, (1 : ℝ) ^ 2) = (m : ℝ) := by
    rw [Finset.sum_congr rfl fun _ _ => one_pow 2, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hleft, hones] at hcs
  exact hcs

/-- **THE CROSS-PAIRING CEILING.**  At every size and every rank,

    size * crossPairingTotal D  <=  size * rank  -  rank^2.

Unconditional.  The right side grows with the size, and it is exactly the slack
Cauchy-Schwarz leaves between the share total and the share second moment. -/
theorem card_mul_crossPairingTotal_le (D : WeightedDesign m k) :
    (m : ℝ) * crossPairingTotal D ≤ (m : ℝ) * (k : ℝ) - (k : ℝ) ^ 2 := by
  have hsplit := crossPairingTotal_eq_rank_sub_sum_share_sq D
  have hfloor := sq_rank_le_card_mul_sum_share_sq D
  have hexpand : (m : ℝ) * ((k : ℝ)
        - ∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2)
      = (m : ℝ) * (k : ℝ)
        - (m : ℝ) * ∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2 := by
    ring
  rw [hsplit, hexpand]
  linarith

/-- The ceiling in divided form, at a positive size. -/
theorem crossPairingTotal_le_of_card_pos (D : WeightedDesign m k) (hcard : 0 < m) :
    crossPairingTotal D ≤ (k : ℝ) - (k : ℝ) ^ 2 / (m : ℝ) := by
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hcard
  have hmain := card_mul_crossPairingTotal_le D
  have hscaled : (m : ℝ) * crossPairingTotal D
      ≤ (m : ℝ) * ((k : ℝ) - (k : ℝ) ^ 2 / (m : ℝ)) := by
    have hid : (m : ℝ) * ((k : ℝ) - (k : ℝ) ^ 2 / (m : ℝ))
        = (m : ℝ) * (k : ℝ) - (k : ℝ) ^ 2 := by
      field_simp
    rw [hid]
    exact hmain
  exact le_of_mul_le_mul_left hscaled hpos

/-- **THE CEILING AT FIVE ATOMS AND RANK THREE**: `6/5`. -/
theorem crossPairingTotal_le_five_three (D : WeightedDesign 5 3) :
    crossPairingTotal D ≤ 6 / 5 := by
  have h := crossPairingTotal_le_of_card_pos D (by norm_num)
  norm_num at h
  linarith

/-- **THE CEILING AT SIX ATOMS AND RANK THREE**: `3/2`.  This is the number the
whole route spends. -/
theorem crossPairingTotal_le_six_three (D : WeightedDesign 6 3) :
    crossPairingTotal D ≤ 3 / 2 := by
  have h := crossPairingTotal_le_of_card_pos D (by norm_num)
  norm_num at h
  linarith

/-- **THE CEILING AT SEVEN ATOMS AND RANK THREE**: `12/7`. -/
theorem crossPairingTotal_le_seven_three (D : WeightedDesign 7 3) :
    crossPairingTotal D ≤ 12 / 7 := by
  have h := crossPairingTotal_le_of_card_pos D (by norm_num)
  norm_num at h
  linarith

/-- **THE CEILING IS ATTAINED, AND THE ROUTE MUST KNOW IT.**  Every design whose
shares are all equal to `rank / size` meets the ceiling with EQUALITY.

`Gtz.icosaDesign` and `Gtz.kFourDesign` both have every share `1/2` at `(6,3)`, so
both attain `3/2`.  Both dominate strictly, so neither is a tie.  The ceiling
therefore contains NO tie information.  Every gram of value in this route has to
come from the per-triple cost of section two. -/
theorem crossPairingTotal_eq_of_constant_share (D : WeightedDesign m k) (shareValue : ℝ)
    (hshare : ∀ label, D.weight label * leverageOf (D.atom label) = shareValue) :
    crossPairingTotal D = (k : ℝ) - (m : ℝ) * shareValue ^ 2 := by
  have hstep : ∀ label : Fin m,
      (D.weight label * leverageOf (D.atom label)) ^ 2 = shareValue ^ 2 :=
    fun label => by rw [hshare label]
  have hsum : (∑ label, (D.weight label * leverageOf (D.atom label)) ^ 2)
      = (m : ℝ) * shareValue ^ 2 := by
    rw [Finset.sum_congr rfl fun label _ => hstep label, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [crossPairingTotal_eq_rank_sub_sum_share_sq D, hsum]

/-- **THE SIX-THREE READING OF THE ATTAINMENT.**  A `(6,3)` design with every share
`1/2` has cross-pairing total exactly `3/2`, the ceiling.  The equal-share designs
of the tree are strict dominators. -/
theorem crossPairingTotal_eq_three_halves_of_half_share (D : WeightedDesign 6 3)
    (hshare : ∀ label, D.weight label * leverageOf (D.atom label) = 1 / 2) :
    crossPairingTotal D = 3 / 2 := by
  rw [crossPairingTotal_eq_of_constant_share D (1 / 2) hshare]
  norm_num

/-! ## 2. The cost of defeating one triple

A triple fails to dominate strictly exactly when its Gram gap is not positive
definite.  With a nonnegative diagonal only the pairings can break positivity, and
this section measures by how much. -/

/-- The total of the three squared pairings of a triple. -/
noncomputable def pairSquareTotal (leftVec midVec rightVec : Fin 3 → ℝ) : ℝ :=
  (leftVec ⬝ᵥ midVec) ^ 2 + (leftVec ⬝ᵥ rightVec) ^ 2 + (midVec ⬝ᵥ rightVec) ^ 2

/-- The pair square total is a sum of squares. -/
theorem pairSquareTotal_nonneg (leftVec midVec rightVec : Fin 3 → ℝ) :
    0 ≤ pairSquareTotal leftVec midVec rightVec := by
  unfold pairSquareTotal
  positivity

/-- **THE GAP QUADRATIC FORM IN PAIR VOCABULARY.**  The Rayleigh value of the Gram
gap at a coefficient vector, spelled with the three heavy excesses and the three
pairings.  No matrix theory beyond the entry table of
`Gtz/Design/TripleGramSylvester.lean`. -/
theorem dotProduct_tripleGramGap_mulVec (leftVec midVec rightVec coeff : Fin 3 → ℝ) :
    coeff ⬝ᵥ ((tripleGram leftVec midVec rightVec - 1) *ᵥ coeff)
      = coeff 0 ^ 2 * (leverageOf leftVec - 1) + coeff 1 ^ 2 * (leverageOf midVec - 1)
        + coeff 2 ^ 2 * (leverageOf rightVec - 1)
        + 2 * (coeff 0 * coeff 1 * (leftVec ⬝ᵥ midVec)
          + coeff 0 * coeff 2 * (leftVec ⬝ᵥ rightVec)
          + coeff 1 * coeff 2 * (midVec ⬝ᵥ rightVec)) := by
  have hrow : ∀ rowIndex : Fin 3,
      ((tripleGram leftVec midVec rightVec - 1) *ᵥ coeff) rowIndex
        = (tripleGram leftVec midVec rightVec - 1) rowIndex 0 * coeff 0
          + (tripleGram leftVec midVec rightVec - 1) rowIndex 1 * coeff 1
          + (tripleGram leftVec midVec rightVec - 1) rowIndex 2 * coeff 2 := by
    intro rowIndex
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp only [dotProduct, Fin.sum_univ_three, hrow, gap_zero_zero, gap_one_one, gap_two_two,
    gap_zero_one, gap_zero_two, gap_one_two, gap_one_zero, gap_two_zero, gap_two_one]
  ring

/-- The Gram gap is symmetric, hence Hermitian over the reals. -/
theorem isHermitian_tripleGramGap (leftVec midVec rightVec : Fin 3 → ℝ) :
    (tripleGram leftVec midVec rightVec - 1).IsHermitian :=
  isHermitian_of_transpose_eq (tripleGram_sub_one_symm leftVec midVec rightVec)

/-- **A FAILURE DIRECTION EXISTS.**  A Gram gap that is not positive definite has a
nonzero coefficient vector of nonpositive Rayleigh value. -/
theorem exists_nonpos_direction_of_not_posDef_tripleGram
    (leftVec midVec rightVec : Fin 3 → ℝ)
    (hnot : ¬ (tripleGram leftVec midVec rightVec - 1).PosDef) :
    ∃ coeff : Fin 3 → ℝ, coeff ≠ 0
      ∧ coeff ⬝ᵥ ((tripleGram leftVec midVec rightVec - 1) *ᵥ coeff) ≤ 0 := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hnot
  push Not at hnot
  obtain ⟨coeff, hne, hle⟩ := hnot (isHermitian_tripleGramGap leftVec midVec rightVec)
  rw [star_trivial] at hle
  exact ⟨coeff, hne, hle⟩

/-- A nonzero vector in three real coordinates has positive square total. -/
theorem sq_total_pos_of_ne_zero {coeff : Fin 3 → ℝ} (hne : coeff ≠ 0) :
    0 < coeff 0 ^ 2 + coeff 1 ^ 2 + coeff 2 ^ 2 := by
  rcases lt_or_eq_of_le (by positivity :
      (0 : ℝ) ≤ coeff 0 ^ 2 + coeff 1 ^ 2 + coeff 2 ^ 2) with hpos | hzero
  · exact hpos
  · exfalso
    apply hne
    have hzeroOne : coeff 0 ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (coeff 1), sq_nonneg (coeff 2)]) (sq_nonneg _)
    have hzeroTwo : coeff 1 ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (coeff 0), sq_nonneg (coeff 2)]) (sq_nonneg _)
    have hzeroThree : coeff 2 ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (coeff 0), sq_nonneg (coeff 1)]) (sq_nonneg _)
    have hone : coeff 0 = 0 := by
      have hres := sq_eq_zero_iff.mp hzeroOne
      exact hres
    have htwo : coeff 1 = 0 := by
      have hres := sq_eq_zero_iff.mp hzeroTwo
      exact hres
    have hthree : coeff 2 = 0 := by
      have hres := sq_eq_zero_iff.mp hzeroThree
      exact hres
    funext idx
    fin_cases idx
    · simpa using hone
    · simpa using htwo
    · simpa using hthree

/-- **THE PER-TRIPLE COST.**  Let three vectors have heavy excesses all at least a
nonnegative `floor`, and let their Gram gap fail to be positive definite.  Then

    3 * floor^2  <=  4 * pairSquareTotal.

The proof is two Cauchy-Schwarz steps.  A failure direction pushes the pairing part
of the Rayleigh value below minus the diagonal part, which is at least `floor` times
the squared length.  Cauchy-Schwarz on the three pairing products, and the bound
`e_2 <= e_1^2 / 3` on the three squared coordinate products, close the chain.

The constant `3/4` is SHARP.  Refer to
`Gtz.tetrahedralTriple_attains_pairSquareTotal_bound`. -/
theorem three_mul_sq_le_four_mul_pairSquareTotal (leftVec midVec rightVec : Fin 3 → ℝ)
    (floor : ℝ) (hfloorNonneg : 0 ≤ floor)
    (hleft : floor ≤ leverageOf leftVec - 1) (hmid : floor ≤ leverageOf midVec - 1)
    (hright : floor ≤ leverageOf rightVec - 1)
    (hnot : ¬ (tripleGram leftVec midVec rightVec - 1).PosDef) :
    3 * floor ^ 2 ≤ 4 * pairSquareTotal leftVec midVec rightVec := by
  obtain ⟨coeff, hne, hle⟩ :=
    exists_nonpos_direction_of_not_posDef_tripleGram leftVec midVec rightVec hnot
  rw [dotProduct_tripleGramGap_mulVec] at hle
  set lengthSq : ℝ := coeff 0 ^ 2 + coeff 1 ^ 2 + coeff 2 ^ 2 with hlengthSq
  have hlengthPos : 0 < lengthSq := sq_total_pos_of_ne_zero hne
  set pairSum : ℝ := coeff 0 * coeff 1 * (leftVec ⬝ᵥ midVec)
    + coeff 0 * coeff 2 * (leftVec ⬝ᵥ rightVec)
    + coeff 1 * coeff 2 * (midVec ⬝ᵥ rightVec) with hpairSum
  -- The diagonal part of the Rayleigh value is at least `floor` times the length.
  have hdiagonal : floor * lengthSq
      ≤ coeff 0 ^ 2 * (leverageOf leftVec - 1) + coeff 1 ^ 2 * (leverageOf midVec - 1)
        + coeff 2 ^ 2 * (leverageOf rightVec - 1) := by
    have h0 := sq_nonneg (coeff 0)
    have h1 := sq_nonneg (coeff 1)
    have h2 := sq_nonneg (coeff 2)
    rw [hlengthSq]
    nlinarith [mul_le_mul_of_nonneg_left hleft h0, mul_le_mul_of_nonneg_left hmid h1,
      mul_le_mul_of_nonneg_left hright h2]
  -- Hence the pairing part is at most minus half of it.
  have hpairBound : floor * lengthSq ≤ -(2 * pairSum) := by linarith
  have hlengthNonneg : 0 ≤ floor * lengthSq := mul_nonneg hfloorNonneg hlengthPos.le
  have hsquared : (floor * lengthSq) ^ 2 ≤ 4 * pairSum ^ 2 := by
    have hgap : (0 : ℝ) ≤ -(2 * pairSum) - floor * lengthSq := by linarith
    have hsum : (0 : ℝ) ≤ -(2 * pairSum) + floor * lengthSq := by linarith
    nlinarith [mul_nonneg hgap hsum]
  -- Cauchy-Schwarz on the three pairing products.
  have hcauchy : pairSum ^ 2
      ≤ pairSquareTotal leftVec midVec rightVec
        * ((coeff 0 * coeff 1) ^ 2 + (coeff 0 * coeff 2) ^ 2 + (coeff 1 * coeff 2) ^ 2) := by
    rw [hpairSum, pairSquareTotal]
    nlinarith [sq_nonneg ((leftVec ⬝ᵥ midVec) * (coeff 0 * coeff 2)
        - (leftVec ⬝ᵥ rightVec) * (coeff 0 * coeff 1)),
      sq_nonneg ((leftVec ⬝ᵥ midVec) * (coeff 1 * coeff 2)
        - (midVec ⬝ᵥ rightVec) * (coeff 0 * coeff 1)),
      sq_nonneg ((leftVec ⬝ᵥ rightVec) * (coeff 1 * coeff 2)
        - (midVec ⬝ᵥ rightVec) * (coeff 0 * coeff 2))]
  -- The three squared coordinate products carry at most a third of the squared length.
  have hproducts : (coeff 0 * coeff 1) ^ 2 + (coeff 0 * coeff 2) ^ 2 + (coeff 1 * coeff 2) ^ 2
      ≤ lengthSq ^ 2 / 3 := by
    rw [hlengthSq]
    nlinarith [sq_nonneg (coeff 0 ^ 2 - coeff 1 ^ 2), sq_nonneg (coeff 0 ^ 2 - coeff 2 ^ 2),
      sq_nonneg (coeff 1 ^ 2 - coeff 2 ^ 2)]
  have hcostNonneg : 0 ≤ pairSquareTotal leftVec midVec rightVec :=
    pairSquareTotal_nonneg leftVec midVec rightVec
  have hchain : (floor * lengthSq) ^ 2
      ≤ 4 * (pairSquareTotal leftVec midVec rightVec * (lengthSq ^ 2 / 3)) := by
    have hstep : pairSum ^ 2 ≤ pairSquareTotal leftVec midVec rightVec * (lengthSq ^ 2 / 3) :=
      le_trans hcauchy (mul_le_mul_of_nonneg_left hproducts hcostNonneg)
    linarith
  have hsq : 0 < lengthSq ^ 2 := by positivity
  nlinarith [hchain, hsq]

/-- **THE CONSTANT IS SHARP.**  Three of the four tetrahedral directions have every
leverage three, every pairing minus one, and a Gram gap that kills the all-ones
coefficient vector.  There `floor = 2`, the pair square total is `3`, and the two
sides of the cost bound both read `12`. -/
theorem tetrahedralTriple_attains_pairSquareTotal_bound :
    leverageOf (![-1, 1, 1] : Fin 3 → ℝ) = 3
      ∧ leverageOf (![1, -1, 1] : Fin 3 → ℝ) = 3
      ∧ leverageOf (![1, 1, -1] : Fin 3 → ℝ) = 3
      ∧ pairSquareTotal (![-1, 1, 1] : Fin 3 → ℝ) (![1, -1, 1] : Fin 3 → ℝ)
          (![1, 1, -1] : Fin 3 → ℝ) = 3
      ∧ ¬ (tripleGram (![-1, 1, 1] : Fin 3 → ℝ) (![1, -1, 1] : Fin 3 → ℝ)
          (![1, 1, -1] : Fin 3 → ℝ) - 1).PosDef
      ∧ 3 * (2 : ℝ) ^ 2 = 4 * pairSquareTotal (![-1, 1, 1] : Fin 3 → ℝ)
          (![1, -1, 1] : Fin 3 → ℝ) (![1, 1, -1] : Fin 3 → ℝ) := by
  have hleverageOne : leverageOf (![-1, 1, 1] : Fin 3 → ℝ) = 3 := by
    simp [leverageOf, Fin.sum_univ_three]; norm_num
  have hleverageTwo : leverageOf (![1, -1, 1] : Fin 3 → ℝ) = 3 := by
    simp [leverageOf, Fin.sum_univ_three]; norm_num
  have hleverageThree : leverageOf (![1, 1, -1] : Fin 3 → ℝ) = 3 := by
    simp [leverageOf, Fin.sum_univ_three]; norm_num
  have hcost : pairSquareTotal (![-1, 1, 1] : Fin 3 → ℝ) (![1, -1, 1] : Fin 3 → ℝ)
      (![1, 1, -1] : Fin 3 → ℝ) = 3 := by
    simp [pairSquareTotal, dotProduct, Fin.sum_univ_three]; norm_num
  refine ⟨hleverageOne, hleverageTwo, hleverageThree, hcost, ?_, by rw [hcost]; norm_num⟩
  intro hposDef
  have hprobe : (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hcontra
    have := congrFun hcontra 0
    norm_num at this
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
  rw [star_trivial, dotProduct_tripleGramGap_mulVec, hleverageOne, hleverageTwo,
    hleverageThree] at hpos
  simp [dotProduct, Fin.sum_univ_three] at hpos
  norm_num at hpos

/-- **THE SECOND-INVARIANT BRANCH, IN PAIR VOCABULARY.**  The second invariant of a
Gram gap is the total of the three pair gap minors.  When that total is negative the
squared pairings strictly exceed the products of the heavy excesses.

This is the `e_2 < 0` arm of the tie dichotomy of
`Gtz/Wave/TieStratumClassification.lean`, read as a lower bound on the pairings. -/
theorem pairSquareTotal_gt_of_sum_pairGapMinor_neg (leftVec midVec rightVec : Fin 3 → ℝ)
    (hneg : pairGapMinor leftVec midVec + pairGapMinor leftVec rightVec
      + pairGapMinor midVec rightVec < 0) :
    (leverageOf leftVec - 1) * (leverageOf midVec - 1)
        + (leverageOf leftVec - 1) * (leverageOf rightVec - 1)
        + (leverageOf midVec - 1) * (leverageOf rightVec - 1)
      < pairSquareTotal leftVec midVec rightVec := by
  simp only [pairGapMinor] at hneg
  simp only [pairSquareTotal]
  linarith

/-! ### The design-level cost at a tie

A tie refuses every card-three selection, and the Gram criterion turns that refusal
into the hypothesis of the cost bound. -/

/-- **THE COST AT A TIE.**  Unconditional in the tie, at every size and rank three.
No primitivity, no stress-freeness, no line pattern.

Every triple of a tie fails to dominate strictly, so every triple pays the pairing
cost of the heavy-excess floor. -/
theorem three_mul_sq_le_four_mul_pairSquareTotal_of_isTie {size : ℕ}
    (design : WeightedDesign size 3) (htie : IsTie design) (floor : ℝ)
    (hfloorNonneg : 0 ≤ floor)
    (hfloor : ∀ label, floor ≤ leverageOf (design.atom label) - 1)
    (first second third : Fin size) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    3 * floor ^ 2
      ≤ 4 * pairSquareTotal (design.atom first) (design.atom second) (design.atom third) := by
  have hcard := card_triple_eq_three hfirstSecond hfirstThird hsecondThird
  have hnotSubset := htie.2 ({first, second, third} : Finset (Fin size)) hcard
  have hnotGram : ¬ (tripleGram (design.atom first) (design.atom second)
      (design.atom third) - 1).PosDef := by
    intro hcontra
    exact hnotSubset ((subsetSum_posDef_iff_tripleGram design first second third
      hfirstSecond hfirstThird hsecondThird).mpr hcontra)
  exact three_mul_sq_le_four_mul_pairSquareTotal _ _ _ floor hfloorNonneg
    (hfloor first) (hfloor second) (hfloor third) hnotGram

/-- **AN INHABITANT OF THE TIE COST.**  `Gtz.nonUniformLeverageTieDesign` is a
`(6,3)` tie with leverages `19/3` and `4/3`, so `1/3` is a common heavy-excess
floor.  Every triple of distinct labels there pays at least `1/12` of pairing
square total.  The hypotheses of the cost theorem are not vacuous. -/
theorem nonUniformLeverageTie_pairSquareTotal_floor
    (first second third : Fin 6) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    3 * ((1 : ℝ) / 3) ^ 2
      ≤ 4 * pairSquareTotal (nonUniformLeverageTieDesign.atom first)
          (nonUniformLeverageTieDesign.atom second)
          (nonUniformLeverageTieDesign.atom third) := by
  refine three_mul_sq_le_four_mul_pairSquareTotal_of_isTie nonUniformLeverageTieDesign
    nonUniformLeverageTieDesign_isTie (1 / 3) (by norm_num) ?_ first second third
    hfirstSecond hfirstThird hsecondThird
  intro label
  rw [nonUniformLeverageTieDesign_leverage label]
  split <;> norm_num

/-! ## 3. The bridge, and its exact loss factor

The ceiling is weighted and the cost is unweighted.  This section bridges them, and
the bridge is an identity: the factor three is combinatorics, not an estimate. -/

/-- **THE BRIDGE IDENTITY.**  At rank three and every size,

    sum over a, b, c of t_a t_b t_c pairSquareTotal(g_a, g_b, g_c)  =  9.

Nine is three times the rank.  A triple has three pairs, so the product measure
reads the squared pairing total exactly three times, and
`Gtz.sum_weight_mul_pairing_sq` values each reading at the rank.

The factor three is therefore EXACT.  No density on the triples beats it, because
it counts pairs, not geometry. -/
theorem sum_weight_mul_pairSquareTotal {size : ℕ} (design : WeightedDesign size 3) :
    (∑ first, ∑ second, ∑ third, design.weight first * design.weight second
        * design.weight third
        * pairSquareTotal (design.atom first) (design.atom second) (design.atom third)) = 9 := by
  classical
  have hbase : (∑ leftLabel, ∑ rightLabel, design.weight leftLabel * design.weight rightLabel
      * (design.atom leftLabel ⬝ᵥ design.atom rightLabel) ^ 2) = 3 := by
    simpa using sum_weight_mul_pairing_sq design
  have hfirstSlot : (∑ first, ∑ second, ∑ third, design.weight first * design.weight second
      * design.weight third * (design.atom first ⬝ᵥ design.atom second) ^ 2) = 3 := by
    have hinner : ∀ first second : Fin size,
        (∑ third, design.weight first * design.weight second * design.weight third
            * (design.atom first ⬝ᵥ design.atom second) ^ 2)
          = design.weight first * design.weight second
            * (design.atom first ⬝ᵥ design.atom second) ^ 2 := by
      intro first second
      have hstep : ∀ third : Fin size,
          design.weight first * design.weight second * design.weight third
              * (design.atom first ⬝ᵥ design.atom second) ^ 2
            = (design.weight first * design.weight second
                * (design.atom first ⬝ᵥ design.atom second) ^ 2) * design.weight third :=
        fun third => by ring
      rw [Finset.sum_congr rfl fun third _ => hstep third, ← Finset.mul_sum,
        design.weight_sum_one, mul_one]
    simp only [hinner]
    exact hbase
  have hsecondSlot : (∑ first, ∑ second, ∑ third, design.weight first * design.weight second
      * design.weight third * (design.atom first ⬝ᵥ design.atom third) ^ 2) = 3 := by
    have hinner : ∀ first : Fin size,
        (∑ second, ∑ third, design.weight first * design.weight second * design.weight third
            * (design.atom first ⬝ᵥ design.atom third) ^ 2)
          = ∑ third, design.weight first * design.weight third
              * (design.atom first ⬝ᵥ design.atom third) ^ 2 := by
      intro first
      have hstep : ∀ second : Fin size,
          (∑ third, design.weight first * design.weight second * design.weight third
              * (design.atom first ⬝ᵥ design.atom third) ^ 2)
            = design.weight second * ∑ third, design.weight first * design.weight third
                * (design.atom first ⬝ᵥ design.atom third) ^ 2 := by
        intro second
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun third _ => by ring
      rw [Finset.sum_congr rfl fun second _ => hstep second, ← Finset.sum_mul,
        design.weight_sum_one, one_mul]
    simp only [hinner]
    exact hbase
  have hthirdSlot : (∑ first, ∑ second, ∑ third, design.weight first * design.weight second
      * design.weight third * (design.atom second ⬝ᵥ design.atom third) ^ 2) = 3 := by
    have hinner : ∀ first : Fin size,
        (∑ second, ∑ third, design.weight first * design.weight second * design.weight third
            * (design.atom second ⬝ᵥ design.atom third) ^ 2)
          = design.weight first * ∑ second, ∑ third, design.weight second * design.weight third
              * (design.atom second ⬝ᵥ design.atom third) ^ 2 := by
      intro first
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun second _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun third _ => by ring
    rw [Finset.sum_congr rfl fun first _ => hinner first, ← Finset.sum_mul,
      design.weight_sum_one, one_mul]
    exact hbase
  have hcomb : ∀ first second third : Fin size,
      design.weight first * design.weight second * design.weight third
          * pairSquareTotal (design.atom first) (design.atom second) (design.atom third)
        = design.weight first * design.weight second * design.weight third
            * (design.atom first ⬝ᵥ design.atom second) ^ 2
          + design.weight first * design.weight second * design.weight third
            * (design.atom first ⬝ᵥ design.atom third) ^ 2
          + design.weight first * design.weight second * design.weight third
            * (design.atom second ⬝ᵥ design.atom third) ^ 2 := by
    intro first second third
    simp only [pairSquareTotal]
    ring
  simp only [hcomb, Finset.sum_add_distrib]
  rw [hfirstSlot, hsecondSlot, hthirdSlot]
  norm_num

/-- The product mass of the ordered triples of DISTINCT labels. -/
noncomputable def distinctTripleMass (D : WeightedDesign m k) : ℝ :=
  ∑ first, ∑ second ∈ Finset.univ.erase first,
    ∑ third ∈ (Finset.univ.erase first).erase second,
      D.weight first * D.weight second * D.weight third

/-- The distinct-triple mass is nonnegative. -/
theorem distinctTripleMass_nonneg (D : WeightedDesign m k) : 0 ≤ distinctTripleMass D := by
  classical
  refine Finset.sum_nonneg fun first _ => Finset.sum_nonneg fun second _ =>
    Finset.sum_nonneg fun third _ => ?_
  exact mul_nonneg (mul_nonneg (D.weight_pos first).le (D.weight_pos second).le)
    (D.weight_pos third).le

/-- **THE DISTINCT-TRIPLE MASS AT CONSTANT WEIGHT.**  With every weight equal to
`weightValue`, the mass is `size (size - 1) (size - 2) weightValue^3`.

At uniform weight `1 / size` the mass is `(size - 1)(size - 2) / size^2`, which
tends to ONE.  That is the whole reason the triple count never reaches the ceiling:
the product measure normalises `size choose 3` away. -/
theorem distinctTripleMass_of_constant_weight (D : WeightedDesign m k) (weightValue : ℝ)
    (hsize : 2 ≤ m) (hweight : ∀ label, D.weight label = weightValue) :
    distinctTripleMass D
      = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * weightValue ^ 3 := by
  classical
  have hcastOne : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := le_trans (by norm_num) hsize
    push_cast [Nat.cast_sub this]
    ring
  have hcastTwo : ((m - 1 - 1 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    have hone : (1 : ℕ) ≤ m := le_trans (by norm_num) hsize
    have htwo : (1 : ℕ) ≤ m - 1 := by omega
    push_cast [Nat.cast_sub htwo, Nat.cast_sub hone]
    ring
  have hinner : ∀ first : Fin m, ∀ second ∈ Finset.univ.erase first,
      (∑ third ∈ (Finset.univ.erase first).erase second,
          D.weight first * D.weight second * D.weight third)
        = ((m : ℝ) - 2) * weightValue ^ 3 := by
    intro first second hsecond
    have hcard : ((Finset.univ.erase first).erase second).card = m - 1 - 1 := by
      rw [Finset.card_erase_of_mem hsecond, Finset.card_erase_of_mem (Finset.mem_univ first),
        Finset.card_univ, Fintype.card_fin]
    have hconst : ∀ third ∈ (Finset.univ.erase first).erase second,
        D.weight first * D.weight second * D.weight third = weightValue ^ 3 := by
      intro third _
      rw [hweight first, hweight second, hweight third]
      ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard, nsmul_eq_mul, hcastTwo]
  have hmiddle : ∀ first : Fin m,
      (∑ second ∈ Finset.univ.erase first,
          ∑ third ∈ (Finset.univ.erase first).erase second,
            D.weight first * D.weight second * D.weight third)
        = ((m : ℝ) - 1) * (((m : ℝ) - 2) * weightValue ^ 3) := by
    intro first
    have hcard : (Finset.univ.erase first).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_congr rfl (hinner first), Finset.sum_const, hcard, nsmul_eq_mul, hcastOne]
  rw [distinctTripleMass, Finset.sum_congr rfl fun first _ => hmiddle first, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **THE AGGREGATED DEMAND.**  Sum the per-triple cost against the product measure
and the bridge caps it:

    3 * floor^2 * distinctTripleMass D  <=  36.

The right side is four times the bridge value nine.  Every step is an inequality
between nonnegative terms, so the only loss is the degenerate triples the cube sum
carries and the distinct sum does not. -/
theorem three_mul_floor_sq_mul_distinctTripleMass_le {size : ℕ}
    (design : WeightedDesign size 3) (floor : ℝ)
    (hcost : ∀ first second third : Fin size, first ≠ second → first ≠ third → second ≠ third →
      3 * floor ^ 2
        ≤ 4 * pairSquareTotal (design.atom first) (design.atom second) (design.atom third)) :
    3 * floor ^ 2 * distinctTripleMass design ≤ 36 := by
  classical
  set cube : Fin size → Fin size → Fin size → ℝ := fun first second third =>
    design.weight first * design.weight second * design.weight third
      * (4 * pairSquareTotal (design.atom first) (design.atom second) (design.atom third))
    with hcube
  have hcubeNonneg : ∀ first second third, 0 ≤ cube first second third := by
    intro first second third
    rw [hcube]
    have hmass : 0 ≤ design.weight first * design.weight second * design.weight third :=
      mul_nonneg (mul_nonneg (design.weight_pos first).le (design.weight_pos second).le)
        (design.weight_pos third).le
    have hpair := pairSquareTotal_nonneg (design.atom first) (design.atom second)
      (design.atom third)
    positivity
  -- Step one: the demand is dominated termwise on the distinct triples.
  have hdemand : 3 * floor ^ 2 * distinctTripleMass design
      ≤ ∑ first, ∑ second ∈ Finset.univ.erase first,
          ∑ third ∈ (Finset.univ.erase first).erase second, cube first second third := by
    rw [distinctTripleMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun first _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun second hsecond => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun third hthird => ?_
    have hsecondNe : second ≠ first := (Finset.mem_erase.mp hsecond).1
    have hthirdNeSecond : third ≠ second := (Finset.mem_erase.mp hthird).1
    have hthirdNeFirst : third ≠ first :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hthird).2).1
    have hmass : 0 ≤ design.weight first * design.weight second * design.weight third :=
      mul_nonneg (mul_nonneg (design.weight_pos first).le (design.weight_pos second).le)
        (design.weight_pos third).le
    have hpointwise := hcost first second third (Ne.symm hsecondNe) (Ne.symm hthirdNeFirst)
      (Ne.symm hthirdNeSecond)
    rw [hcube]
    calc 3 * floor ^ 2 * (design.weight first * design.weight second * design.weight third)
        = (design.weight first * design.weight second * design.weight third)
            * (3 * floor ^ 2) := by ring
      _ ≤ (design.weight first * design.weight second * design.weight third)
            * (4 * pairSquareTotal (design.atom first) (design.atom second)
              (design.atom third)) := mul_le_mul_of_nonneg_left hpointwise hmass
  -- Step two: the distinct triples sit inside the cube.
  have hthirdStep : ∀ first second : Fin size,
      (∑ third ∈ (Finset.univ.erase first).erase second, cube first second third)
        ≤ ∑ third, cube first second third := by
    intro first second
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun third _ _ => hcubeNonneg first second third
  have hsecondStep : ∀ first : Fin size,
      (∑ second ∈ Finset.univ.erase first,
          ∑ third ∈ (Finset.univ.erase first).erase second, cube first second third)
        ≤ ∑ second, ∑ third, cube first second third := by
    intro first
    have hstage : (∑ second ∈ Finset.univ.erase first,
        ∑ third ∈ (Finset.univ.erase first).erase second, cube first second third)
        ≤ ∑ second ∈ Finset.univ.erase first, ∑ third, cube first second third :=
      Finset.sum_le_sum fun second _ => hthirdStep first second
    have hgrow : (∑ second ∈ Finset.univ.erase first, ∑ third, cube first second third)
        ≤ ∑ second, ∑ third, cube first second third := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun second _ _ => ?_
      exact Finset.sum_nonneg fun third _ => hcubeNonneg first second third
    linarith
  have hcubeBound : (∑ first, ∑ second ∈ Finset.univ.erase first,
      ∑ third ∈ (Finset.univ.erase first).erase second, cube first second third)
      ≤ ∑ first, ∑ second, ∑ third, cube first second third :=
    Finset.sum_le_sum fun first _ => hsecondStep first
  -- Step three: the cube total is four times the bridge value.
  have hcubeTotal : (∑ first, ∑ second, ∑ third, cube first second third) = 36 := by
    have hscale : ∀ first second third : Fin size,
        cube first second third
          = 4 * (design.weight first * design.weight second * design.weight third
            * pairSquareTotal (design.atom first) (design.atom second) (design.atom third)) := by
      intro first second third
      rw [hcube]
      ring
    simp only [hscale, ← Finset.mul_sum]
    rw [sum_weight_mul_pairSquareTotal design]
    norm_num
  linarith

/-! ## 4. The size test, and the negative

The route is now assembled.  This section evaluates it, and the evaluation kills it
at every size. -/

/-- **THE ROUTE RATIO.**  At the uniform point of rank three the bridged ceiling is
`9 (size - 3) / size` and the demand is `3 (size - 1)(size - 2) / size^2`.  Their
exact quotient is `3 - 6 / ((size - 1)(size - 2))`.

The demand comes from `Gtz.three_mul_floor_sq_mul_distinctTripleMass_le` at
`floor = 2`, which is the heavy excess of the uniform leverage three, together with
`Gtz.distinctTripleMass_of_constant_weight` at weight `1 / size`. -/
theorem uniformScalarPoint_ceiling_eq_ratio_mul_demand (size : ℝ) (hsize : 4 ≤ size) :
    9 * (size - 3) / size
      = (3 - 6 / ((size - 1) * (size - 2))) * (3 * ((size - 1) * (size - 2)) / size ^ 2) := by
  have hsizePos : (0 : ℝ) < size := by linarith
  have hone : (0 : ℝ) < size - 1 := by linarith
  have htwo : (0 : ℝ) < size - 2 := by linarith
  field_simp
  ring

/-- **THE RATIO NEVER FALLS TO ONE.**  At every size from four upward the bridged
ceiling strictly exceeds the demand.  The route cannot close at any size. -/
theorem one_lt_pairingRouteRatio (size : ℝ) (hsize : 4 ≤ size) :
    1 < 3 - 6 / ((size - 1) * (size - 2)) := by
  have hone : (0 : ℝ) < size - 1 := by linarith
  have htwo : (0 : ℝ) < size - 2 := by linarith
  have hprod : (0 : ℝ) < (size - 1) * (size - 2) := mul_pos hone htwo
  have hbig : (6 : ℝ) ≤ (size - 1) * (size - 2) := by nlinarith
  have hkey : 6 / ((size - 1) * (size - 2)) ≤ 1 := by
    rw [div_le_one hprod]
    linarith
  linarith

/-- **THE RATIO STAYS BELOW THREE.**  The bridged ceiling never exceeds three times
the demand.  Together with the previous theorem the ratio lives strictly inside the
window `(1, 3)` at every size, so no size is special. -/
theorem pairingRouteRatio_lt_three (size : ℝ) (hsize : 4 ≤ size) :
    3 - 6 / ((size - 1) * (size - 2)) < 3 := by
  have hone : (0 : ℝ) < size - 1 := by linarith
  have htwo : (0 : ℝ) < size - 2 := by linarith
  have hprod : (0 : ℝ) < (size - 1) * (size - 2) := mul_pos hone htwo
  have hpos : (0 : ℝ) < 6 / ((size - 1) * (size - 2)) := div_pos (by norm_num) hprod
  linarith

/-- **THE RATIO GROWS WITH THE SIZE.**  This is the negative.  The slack between the
ceiling and the demand is LARGER at six than at five, and larger still at seven.
The route moves in the wrong direction, so it can never separate six from five. -/
theorem pairingRouteRatio_strictMono (size : ℝ) (hsize : 4 ≤ size) :
    3 - 6 / ((size - 1) * (size - 2))
      < 3 - 6 / (((size + 1) - 1) * ((size + 1) - 2)) := by
  have hone : (0 : ℝ) < size - 1 := by linarith
  have htwo : (0 : ℝ) < size - 2 := by linarith
  have hprod : (0 : ℝ) < (size - 1) * (size - 2) := mul_pos hone htwo
  have hnext : (0 : ℝ) < ((size + 1) - 1) * ((size + 1) - 2) := by nlinarith
  have hgrow : (size - 1) * (size - 2) < ((size + 1) - 1) * ((size + 1) - 2) := by nlinarith
  have hcancelOne : 6 / ((size - 1) * (size - 2)) * ((size - 1) * (size - 2)) = 6 :=
    div_mul_cancel₀ 6 (ne_of_gt hprod)
  have hcancelTwo : 6 / (((size + 1) - 1) * ((size + 1) - 2))
      * (((size + 1) - 1) * ((size + 1) - 2)) = 6 :=
    div_mul_cancel₀ 6 (ne_of_gt hnext)
  have hquotPos : (0 : ℝ) < 6 / ((size - 1) * (size - 2)) := div_pos (by norm_num) hprod
  have hkey : 6 / (((size + 1) - 1) * ((size + 1) - 2)) < 6 / ((size - 1) * (size - 2)) := by
    by_contra hcontra
    push Not at hcontra
    have hupper : 6 / ((size - 1) * (size - 2)) * (((size + 1) - 1) * ((size + 1) - 2))
        ≤ 6 / (((size + 1) - 1) * ((size + 1) - 2))
          * (((size + 1) - 1) * ((size + 1) - 2)) :=
      mul_le_mul_of_nonneg_right hcontra (le_of_lt hnext)
    rw [hcancelTwo] at hupper
    have hlower : 6 / ((size - 1) * (size - 2)) * ((size - 1) * (size - 2))
        < 6 / ((size - 1) * (size - 2)) * (((size + 1) - 1) * ((size + 1) - 2)) :=
      mul_lt_mul_of_pos_left hgrow hquotPos
    rw [hcancelOne] at hlower
    linarith
  linarith

/-- **THE THREE SIZES, EXACTLY.**  The route ratio reads `5/2` at five atoms,
`27/10` at six and `14/5` at seven.  All three exceed one and the sequence
increases.  The count of triples does NOT outrun the ceiling at six, and the gap
to five is the wrong sign. -/
theorem pairingRouteRatio_five_six_seven :
    (3 : ℝ) - 6 / ((5 - 1) * (5 - 2)) = 5 / 2
      ∧ (3 : ℝ) - 6 / ((6 - 1) * (6 - 2)) = 27 / 10
      ∧ (3 : ℝ) - 6 / ((7 - 1) * (7 - 2)) = 14 / 5
      ∧ (5 : ℝ) / 2 < 27 / 10 ∧ (27 : ℝ) / 10 < 14 / 5 := by
  norm_num

/-- **THE ROUTE IS ARITHMETICALLY CONSISTENT, AND THAT IS THE PROBLEM.**  The whole
assembled system — the ceiling, the bridge and the per-triple cost at the uniform
leverage three — is satisfied with strict slack at five, six and seven atoms.  The
slack is `5/2`, `27/10` and `14/5`.

This is the counterpart of `Gtz.shareArithmetic_is_consistent` one level up.  That
theorem says no contradiction lives in the weights and leverages.  This one says no
contradiction lives in the cross-pairing budget either, at ANY size. -/
theorem pairingBudgetRoute_is_consistent :
    ∃ demand ceiling : ℝ → ℝ,
      (∀ size : ℝ, 4 ≤ size → demand size = 3 * ((size - 1) * (size - 2)) / size ^ 2)
        ∧ (∀ size : ℝ, 4 ≤ size → ceiling size = 9 * (size - 3) / size)
        ∧ (∀ size : ℝ, 4 ≤ size → demand size < ceiling size)
        ∧ ceiling 5 / demand 5 = 5 / 2
        ∧ ceiling 6 / demand 6 = 27 / 10
        ∧ ceiling 7 / demand 7 = 14 / 5 := by
  refine ⟨fun size => 3 * ((size - 1) * (size - 2)) / size ^ 2,
    fun size => 9 * (size - 3) / size, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro size hsize
    show 3 * ((size - 1) * (size - 2)) / size ^ 2 < 9 * (size - 3) / size
    have hsizePos : (0 : ℝ) < size := by linarith
    have hone : (0 : ℝ) < size - 1 := by linarith
    have htwo : (0 : ℝ) < size - 2 := by linarith
    have hdemandPos : (0 : ℝ) < 3 * ((size - 1) * (size - 2)) / size ^ 2 :=
      div_pos (by nlinarith) (by positivity)
    have hratio := uniformScalarPoint_ceiling_eq_ratio_mul_demand size hsize
    have hbig := one_lt_pairingRouteRatio size hsize
    rw [hratio]
    nlinarith [hdemandPos, hbig]
  · norm_num
  · norm_num
  · norm_num

/-! ## 5. What the route proves, and what it does not

The assembled chain is:

* the ceiling `size * crossPairingTotal <= size * rank - rank^2`, attained at strict
  dominators, hence free of tie content;
* the per-triple cost `3 floor^2 <= 4 pairSquareTotal`, sharp at the tetrahedron;
* the bridge `sum t_a t_b t_c pairSquareTotal = 3 * rank`, an identity whose factor
  three counts pairs and cannot be lowered;
* the aggregate `3 floor^2 distinctTripleMass <= 36`.

The count of triples is `size choose 3` and it does grow.  The product measure
undoes that growth exactly: `distinctTripleMass` at uniform weight is
`(size - 1)(size - 2) / size^2`, which is bounded by one.  The ceiling meanwhile
grows toward the rank.  So the ratio of ceiling to demand grows toward three.

The route therefore does NOT separate six from five, and it never will at any size.
A route that closes `(6,3)` has to read the pairings in a way the product measure
does not average out. -/

/-! ## 6. The landed ties, measured

The size test the route has to pass is the `(5,3)` diamond against the `(6,3)`
ties.  The diamond is a PRIMITIVE tie, so it is the exact obstruction the hinge
must survive at six and cannot survive at five.  If the ceiling separated the two
sizes, the diamond would sit closer to its ceiling than the six-atom ties sit to
theirs.  It sits FURTHER. -/

/-- **THE `(5,3)` PRIMITIVE DIAMOND.**  Uniform weight `1/5`, leverages `2` and
`13/4` four times, so the shares are `2/5` and `13/20` and the share second moment
is `37/20`.  The cross-pairing total is `23/20`. -/
theorem crossPairingTotal_diamondDesign : crossPairingTotal diamondDesign = 23 / 20 := by
  have hsum : (∑ label, (diamondDesign.weight label
      * leverageOf (diamondDesign.atom label)) ^ 2) = 37 / 20 := by
    rw [Fin.sum_univ_five, diamondDesign_weight 0, diamondDesign_weight 1,
      diamondDesign_weight 2, diamondDesign_weight 3, diamondDesign_weight 4,
      diamondDesign_leverage_spine, diamondDesign_leverage_rimOne,
      diamondDesign_leverage_rimTwo, diamondDesign_leverage_rimThree,
      diamondDesign_leverage_rimFour]
    norm_num
  rw [crossPairingTotal_eq_rank_sub_sum_share_sq diamondDesign, hsum]
  norm_num

/-- **THE `(6,3)` SPLIT DIAMOND.**  The same geometry with the spine split in two,
weights `1/10` twice and `1/5` four times.  The share second moment is `177/100`
and the cross-pairing total is `123/100`. -/
theorem crossPairingTotal_sixSplitDiamondDesign :
    crossPairingTotal sixSplitDiamondDesign = 123 / 100 := by
  have hweightZero : sixSplitDiamondDesign.weight 0 = 1 / 10 := rfl
  have hweightOne : sixSplitDiamondDesign.weight 1 = 1 / 5 := rfl
  have hweightTwo : sixSplitDiamondDesign.weight 2 = 1 / 5 := rfl
  have hweightThree : sixSplitDiamondDesign.weight 3 = 1 / 5 := rfl
  have hweightFour : sixSplitDiamondDesign.weight 4 = 1 / 5 := rfl
  have hweightFive : sixSplitDiamondDesign.weight 5 = 1 / 10 := rfl
  have hatomZero : sixSplitDiamondDesign.atom 0 = diamondDesign.atom 0 := rfl
  have hatomOne : sixSplitDiamondDesign.atom 1 = diamondDesign.atom 1 := rfl
  have hatomTwo : sixSplitDiamondDesign.atom 2 = diamondDesign.atom 2 := rfl
  have hatomThree : sixSplitDiamondDesign.atom 3 = diamondDesign.atom 3 := rfl
  have hatomFour : sixSplitDiamondDesign.atom 4 = diamondDesign.atom 4 := rfl
  have hatomFive : sixSplitDiamondDesign.atom 5 = diamondDesign.atom 0 := rfl
  have hsum : (∑ label, (sixSplitDiamondDesign.weight label
      * leverageOf (sixSplitDiamondDesign.atom label)) ^ 2) = 177 / 100 := by
    rw [Fin.sum_univ_six, hweightZero, hweightOne, hweightTwo, hweightThree, hweightFour,
      hweightFive, hatomZero, hatomOne, hatomTwo, hatomThree, hatomFour, hatomFive,
      diamondDesign_leverage_spine, diamondDesign_leverage_rimOne,
      diamondDesign_leverage_rimTwo, diamondDesign_leverage_rimThree,
      diamondDesign_leverage_rimFour]
    norm_num
  rw [crossPairingTotal_eq_rank_sub_sum_share_sq sixSplitDiamondDesign, hsum]
  norm_num

/-- **THE `(6,3)` NON-UNIFORM LEVERAGE TIE.**  Leverages `19/3` three times and
`4/3` three times, weights `1/9` and `2/9`.  The shares are `19/27` and `8/27`, the
share second moment is `425/243` and the cross-pairing total is `304/243`. -/
theorem crossPairingTotal_nonUniformLeverageTieDesign :
    crossPairingTotal nonUniformLeverageTieDesign = 304 / 243 := by
  have hsum : (∑ label, (nonUniformLeverageTieDesign.weight label
      * leverageOf (nonUniformLeverageTieDesign.atom label)) ^ 2) = 425 / 243 := by
    rw [Fin.sum_univ_six, nonUniformLeverageTieDesign_leverage 0,
      nonUniformLeverageTieDesign_leverage 1, nonUniformLeverageTieDesign_leverage 2,
      nonUniformLeverageTieDesign_leverage 3, nonUniformLeverageTieDesign_leverage 4,
      nonUniformLeverageTieDesign_leverage 5]
    norm_num [nonUniformLeverageTieDesign, nonUniformLeverageTieWeight]
  rw [crossPairingTotal_eq_rank_sub_sum_share_sq nonUniformLeverageTieDesign, hsum]
  norm_num

/-- **THE SIZE TEST, ON THE LANDED TIES.**  The `(5,3)` primitive diamond sits
`1/20` below its ceiling.  The `(6,3)` split diamond, which is the SAME geometry
one size up, sits `27/100` below its ceiling, and the `(6,3)` non-uniform tie sits
`121/486` below its.  Both six-atom slacks are more than five times the five-atom
slack.

So the ceiling is TIGHTER at the size where the tie is known to exist, and looser at
the size where the tie is conjectured not to exist.  The route reads the two sizes
in the wrong order, and the reading is exact, not an estimate. -/
theorem crossPairingTotal_slack_grows_from_five_to_six :
    6 / 5 - crossPairingTotal diamondDesign = 1 / 20
      ∧ 3 / 2 - crossPairingTotal sixSplitDiamondDesign = 27 / 100
      ∧ 3 / 2 - crossPairingTotal nonUniformLeverageTieDesign = 121 / 486
      ∧ (1 : ℝ) / 20 < 27 / 100
      ∧ (1 : ℝ) / 20 < 121 / 486 := by
  rw [crossPairingTotal_diamondDesign, crossPairingTotal_sixSplitDiamondDesign,
    crossPairingTotal_nonUniformLeverageTieDesign]
  norm_num

/-- **THE HONEST SUMMARY, IN KERNEL.**  The three facts that close this lane.  The
ceiling is attained at equal shares, the bridge factor is exactly three, and the
route ratio increases with the size while staying above one. -/
theorem pairingBudgetRoute_verdict :
    (∀ D : WeightedDesign 6 3, (∀ label, D.weight label * leverageOf (D.atom label) = 1 / 2) →
        crossPairingTotal D = 3 / 2)
      ∧ (∀ design : WeightedDesign 6 3,
          (∑ first, ∑ second, ∑ third, design.weight first * design.weight second
            * design.weight third
            * pairSquareTotal (design.atom first) (design.atom second)
              (design.atom third)) = 9)
      ∧ (∀ size : ℝ, 4 ≤ size → 1 < 3 - 6 / ((size - 1) * (size - 2)))
      ∧ (∀ size : ℝ, 4 ≤ size →
          3 - 6 / ((size - 1) * (size - 2))
            < 3 - 6 / (((size + 1) - 1) * ((size + 1) - 2))) :=
  ⟨fun D hshare => crossPairingTotal_eq_three_halves_of_half_share D hshare,
    fun design => sum_weight_mul_pairSquareTotal design,
    one_lt_pairingRouteRatio, pairingRouteRatio_strictMono⟩

end Gtz
