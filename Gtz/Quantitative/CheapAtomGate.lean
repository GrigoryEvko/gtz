/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Design.RhoNormalForm
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.WeightProductFloor
import Gtz.Reduction.PrincipalMinorsThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

/-!
# The cheap-atom gates of the free-weight `(6,3)` stratum

The stratum is the pen's V6 object: a `(6,3)` weighted design all of whose atom
shares are `1/2`, so the six unit directions form a tight frame at level two and
`M = Gamma - 1` is a hollow symmetric involution, but the weights are FREE.  The
uniform-leverage point `leverage = 3` (U6) is the single weight vector
`t = 1/6`; everything here is stated at an arbitrary weight vector on the same
frame.

Write `tau_c = 1 - 2 t_c` for the atom's WEIGHT SLACK (`Gtz.atomWeightSlack`).  At
share `1/2` this is `1 - 1/l_c`, so the criterion `Gamma[T] >= diag(1/l_c)` reads
`diag(tau) + M[T] >= 0`, and the six slacks sum to `4` rather than to `1`.
Expanded by the all-principal-minors criterion that is three PAIRWISE
clauses `w_cd <= tau_c tau_d` and one DETERMINANT clause
`Delta(T) = tau_a tau_b tau_c - (tau_a w_bc + tau_b w_ac + tau_c w_ab) + 2 P_T >= 0`
(`Gtz.slackTripleDeterminant`), where `w_cd = gamma_cd^2` is `Gtz.edgeWeight` and
`P_T` is `Gtz.directionTripleProduct`.

## What is proved here

**The flat-quadruple classification** (section 3).  The pen's V6 gate "no four of
the six atoms are coplanar" is FALSE as stated on this stratum -- the octahedron
is a landed member and `{e2, -e2, e3, -e3}` is coplanar.  What is true is an
IFF: a quadruple is coplanar exactly when the complementary PAIR is parallel
(`Gtz.exists_unitNormal_iff_edgeWeight_eq_one`).  Both directions are one line of
the conservation law `sum_c <n, u_c>^2 = 2` -- forward, the two survivors split a
budget of `2` between them with each term capped at `1`; backward, a parallel pair
eats the whole row budget of its own row law, so every other correlation to it
vanishes.  The pen's stated form is recovered under pairwise non-parallelism
(`Gtz.not_exists_unitNormal_of_edgeWeight_ne_one`), and the octahedron is the
explicit witness that the hypothesis cannot be dropped
(`Gtz.exists_unitNormal_octahedronDesign`).

**The four-set determinant identity** (section 4).
`sum over the four triples of a 4-set F of det Gamma[T] = 2 (1 - w_pq)`, `{p,q}`
the complementary pair.  The pen derives it from the spectrum of `M[F]`; no
spectral theory is needed.  Summing the row law over `F` gives
`sum of the six edge weights inside F = 1 + w_pq`
(`Gtz.sum_edgeWeight_within_quadruple_eq`), and the mirror law turns the four
triangle products of `F` into the four triangle products through the pair `{p,q}`,
which the vanishing supply chain kills
(`Gtz.sum_directionTripleProduct_within_quadruple_eq_zero`); the identity itself is
`Gtz.sum_directionTripleDeterminant_within_quadruple_eq`.

**The two-cheap-atom gate** (section 5) with the pen's explicit constant.  At most
two atoms can be cheap (`sum tau = 4` with `tau < 1`, so three slacks at most `1/3`
are arithmetically impossible -- `Gtz.not_three_cheap_atoms`), and if the two cheap
slacks are at most `epsilon` with `12 epsilon < 1 - w_pq` then one of the four
triples of the expensive quadruple dominates
(`Gtz.exists_dominates_triple_of_twoCheapAtoms`).  The pen states the constant for
the determinant clause only; it is in fact strong enough for the pairwise clauses
too, because `det Gamma[T] <= 1 - w_ab` caps every edge of the selected triple
(`Gtz.directionTripleDeterminant_le_one_sub_edgeWeight`) and the pairwise clauses
need only `8 epsilon <= 1 - w_pq`.

**The pair-sum gate is VACUOUS** (section 6), and that is this module's headline.
Summing the four determinant clauses through a fixed pair is an exact IDENTITY,
not an inequality: the row law collapses the edge sums to `1 - w_pq` and the
supply chain kills the products outright, leaving
`sum_k Delta({p,q,k}) = (tau_p tau_q - w_pq)(4 - tau_p - tau_q)
  - (tau_p + tau_q)(1 - w_pq)`
(`Gtz.sum_slackTripleDeterminant_through_pair_eq`).  The pen reads the
contrapositive as a gate: if that expression is nonnegative, some triple through
the pair passes.  It never is.  Writing `s = tau_p + tau_q`, the value is bounded
by `-s(2-s)^2/4 - 2 w_pq (2-s)` (`Gtz.pairSumValue_le`), hence is at most zero on
the whole polytope and STRICTLY negative wherever `0 < s < 2`
(`Gtz.pairSumValue_neg_of_lt_two`) -- which is everywhere a genuine design lives,
since positive weights give `0 < tau_p + tau_q < 2`.  The gate can therefore never
fire.  What it does deliver is the reverse reading, which is new and is not
vacuous: through EVERY pair of atoms at least one of the four triples fails the
determinant clause outright, so at least one of them does not dominate
(`Gtz.exists_not_dominates_through_pair`).

**The equality case is the two-atom deletion corner, and the tie showing through
is the `(4,3)` cell's** (section 7).  The pair-sum value vanishes exactly at
`tau_p = tau_q = 1`, i.e. `t_p = t_q = 0`, for every edge weight
(`Gtz.pairSumValue_eq_zero_iff`).  There the identity degenerates to
`sum_k Delta({p,q,k}) = (1 - w_pq) (sum_k tau_k) - sum_k projectionMass_k`, where
the conservation law fixes `sum_k projectionMass_k = 2 (1 - w_pq)`
(`Gtz.sum_planarProjectionMass_through_pair_eq`) and the weight budget fixes
`sum_k tau_k = 2` exactly when the two deleted weights vanish.  So the vanishing
of the pair-sum functional at the corner IS the coincidence of the frame's
conservation total with the surviving quadruple's weight budget: the tie is the
`(4,3)` cell's tetrahedral tie, inherited, not a new phenomenon of `(6,3)`.
Each `Delta({p,q,k})` at the corner is exactly
`(1 - w_pq) tau_k - projectionMass_k`, i.e. `(1 - w_pq)` times the pen's
`<u_k, n>^2 - 2 t_k` where `n` is the unit normal of `span(u_p, u_q)`.

**The coherent-counting bound** (section 8).  At most seven of the ten triples
through a fixed atom are coherent, so at least three coherent triples avoid every
atom.  The combinatorial core is landed here in the form that carries the whole
argument: for edge signs in `[-1, 1]` on `K_5` whose triangle products satisfy the
mirror balance `sum of edges + sum of triangles = 0`, the edge sum is at most `5`
(`Gtz.edgeSignSum_le_five_of_mirrorBalance`), whence the integer count of
positive edges -- which is the count of coherent triples through the sixth atom --
is at most `7` (`Gtz.coherentCount_le_seven`), so at least three coherent triples
avoid every atom (`Gtz.three_le_coherent_avoiding_atom`).  The per-triangle
inequality driving it is the factorization
`x y z - x - y - z + 2 = (z-1)(xy-1) + (x-1)(y-1)`, valid on the whole cube
(`Gtz.triangleCertificate_nonneg`).

## Reading the slack

`Gtz.atomWeightSlack` is the WEIGHT slack `1 - 2 t_c`, chosen because its total is
`m - 2` with no hypothesis at all.  At a share of one half -- the standing
hypothesis of every criterion below -- it coincides with the LEVERAGE capacity
`1 - 1/l_c` that actually sits on the diagonal of `diag(tau) + M[T] >= 0`; the
bridge is `Gtz.leverage_mul_atomWeightSlack`, which reads `l_c tau_c = l_c - 1`.
Off that share the two part company and only the leverage one decides domination.

## Honesty

Nothing here needs the pen's pairwise non-parallel hypothesis except the
flat-quadruple corollary, which is exactly where it is genuinely required.  The
domination criterion of section 2 is one-directional -- the four clauses are
SUFFICIENT (`Gtz.dominates_triple_of_slackMinors`) and the determinant clause alone
is NECESSARY (`Gtz.slackTripleDeterminant_nonneg_of_dominates`).  Those two are
everything the four gates consume, and the full equivalence in slack coordinates is
deliberately not re-proved here.  The design-level assembly
of section 8 -- the sign gauge `s_c = sign(gamma_6c)` and the ten mirror
instantiations that produce the balance hypothesis -- is NOT mechanized; only the
combinatorial core is, and the core is the part that was in doubt.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The weight slack

`tau_c = 1 - 2 t_c`.  Division-free by design: at share `1/2` it equals
`1 - 1/l_c`, but writing it on the weight makes `sum_c tau_c = m - 2` a one-line
consequence of `weight_sum_one` and makes every statement below polynomial in the
design's own data. -/

/-- **The weight slack** `tau_c = 1 - 2 t_c` of an atom.  On the equal-share
`(6,3)` stratum this is the pen's `tau`, the diagonal of the shifted criterion
`diag(tau) + M[T] >= 0`; the six slacks sum to `4`. -/
noncomputable def atomWeightSlack (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  1 - 2 * D.weight atomIndex

/-- The slacks sum to `m - 2`: at `(6,3)` the pen's `sum tau = 4`. -/
theorem sum_atomWeightSlack (D : WeightedDesign m k) :
    ∑ atomIndex, atomWeightSlack D atomIndex = (m : ℝ) - 2 := by
  simp only [atomWeightSlack]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, D.weight_sum_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, mul_one]

/-- Every slack is strictly below one, because every weight is strictly positive.
This is what makes the deletion corner `tau = 1` unreachable by a design. -/
theorem atomWeightSlack_lt_one (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomWeightSlack D atomIndex < 1 := by
  have hpositive := D.weight_pos atomIndex
  rw [atomWeightSlack]
  linarith

/-- **The corner names itself**: slack one is weight zero, so `tau_p = tau_q = 1` is
literally the two-atom deletion.  Together with `Gtz.atomWeightSlack_lt_one` this
says a genuine design never reaches it -- the corner is a limit point of the weight
polytope, not a member. -/
theorem atomWeightSlack_eq_one_iff (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomWeightSlack D atomIndex = 1 ↔ D.weight atomIndex = 0 := by
  rw [atomWeightSlack]
  constructor <;> intro hvalue <;> linarith

/-- **The slack in leverage coordinates**, at a share of one half:
`tau_c = 1 - 1/l_c`, so `l_c tau_c = l_c - 1` is the heavy excess. -/
theorem leverage_mul_atomWeightSlack (D : WeightedDesign m 3) {atomIndex : Fin m}
    (hshare : atomShare D atomIndex = 1 / 2) :
    leverageOf (D.atom atomIndex) * atomWeightSlack D atomIndex = heavyExcess D atomIndex := by
  rw [atomWeightSlack, heavyExcess]
  have hshareValue : D.weight atomIndex * leverageOf (D.atom atomIndex) = 1 / 2 := hshare
  nlinarith [hshareValue]

/-! ## 2. The slack criterion

The gate direction of the pen's V1: the three pairwise clauses and the one
determinant clause, in slack coordinates, imply domination.  The transport to the
landed `Gtz.tripleGapMatrix` is the congruence by `diag(sqrt l)`, executed here
entry by entry rather than as a matrix identity: the diagonal picks up one factor
`l_c` each, every squared pairing picks up `l_x l_y`, and the triple product picks
up `l_a l_b l_c`, so all seven principal minors of the gap matrix are the slack
minors scaled by positive leverages. -/

/-- **The determinant clause** `Delta(T)` of the slack criterion, at an EXTERNAL
slack vector.  The slack is a parameter rather than the design's own
`Gtz.atomWeightSlack` because the pen's V6 polytope varies the weights on a FIXED
frame; the design's own slack is the instance that decides `Gtz.Dominates`. -/
noncomputable def slackTripleDeterminant (D : WeightedDesign m k) (slack : Fin m → ℝ)
    (first second third : Fin m) : ℝ :=
  slack first * slack second * slack third
    - (slack first * edgeWeight D second third + slack second * edgeWeight D first third
        + slack third * edgeWeight D first second)
    + 2 * directionTripleProduct D first second third

/-- The squared raw pairing is the edge weight scaled by the two leverages. -/
private theorem sq_atomPairing_eq (D : WeightedDesign m 3) {first second : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second)) :
    atomPairing D first second ^ 2
      = leverageOf (D.atom first) * leverageOf (D.atom second) * edgeWeight D first second := by
  have hscaled := directionGram_eq_scaled_atomPairing D first second
  have hfirstSqrt : Real.sqrt (leverageOf (D.atom first)) ^ 2 = leverageOf (D.atom first) :=
    Real.sq_sqrt hfirst.le
  have hsecondSqrt : Real.sqrt (leverageOf (D.atom second)) ^ 2 = leverageOf (D.atom second) :=
    Real.sq_sqrt hsecond.le
  have hfirstNe : Real.sqrt (leverageOf (D.atom first)) ≠ 0 := by positivity
  have hsecondNe : Real.sqrt (leverageOf (D.atom second)) ≠ 0 := by positivity
  have hpairing : atomPairing D first second
      = Real.sqrt (leverageOf (D.atom first)) * Real.sqrt (leverageOf (D.atom second))
        * directionGram D first second := by
    rw [hscaled, atomPairing]
    field_simp
  rw [hpairing, edgeWeight, mul_pow, mul_pow, hfirstSqrt, hsecondSqrt]

/-- The oriented product of the three raw pairings is the direction triple product
scaled by all three leverages. -/
private theorem atomPairing_triple_eq (D : WeightedDesign m 3) {first second third : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second))
    (hthird : 0 < leverageOf (D.atom third)) :
    atomPairing D first second * atomPairing D first third * atomPairing D second third
      = leverageOf (D.atom first) * leverageOf (D.atom second) * leverageOf (D.atom third)
        * directionTripleProduct D first second third := by
  have hpairing : ∀ left right : Fin m, 0 < leverageOf (D.atom left) →
      0 < leverageOf (D.atom right) →
      atomPairing D left right
        = Real.sqrt (leverageOf (D.atom left)) * Real.sqrt (leverageOf (D.atom right))
          * directionGram D left right := by
    intro left right hleft hright
    have hleftNe : Real.sqrt (leverageOf (D.atom left)) ≠ 0 := by positivity
    have hrightNe : Real.sqrt (leverageOf (D.atom right)) ≠ 0 := by positivity
    rw [directionGram_eq_scaled_atomPairing D left right, atomPairing]
    field_simp
  rw [hpairing first second hfirst hsecond, hpairing first third hfirst hthird,
    hpairing second third hsecond hthird, directionTripleProduct]
  have hfirstSq : Real.sqrt (leverageOf (D.atom first)) * Real.sqrt (leverageOf (D.atom first))
      = leverageOf (D.atom first) := Real.mul_self_sqrt hfirst.le
  have hsecondSq : Real.sqrt (leverageOf (D.atom second)) * Real.sqrt (leverageOf (D.atom second))
      = leverageOf (D.atom second) := Real.mul_self_sqrt hsecond.le
  have hthirdSq : Real.sqrt (leverageOf (D.atom third)) * Real.sqrt (leverageOf (D.atom third))
      = leverageOf (D.atom third) := Real.mul_self_sqrt hthird.le
  linear_combination
    (Real.sqrt (leverageOf (D.atom second)) * Real.sqrt (leverageOf (D.atom second))
        * Real.sqrt (leverageOf (D.atom third)) * Real.sqrt (leverageOf (D.atom third))
        * (directionGram D first second * directionGram D first third
            * directionGram D second third)) * hfirstSq
      + (leverageOf (D.atom first) * Real.sqrt (leverageOf (D.atom third))
          * Real.sqrt (leverageOf (D.atom third))
          * (directionGram D first second * directionGram D first third
              * directionGram D second third)) * hsecondSq
      + (leverageOf (D.atom first) * leverageOf (D.atom second)
          * (directionGram D first second * directionGram D first third
              * directionGram D second third)) * hthirdSq

/-- **The congruence, at the determinant.**  The gap matrix's determinant is the
slack determinant scaled by the three leverages -- the `diag(sqrt l)` congruence
read on one minor.  This is the single computation both directions of the slack
criterion consume. -/
theorem det_tripleGapMatrix_eq_slack (D : WeightedDesign m 3) {first second third : Fin m}
    (hfirstShare : atomShare D first = 1 / 2) (hsecondShare : atomShare D second = 1 / 2)
    (hthirdShare : atomShare D third = 1 / 2) :
    (tripleGapMatrix D first second third).det
      = leverageOf (D.atom first) * leverageOf (D.atom second) * leverageOf (D.atom third)
        * slackTripleDeterminant D (atomWeightSlack D) first second third := by
  have hfirstLev : 0 < leverageOf (D.atom first) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hfirstShare]; norm_num)
  have hsecondLev : 0 < leverageOf (D.atom second) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hsecondShare]; norm_num)
  have hthirdLev : 0 < leverageOf (D.atom third) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hthirdShare]; norm_num)
  have hfirstExcess := leverage_mul_atomWeightSlack D hfirstShare
  have hsecondExcess := leverage_mul_atomWeightSlack D hsecondShare
  have hthirdExcess := leverage_mul_atomWeightSlack D hthirdShare
  have hpairOne := sq_atomPairing_eq D hfirstLev hsecondLev
  have hpairTwo := sq_atomPairing_eq D hfirstLev hthirdLev
  have hpairThree := sq_atomPairing_eq D hsecondLev hthirdLev
  have hproduct := atomPairing_triple_eq D hfirstLev hsecondLev hthirdLev
  rw [Matrix.det_fin_three]
  simp only [tripleGapMatrix, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  rw [slackTripleDeterminant, ← hfirstExcess, ← hsecondExcess, ← hthirdExcess]
  linear_combination (-(leverageOf (D.atom third) * atomWeightSlack D third)) * hpairOne
    + (-(leverageOf (D.atom second) * atomWeightSlack D second)) * hpairTwo
    + (-(leverageOf (D.atom first) * atomWeightSlack D first)) * hpairThree
    + 2 * hproduct

/-- **THE SLACK GATE.**  Three pairwise clauses, one determinant clause, and
nonnegative slacks give domination.  The only hypothesis on the design is that the
three atoms have share one half -- no all-heaviness, no non-parallelism, no
equal leverage. -/
theorem dominates_triple_of_slackMinors (D : WeightedDesign m 3) {first second third : Fin m}
    (hfirstShare : atomShare D first = 1 / 2) (hsecondShare : atomShare D second = 1 / 2)
    (hthirdShare : atomShare D third = 1 / 2)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfirstNonneg : 0 ≤ atomWeightSlack D first) (hsecondNonneg : 0 ≤ atomWeightSlack D second)
    (hthirdNonneg : 0 ≤ atomWeightSlack D third)
    (hpairFirstSecond :
      edgeWeight D first second ≤ atomWeightSlack D first * atomWeightSlack D second)
    (hpairFirstThird :
      edgeWeight D first third ≤ atomWeightSlack D first * atomWeightSlack D third)
    (hpairSecondThird :
      edgeWeight D second third ≤ atomWeightSlack D second * atomWeightSlack D third)
    (hdeterminant : 0 ≤ slackTripleDeterminant D (atomWeightSlack D) first second third) :
    Dominates D {first, second, third} := by
  have hfirstLev : 0 < leverageOf (D.atom first) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hfirstShare]; norm_num)
  have hsecondLev : 0 < leverageOf (D.atom second) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hsecondShare]; norm_num)
  have hthirdLev : 0 < leverageOf (D.atom third) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hthirdShare]; norm_num)
  have hfirstExcess := leverage_mul_atomWeightSlack D hfirstShare
  have hsecondExcess := leverage_mul_atomWeightSlack D hsecondShare
  have hthirdExcess := leverage_mul_atomWeightSlack D hthirdShare
  have hpairOne := sq_atomPairing_eq D hfirstLev hsecondLev
  have hpairTwo := sq_atomPairing_eq D hfirstLev hthirdLev
  have hpairThree := sq_atomPairing_eq D hsecondLev hthirdLev
  rw [dominates_triple_iff_posSemidef_tripleGapMatrix D hfirstSecond hfirstThird hsecondThird]
  have hzeroZero : tripleGapMatrix D first second third 0 0 = heavyExcess D first := rfl
  have honeOne : tripleGapMatrix D first second third 1 1 = heavyExcess D second := rfl
  have htwoTwo : tripleGapMatrix D first second third 2 2 = heavyExcess D third := rfl
  have hzeroOne : tripleGapMatrix D first second third 0 1 = atomPairing D first second := rfl
  have hzeroTwo : tripleGapMatrix D first second third 0 2 = atomPairing D first third := rfl
  have honeTwo : tripleGapMatrix D first second third 1 2 = atomPairing D second third := rfl
  have hdet := det_tripleGapMatrix_eq_slack D hfirstShare hsecondShare hthirdShare
  refine posSemidef_three_of_principalMinors (tripleGapMatrix_transpose D first second third)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hzeroZero, ← hfirstExcess]; positivity
  · rw [honeOne, ← hsecondExcess]; positivity
  · rw [htwoTwo, ← hthirdExcess]; positivity
  · rw [hzeroZero, honeOne, hzeroOne, ← hfirstExcess, ← hsecondExcess, hpairOne]
    nlinarith [mul_nonneg (mul_pos hfirstLev hsecondLev).le (sub_nonneg.mpr hpairFirstSecond)]
  · rw [hzeroZero, htwoTwo, hzeroTwo, ← hfirstExcess, ← hthirdExcess, hpairTwo]
    nlinarith [mul_nonneg (mul_pos hfirstLev hthirdLev).le (sub_nonneg.mpr hpairFirstThird)]
  · rw [honeOne, htwoTwo, honeTwo, ← hsecondExcess, ← hthirdExcess, hpairThree]
    nlinarith [mul_nonneg (mul_pos hsecondLev hthirdLev).le (sub_nonneg.mpr hpairSecondThird)]
  · rw [hdet]; positivity

/-- **The determinant clause is NECESSARY.**  A dominating triple has nonnegative
slack determinant, because the gap matrix is positive semidefinite and its
determinant is the slack determinant scaled by the three positive leverages.  This
is the direction the pair-sum vacuity consumes. -/
theorem slackTripleDeterminant_nonneg_of_dominates (D : WeightedDesign m 3)
    {first second third : Fin m}
    (hfirstShare : atomShare D first = 1 / 2) (hsecondShare : atomShare D second = 1 / 2)
    (hthirdShare : atomShare D third = 1 / 2)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hdominates : Dominates D {first, second, third}) :
    0 ≤ slackTripleDeterminant D (atomWeightSlack D) first second third := by
  have hfirstLev : 0 < leverageOf (D.atom first) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hfirstShare]; norm_num)
  have hsecondLev : 0 < leverageOf (D.atom second) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hsecondShare]; norm_num)
  have hthirdLev : 0 < leverageOf (D.atom third) :=
    leverageOf_pos_of_atomShare_pos D (by rw [hthirdShare]; norm_num)
  have hpsd := (dominates_triple_iff_posSemidef_tripleGapMatrix D hfirstSecond hfirstThird
    hsecondThird).mp hdominates
  have hdetNonneg := hpsd.det_nonneg
  rw [det_tripleGapMatrix_eq_slack D hfirstShare hsecondShare hthirdShare] at hdetNonneg
  have hproduct : 0 < leverageOf (D.atom first) * leverageOf (D.atom second)
      * leverageOf (D.atom third) := by positivity
  by_contra hnegative
  rw [not_le] at hnegative
  nlinarith [hdetNonneg, hproduct, hnegative]

/-! ## 3. The conservation law and the flat-quadruple classification

The frame law tested twice at the same probe says `sum_c s_c <n, u_c>^2 = |n|^2`;
at share `1/2` that is the pen's `sum_c <n, u_c>^2 = 2` for a unit `n`.  Four
atoms orthogonal to `n` leave a budget of exactly `2` for the other two, and each
term is capped at `1` by Cauchy-Schwarz, so both saturate and both directions
coincide with `n` up to sign.  Conversely a parallel pair eats the whole budget of
its own row law, so it is orthogonal to everything else.  The two readings make
coplanarity of a quadruple EQUIVALENT to parallelism of the complementary pair. -/

/-- **THE CONSERVATION LAW ALONG A PROBE.**  At a uniform share the squared
correlations of a probe with the six unit directions total `|probe|^2 / share`.
No rank hypothesis, no size hypothesis, no nondegeneracy. -/
theorem shareValue_mul_sum_sq_dotProduct_unitAtom (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (probe : Fin k → ℝ) :
    shareValue * ∑ atomIndex, (probe ⬝ᵥ unitAtom D atomIndex) ^ 2 = probe ⬝ᵥ probe := by
  have hframe := frameLaw_bilinear D probe probe
  rw [Finset.mul_sum, ← hframe]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [huniform atomIndex, dotProduct_comm (unitAtom D atomIndex) probe]
  ring

/-- **The Cauchy-Schwarz equality case, concretely.**  A unit vector whose
correlation with a unit probe has square one IS that probe up to sign: the
residual `target - <n,target> n` has vanishing self-product. -/
theorem eq_smul_of_sq_dotProduct_eq_one {dim : ℕ} {normal target : Fin dim → ℝ}
    (hnormal : normal ⬝ᵥ normal = 1) (htarget : target ⬝ᵥ target = 1)
    (hsaturated : (normal ⬝ᵥ target) ^ 2 = 1) :
    target = (normal ⬝ᵥ target) • normal := by
  have hcomm : target ⬝ᵥ normal = normal ⬝ᵥ target := dotProduct_comm target normal
  have hexpand : (target - (normal ⬝ᵥ target) • normal)
      ⬝ᵥ (target - (normal ⬝ᵥ target) • normal)
      = target ⬝ᵥ target - 2 * ((normal ⬝ᵥ target) * (normal ⬝ᵥ target))
        + (normal ⬝ᵥ target) * (normal ⬝ᵥ target) * (normal ⬝ᵥ normal) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hcomm]
    ring
  have hvanishes : (target - (normal ⬝ᵥ target) • normal)
      ⬝ᵥ (target - (normal ⬝ᵥ target) • normal) = 0 := by
    rw [hexpand, hnormal, htarget]
    nlinarith [hsaturated]
  have hzero := eq_zero_of_dotProduct_self_eq_zero hvanishes
  exact sub_eq_zero.mp hzero

/-- The unit direction of a nondegenerate atom really is a unit vector. -/
theorem dotProduct_unitAtom_self (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    unitAtom D atomIndex ⬝ᵥ unitAtom D atomIndex = 1 := by
  rw [← leverageOf_eq_dotProduct, leverageOf_unitAtom D hpositive]

/-- **THE FLAT-QUADRUPLE CLASSIFICATION.**  On the free-weight `(6,3)` stratum a
quadruple of atoms lies in a plane through the origin EXACTLY when the
complementary pair is parallel.  The pen's V6 gate asserts the left side is always
false; it is not (`Gtz.exists_unitNormal_octahedronDesign` below), and this iff
says precisely when.

Forward: the conservation law hands the two survivors a budget of `2` with each
term capped at `1`, so both saturate and both directions are `+-n`.  Backward: the
row law at one endpoint of a parallel pair is already exhausted by its own
diagonal and its partner, so every other correlation to it vanishes and the
partner's direction serves as the normal. -/
theorem exists_unitNormal_iff_edgeWeight_eq_one (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    (∃ normal : Fin 3 → ℝ, normal ⬝ᵥ normal = 1
        ∧ normal ⬝ᵥ unitAtom D quadFirst = 0 ∧ normal ⬝ᵥ unitAtom D quadSecond = 0
        ∧ normal ⬝ᵥ unitAtom D quadThird = 0 ∧ normal ⬝ᵥ unitAtom D quadFourth = 0)
      ↔ edgeWeight D pairFirst pairSecond = 1 := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  constructor
  · rintro ⟨normal, hunit, hfirst, hsecond, hthird, hfourth⟩
    have hconservation := shareValue_mul_sum_sq_dotProduct_unitAtom D huniform normal
    rw [sum_eq_of_bijective_six hbijective (fun atomIndex => (normal ⬝ᵥ unitAtom D atomIndex) ^ 2),
      hunit, hfirst, hsecond, hthird, hfourth] at hconservation
    have hcapFirst : (normal ⬝ᵥ unitAtom D pairFirst) ^ 2 ≤ 1 := by
      have hcauchy := dotProduct_sq_le_mul normal (unitAtom D pairFirst)
      rw [hunit, dotProduct_unitAtom_self D (hleverage pairFirst)] at hcauchy
      linarith [hcauchy]
    have hcapSecond : (normal ⬝ᵥ unitAtom D pairSecond) ^ 2 ≤ 1 := by
      have hcauchy := dotProduct_sq_le_mul normal (unitAtom D pairSecond)
      rw [hunit, dotProduct_unitAtom_self D (hleverage pairSecond)] at hcauchy
      linarith [hcauchy]
    have hsaturatedFirst : (normal ⬝ᵥ unitAtom D pairFirst) ^ 2 = 1 := by linarith [hconservation]
    have hsaturatedSecond : (normal ⬝ᵥ unitAtom D pairSecond) ^ 2 = 1 := by linarith [hconservation]
    have hshapeFirst := eq_smul_of_sq_dotProduct_eq_one hunit
      (dotProduct_unitAtom_self D (hleverage pairFirst)) hsaturatedFirst
    have hshapeSecond := eq_smul_of_sq_dotProduct_eq_one hunit
      (dotProduct_unitAtom_self D (hleverage pairSecond)) hsaturatedSecond
    have hgram : directionGram D pairFirst pairSecond
        = (normal ⬝ᵥ unitAtom D pairFirst) * (normal ⬝ᵥ unitAtom D pairSecond) := by
      rw [directionGram]
      conv_lhs => rw [hshapeFirst, hshapeSecond]
      rw [smul_dotProduct, dotProduct_smul, hunit]
      ring
    rw [edgeWeight, hgram, mul_pow, hsaturatedFirst, hsaturatedSecond, one_mul]
  · intro hparallel
    have hrow := sum_directionGram_sq_split D huniform hbijective pairFirst
    rw [directionGram_self D (hleverage pairFirst), one_pow] at hrow
    rw [edgeWeight] at hparallel
    have hnonnegFirst := sq_nonneg (directionGram D pairFirst quadFirst)
    have hnonnegSecond := sq_nonneg (directionGram D pairFirst quadSecond)
    have hnonnegThird := sq_nonneg (directionGram D pairFirst quadThird)
    have hnonnegFourth := sq_nonneg (directionGram D pairFirst quadFourth)
    have hquietFirst : directionGram D pairFirst quadFirst = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have hquietSecond : directionGram D pairFirst quadSecond = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have hquietThird : directionGram D pairFirst quadThird = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have hquietFourth : directionGram D pairFirst quadFourth = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    exact ⟨unitAtom D pairFirst, dotProduct_unitAtom_self D (hleverage pairFirst),
      hquietFirst, hquietSecond, hquietThird, hquietFourth⟩

/-- **The pen's V6 gate, with the hypothesis it genuinely needs.**  Under pairwise
non-parallelism no quadruple is coplanar. -/
theorem not_exists_unitNormal_of_edgeWeight_ne_one (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond])
    (hnonParallel : edgeWeight D pairFirst pairSecond ≠ 1) :
    ¬ ∃ normal : Fin 3 → ℝ, normal ⬝ᵥ normal = 1
        ∧ normal ⬝ᵥ unitAtom D quadFirst = 0 ∧ normal ⬝ᵥ unitAtom D quadSecond = 0
        ∧ normal ⬝ᵥ unitAtom D quadThird = 0 ∧ normal ⬝ᵥ unitAtom D quadFourth = 0 :=
  fun hflat => hnonParallel
    ((exists_unitNormal_iff_edgeWeight_eq_one D huniform hbijective).mp hflat)

/-- **REFUTATION of the pen's V6 gate as stated.**  The octahedron is a landed
member of the stratum (`Gtz.isEqualShare_octahedronDesign`) and its quadruple
`{e_2, -e_2, e_3, -e_3}` IS coplanar, with normal `e_1` -- because its complement
`{e_1, -e_1}` is an antipodal, hence parallel, pair.  "No four of the six atoms
are coplanar" is therefore false on this stratum, and the pairwise non-parallel
hypothesis the pen carries is exactly what its proof needs. -/
theorem exists_unitNormal_octahedronDesign :
    ∃ normal : Fin 3 → ℝ, normal ⬝ᵥ normal = 1
      ∧ normal ⬝ᵥ unitAtom octahedronDesign 2 = 0 ∧ normal ⬝ᵥ unitAtom octahedronDesign 3 = 0
      ∧ normal ⬝ᵥ unitAtom octahedronDesign 4 = 0
      ∧ normal ⬝ᵥ unitAtom octahedronDesign 5 = 0 := by
  have huniform : ∀ atomIndex : Fin 6, atomShare octahedronDesign atomIndex = 1 / 2 := by
    intro atomIndex
    rw [isEqualShare_octahedronDesign.atomShare_eq atomIndex]
    norm_num
  refine (exists_unitNormal_iff_edgeWeight_eq_one octahedronDesign huniform
    (quadFirst := 2) (quadSecond := 3) (quadThird := 4) (quadFourth := 5)
    (pairFirst := 0) (pairSecond := 1) (by decide)).mpr ?_
  rw [edgeWeight, directionGram_octahedronDesign_zero_one]
  norm_num

/-! ## 4. The four-set determinant identity

`sum over the four triples of a 4-set F of det Gamma[T] = 2 (1 - w_pq)`, with
`{p,q}` the complementary pair.  Two halves, each elementary.  Summing the row law
over the four atoms of `F` and reading the two rows at `p` and `q` gives the edge
mass `1 + w_pq` inside `F`.  And the mirror law sends the four triangle products
of `F` to the four triangle products through `{p,q}`, which factor as
`gamma_pq` times the supply chain at `(p,q)` -- and that chain vanishes.  No
spectrum of `M[F]`, no complementary-minor identity. -/

/-- The determinant of the direction Gram of a triple, in the triple's own two
scalars: `det Gamma[T] = 1 - sigma_T + 2 P_T`. -/
noncomputable def directionTripleDeterminant (D : WeightedDesign m k)
    (first second third : Fin m) : ℝ :=
  1 - directionTripleSigma D first second third + 2 * directionTripleProduct D first second third

/-- Reindexing a bijective six-tuple keeps it bijective. -/
private theorem bijective_reindex_six {first second third fourth fifth sixth : Fin 6}
    (hbijective : Function.Bijective ![first, second, third, fourth, fifth, sixth])
    {reindex : Fin 6 → Fin 6} (hreindex : Function.Bijective reindex) :
    Function.Bijective (![first, second, third, fourth, fifth, sixth] ∘ reindex) :=
  hbijective.comp hreindex

/-- **THE SUPPLY CHAIN THROUGH A PAIR, expanded.**  At share one half the
two-step correlations of a pair through the other four atoms cancel exactly. -/
theorem sum_directionGram_chain_through_pair (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    directionGram D pairFirst quadFirst * directionGram D quadFirst pairSecond
        + directionGram D pairFirst quadSecond * directionGram D quadSecond pairSecond
        + directionGram D pairFirst quadThird * directionGram D quadThird pairSecond
        + directionGram D pairFirst quadFourth * directionGram D quadFourth pairSecond
      = 0 := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hmaster := sum_atomShare_mul_directionGram_mul_directionGram D pairFirst pairSecond
  rw [Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex],
    sum_eq_of_bijective_six hbijective, directionGram_self D (hleverage pairFirst),
    directionGram_self D (hleverage pairSecond)] at hmaster
  linarith [hmaster]

/-- **THE EDGE MASS OF A QUADRUPLE.**  The six edge weights inside a 4-set total
`1 + w_pq` -- the row law summed over the quadruple, with the two rows at the
complementary pair supplying the cross mass. -/
theorem sum_edgeWeight_within_quadruple_eq (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    edgeWeight D quadFirst quadSecond + edgeWeight D quadFirst quadThird
        + edgeWeight D quadFirst quadFourth + edgeWeight D quadSecond quadThird
        + edgeWeight D quadSecond quadFourth + edgeWeight D quadThird quadFourth
      = 1 + edgeWeight D pairFirst pairSecond := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hrowFirst := sum_directionGram_sq_split D huniform hbijective quadFirst
  have hrowSecond := sum_directionGram_sq_split D huniform hbijective quadSecond
  have hrowThird := sum_directionGram_sq_split D huniform hbijective quadThird
  have hrowFourth := sum_directionGram_sq_split D huniform hbijective quadFourth
  have hrowPairFirst := sum_directionGram_sq_split D huniform hbijective pairFirst
  have hrowPairSecond := sum_directionGram_sq_split D huniform hbijective pairSecond
  rw [directionGram_self D (hleverage quadFirst), one_pow] at hrowFirst
  rw [directionGram_self D (hleverage quadSecond), one_pow,
    directionGram_comm D quadSecond quadFirst] at hrowSecond
  rw [directionGram_self D (hleverage quadThird), one_pow,
    directionGram_comm D quadThird quadFirst, directionGram_comm D quadThird quadSecond]
    at hrowThird
  rw [directionGram_self D (hleverage quadFourth), one_pow,
    directionGram_comm D quadFourth quadFirst, directionGram_comm D quadFourth quadSecond,
    directionGram_comm D quadFourth quadThird] at hrowFourth
  rw [directionGram_self D (hleverage pairFirst), one_pow,
    directionGram_comm D pairFirst quadFirst, directionGram_comm D pairFirst quadSecond,
    directionGram_comm D pairFirst quadThird, directionGram_comm D pairFirst quadFourth]
    at hrowPairFirst
  rw [directionGram_self D (hleverage pairSecond), one_pow,
    directionGram_comm D pairSecond quadFirst, directionGram_comm D pairSecond quadSecond,
    directionGram_comm D pairSecond quadThird, directionGram_comm D pairSecond quadFourth,
    directionGram_comm D pairSecond pairFirst] at hrowPairSecond
  simp only [edgeWeight]
  linarith [hrowFirst, hrowSecond, hrowThird, hrowFourth, hrowPairFirst, hrowPairSecond]

/-- **THE TRIANGLE PRODUCTS OF A QUADRUPLE CANCEL.**  Mirror each triple of `F` to
its complement, a triple through the pair `{p,q}`; the four complements share the
factor `gamma_pq` and the rest is the supply chain at `(p,q)`, which vanishes. -/
theorem sum_directionTripleProduct_within_quadruple_eq_zero (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    directionTripleProduct D quadFirst quadSecond quadThird
        + directionTripleProduct D quadFirst quadSecond quadFourth
        + directionTripleProduct D quadFirst quadThird quadFourth
        + directionTripleProduct D quadSecond quadThird quadFourth
      = 0 := by
  have hswapThird : Function.Bijective
      ![quadFirst, quadSecond, quadFourth, quadThird, pairFirst, pairSecond] := by
    have hcomp : ![quadFirst, quadSecond, quadFourth, quadThird, pairFirst, pairSecond]
        = ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]
          ∘ ![0, 1, 3, 2, 4, 5] := by
      funext index; fin_cases index <;> rfl
    rw [hcomp]
    exact bijective_reindex_six hbijective (by decide)
  have hswapSecond : Function.Bijective
      ![quadFirst, quadThird, quadFourth, quadSecond, pairFirst, pairSecond] := by
    have hcomp : ![quadFirst, quadThird, quadFourth, quadSecond, pairFirst, pairSecond]
        = ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]
          ∘ ![0, 2, 3, 1, 4, 5] := by
      funext index; fin_cases index <;> rfl
    rw [hcomp]
    exact bijective_reindex_six hbijective (by decide)
  have hswapFirst : Function.Bijective
      ![quadSecond, quadThird, quadFourth, quadFirst, pairFirst, pairSecond] := by
    have hcomp : ![quadSecond, quadThird, quadFourth, quadFirst, pairFirst, pairSecond]
        = ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]
          ∘ ![1, 2, 3, 0, 4, 5] := by
      funext index; fin_cases index <;> rfl
    rw [hcomp]
    exact bijective_reindex_six hbijective (by decide)
  have hmirrorFourth :=
    directionTripleProduct_compl_eq_neg D huniform hbijective
  have hmirrorThird := directionTripleProduct_compl_eq_neg D huniform hswapThird
  have hmirrorSecond := directionTripleProduct_compl_eq_neg D huniform hswapSecond
  have hmirrorFirst := directionTripleProduct_compl_eq_neg D huniform hswapFirst
  have hchain := sum_directionGram_chain_through_pair D huniform hbijective
  simp only [directionTripleProduct] at hmirrorFourth hmirrorThird hmirrorSecond hmirrorFirst ⊢
  rw [directionGram_comm D pairFirst quadFirst, directionGram_comm D pairFirst quadSecond,
    directionGram_comm D pairFirst quadThird, directionGram_comm D pairFirst quadFourth]
    at hchain
  linear_combination hmirrorFourth + hmirrorThird + hmirrorSecond + hmirrorFirst
    - directionGram D pairFirst pairSecond * hchain

/-- **THE FOUR-SET DETERMINANT IDENTITY.**  The four principal `3 x 3` direction
Gram determinants of a quadruple total `2 (1 - w_pq)`. -/
theorem sum_directionTripleDeterminant_within_quadruple_eq (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    directionTripleDeterminant D quadFirst quadSecond quadThird
        + directionTripleDeterminant D quadFirst quadSecond quadFourth
        + directionTripleDeterminant D quadFirst quadThird quadFourth
        + directionTripleDeterminant D quadSecond quadThird quadFourth
      = 2 * (1 - edgeWeight D pairFirst pairSecond) := by
  have hedge := sum_edgeWeight_within_quadruple_eq D huniform hbijective
  have hproduct := sum_directionTripleProduct_within_quadruple_eq_zero D huniform hbijective
  simp only [directionTripleDeterminant, directionTripleSigma, edgeWeight] at hedge ⊢
  linarith [hedge, hproduct]

/-! ## 5. The two-cheap-atom gate

At most two atoms can be cheap: the six slacks sum to `4` and each is below `1`,
so three cheap slacks are arithmetically impossible.  When exactly two are cheap,
bounded by `epsilon`, every other slack exceeds `1 - 2 epsilon`, the four-set
identity hands one triple of the expensive quadruple a determinant of at least
`(1 - w_pq)/2`, and the pen's constant `12 epsilon < 1 - w_pq` closes both clauses:
the determinant clause because the slack determinant sits within `6 epsilon` of the
Gram determinant, and the pairwise clauses because `det Gamma[T] <= 1 - w_ab` caps
every edge of the selected triple and only `8 epsilon <= 1 - w_pq` is needed there. -/

/-- `s^2 + t^2 - 2 f s t = (s - f t)^2 + t^2 (1 - f^2)`: the exact certificate
behind the `3 x 3` Fischer bound. -/
private theorem elliptopeCap (first second third : ℝ) (hfirst : first ^ 2 ≤ 1) :
    1 - (first ^ 2 + second ^ 2 + third ^ 2) + 2 * (first * second * third) ≤ 1 - first ^ 2 := by
  nlinarith [sq_nonneg (second - first * third),
    mul_nonneg (sq_nonneg third) (sub_nonneg.mpr hfirst)]

/-- **THE THREE-BY-THREE FISCHER BOUND.**  A triple's Gram determinant is capped by
`1 - w` at EVERY one of its three edges. -/
theorem directionTripleDeterminant_le_one_sub_edgeWeight (D : WeightedDesign m k)
    (first second third : Fin m) :
    directionTripleDeterminant D first second third ≤ 1 - edgeWeight D first second
      ∧ directionTripleDeterminant D first second third ≤ 1 - edgeWeight D first third
      ∧ directionTripleDeterminant D first second third ≤ 1 - edgeWeight D second third := by
  have hcapFirstSecond : directionGram D first second ^ 2 ≤ 1 := by
    have habs := abs_directionGram_le_one D first second
    nlinarith [sq_abs (directionGram D first second), abs_nonneg (directionGram D first second)]
  have hcapFirstThird : directionGram D first third ^ 2 ≤ 1 := by
    have habs := abs_directionGram_le_one D first third
    nlinarith [sq_abs (directionGram D first third), abs_nonneg (directionGram D first third)]
  have hcapSecondThird : directionGram D second third ^ 2 ≤ 1 := by
    have habs := abs_directionGram_le_one D second third
    nlinarith [sq_abs (directionGram D second third), abs_nonneg (directionGram D second third)]
  have hone := elliptopeCap (directionGram D first second) (directionGram D first third)
    (directionGram D second third) hcapFirstSecond
  have htwo := elliptopeCap (directionGram D first third) (directionGram D first second)
    (directionGram D second third) hcapFirstThird
  have hthree := elliptopeCap (directionGram D second third) (directionGram D first second)
    (directionGram D first third) hcapSecondThird
  simp only [directionTripleDeterminant, directionTripleSigma, directionTripleProduct, edgeWeight]
  exact ⟨by linarith [hone], by linarith [htwo], by linarith [hthree]⟩

/-- **THE DETERMINANT-FLOOR GATE.**  A triple whose three slacks all exceed
`1 - 2 epsilon` and whose Gram determinant is at least `detBound >= 6 epsilon`
dominates.  All four clauses of the slack criterion come out of these two numbers;
the pairwise clauses need only `4 epsilon <= detBound`, which the determinant
margin already supplies. -/
theorem dominates_triple_of_directionTripleDeterminant_ge (D : WeightedDesign m 3)
    {first second third : Fin m} {cheapBound detBound : ℝ}
    (hfirstShare : atomShare D first = 1 / 2) (hsecondShare : atomShare D second = 1 / 2)
    (hthirdShare : atomShare D third = 1 / 2)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hcheapNonneg : 0 ≤ cheapBound)
    (hslackFirst : 1 - 2 * cheapBound ≤ atomWeightSlack D first)
    (hslackSecond : 1 - 2 * cheapBound ≤ atomWeightSlack D second)
    (hslackThird : 1 - 2 * cheapBound ≤ atomWeightSlack D third)
    (hdetBound : detBound ≤ directionTripleDeterminant D first second third)
    (hmargin : 6 * cheapBound ≤ detBound) :
    Dominates D {first, second, third} := by
  obtain ⟨hcapOne, hcapTwo, hcapThree⟩ :=
    directionTripleDeterminant_le_one_sub_edgeWeight D first second third
  have hedgeOne := edgeWeight_nonneg D first second
  have hedgeTwo := edgeWeight_nonneg D first third
  have hedgeThree := edgeWeight_nonneg D second third
  have hcheapSmall : cheapBound ≤ 1 / 6 := by linarith [hcapOne, hdetBound, hmargin, hedgeOne]
  have hslackTopFirst := (atomWeightSlack_lt_one D first).le
  have hslackTopSecond := (atomWeightSlack_lt_one D second).le
  have hslackTopThird := (atomWeightSlack_lt_one D third).le
  have hfloorNonneg : (0 : ℝ) ≤ 1 - 2 * cheapBound := by linarith
  have hprodFirstSecond : (1 - 2 * cheapBound) ^ 2
      ≤ atomWeightSlack D first * atomWeightSlack D second := by nlinarith
  have hprodFirstThird : (1 - 2 * cheapBound) ^ 2
      ≤ atomWeightSlack D first * atomWeightSlack D third := by nlinarith
  have hprodSecondThird : (1 - 2 * cheapBound) ^ 2
      ≤ atomWeightSlack D second * atomWeightSlack D third := by nlinarith
  have hprodTriple : (1 - 2 * cheapBound) ^ 3
      ≤ atomWeightSlack D first * atomWeightSlack D second * atomWeightSlack D third := by
    nlinarith [hprodFirstSecond]
  refine dominates_triple_of_slackMinors D hfirstShare hsecondShare hthirdShare hfirstSecond
    hfirstThird hsecondThird (by linarith) (by linarith) (by linarith) ?_ ?_ ?_ ?_
  · nlinarith [hcapOne, hdetBound, hmargin, hprodFirstSecond]
  · nlinarith [hcapTwo, hdetBound, hmargin, hprodFirstThird]
  · nlinarith [hcapThree, hdetBound, hmargin, hprodSecondThird]
  · have hslackGap : atomWeightSlack D first * edgeWeight D second third
        + atomWeightSlack D second * edgeWeight D first third
        + atomWeightSlack D third * edgeWeight D first second
        ≤ edgeWeight D second third + edgeWeight D first third + edgeWeight D first second := by
      nlinarith [hedgeOne, hedgeTwo, hedgeThree]
    have hcube : 1 - 6 * cheapBound ≤ (1 - 2 * cheapBound) ^ 3 := by
      nlinarith [sq_nonneg cheapBound, hcheapNonneg, hcheapSmall,
        mul_nonneg (sq_nonneg cheapBound) hcheapNonneg]
    simp only [slackTripleDeterminant, edgeWeight]
    simp only [directionTripleDeterminant, directionTripleSigma] at hdetBound
    simp only [edgeWeight] at hslackGap
    linarith [hprodTriple, hslackGap, hdetBound, hmargin, hcube]

/-- **THE TWO-CHEAP-ATOM GATE**, with the pen's explicit constant.  If two atoms
have slack at most `epsilon` and `12 epsilon < 1 - w_pq`, then one of the four
triples of the complementary quadruple dominates. -/
theorem exists_dominates_triple_of_twoCheapAtoms (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond])
    {cheapBound : ℝ} (hcheapNonneg : 0 ≤ cheapBound)
    (hcheapFirst : atomWeightSlack D pairFirst ≤ cheapBound)
    (hcheapSecond : atomWeightSlack D pairSecond ≤ cheapBound)
    (hsmall : 12 * cheapBound < 1 - edgeWeight D pairFirst pairSecond) :
    Dominates D {quadFirst, quadSecond, quadThird}
      ∨ Dominates D {quadFirst, quadSecond, quadFourth}
      ∨ Dominates D {quadFirst, quadThird, quadFourth}
      ∨ Dominates D {quadSecond, quadThird, quadFourth} := by
  have hdistinct : ∀ leftSlot rightSlot : Fin 6, leftSlot ≠ rightSlot →
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond] leftSlot
        ≠ ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond] rightSlot :=
    fun leftSlot rightSlot hne heq => hne (hbijective.injective heq)
  have hslackSum : atomWeightSlack D quadFirst + atomWeightSlack D quadSecond
      + atomWeightSlack D quadThird + atomWeightSlack D quadFourth
      + atomWeightSlack D pairFirst + atomWeightSlack D pairSecond = 4 := by
    have htotal := sum_atomWeightSlack D
    rw [sum_eq_of_bijective_six hbijective (atomWeightSlack D)] at htotal
    rw [htotal]
    norm_num
  have hcapFirst := (atomWeightSlack_lt_one D quadFirst).le
  have hcapSecond := (atomWeightSlack_lt_one D quadSecond).le
  have hcapThird := (atomWeightSlack_lt_one D quadThird).le
  have hcapFourth := (atomWeightSlack_lt_one D quadFourth).le
  have hfloorFirst : 1 - 2 * cheapBound ≤ atomWeightSlack D quadFirst := by linarith
  have hfloorSecond : 1 - 2 * cheapBound ≤ atomWeightSlack D quadSecond := by linarith
  have hfloorThird : 1 - 2 * cheapBound ≤ atomWeightSlack D quadThird := by linarith
  have hfloorFourth : 1 - 2 * cheapBound ≤ atomWeightSlack D quadFourth := by linarith
  have hsumDet := sum_directionTripleDeterminant_within_quadruple_eq D huniform hbijective
  have hbig : (1 - edgeWeight D pairFirst pairSecond) / 2
        ≤ directionTripleDeterminant D quadFirst quadSecond quadThird
      ∨ (1 - edgeWeight D pairFirst pairSecond) / 2
        ≤ directionTripleDeterminant D quadFirst quadSecond quadFourth
      ∨ (1 - edgeWeight D pairFirst pairSecond) / 2
        ≤ directionTripleDeterminant D quadFirst quadThird quadFourth
      ∨ (1 - edgeWeight D pairFirst pairSecond) / 2
        ≤ directionTripleDeterminant D quadSecond quadThird quadFourth := by
    by_contra hall
    simp only [not_or, not_le] at hall
    obtain ⟨hone, htwo, hthree, hfour⟩ := hall
    linarith [hsumDet]
  have hmargin : 6 * cheapBound ≤ (1 - edgeWeight D pairFirst pairSecond) / 2 := by linarith
  rcases hbig with hbig | hbig | hbig | hbig
  · exact Or.inl (dominates_triple_of_directionTripleDeterminant_ge D (huniform quadFirst)
      (huniform quadSecond) (huniform quadThird) (hdistinct 0 1 (by decide))
      (hdistinct 0 2 (by decide)) (hdistinct 1 2 (by decide)) hcheapNonneg hfloorFirst
      hfloorSecond hfloorThird hbig hmargin)
  · exact Or.inr (Or.inl (dominates_triple_of_directionTripleDeterminant_ge D (huniform quadFirst)
      (huniform quadSecond) (huniform quadFourth) (hdistinct 0 1 (by decide))
      (hdistinct 0 3 (by decide)) (hdistinct 1 3 (by decide)) hcheapNonneg hfloorFirst
      hfloorSecond hfloorFourth hbig hmargin))
  · exact Or.inr (Or.inr (Or.inl (dominates_triple_of_directionTripleDeterminant_ge D
      (huniform quadFirst) (huniform quadThird) (huniform quadFourth) (hdistinct 0 2 (by decide))
      (hdistinct 0 3 (by decide)) (hdistinct 2 3 (by decide)) hcheapNonneg hfloorFirst
      hfloorThird hfloorFourth hbig hmargin)))
  · exact Or.inr (Or.inr (Or.inr (dominates_triple_of_directionTripleDeterminant_ge D
      (huniform quadSecond) (huniform quadThird) (huniform quadFourth) (hdistinct 1 2 (by decide))
      (hdistinct 1 3 (by decide)) (hdistinct 2 3 (by decide)) hcheapNonneg hfloorSecond
      hfloorThird hfloorFourth hbig hmargin)))

/-- **AT MOST TWO ATOMS ARE CHEAP.**  Three slacks below `1/3` are arithmetically
impossible: the six sum to `4` and the remaining three are each below `1`.  This is
the pen's V2 order statistic `tau_(4) > 1/3` in the form the gate consumes. -/
theorem not_three_cheap_atoms (D : WeightedDesign 6 3)
    {cheapFirst cheapSecond cheapThird expensiveFirst expensiveSecond expensiveThird : Fin 6}
    (hbijective : Function.Bijective
      ![cheapFirst, cheapSecond, cheapThird, expensiveFirst, expensiveSecond, expensiveThird]) :
    ¬ (atomWeightSlack D cheapFirst ≤ 1 / 3 ∧ atomWeightSlack D cheapSecond ≤ 1 / 3
        ∧ atomWeightSlack D cheapThird ≤ 1 / 3) := by
  rintro ⟨hfirst, hsecond, hthird⟩
  have htotal := sum_atomWeightSlack D
  rw [sum_eq_of_bijective_six hbijective (atomWeightSlack D)] at htotal
  have hcapFirst := atomWeightSlack_lt_one D expensiveFirst
  have hcapSecond := atomWeightSlack_lt_one D expensiveSecond
  have hcapThird := atomWeightSlack_lt_one D expensiveThird
  rw [show ((6 : ℕ) : ℝ) - 2 = 4 by norm_num] at htotal
  linarith [htotal]

/-! ## 6. The pair-sum identity, and why the pair-sum gate is vacuous

Sum the four determinant clauses through a fixed pair.  The row law collapses both
edge sums to `1 - w_pq`, the supply chain kills the products outright, and the
slack budget supplies `4 - tau_p - tau_q`, so the sum is an exact function of the
pair alone.  The pen reads the contrapositive as a gate: if that function is
nonnegative, some triple through the pair passes its determinant clause.  It is
never nonnegative on the interior.  Writing `s = tau_p + tau_q`, the exact bound

    pairSumValue <= -s (2 - s)^2 / 4 - 2 w_pq (2 - s)

is at most zero for every `s` in `[0, 2]`, hence for every slack vector with
`tau <= 1`, and strictly negative whenever `0 < s < 2` -- which is every genuine
design, because positive weights put both slacks strictly below one and their sum
strictly above zero.  The gate cannot fire anywhere.

The reverse reading is not vacuous, and is new: through EVERY pair at least one of
the four triples fails its determinant clause, hence does not dominate. -/

/-- **The pair-sum functional**, in slack coordinates: the exact value of the four
determinant clauses through a pair, as a function of the pair's two slacks and its
edge weight alone. -/
def pairSumValue (firstSlack secondSlack pairWeight : ℝ) : ℝ :=
  (firstSlack * secondSlack - pairWeight) * (4 - firstSlack - secondSlack)
    - (firstSlack + secondSlack) * (1 - pairWeight)

/-- **THE EXACT CAP.**  `pairSumValue <= -s (2-s)^2/4 - 2 w (2-s)` with
`s = firstSlack + secondSlack`.  The slack of the bound is
`(firstSlack - secondSlack)^2 (4 - s) / 4`, so the cap is attained exactly when the
two slacks are equal.  The edge weight needs no hypothesis at all: the functional is
affine in it and the cap is exact there. -/
theorem pairSumValue_le (firstSlack secondSlack pairWeight : ℝ) (hfirst : firstSlack ≤ 1)
    (hsecond : secondSlack ≤ 1) :
    pairSumValue firstSlack secondSlack pairWeight
      ≤ -(firstSlack + secondSlack) * (2 - firstSlack - secondSlack) ^ 2 / 4
        - 2 * pairWeight * (2 - firstSlack - secondSlack) := by
  have hroom : (0 : ℝ) ≤ 4 - firstSlack - secondSlack := by linarith
  rw [pairSumValue]
  nlinarith [mul_nonneg (sq_nonneg (firstSlack - secondSlack)) hroom]

/-- **THE PAIR-SUM GATE IS VACUOUS.**  On the whole polytope the functional is at
most zero, so the pen's gate condition never holds. -/
theorem pairSumValue_nonpos (firstSlack secondSlack pairWeight : ℝ) (hfirst : firstSlack ≤ 1)
    (hsecond : secondSlack ≤ 1) (hweight : 0 ≤ pairWeight)
    (hsum : 0 ≤ firstSlack + secondSlack) :
    pairSumValue firstSlack secondSlack pairWeight ≤ 0 := by
  have hcap := pairSumValue_le firstSlack secondSlack pairWeight hfirst hsecond
  nlinarith [sq_nonneg (2 - firstSlack - secondSlack), hcap, hweight, hsum]

/-- **AND STRICTLY VACUOUS OFF THE CORNER.**  Away from `tau_p = tau_q = 1` the
functional is strictly negative, so the four determinant clauses through the pair
cannot all be satisfied. -/
theorem pairSumValue_neg_of_lt_two (firstSlack secondSlack pairWeight : ℝ)
    (hfirst : firstSlack ≤ 1) (hsecond : secondSlack ≤ 1) (hweight : 0 ≤ pairWeight)
    (hsumPos : 0 < firstSlack + secondSlack) (hsumLt : firstSlack + secondSlack < 2) :
    pairSumValue firstSlack secondSlack pairWeight < 0 := by
  have hcap := pairSumValue_le firstSlack secondSlack pairWeight hfirst hsecond
  have hsquare : 0 < (2 - firstSlack - secondSlack) ^ 2 := pow_pos (by linarith) 2
  nlinarith [hcap, hweight, hsumPos, hsquare]

/-- **THE DELETION CORNER IS EXACTLY THE ZERO SET.**  Given a positive slack sum,
the pair-sum functional vanishes precisely at `tau_p = tau_q = 1`, i.e. at the
two-atom deletion corner, and it does so for EVERY edge weight. -/
theorem pairSumValue_eq_zero_iff (firstSlack secondSlack pairWeight : ℝ) (hfirst : firstSlack ≤ 1)
    (hsecond : secondSlack ≤ 1) (hweight : 0 ≤ pairWeight)
    (hsumPos : 0 < firstSlack + secondSlack) :
    pairSumValue firstSlack secondSlack pairWeight = 0 ↔ firstSlack = 1 ∧ secondSlack = 1 := by
  constructor
  · intro hzero
    by_contra hnotCorner
    have hsumLt : firstSlack + secondSlack < 2 := by
      rcases lt_or_eq_of_le hfirst with hstrictFirst | heqFirst
      · linarith
      · rcases lt_or_eq_of_le hsecond with hstrictSecond | heqSecond
        · linarith
        · exact absurd ⟨heqFirst, heqSecond⟩ hnotCorner
    linarith [pairSumValue_neg_of_lt_two firstSlack secondSlack pairWeight hfirst hsecond hweight
      hsumPos hsumLt]
  · rintro ⟨hcornerFirst, hcornerSecond⟩
    rw [pairSumValue, hcornerFirst, hcornerSecond]
    ring

/-- The corner value is zero for every edge weight -- the tie there does not depend
on the geometry of the deleted pair at all. -/
theorem pairSumValue_one_one (pairWeight : ℝ) : pairSumValue 1 1 pairWeight = 0 := by
  rw [pairSumValue]; ring

/-- **THE PAIR-SUM IDENTITY.**  The four determinant clauses through a pair sum to
the pair-sum functional -- exactly, at any slack vector with total `4`.  The row law
supplies both `1 - w_pq`, the supply chain supplies the `0`. -/
theorem sum_slackTripleDeterminant_through_pair_eq (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ atomIndex, slack atomIndex = 4) :
    slackTripleDeterminant D slack pairFirst pairSecond quadFirst
        + slackTripleDeterminant D slack pairFirst pairSecond quadSecond
        + slackTripleDeterminant D slack pairFirst pairSecond quadThird
        + slackTripleDeterminant D slack pairFirst pairSecond quadFourth
      = pairSumValue (slack pairFirst) (slack pairSecond)
          (edgeWeight D pairFirst pairSecond) := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  rw [sum_eq_of_bijective_six hbijective slack] at hslackSum
  have hrowFirst := sum_directionGram_sq_split D huniform hbijective pairFirst
  rw [directionGram_self D (hleverage pairFirst), one_pow] at hrowFirst
  have hrowSecond := sum_directionGram_sq_split D huniform hbijective pairSecond
  rw [directionGram_self D (hleverage pairSecond), one_pow,
    directionGram_comm D pairSecond pairFirst] at hrowSecond
  have hchain := sum_directionGram_chain_through_pair D huniform hbijective
  rw [directionGram_comm D quadFirst pairSecond, directionGram_comm D quadSecond pairSecond,
    directionGram_comm D quadThird pairSecond, directionGram_comm D quadFourth pairSecond]
    at hchain
  simp only [slackTripleDeterminant, pairSumValue, edgeWeight, directionTripleProduct]
  linear_combination
    (slack pairFirst * slack pairSecond - directionGram D pairFirst pairSecond ^ 2) * hslackSum
      - slack pairSecond * hrowFirst - slack pairFirst * hrowSecond
      + 2 * directionGram D pairFirst pairSecond * hchain

/-- The design's own slacks total `4` at size six. -/
theorem sum_atomWeightSlack_six (D : WeightedDesign 6 3) :
    ∑ atomIndex, atomWeightSlack D atomIndex = 4 := by
  rw [sum_atomWeightSlack D]; norm_num

/-- The two slacks of a pair sum strictly into `(0, 2)`: strictly below `2` because
both weights are positive, strictly above `0` because the four other weights are.
This is what puts every genuine design strictly inside the vacuity region. -/
theorem atomWeightSlack_pair_mem_open (D : WeightedDesign 6 3) {pairFirst pairSecond : Fin 6}
    (hdistinct : pairFirst ≠ pairSecond) :
    0 < atomWeightSlack D pairFirst + atomWeightSlack D pairSecond
      ∧ atomWeightSlack D pairFirst + atomWeightSlack D pairSecond < 2 := by
  have hsubset : ({pairFirst, pairSecond} : Finset (Fin 6)) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.mpr fun hfull => ?_
    have hcard := congrArg Finset.card hfull
    rw [Finset.card_insert_of_notMem (by simpa using hdistinct), Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin] at hcard
    norm_num at hcard
  obtain ⟨thirdIndex, _, hthirdNot⟩ := Finset.exists_of_ssubset hsubset
  have hpartial : ∑ atomIndex ∈ ({pairFirst, pairSecond} : Finset (Fin 6)), D.weight atomIndex
      < ∑ atomIndex, D.weight atomIndex :=
    Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ thirdIndex) hthirdNot
      (D.weight_pos thirdIndex) (fun otherIndex _ _ => (D.weight_pos otherIndex).le)
  rw [Finset.sum_pair hdistinct, D.weight_sum_one] at hpartial
  have hfirstPos := D.weight_pos pairFirst
  have hsecondPos := D.weight_pos pairSecond
  rw [atomWeightSlack, atomWeightSlack]
  constructor <;> linarith

/-- **THE VACUITY, AT THE DESIGN'S OWN WEIGHTS.**  Every genuine design sits
strictly inside the region where the pair-sum functional is negative. -/
theorem pairSumValue_atomWeightSlack_neg (D : WeightedDesign 6 3) {pairFirst pairSecond : Fin 6}
    (hdistinct : pairFirst ≠ pairSecond) :
    pairSumValue (atomWeightSlack D pairFirst) (atomWeightSlack D pairSecond)
        (edgeWeight D pairFirst pairSecond) < 0 := by
  obtain ⟨hsumPos, hsumLt⟩ := atomWeightSlack_pair_mem_open D hdistinct
  exact pairSumValue_neg_of_lt_two _ _ _ (atomWeightSlack_lt_one D pairFirst).le
    (atomWeightSlack_lt_one D pairSecond).le (edgeWeight_nonneg D pairFirst pairSecond)
    hsumPos hsumLt

/-- **THE PEN'S GATE CONDITION IS UNSATISFIABLE.**  Named so that nobody attempts
it again: there is no design and no pair at which the pair-sum functional is
nonnegative, so the implication the pen calls a gate never has a usable antecedent. -/
theorem not_zero_le_pairSumValue_atomWeightSlack (D : WeightedDesign 6 3)
    {pairFirst pairSecond : Fin 6} (hdistinct : pairFirst ≠ pairSecond) :
    ¬ 0 ≤ pairSumValue (atomWeightSlack D pairFirst) (atomWeightSlack D pairSecond)
        (edgeWeight D pairFirst pairSecond) :=
  not_le.mpr (pairSumValue_atomWeightSlack_neg D hdistinct)

/-- **THROUGH EVERY PAIR SOME TRIPLE FAILS.**  The honest content of the pair-sum
gate, read in the only direction that has any: at every weight vector of a genuine
design, at least one of the four triples through a given pair violates its
determinant clause outright, hence does not dominate.  So no averaging over the
triples through a pair can ever certify domination. -/
theorem exists_not_dominates_through_pair (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    ¬ Dominates D {pairFirst, pairSecond, quadFirst}
      ∨ ¬ Dominates D {pairFirst, pairSecond, quadSecond}
      ∨ ¬ Dominates D {pairFirst, pairSecond, quadThird}
      ∨ ¬ Dominates D {pairFirst, pairSecond, quadFourth} := by
  have hdistinct : ∀ leftSlot rightSlot : Fin 6, leftSlot ≠ rightSlot →
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond] leftSlot
        ≠ ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond] rightSlot :=
    fun leftSlot rightSlot hne heq => hne (hbijective.injective heq)
  have hpairNe : pairFirst ≠ pairSecond := hdistinct 4 5 (by decide)
  have hfirstQuadOne : pairFirst ≠ quadFirst := hdistinct 4 0 (by decide)
  have hsecondQuadOne : pairSecond ≠ quadFirst := hdistinct 5 0 (by decide)
  have hfirstQuadTwo : pairFirst ≠ quadSecond := hdistinct 4 1 (by decide)
  have hsecondQuadTwo : pairSecond ≠ quadSecond := hdistinct 5 1 (by decide)
  have hfirstQuadThree : pairFirst ≠ quadThird := hdistinct 4 2 (by decide)
  have hsecondQuadThree : pairSecond ≠ quadThird := hdistinct 5 2 (by decide)
  have hfirstQuadFour : pairFirst ≠ quadFourth := hdistinct 4 3 (by decide)
  have hsecondQuadFour : pairSecond ≠ quadFourth := hdistinct 5 3 (by decide)
  by_contra hall
  simp only [not_or, not_not] at hall
  obtain ⟨hone, htwo, hthree, hfour⟩ := hall
  have hnonnegOne := slackTripleDeterminant_nonneg_of_dominates D (huniform pairFirst)
    (huniform pairSecond) (huniform quadFirst) hpairNe hfirstQuadOne hsecondQuadOne hone
  have hnonnegTwo := slackTripleDeterminant_nonneg_of_dominates D (huniform pairFirst)
    (huniform pairSecond) (huniform quadSecond) hpairNe hfirstQuadTwo hsecondQuadTwo htwo
  have hnonnegThree := slackTripleDeterminant_nonneg_of_dominates D (huniform pairFirst)
    (huniform pairSecond) (huniform quadThird) hpairNe hfirstQuadThree hsecondQuadThree hthree
  have hnonnegFour := slackTripleDeterminant_nonneg_of_dominates D (huniform pairFirst)
    (huniform pairSecond) (huniform quadFourth) hpairNe hfirstQuadFour hsecondQuadFour hfour
  have hidentity := sum_slackTripleDeterminant_through_pair_eq D huniform hbijective
    (atomWeightSlack D) (sum_atomWeightSlack_six D)
  have hnegative := pairSumValue_atomWeightSlack_neg D hpairNe
  linarith [hnonnegOne, hnonnegTwo, hnonnegThree, hnonnegFour, hidentity, hnegative]

/-! ## 7. The equality case is the deletion corner, and the tie is the `(4,3)` cell's

At `tau_p = tau_q = 1` -- the two-atom deletion corner, where the two deleted
weights vanish -- each determinant clause through the pair becomes

    Delta({p,q,k}) = (1 - w_pq) tau_k - projectionMass(p,q,k),

with `projectionMass(p,q,k) = w_pk + w_qk - 2 P_{pqk}`, which is `(1 - w_pq)` times
the squared length of the component of `u_k` IN the plane `span(u_p, u_q)`.  The row
law and the supply chain then give the CONSERVATION total

    sum over the four live atoms of projectionMass = 2 (1 - w_pq),

while the weight budget gives `sum over the four live atoms of tau_k = 2` exactly
when the two deleted weights vanish.  The two totals coincide, which is why the
pair-sum functional vanishes there and nowhere else: the tie at the corner is the
coincidence of the frame's conservation law with the SURVIVING QUADRUPLE'S weight
budget, i.e. it is the `(4,3)` cell's tie showing through, not a new phenomenon of
`(6,3)`.  In the pen's coordinates `projectionMass/(1 - w_pq) = 1 - <u_k, n>^2` for
the unit normal `n` of the plane, so the criterion reads `<u_k, n>^2 >= 2 t_k` and
the balance reads `sum <u_k, n>^2 = 2 = sum 2 t_k` -- the exact pigeonhole.  That
normal-vector rendering is NOT mechanized here; the edge-weight rendering below is
equivalent to it and needs no plane. -/

/-- **The in-plane mass** `w_pk + w_qk - 2 P_{pqk}` of an atom against a pair.  It
is `(1 - w_pq)` times the squared length of the component of `u_k` inside
`span(u_p, u_q)`; division-free, so it stays meaningful at a parallel pair. -/
noncomputable def planarProjectionMass (D : WeightedDesign m k) (first second third : Fin m) : ℝ :=
  edgeWeight D first third + edgeWeight D second third
    - 2 * directionTripleProduct D first second third

/-- **THE CONSERVATION LAW AGAINST A PAIR.**  The four live atoms carry in-plane
mass exactly `2 (1 - w_pq)` -- one unit per direction of the plane, scaled.  Row law
plus supply chain; no geometry. -/
theorem sum_planarProjectionMass_through_pair_eq (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond]) :
    planarProjectionMass D pairFirst pairSecond quadFirst
        + planarProjectionMass D pairFirst pairSecond quadSecond
        + planarProjectionMass D pairFirst pairSecond quadThird
        + planarProjectionMass D pairFirst pairSecond quadFourth
      = 2 * (1 - edgeWeight D pairFirst pairSecond) := by
  have hleverage : ∀ atomIndex : Fin 6, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hrowFirst := sum_directionGram_sq_split D huniform hbijective pairFirst
  rw [directionGram_self D (hleverage pairFirst), one_pow] at hrowFirst
  have hrowSecond := sum_directionGram_sq_split D huniform hbijective pairSecond
  rw [directionGram_self D (hleverage pairSecond), one_pow,
    directionGram_comm D pairSecond pairFirst] at hrowSecond
  have hchain := sum_directionGram_chain_through_pair D huniform hbijective
  rw [directionGram_comm D quadFirst pairSecond, directionGram_comm D quadSecond pairSecond,
    directionGram_comm D quadThird pairSecond, directionGram_comm D quadFourth pairSecond]
    at hchain
  simp only [planarProjectionMass, edgeWeight, directionTripleProduct]
  linear_combination hrowFirst + hrowSecond
    - 2 * directionGram D pairFirst pairSecond * hchain

/-- **THE DETERMINANT CLAUSE AT THE DELETION CORNER.**  With both deleted slacks at
one, the clause is the live atom's slack against its in-plane mass. -/
theorem slackTripleDeterminant_eq_of_deletionCorner (D : WeightedDesign m k)
    (slack : Fin m → ℝ) {pairFirst pairSecond : Fin m} (hcornerFirst : slack pairFirst = 1)
    (hcornerSecond : slack pairSecond = 1) (liveIndex : Fin m) :
    slackTripleDeterminant D slack pairFirst pairSecond liveIndex
      = (1 - edgeWeight D pairFirst pairSecond) * slack liveIndex
        - planarProjectionMass D pairFirst pairSecond liveIndex := by
  rw [slackTripleDeterminant, planarProjectionMass, hcornerFirst, hcornerSecond]
  ring

/-- **THE CORNER IDENTITY.**  At the deletion corner the four determinant clauses
total `(1 - w_pq)` times the EXCESS of the live weight budget over the conservation
total.  Both are `2` when the deleted weights vanish, which is exactly the vanishing
of the pair-sum functional there. -/
theorem sum_slackTripleDeterminant_eq_of_deletionCorner (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hcornerFirst : slack pairFirst = 1)
    (hcornerSecond : slack pairSecond = 1) :
    slackTripleDeterminant D slack pairFirst pairSecond quadFirst
        + slackTripleDeterminant D slack pairFirst pairSecond quadSecond
        + slackTripleDeterminant D slack pairFirst pairSecond quadThird
        + slackTripleDeterminant D slack pairFirst pairSecond quadFourth
      = (1 - edgeWeight D pairFirst pairSecond)
        * (slack quadFirst + slack quadSecond + slack quadThird + slack quadFourth - 2) := by
  have hconservation := sum_planarProjectionMass_through_pair_eq D huniform hbijective
  rw [slackTripleDeterminant_eq_of_deletionCorner D slack hcornerFirst hcornerSecond quadFirst,
    slackTripleDeterminant_eq_of_deletionCorner D slack hcornerFirst hcornerSecond quadSecond,
    slackTripleDeterminant_eq_of_deletionCorner D slack hcornerFirst hcornerSecond quadThird,
    slackTripleDeterminant_eq_of_deletionCorner D slack hcornerFirst hcornerSecond quadFourth]
  linear_combination -hconservation

/-- **THE CORNER PIGEONHOLE.**  At the deletion corner some live atom passes its
determinant clause, because the four clauses sum to exactly zero: the live weight
budget `sum tau_k = 2` and the conservation total `2` are the same number.  This is
the `(4,3)` tie, inherited.  For a genuine `(6,3)` design the corner is a limit
point rather than a member -- positive weights force `tau < 1` -- which is precisely
why `Gtz.exists_not_dominates_through_pair` holds strictly everywhere else. -/
theorem exists_nonneg_slackTripleDeterminant_of_deletionCorner (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    {quadFirst quadSecond quadThird quadFourth pairFirst pairSecond : Fin 6}
    (hbijective : Function.Bijective
      ![quadFirst, quadSecond, quadThird, quadFourth, pairFirst, pairSecond])
    (slack : Fin 6 → ℝ) (hslackSum : ∑ atomIndex, slack atomIndex = 4)
    (hcornerFirst : slack pairFirst = 1) (hcornerSecond : slack pairSecond = 1) :
    0 ≤ slackTripleDeterminant D slack pairFirst pairSecond quadFirst
      ∨ 0 ≤ slackTripleDeterminant D slack pairFirst pairSecond quadSecond
      ∨ 0 ≤ slackTripleDeterminant D slack pairFirst pairSecond quadThird
      ∨ 0 ≤ slackTripleDeterminant D slack pairFirst pairSecond quadFourth := by
  rw [sum_eq_of_bijective_six hbijective slack, hcornerFirst, hcornerSecond] at hslackSum
  have hcorner := sum_slackTripleDeterminant_eq_of_deletionCorner D huniform hbijective slack
    hcornerFirst hcornerSecond
  rw [show slack quadFirst + slack quadSecond + slack quadThird + slack quadFourth - 2 = 0 by
    linarith [hslackSum], mul_zero] at hcorner
  by_contra hall
  simp only [not_or, not_le] at hall
  obtain ⟨hone, htwo, hthree, hfour⟩ := hall
  linarith [hcorner]

/-! ## 8. Coherent counting: at most seven coherent triples through an atom

Switching-invariance makes the sign of a triangle product a function of edge signs
alone, and the mirror law makes exactly ten of the twenty triples coherent, one per
`3`-`3` split.  Fixing an atom, its ten triples correspond to the ten edges of the
`K_5` on the other five, coherent exactly at the positive edges after the gauge
`s_c = sign(gamma_(atom)c)`; the ten triples avoiding it are the triangles of that
`K_5`, coherent exactly at even numbers of negative edges.  The two counts add to
ten, which in sign coordinates is the MIRROR BALANCE
`sum of edges + sum of triangles = 0`.

The core is one per-triangle inequality with an exact certificate,

    x y z - x - y - z + 2 = (z - 1)(x y - 1) + (x - 1)(y - 1) >= 0     on the cube,

summed over the ten triangles of `K_5`, where each edge is counted three times.  It
gives `sum of edges <= 5`, hence at most seven positive edges once the count is an
integer -- the pen's `k_c <= 7`, hence at least three coherent triples avoiding
every atom.

MECHANIZED HERE: the core, and the count consequence.  NOT mechanized: the design
side, i.e. the gauge `s_c` and the ten instantiations of
`Gtz.directionTripleProduct_compl_eq_neg` that produce the mirror balance, which
also needs every triangle product nonzero. -/

/-- The ten edges of `K_5`, summed. -/
def edgeSignSum (edgeSign : Fin 5 → Fin 5 → ℝ) : ℝ :=
  edgeSign 0 1 + edgeSign 0 2 + edgeSign 0 3 + edgeSign 0 4
    + edgeSign 1 2 + edgeSign 1 3 + edgeSign 1 4
    + edgeSign 2 3 + edgeSign 2 4 + edgeSign 3 4

/-- The ten triangles of `K_5`, each contributing the product of its three edge
signs -- the sign of the corresponding triple's oriented product. -/
def triangleSignSum (edgeSign : Fin 5 → Fin 5 → ℝ) : ℝ :=
  edgeSign 0 1 * edgeSign 0 2 * edgeSign 1 2 + edgeSign 0 1 * edgeSign 0 3 * edgeSign 1 3
    + edgeSign 0 1 * edgeSign 0 4 * edgeSign 1 4 + edgeSign 0 2 * edgeSign 0 3 * edgeSign 2 3
    + edgeSign 0 2 * edgeSign 0 4 * edgeSign 2 4 + edgeSign 0 3 * edgeSign 0 4 * edgeSign 3 4
    + edgeSign 1 2 * edgeSign 1 3 * edgeSign 2 3 + edgeSign 1 2 * edgeSign 1 4 * edgeSign 2 4
    + edgeSign 1 3 * edgeSign 1 4 * edgeSign 3 4 + edgeSign 2 3 * edgeSign 2 4 * edgeSign 3 4

/-- **THE PER-TRIANGLE CERTIFICATE.**  `x y z - x - y - z + 2 >= 0` on the cube, by
the exact factorization `(z - 1)(x y - 1) + (x - 1)(y - 1)`.  In sign coordinates
this says a triangle's negative-edge count plus its coherence indicator is at least
one, with equality exactly when at most one edge is negative. -/
theorem triangleCertificate_nonneg {firstSign secondSign thirdSign : ℝ}
    (hfirstLower : -1 ≤ firstSign) (hfirstUpper : firstSign ≤ 1)
    (hsecondLower : -1 ≤ secondSign) (hsecondUpper : secondSign ≤ 1)
    (hthirdUpper : thirdSign ≤ 1) :
    0 ≤ firstSign * secondSign * thirdSign - firstSign - secondSign - thirdSign + 2 := by
  have hproduct : firstSign * secondSign ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hproduct) (sub_nonneg.mpr hthirdUpper),
    mul_nonneg (sub_nonneg.mpr hfirstUpper) (sub_nonneg.mpr hsecondUpper)]

/-- **THE COMBINATORIAL CORE.**  Edge signs in `[-1, 1]` on `K_5` whose triangle
products satisfy the mirror balance have edge sum at most `5`.  Each edge lies in
three triangles, so summing the per-triangle certificate gives
`triangleSignSum - 3 edgeSignSum + 20 >= 0`, and the balance turns that into
`4 edgeSignSum <= 20`. -/
theorem edgeSignSum_le_five_of_mirrorBalance (edgeSign : Fin 5 → Fin 5 → ℝ)
    (hlower : ∀ first second : Fin 5, -1 ≤ edgeSign first second)
    (hupper : ∀ first second : Fin 5, edgeSign first second ≤ 1)
    (hbalance : edgeSignSum edgeSign + triangleSignSum edgeSign = 0) :
    edgeSignSum edgeSign ≤ 5 := by
  have hcertificate : ∀ firstEdge secondEdge thirdEdge : Fin 5 × Fin 5,
      0 ≤ edgeSign firstEdge.1 firstEdge.2 * edgeSign secondEdge.1 secondEdge.2
            * edgeSign thirdEdge.1 thirdEdge.2
          - edgeSign firstEdge.1 firstEdge.2 - edgeSign secondEdge.1 secondEdge.2
          - edgeSign thirdEdge.1 thirdEdge.2 + 2 :=
    fun firstEdge secondEdge thirdEdge => triangleCertificate_nonneg (hlower _ _) (hupper _ _)
      (hlower _ _) (hupper _ _) (hupper _ _)
  have hdouble : triangleSignSum edgeSign - 3 * edgeSignSum edgeSign + 20
      = (edgeSign 0 1 * edgeSign 0 2 * edgeSign 1 2
            - edgeSign 0 1 - edgeSign 0 2 - edgeSign 1 2 + 2)
        + (edgeSign 0 1 * edgeSign 0 3 * edgeSign 1 3
            - edgeSign 0 1 - edgeSign 0 3 - edgeSign 1 3 + 2)
        + (edgeSign 0 1 * edgeSign 0 4 * edgeSign 1 4
            - edgeSign 0 1 - edgeSign 0 4 - edgeSign 1 4 + 2)
        + (edgeSign 0 2 * edgeSign 0 3 * edgeSign 2 3
            - edgeSign 0 2 - edgeSign 0 3 - edgeSign 2 3 + 2)
        + (edgeSign 0 2 * edgeSign 0 4 * edgeSign 2 4
            - edgeSign 0 2 - edgeSign 0 4 - edgeSign 2 4 + 2)
        + (edgeSign 0 3 * edgeSign 0 4 * edgeSign 3 4
            - edgeSign 0 3 - edgeSign 0 4 - edgeSign 3 4 + 2)
        + (edgeSign 1 2 * edgeSign 1 3 * edgeSign 2 3
            - edgeSign 1 2 - edgeSign 1 3 - edgeSign 2 3 + 2)
        + (edgeSign 1 2 * edgeSign 1 4 * edgeSign 2 4
            - edgeSign 1 2 - edgeSign 1 4 - edgeSign 2 4 + 2)
        + (edgeSign 1 3 * edgeSign 1 4 * edgeSign 3 4
            - edgeSign 1 3 - edgeSign 1 4 - edgeSign 3 4 + 2)
        + (edgeSign 2 3 * edgeSign 2 4 * edgeSign 3 4
            - edgeSign 2 3 - edgeSign 2 4 - edgeSign 3 4 + 2) := by
    rw [triangleSignSum, edgeSignSum]; ring
  have hnonneg : 0 ≤ triangleSignSum edgeSign - 3 * edgeSignSum edgeSign + 20 := by
    rw [hdouble]
    linarith [hcertificate (0, 1) (0, 2) (1, 2), hcertificate (0, 1) (0, 3) (1, 3),
      hcertificate (0, 1) (0, 4) (1, 4), hcertificate (0, 2) (0, 3) (2, 3),
      hcertificate (0, 2) (0, 4) (2, 4), hcertificate (0, 3) (0, 4) (3, 4),
      hcertificate (1, 2) (1, 3) (2, 3), hcertificate (1, 2) (1, 4) (2, 4),
      hcertificate (1, 3) (1, 4) (3, 4), hcertificate (2, 3) (2, 4) (3, 4)]
  linarith [hnonneg, hbalance]

/-- **THE PEN'S `k_c <= 7`.**  With ten edges of sign `+-1`, the count of positive
ones -- equivalently the count of coherent triples through the fixed atom -- is
`(10 + edgeSignSum)/2`, so the core's `edgeSignSum <= 5` caps it at seven. -/
theorem coherentCount_le_seven (edgeSign : Fin 5 → Fin 5 → ℝ)
    (hlower : ∀ first second : Fin 5, -1 ≤ edgeSign first second)
    (hupper : ∀ first second : Fin 5, edgeSign first second ≤ 1)
    (hbalance : edgeSignSum edgeSign + triangleSignSum edgeSign = 0) (coherentCount : ℕ)
    (hcount : edgeSignSum edgeSign = 2 * (coherentCount : ℝ) - 10) :
    coherentCount ≤ 7 := by
  have hbound := edgeSignSum_le_five_of_mirrorBalance edgeSign hlower hupper hbalance
  rw [hcount] at hbound
  by_contra hbig
  rw [Nat.not_le] at hbig
  have hcast : (8 : ℝ) ≤ (coherentCount : ℝ) := by exact_mod_cast hbig
  linarith [hbound, hcast]

/-- **AND AT LEAST THREE COHERENT TRIPLES AVOID EVERY ATOM**, since the mirror
forces exactly ten coherent triples in all. -/
theorem three_le_coherent_avoiding_atom {coherentThrough : ℕ} (hthrough : coherentThrough ≤ 7) :
    3 ≤ 10 - coherentThrough := by omega

end Gtz
