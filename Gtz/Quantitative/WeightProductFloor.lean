/-
# S4 of the U6 pen argument: the weight reduction, and the product floor

The equal-share `(6,3)` stratum is the set of weighted designs whose every atom
share `s_c = t_c * l_c` equals `1/2` — six unit directions in `R^3` with
`sum_c u_c u_c^T = 2 I`.  Write `gamma_cd = <u_c, u_d>` for the direction Gram
(`Gtz.directionGram`), and for a triple `C = {a, b, c}` write

    sigma_C = gamma_ab^2 + gamma_ac^2 + gamma_bc^2,
    P_C     = gamma_ab * gamma_ac * gamma_bc.

The pen's criterion (C1) reads `sigma_C - 3 P_C <= 4/9`, and the mirror law S2
says that across a 3-3 split `sigma` is preserved while `P` changes sign.  So the
BETTER of the two sides of a split has criterion value

    min (sigma - 3 P) (sigma + 3 P) = sigma - 3 |P|,

and `|P| = |gamma_ab gamma_ac gamma_bc| = sqrt(gamma_ab^2 gamma_ac^2 gamma_bc^2)`.
Setting `w_e = gamma_e^2` on each of the fifteen edges, the split test becomes a
function of the WEIGHTS ALONE,

    h(w_T) = sigma_T - 3 sqrt(p_T),     p_T = product of the three edge weights,

which is what this file calls `Gtz.signFreeTripleResidual`.  The signs evaporate.

## What is in this file

* **The weight variables.**  `Gtz.edgeWeight D a b = gamma_ab^2`, symmetric,
  in `[0, 1]`, one on the diagonal.

* **The vertex-sum law.**  The row law
  `Gtz.atomShare_add_sum_erase_atomShare_mul_sq_directionGram` says
  `s_a + sum_{d /= a} s_d gamma_ad^2 = 1`.  At a CONSTANT share `s` this
  collapses to `sum_{d /= a} w_ad = (1 - s)/s`, and the share sum
  `Gtz.sum_atomShare_eq_rank` then forces `s = k/m`, so the vertex sum is
  `(m - k)/k` at every size and rank.  At `(6,3)` that is exactly `1`; summing
  over the six atoms gives the ordered total `6`, so the fifteen unordered edge
  weights sum to `3`.  This is proved on the SHARE hypothesis alone, which
  is strictly weaker than the `t_c = 1/6, l_c = 3` pair; the `(6,3)` instance
  under that pair is supplied as a corollary because domination is NOT invariant
  under the rescaling that fixes the shares, so the assembly must carry the
  leverage hypothesis even though this particular law does not need it.

* **The sign-free residual and the split reduction.**
  `signFreeTripleResidual (a^2) (b^2) (c^2) = min (sigma - 3 P) (sigma + 3 P)`,
  with the coherent branch `= sigma - 3 P` when `0 <= P`.  This is the exact
  content of "the reduction of the split-pair test to `h`", stated WITHOUT
  assuming the mirror: the mirror (S2, proved elsewhere) is what identifies the
  second argument of the `min` with the complementary triple's criterion value.

* **The product floor.**  `p_T >= m^2 (sigma_T - 2m)` on both branches, each by
  a two-line polynomial identity:

      p - m^2 (sigma - 2m) = m * e_2(w - m) + e_3(w - m)             (all w >= m)
      p - m^2 (sigma - 2m) = y_1 y_2 w_3 + m y_1 y_3 + m y_2 y_3     (all w <= m,
                                                                      y_i = m - w_i)

  BOTH are proved here in the sharpest form the identity supports, and the light
  branch is STRONGER than the pen statement on three counts: the pen asks for
  `sigma >= 2m`, which the expansion does not need (when `sigma < 2m` the floor
  is negative and the claim is free); it asks for all three weights nonnegative,
  where the identity needs only the one it puts in the special role and the
  conclusion is symmetric; and `0 <= m` follows rather than being assumed.
  The general-arity versions
  `Gtz.pow_mul_sub_le_prod_of_bound_le` and `Gtz.pow_mul_sub_le_prod_of_le_bound`
  are proved by induction on the support, so the vertex-argument heuristic is
  replaced by a proof at every arity.

* **The sqrt-free interface.**  Every consumer of `h` can avoid `Real.sqrt`
  entirely: `signFreeTripleResidual_le_of_sq_le_edgeProduct` turns any rational
  witness `q` with `q^2 <= p` into `h <= sigma - 3 q`, and its converse turns
  `p <= q^2` into a lower bound.  In the pen's substitution `r = sqrt m`,
  `q = sqrt p` the product floor reads `q^2 >= r^4 (sigma - 2 r^2)` and the case
  boundary `81 m^3 >= 1` reads `9 r^3 >= 1`, both polynomial over the rationals.

* **The failure quadratic and its convexity.**  `Psi_m(sigma) =
  (sigma - threshold)^2 - 9 m^2 (sigma - 2m)` is `Gtz.failureQuadratic`.  Failure
  of the residual test forces `Psi > 0` (`lt_failureQuadratic_of_lt_...`), so a
  proof that `Psi <= 0` closes a case.  `Psi` is a monic quadratic in `sigma`,
  hence convex, so it suffices to check the two ENDPOINTS of any interval
  containing `sigma`: `Gtz.quadratic_nonpos_of_endpoints_nonpos` is the general
  standalone fact (any nonnegative lead coefficient, any interval), and
  `Gtz.signFreeTripleResidual_le_of_heavyTriangle_endpoints` /
  `..._of_lightTriangle_endpoints` are the two ready-made case closers of the
  four-case squeeze: hand them a bound, the two branch inequalities and two
  endpoint checks, and they return `h <= threshold`.

## What is NOT in this file

The involution `M^2 = I`, the norm cap `sigma + 2|P| <= 1`, the mirror law, the
criterion (C1) as an iff, and the four-case squeeze itself.  The norm cap enters
here only as a HYPOTHESIS, in `signFreeTripleResidual_le_sub_of_normCap` — which
is the pen's (C3) arithmetic, and is stated for the COHERENT reading only,
because the two-sided reading is false: for `P < 0` one has
`sigma - 3P = sigma + 3|P|` and the cap runs the wrong way.  Working in `h`
rather than in `sigma - 3P` is exactly what makes that trap unreachable.

The tight configuration (two disjoint triangles at `4/9`, nine cross edges at
`1/27`, all twenty triangles at `h = 4/9` exactly) is deliberately absent: it
does NOT refute the weight statement, it witnesses that the constant `4/9`
cannot be lowered, and its exclusion is by the norm cap, not by any weight-level
fact.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {m k : ℕ}

/-! ## 1. The weight variables `w_e = gamma_e^2` -/

/-- **THE EDGE WEIGHT** `w_cd = gamma_cd^2`, the squared direction correlation.
This is the coordinate in which the pen's S4 reduction lives: every quantity the
split test needs is a function of these fifteen numbers, and no sign survives. -/
noncomputable def edgeWeight (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) : ℝ :=
  directionGram D firstIndex secondIndex ^ 2

theorem edgeWeight_comm (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) :
    edgeWeight D firstIndex secondIndex = edgeWeight D secondIndex firstIndex := by
  rw [edgeWeight, edgeWeight, directionGram_comm]

theorem edgeWeight_nonneg (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) :
    0 ≤ edgeWeight D firstIndex secondIndex :=
  sq_nonneg _

/-- Every edge weight is at most one, because the direction Gram is a correlation
matrix (`Gtz.abs_directionGram_le_one`) — no hypothesis, a degenerate atom simply
contributes a zero row. -/
theorem edgeWeight_le_one (D : WeightedDesign m k) (firstIndex secondIndex : Fin m) :
    edgeWeight D firstIndex secondIndex ≤ 1 := by
  have habs := abs_directionGram_le_one D firstIndex secondIndex
  have hsq := sq_abs (directionGram D firstIndex secondIndex)
  have hnonneg := abs_nonneg (directionGram D firstIndex secondIndex)
  rw [edgeWeight, ← hsq]
  nlinarith [habs, hnonneg]

/-- A nondegenerate atom carries weight one on its own diagonal. -/
theorem edgeWeight_self (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) : edgeWeight D atomIndex atomIndex = 1 := by
  rw [edgeWeight, directionGram_self D hpositive, one_pow]

/-! ## 2. The vertex-sum law -/

/-- **THE VERTEX-SUM LAW, at a constant share.**  The row law
`s_a + sum_{d /= a} s_d gamma_ad^2 = 1` with every share equal to `shareValue`
becomes `sum_{d /= a} w_ad = (1 - shareValue)/shareValue`.  Positivity of the
share is not a hypothesis: it is forced at the atom in question by
`D.weight_pos` together with nondegeneracy. -/
theorem sum_erase_edgeWeight_eq_of_atomShare_eq (D : WeightedDesign m k) {shareValue : ℝ}
    (hshare : ∀ otherIndex, atomShare D otherIndex = shareValue) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex
      = (1 - shareValue) / shareValue := by
  have hsharePositive : 0 < shareValue := by
    rw [← hshare atomIndex, atomShare]
    exact mul_pos (D.weight_pos atomIndex) hpositive
  have hrow := atomShare_add_sum_erase_atomShare_mul_sq_directionGram D hpositive
  have hpull : ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 2
      = shareValue * ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        edgeWeight D atomIndex otherIndex := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [hshare otherIndex, edgeWeight]
  rw [hpull, hshare atomIndex] at hrow
  rw [eq_div_iff hsharePositive.ne']
  linear_combination hrow

/-- **THE CONSTANT SHARE IS FORCED TO BE `k/m`.**  The shares sum to the rank
(`Gtz.sum_atomShare_eq_rank`), so a design all of whose shares agree has them all
equal to `k/m` — stated division-free. -/
theorem size_mul_atomShare_eq_rank_of_atomShare_eq (D : WeightedDesign m k) {shareValue : ℝ}
    (hshare : ∀ otherIndex, atomShare D otherIndex = shareValue) :
    (m : ℝ) * shareValue = (k : ℝ) := by
  have hsum := sum_atomShare_eq_rank D
  rw [Finset.sum_congr rfl fun otherIndex _ => hshare otherIndex, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul] at hsum
  exact hsum

/-- **THE VERTEX-SUM LAW, in its sharpest form.**  On ANY equal-share design, of
any size and any rank, every vertex sum of edge weights equals `(m - k)/k`.  At
the `(6,3)` stratum of the pen argument that is `1`, and the total over the
fifteen unordered edges is `3` — the rank.  Only the equality of the shares is
assumed; neither uniform weights nor uniform leverages are needed. -/
theorem sum_erase_edgeWeight_eq_of_equalShare (D : WeightedDesign m k)
    (hshare : ∀ firstIndex secondIndex, atomShare D firstIndex = atomShare D secondIndex)
    {atomIndex : Fin m} (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex
      = ((m : ℝ) - (k : ℝ)) / (k : ℝ) := by
  have hconstant : ∀ otherIndex, atomShare D otherIndex = atomShare D atomIndex :=
    fun otherIndex => hshare otherIndex atomIndex
  have hsharePositive : 0 < atomShare D atomIndex :=
    mul_pos (D.weight_pos atomIndex) hpositive
  have hforced := size_mul_atomShare_eq_rank_of_atomShare_eq D hconstant
  have hsizePositive : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Fin.pos atomIndex
  have hrankPositive : (0 : ℝ) < (k : ℝ) := by
    rw [← hforced]; exact mul_pos hsizePositive hsharePositive
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq D hconstant hpositive,
    div_eq_div_iff hsharePositive.ne' hrankPositive.ne']
  linear_combination -hforced

/-- The `(6,3)` instance of the vertex-sum law under the pen's stratum
hypotheses `t_c = 1/6` and `l_c = 3`: every vertex sum is exactly one.  The
leverage hypothesis is redundant FOR THIS LAW (the share hypothesis alone
suffices — see `sum_erase_edgeWeight_eq_of_equalShare`) but is carried because
the assembly needs it: `Gtz.Dominates` is stated on the design's own atoms and is
not invariant under the rescaling that fixes the shares. -/
theorem sum_erase_edgeWeight_eq_one_of_uniformSixThree (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex : Fin 6, D.weight atomIndex = 1 / 6)
    (hleverage : ∀ atomIndex : Fin 6, leverageOf (D.atom atomIndex) = 3)
    (atomIndex : Fin 6) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex = 1 := by
  have hshare : ∀ otherIndex : Fin 6, atomShare D otherIndex = 1 / 2 := fun otherIndex => by
    rw [atomShare, huniform otherIndex, hleverage otherIndex]; norm_num
  have hpositive : 0 < leverageOf (D.atom atomIndex) := by rw [hleverage atomIndex]; norm_num
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq D hshare hpositive]
  norm_num

/-- **THE TOTAL EDGE BUDGET.**  Summing the vertex-sum law over the atoms:
the ordered off-diagonal total is `m (m - k)/k`, hence the unordered edge total
is half of that.  At `(6,3)` the ordered total is `6` and the edge total is `3`. -/
theorem sum_sum_erase_edgeWeight_eq_of_equalShare (D : WeightedDesign m k)
    (hshare : ∀ firstIndex secondIndex, atomShare D firstIndex = atomShare D secondIndex)
    (hpositive : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex)) :
    ∑ atomIndex : Fin m, ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        edgeWeight D atomIndex otherIndex
      = (m : ℝ) * (((m : ℝ) - (k : ℝ)) / (k : ℝ)) := by
  rw [Finset.sum_congr rfl fun atomIndex _ =>
    sum_erase_edgeWeight_eq_of_equalShare D hshare (hpositive atomIndex), Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul]

/-! ## 3. The sign-free triple residual `h` -/

/-- **THE SIGN-FREE RESIDUAL** `h(w_T) = sigma_T - 3 sqrt(p_T)`.  By the mirror
law this is the criterion value of the BETTER side of a 3-3 split, and it depends
on the edge WEIGHTS alone — the pen's "signs evaporate". -/
noncomputable def signFreeTripleResidual (firstWeight secondWeight thirdWeight : ℝ) : ℝ :=
  firstWeight + secondWeight + thirdWeight
    - 3 * Real.sqrt (firstWeight * secondWeight * thirdWeight)

theorem signFreeTripleResidual_swap_first_second (firstWeight secondWeight thirdWeight : ℝ) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      = signFreeTripleResidual secondWeight firstWeight thirdWeight := by
  simp only [signFreeTripleResidual]
  rw [show firstWeight * secondWeight * thirdWeight
      = secondWeight * firstWeight * thirdWeight from by ring]
  ring

theorem signFreeTripleResidual_swap_second_third (firstWeight secondWeight thirdWeight : ℝ) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      = signFreeTripleResidual firstWeight thirdWeight secondWeight := by
  simp only [signFreeTripleResidual]
  rw [show firstWeight * secondWeight * thirdWeight
      = firstWeight * thirdWeight * secondWeight from by ring]
  ring

/-- `h <= sigma`, unconditionally — the square root is nonnegative.  This single
line is the whole of Case 1 of the four-case squeeze. -/
theorem signFreeTripleResidual_le_sum (firstWeight secondWeight thirdWeight : ℝ) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      ≤ firstWeight + secondWeight + thirdWeight := by
  simp only [signFreeTripleResidual]
  have := Real.sqrt_nonneg (firstWeight * secondWeight * thirdWeight)
  linarith

/-- **CASE 1 OF THE SQUEEZE.**  A triangle all of whose edges are at most `bound`
has residual at most `3 * bound`. -/
theorem signFreeTripleResidual_le_three_mul_of_le_bound {bound firstWeight secondWeight
    thirdWeight : ℝ} (hfirst : firstWeight ≤ bound) (hsecond : secondWeight ≤ bound)
    (hthird : thirdWeight ≤ bound) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 3 * bound :=
  le_trans (signFreeTripleResidual_le_sum firstWeight secondWeight thirdWeight) (by linarith)

/-- **`|P| = sqrt(p)`.**  The oriented triangle product's magnitude is the square
root of the weight product — the identity that makes `h` a function of the
weights. -/
theorem sqrt_sq_mul_sq_mul_sq (firstGram secondGram thirdGram : ℝ) :
    Real.sqrt (firstGram ^ 2 * secondGram ^ 2 * thirdGram ^ 2)
      = |firstGram * secondGram * thirdGram| := by
  rw [show firstGram ^ 2 * secondGram ^ 2 * thirdGram ^ 2
      = (firstGram * secondGram * thirdGram) ^ 2 from by ring, Real.sqrt_sq_eq_abs]

/-- In the correlation coordinates, `h = sigma - 3 |P|`. -/
theorem signFreeTripleResidual_sq_eq_sub_abs (firstGram secondGram thirdGram : ℝ) :
    signFreeTripleResidual (firstGram ^ 2) (secondGram ^ 2) (thirdGram ^ 2)
      = firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
        - 3 * |firstGram * secondGram * thirdGram| := by
  rw [signFreeTripleResidual, sqrt_sq_mul_sq_mul_sq]

/-- **THE SPLIT REDUCTION.**  `h` is the minimum of the two sign readings of the
criterion, `sigma - 3P` and `sigma + 3P`.  Combined with the mirror law S2 —
which says the complementary triple of a 3-3 split has the same `sigma` and the
opposite `P` — this says exactly that `h` is the criterion value of the better
side of the split.  The mirror is NOT assumed here: what is proved is the
arithmetic identity, which is what the mirror is then applied to. -/
theorem signFreeTripleResidual_sq_eq_min (firstGram secondGram thirdGram : ℝ) :
    signFreeTripleResidual (firstGram ^ 2) (secondGram ^ 2) (thirdGram ^ 2)
      = min (firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
              - 3 * (firstGram * secondGram * thirdGram))
            (firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
              + 3 * (firstGram * secondGram * thirdGram)) := by
  rw [signFreeTripleResidual_sq_eq_sub_abs]
  rcases abs_cases (firstGram * secondGram * thirdGram) with ⟨habs, _⟩ | ⟨habs, _⟩ <;>
    rw [habs] <;> rw [min_def] <;> split <;> linarith

/-- On the COHERENT branch `0 <= P` the sign-free residual IS the criterion
value.  This is the branch the mirror selects, and the only branch on which the
pen's (C3) is true. -/
theorem signFreeTripleResidual_sq_eq_of_nonneg_product {firstGram secondGram thirdGram : ℝ}
    (hcoherent : 0 ≤ firstGram * secondGram * thirdGram) :
    signFreeTripleResidual (firstGram ^ 2) (secondGram ^ 2) (thirdGram ^ 2)
      = firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
        - 3 * (firstGram * secondGram * thirdGram) := by
  rw [signFreeTripleResidual_sq_eq_min, min_eq_left (by linarith)]

/-- The sign-free residual never exceeds either sign reading. -/
theorem signFreeTripleResidual_sq_le_sub (firstGram secondGram thirdGram : ℝ) :
    signFreeTripleResidual (firstGram ^ 2) (secondGram ^ 2) (thirdGram ^ 2)
      ≤ firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
        - 3 * (firstGram * secondGram * thirdGram) := by
  rw [signFreeTripleResidual_sq_eq_min]; exact min_le_left _ _

theorem signFreeTripleResidual_sq_le_add (firstGram secondGram thirdGram : ℝ) :
    signFreeTripleResidual (firstGram ^ 2) (secondGram ^ 2) (thirdGram ^ 2)
      ≤ firstGram ^ 2 + secondGram ^ 2 + thirdGram ^ 2
        + 3 * (firstGram * secondGram * thirdGram) := by
  rw [signFreeTripleResidual_sq_eq_min]; exact min_le_right _ _

/-! ### The square-root-free interface

Every downstream case of the squeeze is closed by exhibiting a RATIONAL witness
`q` for the square root: `q^2 <= p` bounds `h` above, `p <= q^2` bounds it below.
No consumer of this file has to touch `Real.sqrt`. -/

/-- **SQRT-FREE UPPER BOUND.**  Any witness `q >= 0` with `q^2 <= p` gives
`h <= sigma - 3 q`.  In the pen's substitution this is what turns Case 4 into a
polynomial statement: at `w_e >= r^2` for all three edges, `q = r^3` works. -/
theorem signFreeTripleResidual_le_of_sq_le_edgeProduct {productRoot firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ productRoot)
    (hsq : productRoot ^ 2 ≤ firstWeight * secondWeight * thirdWeight) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight
      ≤ firstWeight + secondWeight + thirdWeight - 3 * productRoot := by
  have hle : productRoot ≤ Real.sqrt (firstWeight * secondWeight * thirdWeight) :=
    (Real.le_sqrt hrootNonneg (le_trans (sq_nonneg productRoot) hsq)).mpr hsq
  simp only [signFreeTripleResidual]
  linarith

/-- **SQRT-FREE LOWER BOUND.**  Any witness `q >= 0` with `p <= q^2` gives
`sigma - 3 q <= h`. -/
theorem sub_le_signFreeTripleResidual_of_edgeProduct_le_sq {productRoot firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ productRoot)
    (hsq : firstWeight * secondWeight * thirdWeight ≤ productRoot ^ 2) :
    firstWeight + secondWeight + thirdWeight - 3 * productRoot
      ≤ signFreeTripleResidual firstWeight secondWeight thirdWeight := by
  have hle : Real.sqrt (firstWeight * secondWeight * thirdWeight) ≤ productRoot :=
    le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq (Real.sqrt_sq hrootNonneg))
  simp only [signFreeTripleResidual]
  linarith

/-- **CASE 4 OF THE SQUEEZE, the pen's (C3), in sqrt-free form.**  Under the norm
cap `sigma + 2 q <= capValue` and a lower witness `q^2 <= p`, the residual obeys
`h <= capValue - 5 q`.  At `capValue = 1` and `q >= 1/9` this is `h <= 4/9`.

The cap is a HYPOTHESIS: it is the pen's (C2), which is where realness is
consumed, and it is proved in the involution layer, not here.  Note that the
statement is about `h`, not about `sigma - 3P`; that is deliberate, since the
naive two-sided reading of (C3) is FALSE on the incoherent branch, where
`sigma - 3P = sigma + 3|P|` and the cap runs the wrong way.  Working in `h`
makes the wrong branch unreachable. -/
theorem signFreeTripleResidual_le_sub_of_normCap {productRoot capValue firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ productRoot)
    (hsq : productRoot ^ 2 ≤ firstWeight * secondWeight * thirdWeight)
    (hcap : firstWeight + secondWeight + thirdWeight + 2 * productRoot ≤ capValue) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ capValue - 5 * productRoot := by
  have hupper := signFreeTripleResidual_le_of_sq_le_edgeProduct hrootNonneg hsq
  linarith

/-! ## 4. The product floor -/

/-- **THE PRODUCT FLOOR VALUE** `m^2 (sigma - 2m)`.  Named after the pen's S5
step; the repository's `Gtz.productFloorCell` is an unrelated decision-cell
parameter and must not be confused with it. -/
def triangleProductFloor (bound edgeSum : ℝ) : ℝ :=
  bound ^ 2 * (edgeSum - 2 * bound)

/-- **THE PRODUCT FLOOR, HEAVY BRANCH.**  A triangle all of whose edges are at
least `bound >= 0` has `p >= bound^2 (sigma - 2 bound)`.  The pen argues by
multilinearity and vertex enumeration; the substitution `w_i = bound + x_i` turns
the claim into the polynomial identity

    p - bound^2 (sigma - 2 bound) = bound * e_2(x) + e_3(x),

whose right side is manifestly nonnegative.  No upper bound on the weights is
needed — the vertex-enumeration route silently requires one. -/
theorem triangleProductFloor_le_edgeProduct_of_bound_le {bound firstWeight secondWeight
    thirdWeight : ℝ} (hboundNonneg : 0 ≤ bound) (hfirst : bound ≤ firstWeight)
    (hsecond : bound ≤ secondWeight) (hthird : bound ≤ thirdWeight) :
    triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      ≤ firstWeight * secondWeight * thirdWeight := by
  have hkey : firstWeight * secondWeight * thirdWeight
        - triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      = bound * ((firstWeight - bound) * (secondWeight - bound)
            + (firstWeight - bound) * (thirdWeight - bound)
            + (secondWeight - bound) * (thirdWeight - bound))
        + (firstWeight - bound) * (secondWeight - bound) * (thirdWeight - bound) := by
    simp only [triangleProductFloor]; ring
  have hfirstGap : (0 : ℝ) ≤ firstWeight - bound := by linarith
  have hsecondGap : (0 : ℝ) ≤ secondWeight - bound := by linarith
  have hthirdGap : (0 : ℝ) ≤ thirdWeight - bound := by linarith
  have hpairOne := mul_nonneg hfirstGap hsecondGap
  have hpairTwo := mul_nonneg hfirstGap hthirdGap
  have hpairThree := mul_nonneg hsecondGap hthirdGap
  have htriple := mul_nonneg hpairOne hthirdGap
  have hbracket := mul_nonneg hboundNonneg (by linarith : (0 : ℝ) ≤
    (firstWeight - bound) * (secondWeight - bound) + (firstWeight - bound) * (thirdWeight - bound)
      + (secondWeight - bound) * (thirdWeight - bound))
  linarith

/-- **THE PRODUCT FLOOR, LIGHT BRANCH.**  A triangle all of whose edges are at
most `bound`, ONE of them nonnegative, has `p >= bound^2 (sigma - 2 bound)`.  The
substitution `w_i = bound - y_i` turns the claim into

    p - bound^2 (sigma - 2 bound)
      = y_1 y_2 w_3 + bound * y_1 y_3 + bound * y_2 y_3,

every term nonnegative.  Three hypotheses of the pen statement are therefore
unnecessary and are NOT assumed here.  The pen asks for `sigma >= 2 bound`; the
identity does not need it, and indeed when `sigma < 2 bound` the floor is
negative and the claim is free.  The pen asks for all three weights nonnegative;
the identity needs only the one it puts in the special role, and the conclusion
is symmetric, so any one of the three suffices — `thirdWeight` is chosen here.
And `0 <= bound` follows from `0 <= w_3 <= bound` rather than being assumed.

The only consumer that genuinely needs more is the four-case squeeze, whose
weights are squared correlations and hence nonnegative on the nose. -/
theorem triangleProductFloor_le_edgeProduct_of_le_bound {bound firstWeight secondWeight
    thirdWeight : ℝ} (hthirdNonneg : 0 ≤ thirdWeight) (hfirst : firstWeight ≤ bound)
    (hsecond : secondWeight ≤ bound) (hthird : thirdWeight ≤ bound) :
    triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      ≤ firstWeight * secondWeight * thirdWeight := by
  have hboundNonneg : (0 : ℝ) ≤ bound := le_trans hthirdNonneg hthird
  have hkey : firstWeight * secondWeight * thirdWeight
        - triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      = (bound - firstWeight) * (bound - secondWeight) * thirdWeight
        + bound * ((bound - firstWeight) * (bound - thirdWeight))
        + bound * ((bound - secondWeight) * (bound - thirdWeight)) := by
    simp only [triangleProductFloor]; ring
  have hfirstGap : (0 : ℝ) ≤ bound - firstWeight := by linarith
  have hsecondGap : (0 : ℝ) ≤ bound - secondWeight := by linarith
  have hthirdGap : (0 : ℝ) ≤ bound - thirdWeight := by linarith
  have htermOne := mul_nonneg (mul_nonneg hfirstGap hsecondGap) hthirdNonneg
  have htermTwo := mul_nonneg hboundNonneg (mul_nonneg hfirstGap hthirdGap)
  have htermThree := mul_nonneg hboundNonneg (mul_nonneg hsecondGap hthirdGap)
  linarith

/-! ### The product floor in the polynomial coordinates `r = sqrt m`, `q = sqrt p`

The pen's implementation hint: substituting `m = r^2` removes every square root
from the squeeze.  The floor becomes `q^2 >= r^4 (sigma - 2 r^2)`, the case
boundary `81 m^3 >= 1` becomes `9 r^3 >= 1`, and Case 4's product bound
`sqrt p >= m^(3/2)` becomes `(r^3)^2 <= p`. -/

/-- The heavy product floor in the root coordinate: no sign hypothesis on `r` is
needed, because `r^2 >= 0` always. -/
theorem rootProductFloor_le_edgeProduct_of_sq_le {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight) :
    rootBound ^ 4 * (firstWeight + secondWeight + thirdWeight - 2 * rootBound ^ 2)
      ≤ firstWeight * secondWeight * thirdWeight := by
  have hfloor := triangleProductFloor_le_edgeProduct_of_bound_le (bound := rootBound ^ 2)
    (sq_nonneg rootBound) hfirst hsecond hthird
  simp only [triangleProductFloor] at hfloor
  nlinarith [hfloor]

/-- The light product floor in the root coordinate. -/
theorem rootProductFloor_le_edgeProduct_of_le_sq {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hthirdNonneg : 0 ≤ thirdWeight) (hfirst : firstWeight ≤ rootBound ^ 2)
    (hsecond : secondWeight ≤ rootBound ^ 2) (hthird : thirdWeight ≤ rootBound ^ 2) :
    rootBound ^ 4 * (firstWeight + secondWeight + thirdWeight - 2 * rootBound ^ 2)
      ≤ firstWeight * secondWeight * thirdWeight := by
  have hfloor := triangleProductFloor_le_edgeProduct_of_le_bound (bound := rootBound ^ 2)
    hthirdNonneg hfirst hsecond hthird
  simp only [triangleProductFloor] at hfloor
  nlinarith [hfloor]

/-- **CASE 4'S PRODUCT BOUND**, sqrt-free: a triangle all of whose edges are at
least `r^2` has `p >= (r^3)^2`, so `r^3` is an admissible witness for
`signFreeTripleResidual_le_of_sq_le_edgeProduct`. -/
theorem sq_pow_three_le_edgeProduct_of_sq_le {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight) :
    (rootBound ^ 3) ^ 2 ≤ firstWeight * secondWeight * thirdWeight := by
  have hsquareNonneg : (0 : ℝ) ≤ rootBound ^ 2 := sq_nonneg rootBound
  have hfirstNonneg : (0 : ℝ) ≤ firstWeight := le_trans hsquareNonneg hfirst
  have hsecondNonneg : (0 : ℝ) ≤ secondWeight := le_trans hsquareNonneg hsecond
  have hpair : rootBound ^ 2 * rootBound ^ 2 ≤ firstWeight * secondWeight :=
    mul_le_mul hfirst hsecond hsquareNonneg hfirstNonneg
  have htriple : rootBound ^ 2 * rootBound ^ 2 * rootBound ^ 2
      ≤ firstWeight * secondWeight * thirdWeight :=
    mul_le_mul hpair hthird hsquareNonneg (mul_nonneg hfirstNonneg hsecondNonneg)
  nlinarith [htriple]

/-! ### The product floor at every arity

The three-variable identities above are sharp, but the same statement holds for
any number of edges, and the pen's appeal to "the minimum of a multilinear
function on a box is attained at a vertex" is replaced here by an induction on
the support.  Both branches share one algebraic step:

    alpha * A - bound^(n+1) * alpha  >=  bound * (A - bound^(n+1))

which holds when `alpha >= bound` and `A >= bound^(n+1)` (heavy branch) and
equally when `alpha <= bound` and `A <= bound^(n+1)` (light branch). -/

/-- **THE PRODUCT FLOOR AT EVERY ARITY, HEAVY BRANCH.**  For a support of
cardinality `n + 1` all of whose weights are at least `bound >= 0`,

    bound^n * (sum of the weights - n * bound)  <=  product of the weights.

At `n = 2` this is `triangleProductFloor_le_edgeProduct_of_bound_le`. -/
theorem pow_mul_sub_le_prod_of_bound_le {index : Type*} [DecidableEq index] {bound : ℝ}
    (hboundNonneg : 0 ≤ bound) (weight : index → ℝ) (size : ℕ) :
    ∀ support : Finset index, support.card = size + 1 → (∀ i ∈ support, bound ≤ weight i) →
      bound ^ size * (∑ i ∈ support, weight i - (size : ℝ) * bound)
        ≤ ∏ i ∈ support, weight i := by
  induction size with
  | zero =>
    intro support hcard _
    obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hcard
    subst honly
    simp
  | succ predecessor inductionHypothesis =>
    intro support hcard hlower
    have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨chosen, hchosen⟩ := hnonempty
    set remaining := support.erase chosen with hremaining
    have hremainingCard : remaining.card = predecessor + 1 := by
      rw [hremaining, Finset.card_erase_of_mem hchosen, hcard]
      omega
    have hremainingLower : ∀ i ∈ remaining, bound ≤ weight i := fun i hmember =>
      hlower i (Finset.mem_of_mem_erase hmember)
    have hinner := inductionHypothesis remaining hremainingCard hremainingLower
    have hproductLower : bound ^ (predecessor + 1) ≤ ∏ i ∈ remaining, weight i := by
      have hconstant : ∏ _i ∈ remaining, bound = bound ^ (predecessor + 1) := by
        rw [Finset.prod_const, hremainingCard]
      rw [← hconstant]
      exact Finset.prod_le_prod (fun i _ => hboundNonneg) hremainingLower
    have hsumSplit : ∑ i ∈ support, weight i = weight chosen + ∑ i ∈ remaining, weight i := by
      rw [hremaining, Finset.add_sum_erase support weight hchosen]
    have hproductSplit : ∏ i ∈ support, weight i
        = weight chosen * ∏ i ∈ remaining, weight i := by
      rw [hremaining, Finset.mul_prod_erase support weight hchosen]
    have hpowerNonneg : (0 : ℝ) ≤ bound ^ predecessor := pow_nonneg hboundNonneg predecessor
    have hstepOne : (0 : ℝ) ≤ (weight chosen - bound)
        * (∏ i ∈ remaining, weight i - bound ^ predecessor * bound) := by
      refine mul_nonneg (by linarith [hlower chosen hchosen]) ?_
      have : bound ^ predecessor * bound = bound ^ (predecessor + 1) := (pow_succ bound _).symm
      linarith [hproductLower, this]
    have hstepTwo : (0 : ℝ) ≤ bound * (∏ i ∈ remaining, weight i
        - bound ^ predecessor * (∑ i ∈ remaining, weight i - (predecessor : ℝ) * bound)) :=
      mul_nonneg hboundNonneg (by linarith)
    rw [hsumSplit, hproductSplit, pow_succ]
    push_cast
    nlinarith [hstepOne, hstepTwo]

/-- **THE PRODUCT FLOOR AT EVERY ARITY, LIGHT BRANCH.**  For a support of
cardinality `n + 1` all of whose weights lie in `[0, bound]`, the same floor
holds.  At `n = 2` this is `triangleProductFloor_le_edgeProduct_of_le_bound`. -/
theorem pow_mul_sub_le_prod_of_le_bound {index : Type*} [DecidableEq index] {bound : ℝ}
    (weight : index → ℝ) (size : ℕ) :
    ∀ support : Finset index, support.card = size + 1 → (∀ i ∈ support, 0 ≤ weight i) →
      (∀ i ∈ support, weight i ≤ bound) →
      bound ^ size * (∑ i ∈ support, weight i - (size : ℝ) * bound)
        ≤ ∏ i ∈ support, weight i := by
  induction size with
  | zero =>
    intro support hcard _ _
    obtain ⟨only, honly⟩ := Finset.card_eq_one.mp hcard
    subst honly
    simp
  | succ predecessor inductionHypothesis =>
    intro support hcard hnonneg hupper
    have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨chosen, hchosen⟩ := hnonempty
    have hboundNonneg : (0 : ℝ) ≤ bound := le_trans (hnonneg chosen hchosen) (hupper chosen hchosen)
    set remaining := support.erase chosen with hremaining
    have hremainingCard : remaining.card = predecessor + 1 := by
      rw [hremaining, Finset.card_erase_of_mem hchosen, hcard]
      omega
    have hremainingNonneg : ∀ i ∈ remaining, 0 ≤ weight i := fun i hmember =>
      hnonneg i (Finset.mem_of_mem_erase hmember)
    have hremainingUpper : ∀ i ∈ remaining, weight i ≤ bound := fun i hmember =>
      hupper i (Finset.mem_of_mem_erase hmember)
    have hinner := inductionHypothesis remaining hremainingCard hremainingNonneg hremainingUpper
    have hproductUpper : ∏ i ∈ remaining, weight i ≤ bound ^ (predecessor + 1) := by
      have hconstant : ∏ _i ∈ remaining, bound = bound ^ (predecessor + 1) := by
        rw [Finset.prod_const, hremainingCard]
      rw [← hconstant]
      exact Finset.prod_le_prod hremainingNonneg hremainingUpper
    have hsumSplit : ∑ i ∈ support, weight i = weight chosen + ∑ i ∈ remaining, weight i := by
      rw [hremaining, Finset.add_sum_erase support weight hchosen]
    have hproductSplit : ∏ i ∈ support, weight i
        = weight chosen * ∏ i ∈ remaining, weight i := by
      rw [hremaining, Finset.mul_prod_erase support weight hchosen]
    have hpowerNonneg : (0 : ℝ) ≤ bound ^ predecessor := pow_nonneg hboundNonneg predecessor
    have hstepOne : (0 : ℝ) ≤ (bound - weight chosen)
        * (bound ^ predecessor * bound - ∏ i ∈ remaining, weight i) := by
      refine mul_nonneg (by linarith [hupper chosen hchosen]) ?_
      have : bound ^ predecessor * bound = bound ^ (predecessor + 1) := (pow_succ bound _).symm
      linarith [hproductUpper, this]
    have hstepTwo : (0 : ℝ) ≤ bound * (∏ i ∈ remaining, weight i
        - bound ^ predecessor * (∑ i ∈ remaining, weight i - (predecessor : ℝ) * bound)) :=
      mul_nonneg hboundNonneg (by linarith)
    rw [hsumSplit, hproductSplit, pow_succ]
    push_cast
    nlinarith [hstepOne, hstepTwo]

/-! ## 5. The failure quadratic -/

/-- **THE FAILURE QUADRATIC**
`Psi_m(sigma) = (sigma - threshold)^2 - 9 m^2 (sigma - 2m)`.  Failure of the
residual test at a triangle carrying the product floor forces `Psi > 0`, so any
proof that `Psi <= 0` closes the case.  It is monic in `sigma`, hence convex. -/
def failureQuadratic (threshold bound edgeSum : ℝ) : ℝ :=
  (edgeSum - threshold) ^ 2 - 9 * triangleProductFloor bound edgeSum

theorem failureQuadratic_eq (threshold bound edgeSum : ℝ) :
    failureQuadratic threshold bound edgeSum
      = (edgeSum - threshold) ^ 2 - 9 * bound ^ 2 * (edgeSum - 2 * bound) := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- The failure quadratic in the root coordinate `m = r^2`: fully polynomial in
`(threshold, r, sigma)`, no square root anywhere. -/
theorem failureQuadratic_sq (threshold rootBound edgeSum : ℝ) :
    failureQuadratic threshold (rootBound ^ 2) edgeSum
      = (edgeSum - threshold) ^ 2 - 9 * rootBound ^ 4 * (edgeSum - 2 * rootBound ^ 2) := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- The failure quadratic written out as a quadratic in `sigma`, with lead
coefficient one. -/
theorem failureQuadratic_expand (threshold bound edgeSum : ℝ) :
    failureQuadratic threshold bound edgeSum
      = 1 * edgeSum ^ 2 + (-(2 * threshold + 9 * bound ^ 2)) * edgeSum
        + (threshold ^ 2 + 18 * bound ^ 3) := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- **FAILURE FORCES `Psi > 0`.**  If the sign-free residual of a triangle
carrying the product floor exceeds the threshold then the failure quadratic is
strictly positive at its edge sum.  This is the pen's

    sigma - 4/9 > 3 sqrt p >= 0  ==>  (sigma - 4/9)^2 > 9 p >= 9 m^2 (sigma - 2m),

with the threshold left general.  Nonnegativity of the weight product is NOT a
hypothesis: when the product is negative the floor is negative too, so the
quadratic is positive for free — Lean's `Real.sqrt` junk value on the negatives
does not have to be fenced. -/
theorem lt_failureQuadratic_of_lt_signFreeTripleResidual {threshold bound firstWeight secondWeight
    thirdWeight : ℝ}
    (hfloor : triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      ≤ firstWeight * secondWeight * thirdWeight)
    (hfailure : threshold < signFreeTripleResidual firstWeight secondWeight thirdWeight) :
    0 < failureQuadratic threshold bound (firstWeight + secondWeight + thirdWeight) := by
  rcases le_or_gt 0 (firstWeight * secondWeight * thirdWeight) with hproductNonneg | hproductNeg
  · set productRoot := Real.sqrt (firstWeight * secondWeight * thirdWeight) with hproductRoot
    have hrootNonneg : 0 ≤ productRoot := Real.sqrt_nonneg _
    have hrootSq : productRoot ^ 2 = firstWeight * secondWeight * thirdWeight :=
      Real.sq_sqrt hproductNonneg
    have hgap : 3 * productRoot < firstWeight + secondWeight + thirdWeight - threshold := by
      simp only [signFreeTripleResidual, ← hproductRoot] at hfailure
      linarith
    have hleftFactor : (0 : ℝ)
        < firstWeight + secondWeight + thirdWeight - threshold - 3 * productRoot := by linarith
    have hrightFactor : (0 : ℝ)
        < firstWeight + secondWeight + thirdWeight - threshold + 3 * productRoot := by linarith
    have hfactored := mul_pos hleftFactor hrightFactor
    have hzero : productRoot ^ 2 - firstWeight * secondWeight * thirdWeight = 0 := by
      rw [hrootSq]; ring
    simp only [failureQuadratic]
    linarith
  · simp only [failureQuadratic]
    linarith [sq_nonneg (firstWeight + secondWeight + thirdWeight - threshold), hfloor,
      hproductNeg]

/-- **`Psi <= 0` CLOSES THE TEST.**  The contrapositive of the previous theorem,
and the form the squeeze actually applies: a triangle carrying the product floor
whose failure quadratic is nonpositive at its edge sum has residual at most the
threshold. -/
theorem signFreeTripleResidual_le_of_failureQuadratic_nonpos {threshold bound firstWeight
    secondWeight thirdWeight : ℝ}
    (hfloor : triangleProductFloor bound (firstWeight + secondWeight + thirdWeight)
      ≤ firstWeight * secondWeight * thirdWeight)
    (hquadratic : failureQuadratic threshold bound
      (firstWeight + secondWeight + thirdWeight) ≤ 0) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ threshold := by
  by_contra hcontra
  exact absurd hquadratic (not_le.mpr (lt_failureQuadratic_of_lt_signFreeTripleResidual
    hfloor (not_le.mp hcontra)))

/-! ## 6. Convexity: a convex quadratic nonpositive at both endpoints -/

/-- **CONVEXITY, AS A REUSABLE FACT.**  A quadratic with nonnegative lead
coefficient that is nonpositive at both endpoints of an interval is nonpositive
throughout it.  The proof is the Lagrange identity

    (upper - lower) Q(x)
      = (upper - x) Q(lower) + (x - lower) Q(upper)
        - leadCoeff (upper - x)(x - lower)(upper - lower),

so no analysis and no `Convex` API is involved.  The degenerate interval
`lower = upper` is handled separately rather than excluded. -/
theorem quadratic_nonpos_of_endpoints_nonpos {leadCoeff linearCoeff constCoeff lower upper
    point : ℝ} (hconvex : 0 ≤ leadCoeff)
    (hlowerNonpos : leadCoeff * lower ^ 2 + linearCoeff * lower + constCoeff ≤ 0)
    (hupperNonpos : leadCoeff * upper ^ 2 + linearCoeff * upper + constCoeff ≤ 0)
    (hlower : lower ≤ point) (hupper : point ≤ upper) :
    leadCoeff * point ^ 2 + linearCoeff * point + constCoeff ≤ 0 := by
  rcases eq_or_lt_of_le (hlower.trans hupper) with hdegenerate | hproper
  · have hpoint : point = lower := le_antisymm (by linarith) hlower
    rw [hpoint]; exact hlowerNonpos
  · have hwidth : (0 : ℝ) < upper - lower := by linarith
    have hkey : (upper - lower) * (leadCoeff * point ^ 2 + linearCoeff * point + constCoeff)
        = (upper - point) * (leadCoeff * lower ^ 2 + linearCoeff * lower + constCoeff)
          + (point - lower) * (leadCoeff * upper ^ 2 + linearCoeff * upper + constCoeff)
          - leadCoeff * ((upper - point) * ((point - lower) * (upper - lower))) := by ring
    have htermLower : (upper - point) * (leadCoeff * lower ^ 2 + linearCoeff * lower
        + constCoeff) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hlowerNonpos
    have htermUpper : (point - lower) * (leadCoeff * upper ^ 2 + linearCoeff * upper
        + constCoeff) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hupperNonpos
    have htermLead : (0 : ℝ) ≤ leadCoeff * ((upper - point) * ((point - lower)
        * (upper - lower))) :=
      mul_nonneg hconvex (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
    have hscaled : (upper - lower) * (leadCoeff * point ^ 2 + linearCoeff * point
        + constCoeff) ≤ 0 := by rw [hkey]; linarith
    by_contra hcontra
    exact absurd hscaled (not_le.mpr (mul_pos hwidth (not_le.mp hcontra)))

/-- The strict companion: a convex quadratic strictly negative at both endpoints
is strictly negative throughout the interval. -/
theorem quadratic_neg_of_endpoints_neg {leadCoeff linearCoeff constCoeff lower upper
    point : ℝ} (hconvex : 0 ≤ leadCoeff)
    (hlowerNeg : leadCoeff * lower ^ 2 + linearCoeff * lower + constCoeff < 0)
    (hupperNeg : leadCoeff * upper ^ 2 + linearCoeff * upper + constCoeff < 0)
    (hlower : lower ≤ point) (hupper : point ≤ upper) :
    leadCoeff * point ^ 2 + linearCoeff * point + constCoeff < 0 := by
  rcases eq_or_lt_of_le hlower with hatLower | hstrictLower
  · rw [← hatLower]; exact hlowerNeg
  · have hwidth : (0 : ℝ) < upper - lower := by linarith
    have hkey : (upper - lower) * (leadCoeff * point ^ 2 + linearCoeff * point + constCoeff)
        = (upper - point) * (leadCoeff * lower ^ 2 + linearCoeff * lower + constCoeff)
          + (point - lower) * (leadCoeff * upper ^ 2 + linearCoeff * upper + constCoeff)
          - leadCoeff * ((upper - point) * ((point - lower) * (upper - lower))) := by ring
    have htermLead : (0 : ℝ) ≤ leadCoeff * ((upper - point) * ((point - lower)
        * (upper - lower))) :=
      mul_nonneg hconvex (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
    have htermLower : (upper - point) * (leadCoeff * lower ^ 2 + linearCoeff * lower
        + constCoeff) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hlowerNeg.le
    have htermUpper : (point - lower) * (leadCoeff * upper ^ 2 + linearCoeff * upper
        + constCoeff) < 0 := mul_neg_of_pos_of_neg (by linarith) hupperNeg
    have hscaled : (upper - lower) * (leadCoeff * point ^ 2 + linearCoeff * point
        + constCoeff) < 0 := by rw [hkey]; linarith
    by_contra hcontra
    exact absurd hscaled (not_lt.mpr (mul_nonneg hwidth.le (not_lt.mp hcontra)))

/-- **THE ENDPOINT TEST FOR `Psi`.**  The failure quadratic is monic in its edge
sum, hence convex, so two endpoint checks bound it on the whole interval.  This
is what replaces every interior estimate in Cases 2 and 3 of the squeeze. -/
theorem failureQuadratic_nonpos_of_endpoints_nonpos {threshold bound lower upper edgeSum : ℝ}
    (hlowerNonpos : failureQuadratic threshold bound lower ≤ 0)
    (hupperNonpos : failureQuadratic threshold bound upper ≤ 0)
    (hlower : lower ≤ edgeSum) (hupper : edgeSum ≤ upper) :
    failureQuadratic threshold bound edgeSum ≤ 0 := by
  rw [failureQuadratic_expand] at hlowerNonpos hupperNonpos ⊢
  exact quadratic_nonpos_of_endpoints_nonpos zero_le_one hlowerNonpos hupperNonpos hlower hupper

/-! ## 7. The four-case squeeze, at the weight level

The two generic closers below take a bound, a branch and two endpoint checks.
The subsection after them spends those checks once and for all at the pen's
threshold `4/9`, so that the four cases of S5 become four named theorems about
real numbers, with no design, no domination and no square root in sight. -/

/-- **CASE CLOSER, HEAVY BRANCH** (the squeeze's Case 3).  A triangle whose edges
are all at least `bound >= 0` and whose edge sum lies in an interval at both ends
of which the failure quadratic is nonpositive has residual at most `threshold`.
The caller supplies exactly two polynomial checks. -/
theorem signFreeTripleResidual_le_of_heavyTriangle_endpoints {threshold bound lower upper
    firstWeight secondWeight thirdWeight : ℝ} (hboundNonneg : 0 ≤ bound)
    (hfirst : bound ≤ firstWeight) (hsecond : bound ≤ secondWeight)
    (hthird : bound ≤ thirdWeight)
    (hlowerNonpos : failureQuadratic threshold bound lower ≤ 0)
    (hupperNonpos : failureQuadratic threshold bound upper ≤ 0)
    (hlower : lower ≤ firstWeight + secondWeight + thirdWeight)
    (hupper : firstWeight + secondWeight + thirdWeight ≤ upper) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ threshold :=
  signFreeTripleResidual_le_of_failureQuadratic_nonpos
    (triangleProductFloor_le_edgeProduct_of_bound_le hboundNonneg hfirst hsecond hthird)
    (failureQuadratic_nonpos_of_endpoints_nonpos hlowerNonpos hupperNonpos hlower hupper)

/-- **CASE CLOSER, LIGHT BRANCH** (the squeeze's Case 2).  A triangle whose edges
are all at most `bound`, one of them nonnegative, and whose edge sum lies in an
interval at both ends of which the failure quadratic is nonpositive, has residual
at most `threshold`. -/
theorem signFreeTripleResidual_le_of_lightTriangle_endpoints {threshold bound lower upper
    firstWeight secondWeight thirdWeight : ℝ} (hthirdNonneg : 0 ≤ thirdWeight)
    (hfirst : firstWeight ≤ bound) (hsecond : secondWeight ≤ bound) (hthird : thirdWeight ≤ bound)
    (hlowerNonpos : failureQuadratic threshold bound lower ≤ 0)
    (hupperNonpos : failureQuadratic threshold bound upper ≤ 0)
    (hlower : lower ≤ firstWeight + secondWeight + thirdWeight)
    (hupper : firstWeight + secondWeight + thirdWeight ≤ upper) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ threshold :=
  signFreeTripleResidual_le_of_failureQuadratic_nonpos
    (triangleProductFloor_le_edgeProduct_of_le_bound hthirdNonneg hfirst hsecond hthird)
    (failureQuadratic_nonpos_of_endpoints_nonpos hlowerNonpos hupperNonpos hlower hupper)

/-! ### The endpoint values of `Psi`, and the factorisation that explains `4/9` -/

/-- `Psi` at the threshold itself: `Psi_m(threshold) = -9 m^2 (threshold - 2m)`. -/
theorem failureQuadratic_at_threshold (threshold bound : ℝ) :
    failureQuadratic threshold bound threshold = -(9 * bound ^ 2 * (threshold - 2 * bound)) := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- The left-endpoint check of the squeeze's Case 2: `Psi_m(threshold) <= 0` for
every `m` with `2m <= threshold`.  At the pen's threshold that is `m <= 2/9`,
which is exactly the upper end of Case 2's range. -/
theorem failureQuadratic_at_threshold_nonpos {threshold bound : ℝ}
    (hbound : 2 * bound ≤ threshold) : failureQuadratic threshold bound threshold ≤ 0 := by
  rw [failureQuadratic_at_threshold]
  exact neg_nonpos.mpr (mul_nonneg (by positivity) (by linarith))

/-- `Psi` at `sigma = 3m`, the light triangle's largest possible edge sum. -/
theorem failureQuadratic_at_three_mul (threshold bound : ℝ) :
    failureQuadratic threshold bound (3 * bound) = (3 * bound - threshold) ^ 2 - 9 * bound ^ 3 := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- **THE FACTORISATION THAT EXPLAINS THE CONSTANT `4/9`.**  At the pen's
threshold the value of `Psi` at `sigma = 3m` is minus the pen's cubic

    rho(m) = 9 m^3 - 9 m^2 + (8/3) m - 16/81,

and that cubic factors exactly:

    rho(m) = 9 (m - 1/9) (m - 4/9)^2.

The simple root `m = 1/9` is the square of the tetrahedral tripod's correlation
`-1/3` — the tie, where the criterion holds with equality — and the DOUBLE root
`m = 4/9` is the square of `2/3`, the tangency at which the tight weight
configuration sits and which the norm cap excludes.  One identity therefore
replaces all three of the pen's separate rational evaluations
(`rho(4/27) = 576/19683`, `rho(2/9) = 4/81`, and the `9^(-2/3)` endpoint) and
shows that `Psi_m(3m) <= 0` on the whole range `m >= 1/9`, not just on the two
intervals the pen checks. -/
theorem failureQuadratic_four_ninths_at_three_mul (bound : ℝ) :
    failureQuadratic (4 / 9) bound (3 * bound)
      = -(9 * (bound - 1 / 9) * (bound - 4 / 9) ^ 2) := by
  simp only [failureQuadratic, triangleProductFloor]; ring

/-- The right-endpoint check of Cases 2 and 3 at once: `Psi_m(3m) <= 0` whenever
`m >= 1/9`.  The pen needs `m > 4/27` in Case 2 and `m > 2/9` in Case 3; both are
strictly inside this range, so one lemma serves both. -/
theorem failureQuadratic_four_ninths_at_three_mul_nonpos {bound : ℝ} (hbound : 1 / 9 ≤ bound) :
    failureQuadratic (4 / 9) bound (3 * bound) ≤ 0 := by
  rw [failureQuadratic_four_ninths_at_three_mul]
  exact neg_nonpos.mpr (mul_nonneg (by linarith) (sq_nonneg _))

/-- **CASE 3'S RIGHT ENDPOINT**, in the root coordinate.  Under `r^2 >= 2/9` and
`9 r^3 <= 1` the failure quadratic is nonpositive at the norm cap's edge-sum
ceiling `1 - 2 r^3`.  Every constant is rational and the check is a single
`nlinarith`; the true margin is about `0.034` at the left end of the range and
about `0.041` at the right, so the pen's quoted uniform figures
(`0.11975 - 0.14024`) understate the subtracted term — the conclusion is
unaffected but the figure should not be repeated. -/
theorem failureQuadratic_four_ninths_at_normCap_nonpos {rootBound : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hlow : 2 / 9 ≤ rootBound ^ 2)
    (hcap : 9 * rootBound ^ 3 ≤ 1) :
    failureQuadratic (4 / 9) (rootBound ^ 2) (1 - 2 * rootBound ^ 3) ≤ 0 := by
  simp only [failureQuadratic, triangleProductFloor]
  nlinarith [hrootNonneg, sq_nonneg (rootBound - 1 / 2), sq_nonneg (3 * rootBound ^ 2 - 2 / 3),
    mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hcap), mul_nonneg hrootNonneg hrootNonneg,
    sq_nonneg (rootBound ^ 2 - 2 / 9), sq_nonneg (9 * rootBound ^ 3 - 1),
    mul_nonneg (mul_nonneg hrootNonneg hrootNonneg) hrootNonneg]

/-- Case 3's interval is nonempty: the heavy triangle's floor `3 r^2` really does
sit below the norm cap's ceiling `1 - 2 r^3`.  Only `9 r^3 <= 1` is needed. -/
theorem three_mul_sq_le_one_sub_two_mul_pow_three {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hcap : 9 * rootBound ^ 3 ≤ 1) : 3 * rootBound ^ 2 ≤ 1 - 2 * rootBound ^ 3 := by
  nlinarith [hrootNonneg, sq_nonneg (rootBound - 1 / 2), sq_nonneg (3 * rootBound ^ 2 - 2 / 3),
    mul_nonneg hrootNonneg hrootNonneg, mul_nonneg (mul_nonneg hrootNonneg hrootNonneg)
      hrootNonneg]

/-! ### The four cases as four theorems about real numbers -/

/-- **CASES 1 AND 2 OF THE SQUEEZE, COMPLETE.**  A triangle whose edges are all at
most `bound <= 2/9`, one of them nonnegative, has sign-free residual at most
`4/9`.  No norm cap, no coherence, no design.

The pen splits this range at `4/27`; the split here is at `1/9`, and the two
routes overlap on `[1/9, 4/27]` rather than meeting exactly, so the case boundary
carries slack.  Below `1/9` the residual is at most `3 * bound <= 1/3 < 4/9` by
the trivial bound `h <= sigma`.  Above `1/9` the light product floor plus the two
endpoint checks — `Psi(4/9) <= 0` because `2 bound <= 4/9`, and `Psi(3 bound) <= 0`
because `bound >= 1/9` — squeeze the failure quadratic across the band
`[4/9, 3 bound]`, and below that band the trivial bound applies again. -/
theorem signFreeTripleResidual_le_four_ninths_of_lightTriangle {bound firstWeight secondWeight
    thirdWeight : ℝ} (hthirdNonneg : 0 ≤ thirdWeight) (hfirst : firstWeight ≤ bound)
    (hsecond : secondWeight ≤ bound) (hthird : thirdWeight ≤ bound) (hbound : bound ≤ 2 / 9) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 := by
  rcases le_or_gt bound (1 / 9) with hsmallBound | hlargeBound
  · exact le_trans (signFreeTripleResidual_le_three_mul_of_le_bound hfirst hsecond hthird)
      (by linarith)
  · rcases le_or_gt (firstWeight + secondWeight + thirdWeight) (4 / 9) with hsmallSum | hlargeSum
    · exact le_trans (signFreeTripleResidual_le_sum firstWeight secondWeight thirdWeight) hsmallSum
    · exact signFreeTripleResidual_le_of_lightTriangle_endpoints (lower := 4 / 9)
        (upper := 3 * bound) hthirdNonneg hfirst hsecond hthird
        (failureQuadratic_at_threshold_nonpos (by linarith))
        (failureQuadratic_four_ninths_at_three_mul_nonpos hlargeBound.le)
        hlargeSum.le (by linarith)

/-- **CASE 3 OF THE SQUEEZE.**  A triangle all of whose edges are at least `r^2`,
with `r^2 >= 2/9` and `9 r^3 <= 1`, whose edge sum obeys the norm cap
`sigma + 2 r^3 <= 1`, has sign-free residual at most `4/9`.

The norm cap is a hypothesis; it is the pen's (C2), proved in the involution
layer, and it is where realness is consumed.  Everything here is polynomial in
`r`. -/
theorem signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_normCap {rootBound firstWeight
    secondWeight thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hlow : 2 / 9 ≤ rootBound ^ 2)
    (hcap : 9 * rootBound ^ 3 ≤ 1) (hfirst : rootBound ^ 2 ≤ firstWeight)
    (hsecond : rootBound ^ 2 ≤ secondWeight) (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hnormCap : firstWeight + secondWeight + thirdWeight + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 :=
  signFreeTripleResidual_le_of_heavyTriangle_endpoints (lower := 3 * rootBound ^ 2)
    (upper := 1 - 2 * rootBound ^ 3) (sq_nonneg rootBound) hfirst hsecond hthird
    (failureQuadratic_four_ninths_at_three_mul_nonpos (by nlinarith [hlow]))
    (failureQuadratic_four_ninths_at_normCap_nonpos hrootNonneg hlow hcap)
    (by linarith) (by linarith)

/-- **CASE 4 OF THE SQUEEZE.**  A triangle all of whose edges are at least `r^2`,
with `9 r^3 >= 1`, under the same norm cap, has sign-free residual at most `4/9`.

This is the pen's (C3) with no quadratic at all: the heavy branch gives
`sqrt p >= r^3`, the cap then gives `h <= 1 - 5 r^3`, and `r^3 >= 1/9` finishes.
Note it does NOT need `2/9 <= r^2`. -/
theorem signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_largeRoot {rootBound firstWeight
    secondWeight thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hlarge : 1 ≤ 9 * rootBound ^ 3)
    (hfirst : rootBound ^ 2 ≤ firstWeight) (hsecond : rootBound ^ 2 ≤ secondWeight)
    (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hnormCap : firstWeight + secondWeight + thirdWeight + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 :=
  le_trans (signFreeTripleResidual_le_sub_of_normCap (pow_nonneg hrootNonneg 3)
    (sq_pow_three_le_edgeProduct_of_sq_le hfirst hsecond hthird) hnormCap) (by linarith)

/-- **CASES 3 AND 4 OF THE SQUEEZE, COMBINED.**  A triangle all of whose edges are
at least `r^2 >= 2/9`, under the norm cap `sigma + 2 r^3 <= 1`, has sign-free
residual at most `4/9`.  The dichotomy `9 r^3 <= 1` versus `1 <= 9 r^3` is the
pen's `81 m^3 < 1` versus `81 m^3 >= 1`, and the two cases meet with no gap. -/
theorem signFreeTripleResidual_le_four_ninths_of_heavyTriangle {rootBound firstWeight secondWeight
    thirdWeight : ℝ} (hrootNonneg : 0 ≤ rootBound) (hlow : 2 / 9 ≤ rootBound ^ 2)
    (hfirst : rootBound ^ 2 ≤ firstWeight) (hsecond : rootBound ^ 2 ≤ secondWeight)
    (hthird : rootBound ^ 2 ≤ thirdWeight)
    (hnormCap : firstWeight + secondWeight + thirdWeight + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual firstWeight secondWeight thirdWeight ≤ 4 / 9 := by
  rcases le_or_gt (9 * rootBound ^ 3) 1 with hcap | hlarge
  · exact signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_normCap hrootNonneg hlow hcap
      hfirst hsecond hthird hnormCap
  · exact signFreeTripleResidual_le_four_ninths_of_heavyTriangle_of_largeRoot hrootNonneg
      hlarge.le hfirst hsecond hthird hnormCap

/-- **THE FOUR-CASE SQUEEZE, AS ONE STATEMENT ABOUT EIGHT REAL NUMBERS.**  Given a
root `r >= 0`, a LIGHT triangle whose edges are all at most `r^2` (with one of
them nonnegative) and a HEAVY triangle whose edges are all at least `r^2` and
which obeys the norm cap `sigma + 2 r^3 <= 1`, at least one of the two has
sign-free residual at most `4/9`.

That is the whole of S5.  What the assembly still owes is the SELECTION — the
max-min bound `m = r^2`, the Ramsey argument that produces the light triangle,
and the maximizing triangle that is the heavy one — together with the norm cap,
which is the involution layer's (C2) and the only place realness is consumed.
No square root occurs anywhere in the statement or in any of its inputs. -/
theorem signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle
    {rootBound lightFirst lightSecond lightThird heavyFirst heavySecond heavyThird : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hlightThirdNonneg : 0 ≤ lightThird)
    (hlightFirst : lightFirst ≤ rootBound ^ 2) (hlightSecond : lightSecond ≤ rootBound ^ 2)
    (hlightThird : lightThird ≤ rootBound ^ 2) (hheavyFirst : rootBound ^ 2 ≤ heavyFirst)
    (hheavySecond : rootBound ^ 2 ≤ heavySecond) (hheavyThird : rootBound ^ 2 ≤ heavyThird)
    (hnormCap : heavyFirst + heavySecond + heavyThird + 2 * rootBound ^ 3 ≤ 1) :
    signFreeTripleResidual lightFirst lightSecond lightThird ≤ 4 / 9
      ∨ signFreeTripleResidual heavyFirst heavySecond heavyThird ≤ 4 / 9 := by
  rcases le_or_gt (rootBound ^ 2) (2 / 9) with hsmallBound | hlargeBound
  · exact Or.inl (signFreeTripleResidual_le_four_ninths_of_lightTriangle hlightThirdNonneg
      hlightFirst hlightSecond hlightThird hsmallBound)
  · exact Or.inr (signFreeTripleResidual_le_four_ninths_of_heavyTriangle hrootNonneg
      hlargeBound.le hheavyFirst hheavySecond hheavyThird hnormCap)

/-! ## 8. The residual of a design triangle -/

/-- **THE ORIENTED CRITERION VALUE** `sigma_C - 3 P_C` at a triple of a design.
The pen's criterion (C1) — proved in the involution layer, not here — reads
`orientedTripleResidual <= 4/9`. -/
noncomputable def orientedTripleResidual (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) : ℝ :=
  edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex
    - 3 * (directionGram D firstIndex secondIndex * directionGram D firstIndex thirdIndex
      * directionGram D secondIndex thirdIndex)

/-- **THE SIGN-FREE RESIDUAL OF A DESIGN TRIANGLE**, `h` evaluated at the
triple's three edge weights.  It is symmetric in the three indices. -/
noncomputable def triangleResidual (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) : ℝ :=
  signFreeTripleResidual (edgeWeight D firstIndex secondIndex)
    (edgeWeight D firstIndex thirdIndex) (edgeWeight D secondIndex thirdIndex)

theorem triangleResidual_swap_first_second (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    triangleResidual D firstIndex secondIndex thirdIndex
      = triangleResidual D secondIndex firstIndex thirdIndex := by
  rw [triangleResidual, triangleResidual, edgeWeight_comm D secondIndex firstIndex,
    signFreeTripleResidual_swap_second_third]

theorem triangleResidual_swap_second_third (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    triangleResidual D firstIndex secondIndex thirdIndex
      = triangleResidual D firstIndex thirdIndex secondIndex := by
  rw [triangleResidual, triangleResidual, edgeWeight_comm D thirdIndex secondIndex,
    signFreeTripleResidual_swap_first_second]

/-- **SIGNS EVAPORATE**, at a design triple: the square root of the weight
product is the magnitude of the oriented triangle product. -/
theorem sqrt_edgeWeight_product_eq_abs (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    Real.sqrt (edgeWeight D firstIndex secondIndex * edgeWeight D firstIndex thirdIndex
        * edgeWeight D secondIndex thirdIndex)
      = |directionGram D firstIndex secondIndex * directionGram D firstIndex thirdIndex
        * directionGram D secondIndex thirdIndex| := by
  rw [edgeWeight, edgeWeight, edgeWeight, sqrt_sq_mul_sq_mul_sq]

/-- **THE SPLIT REDUCTION AT A DESIGN TRIPLE.**  The sign-free residual is the
minimum of the two sign readings of the criterion.  The mirror law identifies the
second with the complementary triple's criterion value; here only the arithmetic
is claimed. -/
theorem triangleResidual_eq_min (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    triangleResidual D firstIndex secondIndex thirdIndex
      = min (orientedTripleResidual D firstIndex secondIndex thirdIndex)
          (edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
              + edgeWeight D secondIndex thirdIndex
            + 3 * (directionGram D firstIndex secondIndex
              * directionGram D firstIndex thirdIndex
              * directionGram D secondIndex thirdIndex)) := by
  rw [triangleResidual, orientedTripleResidual, edgeWeight, edgeWeight, edgeWeight,
    signFreeTripleResidual_sq_eq_min]

/-- The sign-free residual never exceeds the oriented criterion value. -/
theorem triangleResidual_le_orientedTripleResidual (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    triangleResidual D firstIndex secondIndex thirdIndex
      ≤ orientedTripleResidual D firstIndex secondIndex thirdIndex := by
  rw [triangleResidual_eq_min]; exact min_le_left _ _

/-- On the coherent branch the two agree, so a bound on the sign-free residual is
a bound on the criterion. -/
theorem triangleResidual_eq_orientedTripleResidual_of_coherent (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hcoherent : 0 ≤ directionGram D firstIndex secondIndex
      * directionGram D firstIndex thirdIndex * directionGram D secondIndex thirdIndex) :
    triangleResidual D firstIndex secondIndex thirdIndex
      = orientedTripleResidual D firstIndex secondIndex thirdIndex := by
  rw [triangleResidual, orientedTripleResidual, edgeWeight, edgeWeight, edgeWeight,
    signFreeTripleResidual_sq_eq_of_nonneg_product hcoherent]

/-- **THE PEN'S S4 HEADLINE, ASSEMBLED.**  The criterion value of the better side
of a 3-3 split is a function of the edge WEIGHTS alone: whichever of the two sign
readings is smaller equals `h` evaluated at the three edge weights, and `h` never
sees a sign.  Stated as: the sign-free residual bounds the criterion, with
equality on the coherent side. -/
theorem triangleResidual_le_orientedTripleResidual_and_eq_of_coherent
    (D : WeightedDesign m k) (firstIndex secondIndex thirdIndex : Fin m) :
    triangleResidual D firstIndex secondIndex thirdIndex
        ≤ orientedTripleResidual D firstIndex secondIndex thirdIndex
      ∧ (0 ≤ directionGram D firstIndex secondIndex * directionGram D firstIndex thirdIndex
          * directionGram D secondIndex thirdIndex →
        triangleResidual D firstIndex secondIndex thirdIndex
          = orientedTripleResidual D firstIndex secondIndex thirdIndex) :=
  ⟨triangleResidual_le_orientedTripleResidual D firstIndex secondIndex thirdIndex,
    fun hcoherent =>
      triangleResidual_eq_orientedTripleResidual_of_coherent D hcoherent⟩

/-! ### The case closers, at a design triple -/

/-- The heavy-branch case closer transported to a design triple. -/
theorem triangleResidual_le_of_heavyTriangle_endpoints (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {threshold bound lower upper : ℝ}
    (hboundNonneg : 0 ≤ bound) (hfirst : bound ≤ edgeWeight D firstIndex secondIndex)
    (hsecond : bound ≤ edgeWeight D firstIndex thirdIndex)
    (hthird : bound ≤ edgeWeight D secondIndex thirdIndex)
    (hlowerNonpos : failureQuadratic threshold bound lower ≤ 0)
    (hupperNonpos : failureQuadratic threshold bound upper ≤ 0)
    (hlower : lower ≤ edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex)
    (hupper : edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex ≤ upper) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ threshold :=
  signFreeTripleResidual_le_of_heavyTriangle_endpoints hboundNonneg hfirst hsecond hthird
    hlowerNonpos hupperNonpos hlower hupper

/-- The light-branch case closer transported to a design triple; the weights are
nonnegative by construction, so only the upper bounds are hypotheses. -/
theorem triangleResidual_le_of_lightTriangle_endpoints (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {threshold bound lower upper : ℝ}
    (hfirst : edgeWeight D firstIndex secondIndex ≤ bound)
    (hsecond : edgeWeight D firstIndex thirdIndex ≤ bound)
    (hthird : edgeWeight D secondIndex thirdIndex ≤ bound)
    (hlowerNonpos : failureQuadratic threshold bound lower ≤ 0)
    (hupperNonpos : failureQuadratic threshold bound upper ≤ 0)
    (hlower : lower ≤ edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex)
    (hupper : edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex ≤ upper) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ threshold :=
  signFreeTripleResidual_le_of_lightTriangle_endpoints (edgeWeight_nonneg D _ _)
    hfirst hsecond hthird hlowerNonpos hupperNonpos hlower hupper

/-- **CASE 1 OF THE SQUEEZE, at a design triple.**  A triangle all of whose edge
weights are at most `bound` has residual at most `3 * bound`. -/
theorem triangleResidual_le_three_mul_of_le_bound (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {bound : ℝ}
    (hfirst : edgeWeight D firstIndex secondIndex ≤ bound)
    (hsecond : edgeWeight D firstIndex thirdIndex ≤ bound)
    (hthird : edgeWeight D secondIndex thirdIndex ≤ bound) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ 3 * bound :=
  signFreeTripleResidual_le_three_mul_of_le_bound hfirst hsecond hthird

/-- **CASE 4 OF THE SQUEEZE, at a design triple.**  A triangle all of whose edge
weights are at least `r^2`, under the norm cap `sigma + 2 r^3 <= capValue`, has
residual at most `capValue - 5 r^3`.  Everything is polynomial in `r`. -/
theorem triangleResidual_le_sub_of_normCap (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {rootBound capValue : ℝ}
    (hrootNonneg : 0 ≤ rootBound) (hfirst : rootBound ^ 2 ≤ edgeWeight D firstIndex secondIndex)
    (hsecond : rootBound ^ 2 ≤ edgeWeight D firstIndex thirdIndex)
    (hthird : rootBound ^ 2 ≤ edgeWeight D secondIndex thirdIndex)
    (hcap : edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex + 2 * rootBound ^ 3 ≤ capValue) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ capValue - 5 * rootBound ^ 3 :=
  signFreeTripleResidual_le_sub_of_normCap (pow_nonneg hrootNonneg 3)
    (sq_pow_three_le_edgeProduct_of_sq_le hfirst hsecond hthird) hcap

/-- **CASES 1 AND 2, at a design triple.**  Nonnegativity of the edge weights is
free, so a light triangle of a design needs only the three upper bounds. -/
theorem triangleResidual_le_four_ninths_of_lightTriangle (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {bound : ℝ}
    (hfirst : edgeWeight D firstIndex secondIndex ≤ bound)
    (hsecond : edgeWeight D firstIndex thirdIndex ≤ bound)
    (hthird : edgeWeight D secondIndex thirdIndex ≤ bound) (hbound : bound ≤ 2 / 9) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ 4 / 9 :=
  signFreeTripleResidual_le_four_ninths_of_lightTriangle (edgeWeight_nonneg D _ _)
    hfirst hsecond hthird hbound

/-- **CASES 3 AND 4, at a design triple.** -/
theorem triangleResidual_le_four_ninths_of_heavyTriangle (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m} {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hlow : 2 / 9 ≤ rootBound ^ 2) (hfirst : rootBound ^ 2 ≤ edgeWeight D firstIndex secondIndex)
    (hsecond : rootBound ^ 2 ≤ edgeWeight D firstIndex thirdIndex)
    (hthird : rootBound ^ 2 ≤ edgeWeight D secondIndex thirdIndex)
    (hnormCap : edgeWeight D firstIndex secondIndex + edgeWeight D firstIndex thirdIndex
      + edgeWeight D secondIndex thirdIndex + 2 * rootBound ^ 3 ≤ 1) :
    triangleResidual D firstIndex secondIndex thirdIndex ≤ 4 / 9 :=
  signFreeTripleResidual_le_four_ninths_of_heavyTriangle hrootNonneg hlow hfirst hsecond hthird
    hnormCap

/-- **THE FOUR-CASE SQUEEZE, at a pair of design triples.**  A light triple and a
heavy triple sharing the bound `r^2`, with the norm cap on the heavy one: one of
them has sign-free residual at most `4/9`.  This is the exact shape the assembly
needs after the Ramsey selection. -/
theorem triangleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle
    (D : WeightedDesign m k) {lightFirst lightSecond lightThird heavyFirst heavySecond
      heavyThird : Fin m} {rootBound : ℝ} (hrootNonneg : 0 ≤ rootBound)
    (hlightOne : edgeWeight D lightFirst lightSecond ≤ rootBound ^ 2)
    (hlightTwo : edgeWeight D lightFirst lightThird ≤ rootBound ^ 2)
    (hlightThree : edgeWeight D lightSecond lightThird ≤ rootBound ^ 2)
    (hheavyOne : rootBound ^ 2 ≤ edgeWeight D heavyFirst heavySecond)
    (hheavyTwo : rootBound ^ 2 ≤ edgeWeight D heavyFirst heavyThird)
    (hheavyThree : rootBound ^ 2 ≤ edgeWeight D heavySecond heavyThird)
    (hnormCap : edgeWeight D heavyFirst heavySecond + edgeWeight D heavyFirst heavyThird
      + edgeWeight D heavySecond heavyThird + 2 * rootBound ^ 3 ≤ 1) :
    triangleResidual D lightFirst lightSecond lightThird ≤ 4 / 9
      ∨ triangleResidual D heavyFirst heavySecond heavyThird ≤ 4 / 9 :=
  signFreeTripleResidual_le_four_ninths_of_lightTriangle_or_heavyTriangle hrootNonneg
    (edgeWeight_nonneg D _ _) hlightOne hlightTwo hlightThree hheavyOne hheavyTwo hheavyThree
    hnormCap

end Gtz
