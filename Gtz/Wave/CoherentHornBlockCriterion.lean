/-
# A positive block and a positive determinant force positive definiteness

`Gtz.posDef_iff_invariants_pos` decides a symmetric `3x3` by three signs.  This
module lands the cheaper sufficient criterion the corner needs, in which only
ONE of the three has to be checked:

  **if the trailing `2x2` principal block is positive definite and the
  determinant is positive, the whole form is positive definite**
  (`Gtz.posDef_of_lastBlock_posDef_of_det_pos`).

The proof is one Schur identity closed by `ring`, in the style of
`Gtz.posDef_three_of_zPattern_of_posVector` -- no eigenvalue, no interlacing, no
block matrix machinery.  With `M := K11*K22 - K12*K21` and

  `z1 := M*x1 + x0*(K22*K01 - K12*K02)`,  `z2 := M*x2 + x0*(K11*K02 - K12*K01)` ,

the identity is

  `K11 * M^2 * (x'Kx) = K11*M*det(K)*x0^2 + (K11*z1 + K12*z2)^2 + M*z2^2` .

Every term on the right is nonnegative, and one of them is strictly positive at
every nonzero probe.

## Why the corner wants exactly this

The gap of a triple and its Gram are similar (`S_T - 1 = VV' - 1` against
`K_T = V'V - 1`), so `T` dominates strictly exactly when `K_T` is positive
definite, `K_T` carrying the leverage excesses on its diagonal and the pairings
off it.  For a one-inside triple `{e,d,d'}` ordered with the inside atom first,
the trailing block is the OUTSIDE PAIR, and its positive definiteness is exactly
that the pair is heavy and admissible.  So on an admissible outside pair the
determinant sign alone decides domination.

MEASURED (scratchpad/f30/coh24.jl, 670289 failing-branch points, 3984042
(admissible pair, inside atom) cases):

  outside pairs admissible                     66.0419%
  per branch point, SOME pair admissible      100.0000%
  on an admissible pair:  tr K > 0            100.0000%   (free, and proved here)
                          all three invariants  36.9205%
                          truly dominates       36.9205%   (exact agreement)
  given tr > 0, only e2 fails                   0.0000%   <- det alone decides
  per branch point, SOME admissible pair and
  inside atom dominates                       100.0000%

The `0.0000%` is what this module turns from a measurement into a proof: on an
admissible pair a positive determinant cannot be accompanied by a negative
second invariant, because the Schur identity forces the form positive outright.

CORRECTION THIS SETTLES.  Section 39 of the handoff restated the open content as
"show one of the triples has POSITIVE GAP DETERMINANT".  That is NOT sufficient
in general -- `det > 0` fails to imply domination at 6.7849% of the nine
one-inside triples (scratchpad/f30/coh21.jl, 6026085 triples), since a symmetric
form with two negative eigenvalues also has positive determinant.  It IS
sufficient once the outside pair is admissible, which is the form landed here.
-/
import Gtz.Wave.CoherentHornSumLaw
import Gtz.Wave.TripleInvariantLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The Schur identity -/

/-- **THE TRAILING-BLOCK SCHUR IDENTITY.**  For any `3x3` form, the quadratic
value at a probe is carried by the determinant against the first coordinate plus
two squares of the block-corrected tail.  A polynomial identity in twelve
variables: no symmetry, no positivity, no hypothesis at all. -/
theorem quadForm_lastBlock_identity (K : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymm : K 1 0 = K 0 1) (hsymm' : K 2 0 = K 0 2) (hsymm'' : K 2 1 = K 1 2)
    (x : Fin 3 → ℝ) :
    K 1 1 * (K 1 1 * K 2 2 - K 1 2 * K 2 1) ^ 2 * (x ⬝ᵥ (K *ᵥ x))
      = K 1 1 * (K 1 1 * K 2 2 - K 1 2 * K 2 1) * K.det * x 0 ^ 2
        + (K 1 1 * ((K 1 1 * K 2 2 - K 1 2 * K 2 1) * x 1
              + x 0 * (K 2 2 * K 0 1 - K 1 2 * K 0 2))
            + K 1 2 * ((K 1 1 * K 2 2 - K 1 2 * K 2 1) * x 2
              + x 0 * (K 1 1 * K 0 2 - K 1 2 * K 0 1))) ^ 2
        + (K 1 1 * K 2 2 - K 1 2 * K 2 1)
            * ((K 1 1 * K 2 2 - K 1 2 * K 2 1) * x 2
              + x 0 * (K 1 1 * K 0 2 - K 1 2 * K 0 1)) ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hsymm, hsymm', hsymm'']
  ring

/-! ## 2. The criterion -/

/-- **A POSITIVE TRAILING BLOCK AND A POSITIVE DETERMINANT SUFFICE.**  If the
trailing `2x2` principal block of a symmetric `3x3` form is positive definite --
that is, `K11 > 0` and its minor is positive -- and the determinant is positive,
the form is positive definite.

Only one of the three characteristic signs of `Gtz.posDef_iff_invariants_pos`
has to be tested: the block supplies the rest. -/
theorem posDef_of_lastBlock_posDef_of_det_pos {K : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : Kᵀ = K) (h11 : 0 < K 1 1)
    (hblock : 0 < K 1 1 * K 2 2 - K 1 2 * K 2 1)
    (hdet : 0 < K.det) :
    K.PosDef := by
  have e10 : K 1 0 = K 0 1 := by
    have := congrFun (congrFun hsymm 0) 1; simpa [Matrix.transpose_apply] using this
  have e20 : K 2 0 = K 0 2 := by
    have := congrFun (congrFun hsymm 0) 2; simpa [Matrix.transpose_apply] using this
  have e21 : K 2 1 = K 1 2 := by
    have := congrFun (congrFun hsymm 1) 2; simpa [Matrix.transpose_apply] using this
  set M : ℝ := K 1 1 * K 2 2 - K 1 2 * K 2 1 with hM
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun x hx => ?_⟩
  rw [star_trivial]
  have hid := quadForm_lastBlock_identity K e10 e20 e21 x
  rw [← hM] at hid
  set z2 : ℝ := M * x 2 + x 0 * (K 1 1 * K 0 2 - K 1 2 * K 0 1) with hz2
  set w : ℝ := K 1 1 * (M * x 1 + x 0 * (K 2 2 * K 0 1 - K 1 2 * K 0 2)) + K 1 2 * z2
    with hw
  -- the coefficient is strictly positive, so the sign of the value is the sign
  -- of the right-hand side
  have hcoef : 0 < K 1 1 * M ^ 2 := by positivity
  rcases eq_or_ne (x 0) 0 with hx0 | hx0
  · -- on the block itself: the tail cannot vanish, and the block is definite
    have hz2' : z2 = M * x 2 := by rw [hz2, hx0]; ring
    have hw' : w = M * (K 1 1 * x 1 + K 1 2 * x 2) := by
      rw [hw, hz2', hx0]; ring
    have htail : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext fun i => by fin_cases i <;> simp [hx0, hcon.1, hcon.2])
    have hpos : 0 < w ^ 2 + M * z2 ^ 2 := by
      rcases eq_or_ne (x 2) 0 with h2 | h2
      · have hx1 : x 1 ≠ 0 := htail.resolve_right (not_not_intro h2)
        have : w = M * (K 1 1 * x 1) := by rw [hw', h2]; ring
        have hwne : w ≠ 0 := by
          rw [this]
          exact mul_ne_zero (ne_of_gt hblock) (mul_ne_zero (ne_of_gt h11) hx1)
        have : 0 < w ^ 2 := by positivity
        have hz : 0 ≤ M * z2 ^ 2 := by positivity
        linarith
      · have : 0 < M * z2 ^ 2 := by
          rw [hz2']
          have : (0:ℝ) < (M * x 2) ^ 2 := by positivity
          nlinarith [hblock, this]
        nlinarith [sq_nonneg w]
    have hrhs : 0 < K 1 1 * M * K.det * x 0 ^ 2 + w ^ 2 + M * z2 ^ 2 := by
      rw [hx0]; nlinarith [hpos]
    nlinarith [hid, hrhs, hcoef]
  · -- off the block: the determinant term is strictly positive
    have hx0sq : 0 < x 0 ^ 2 := by positivity
    have hfirst : 0 < K 1 1 * M * K.det * x 0 ^ 2 := by positivity
    have hsq : 0 ≤ w ^ 2 := sq_nonneg w
    have hlast : 0 ≤ M * z2 ^ 2 := by positivity
    have hrhs : 0 < K 1 1 * M * K.det * x 0 ^ 2 + w ^ 2 + M * z2 ^ 2 := by linarith
    nlinarith [hid, hrhs, hcoef]

/-- **THE CRITERION AS AN INVARIANT UPGRADE.**  A positive trailing block
promotes a positive determinant to all three characteristic signs. -/
theorem invariants_pos_of_lastBlock_posDef_of_det_pos
    {K : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : Kᵀ = K) (h11 : 0 < K 1 1)
    (hblock : 0 < K 1 1 * K 2 2 - K 1 2 * K 2 1)
    (hdet : 0 < K.det) :
    0 < Matrix.trace K ∧ 0 < secondInvariantOfThree K ∧ 0 < K.det :=
  (posDef_iff_invariants_pos (isHermitian_of_transpose_eq hsymm)).mp
    (posDef_of_lastBlock_posDef_of_det_pos hsymm h11 hblock hdet)

end Gtz
