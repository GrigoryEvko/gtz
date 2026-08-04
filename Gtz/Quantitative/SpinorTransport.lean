/-
# The Sengupta-Pautov spinor lift at general rank, and where it stops

Sengupta-Pautov (arXiv:2604.05944) prove the unweighted rank-two Goreinov-
Tyrtyshnikov-Zamarashkin hypothesis.  Their engine is a LIFT
`w_i = (x_i ^ 2 - y_i ^ 2, 2 x_i y_i)` of a row `r_i = (x_i, y_i)` into the plane,
together with the identity `(r_i, r_j) ^ 2 = |r_i| ^ 2 |r_j| ^ 2 / 2 + (w_i, w_j) / 2`,
a rank bound on the resulting Gram, and Perron-Frobenius on an entrywise-positive
shift of it.

This file identifies that lift at every rank and measures exactly what survives.

*  `w_i` is `2 H_i` in disguise, where `H = tracelessAtomMatrix` is the shipped
   harmonic part.  The lifting identity is the ADDITION THEOREM
   `trace (H_a * H_b) = (g_a . g_b) ^ 2 - l_a l_b / rank`
   (`trace_tracelessAtomMatrix_mul`), valid at every rank.  So the lift and its
   Gram transport verbatim, and at rank three the identity is the degree-two
   spherical-harmonic addition theorem.

*  What the lift SEES is therefore exactly the leverages and the SQUARED
   pairings -- the sign-blind, or phase-free, level.

*  What it MISSES is one number per triple: the cubic invariant
   `trace (H_a * H_b * H_c)`.  `atomPairing_product_eq_cubicInvariant_add` shows
   the triple product is that invariant plus a function of the lift Gram, and
   `trace_tracelessAtomMatrix_mul_mul_rankTwo` shows THE CUBIC INVARIANT IS
   IDENTICALLY ZERO AT RANK TWO: a traceless symmetric `2 x 2` matrix is
   `u * sigma_3 + v * sigma_1`, the product of two such is a scalar plus an
   ANTISYMMETRIC matrix, and an antisymmetric matrix traces to zero against a
   symmetric one.  That single vanishing is why the rank-two lift loses nothing,
   and its failure at rank three is why the mechanism stops.

*  `icosaDesign_lift_does_not_decide_domination` turns that into a refutation.  At
   `Gtz.icosaDesign` every leverage is `3`, every harmonic norm is `6` and every
   harmonic pairing is `-(6/5)` -- so the harmonic lift is a REGULAR FIVE-SIMPLEX
   and the lift data of all twenty triples coincide -- yet `{0, 2, 4}` dominates
   and `{0, 3, 4}` does not.  `icosaDesign_cubicInvariant_separates` names the one
   number that tells them apart: the cubic invariants differ by exactly
   `2 * icosaRadius ^ 3`.

The sign-blind impossibility itself is NOT new here: the header of
`Gtz.icosaDesign_dominates_iff_tripleParity` already records that nothing
sign-blind can separate the twenty triples.  What is new is the IDENTIFICATION of
the transported Sengupta-Pautov lift with the sign-blind level, which is what
turns that observation into a verdict about the published rank-two proof.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Corner.CornerFiber
import Gtz.Quantitative.CocycleRigidity
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.HarmonicCircuit
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.SevenThreeMetricBound
import Gtz.Quantitative.SwitchingTwoGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The lift Gram at general rank -/

/-- `atomMatrix` is `vecMulVec` of a vector with itself; naming it lets the triple
product be rewritten without unfolding a definition mid-proof. -/
theorem atomMatrix_def_vecMulVec {rank : ℕ} (atom : Fin rank → ℝ) :
    atomMatrix atom = Matrix.vecMulVec atom atom := rfl

/-- The trace of a triple Veronese product is the triple product of the pairings. -/
theorem trace_atomMatrix_mul_mul {rank : ℕ} (first second third : Fin rank → ℝ) :
    Matrix.trace (atomMatrix first * atomMatrix second * atomMatrix third)
      = (first ⬝ᵥ second) * (second ⬝ᵥ third) * (third ⬝ᵥ first) := by
  rw [atomMatrix_mul_atomMatrix, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    atomMatrix_def_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_comm first third]
  ring

/-- Traces of a shifted product, the only matrix bookkeeping this file needs. -/
theorem trace_sub_smul_one_mul_sub_smul_one {rank : ℕ}
    (matFirst matSecond : Matrix (Fin rank) (Fin rank) ℝ) (shiftFirst shiftSecond : ℝ) :
    Matrix.trace ((matFirst - shiftFirst • 1) * (matSecond - shiftSecond • 1))
      = Matrix.trace (matFirst * matSecond) - shiftSecond * Matrix.trace matFirst
        - shiftFirst * Matrix.trace matSecond + shiftFirst * shiftSecond * rank := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- **THE ADDITION THEOREM, at every rank.**  The Gram of the harmonic (spinor)
lift is the squared pairing minus the leverage product over the rank.  At
`rank = 2` this is Sengupta-Pautov's identity
`(r_i, r_j) ^ 2 = |r_i| ^ 2 |r_j| ^ 2 / 2 + (w_i, w_j) / 2` with `w = 2 H`; at
`rank = 3` it is the degree-two spherical-harmonic addition theorem.  Everything
the lift can see about a pair is on the right-hand side.

R6 DISCLOSURE: this carries NO NEW CONTENT over the shipped
`Gtz.frobeniusInner_veroneseTracelessPart`, which states the same theorem for
UNIT-normalised atoms as `directionGram ^ 2 - 1/rank`; the two differ by the
factor `l_a l_b`.  It is restated here at the shipped `Gtz.tracelessAtomMatrix`,
without a nondegeneracy hypothesis, because the cubic-invariant theorems below are
stated there and would otherwise have to carry the normalisation through.  The new
content of this file begins at `atomPairing_product_eq_cubicInvariant_add`. -/
theorem trace_tracelessAtomMatrix_mul {rank : ℕ} (hrank : 1 ≤ rank)
    (first second : Fin rank → ℝ) :
    Matrix.trace (tracelessAtomMatrix rank first * tracelessAtomMatrix rank second)
      = (first ⬝ᵥ second) ^ 2 - leverageOf first * leverageOf second / rank := by
  have hrankne : (rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hrank)
  rw [tracelessAtomMatrix, tracelessAtomMatrix, trace_sub_smul_one_mul_sub_smul_one,
    trace_atomMatrix_mul_atomMatrix, trace_atomMatrix, trace_atomMatrix]
  field_simp
  ring

/-- The lift preserves squared lengths up to the rank factor:
`|H_a| ^ 2 = (rank - 1) / rank * l_a ^ 2`.  At `rank = 2` this is Sengupta-Pautov's
`|w_i| ^ 2 = |r_i| ^ 4`, since `w = 2 H` gives `|w| ^ 2 = 4 |H| ^ 2 = 2 l ^ 2` and
their normalisation halves it. -/
theorem trace_tracelessAtomMatrix_sq {rank : ℕ} (hrank : 1 ≤ rank) (atom : Fin rank → ℝ) :
    Matrix.trace (tracelessAtomMatrix rank atom * tracelessAtomMatrix rank atom)
      = leverageOf atom ^ 2 - leverageOf atom ^ 2 / rank := by
  have hself : atom ⬝ᵥ atom = leverageOf atom := by rw [leverageOf, dotProduct_self_eq_sum_sq]
  rw [trace_tracelessAtomMatrix_mul hrank, hself]
  ring

/-! ## The cubic invariant, and its vanishing at rank two -/

/-- **THE TRIPLE PRODUCT IS THE CUBIC INVARIANT PLUS LIFT DATA.**  Writing `L_ab`
for `trace (H_a * H_b)`, at every rank

`p_ab p_bc p_ca = trace (H_a H_b H_c) + (l_c L_ab + l_b L_ac + l_a L_bc) / rank
                  + l_a l_b l_c / rank ^ 2`.

Every term on the right except the first is a function of the lift Gram.  So the
cubic invariant is EXACTLY the information the lift discards. -/
theorem atomPairing_product_eq_cubicInvariant_add {rank : ℕ} (hrank : 1 ≤ rank)
    (first second third : Fin rank → ℝ) :
    (first ⬝ᵥ second) * (second ⬝ᵥ third) * (third ⬝ᵥ first)
      = Matrix.trace (tracelessAtomMatrix rank first * tracelessAtomMatrix rank second
            * tracelessAtomMatrix rank third)
        + (leverageOf third
              * Matrix.trace (tracelessAtomMatrix rank first * tracelessAtomMatrix rank second)
            + leverageOf second
              * Matrix.trace (tracelessAtomMatrix rank first * tracelessAtomMatrix rank third)
            + leverageOf first
              * Matrix.trace (tracelessAtomMatrix rank second * tracelessAtomMatrix rank third))
          / rank
        + leverageOf first * leverageOf second * leverageOf third / (rank : ℝ) ^ 2 := by
  have hrankne : (rank : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hrank)
  have hexpand : tracelessAtomMatrix rank first * tracelessAtomMatrix rank second
        * tracelessAtomMatrix rank third
      = atomMatrix first * atomMatrix second * atomMatrix third
        - (leverageOf third / rank) • (atomMatrix first * atomMatrix second)
        - (leverageOf second / rank) • (atomMatrix first * atomMatrix third)
        - (leverageOf first / rank) • (atomMatrix second * atomMatrix third)
        + (leverageOf second * leverageOf third / (rank : ℝ) ^ 2) • atomMatrix first
        + (leverageOf first * leverageOf third / (rank : ℝ) ^ 2) • atomMatrix second
        + (leverageOf first * leverageOf second / (rank : ℝ) ^ 2) • atomMatrix third
        - (leverageOf first * leverageOf second * leverageOf third / (rank : ℝ) ^ 3)
            • (1 : Matrix (Fin rank) (Fin rank) ℝ) := by
    simp only [tracelessAtomMatrix, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  rw [hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, trace_atomMatrix_mul_mul, trace_atomMatrix,
    trace_atomMatrix_mul_atomMatrix, trace_tracelessAtomMatrix_mul hrank]
  field_simp
  ring

/-- **THE CUBIC INVARIANT VANISHES IDENTICALLY AT RANK TWO.**  A traceless
symmetric `2 x 2` matrix is `u * sigma_3 + v * sigma_1`; the product of two such is
a scalar matrix plus an ANTISYMMETRIC one, and an antisymmetric matrix traces to
zero against a symmetric one.  (Representation-theoretically the weight-two plane
of `SO(2)` admits no invariant cubic, since no three weights from `{+2, -2}` sum to
zero -- that remark is NOT used and NOT proved here; the identity below is.)

THIS IS WHY THE SENGUPTA-PAUTOV LIFT LOSES NOTHING AT RANK TWO, and it is the one
ingredient of the mechanism that does not transport: the five-dimensional
rank-three harmonic space does carry such a cubic, and
`icosaDesign_cubicInvariant_separates` evaluates it at two triples that the lift
cannot tell apart. -/
theorem trace_tracelessAtomMatrix_mul_mul_rankTwo (first second third : Fin 2 → ℝ) :
    Matrix.trace (tracelessAtomMatrix 2 first * tracelessAtomMatrix 2 second
      * tracelessAtomMatrix 2 third) = 0 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, tracelessAtomMatrix,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, Fin.sum_univ_two, smul_eq_mul]
  norm_num
  ring

/-- The rank-two triple product is therefore a function of the lift Gram alone --
which is exactly why nothing is lost by passing to the lift at rank two. -/
theorem atomPairing_product_rankTwo (first second third : Fin 2 → ℝ) :
    (first ⬝ᵥ second) * (second ⬝ᵥ third) * (third ⬝ᵥ first)
      = (leverageOf third
            * Matrix.trace (tracelessAtomMatrix 2 first * tracelessAtomMatrix 2 second)
          + leverageOf second
            * Matrix.trace (tracelessAtomMatrix 2 first * tracelessAtomMatrix 2 third)
          + leverageOf first
            * Matrix.trace (tracelessAtomMatrix 2 second * tracelessAtomMatrix 2 third)) / 2
        + leverageOf first * leverageOf second * leverageOf third / 4 := by
  have hdecomp :=
    atomPairing_product_eq_cubicInvariant_add (rank := 2) (by norm_num) first second third
  rw [trace_tracelessAtomMatrix_mul_mul_rankTwo] at hdecomp
  rw [hdecomp]
  norm_num

/-! ## The refutation at rank three -/

/-- Every distinct icosahedral pair has the SAME lift Gram entry, `9/5 - 3 * 3 / 3`. -/
theorem icosaDesign_tracelessPairing {atomFirst atomSecond : Fin 6}
    (hne : atomFirst ≠ atomSecond) :
    Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom atomFirst)
      * tracelessAtomMatrix 3 (icosaDesign.atom atomSecond)) = -(6 / 5) := by
  have hpair : (icosaDesign.atom atomFirst ⬝ᵥ icosaDesign.atom atomSecond) ^ 2 = 9 / 5 :=
    icosaDesign_atomPairing_sq_of_ne hne
  rw [trace_tracelessAtomMatrix_mul (by norm_num), hpair, icosaDesign_leverage,
    icosaDesign_leverage]
  norm_num

/-- Each harmonic icosahedral atom has squared length `6`.  With the previous
theorem: SIX POINTS OF SQUARED LENGTH `6` WITH ALL PAIRWISE INNER PRODUCTS
`-(6/5) = -6/5`, i.e. the harmonic lift of the icosahedral design is the REGULAR
FIVE-SIMPLEX in the five-dimensional traceless space. -/
theorem icosaDesign_tracelessNorm (atomIndex : Fin 6) :
    Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom atomIndex)
      * tracelessAtomMatrix 3 (icosaDesign.atom atomIndex)) = 6 := by
  rw [trace_tracelessAtomMatrix_sq (by norm_num), icosaDesign_leverage]
  norm_num

/-- `{0, 3, 4}` is an INCOHERENT icosahedral triple, so it does not dominate. -/
theorem not_dominates_icosaDesign_zeroThreeFour :
    ¬ Dominates icosaDesign {0, 3, 4} := by
  rw [icosaDesign_dominates_iff_tripleParity (by decide) (by decide) (by decide),
    tripleParity_icosaDesign (by decide) (by decide) (by decide)]
  norm_num [icosaOverlapSign, Matrix.cons_val_three, Matrix.cons_val_four]

/-- **THE TRANSPORT IS REFUTED AT RANK THREE.**  The two triples `{0, 2, 4}` and
`{0, 3, 4}` of `Gtz.icosaDesign` carry IDENTICAL spinor-lift data -- every leverage
is `3`, every harmonic norm is `6`, every harmonic pairing is `-(6/5)` -- and the
first dominates while the second does not.

Consequently no predicate whose value depends only on the leverages and the
harmonic lift Gram can imply domination and still hold at a dominating triple of
this design.  The Sengupta-Pautov mechanism computes exactly that data, so it
cannot decide rank-three GTZ however its Perron-Frobenius step is repaired. -/
theorem icosaDesign_lift_does_not_decide_domination :
    (∀ atomIndex : Fin 6, leverageOf (icosaDesign.atom atomIndex) = 3)
      ∧ (∀ atomIndex : Fin 6,
          Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom atomIndex)
            * tracelessAtomMatrix 3 (icosaDesign.atom atomIndex)) = 6)
      ∧ (∀ atomFirst atomSecond : Fin 6, atomFirst ≠ atomSecond →
          Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom atomFirst)
            * tracelessAtomMatrix 3 (icosaDesign.atom atomSecond)) = -(6 / 5))
      ∧ Dominates icosaDesign {0, 2, 4}
      ∧ ¬ Dominates icosaDesign {0, 3, 4} :=
  ⟨icosaDesign_leverage, icosaDesign_tracelessNorm,
    fun _ _ hne => icosaDesign_tracelessPairing hne,
    icosaDesign_dominates, not_dominates_icosaDesign_zeroThreeFour⟩

/-- The cubic invariant at an icosahedral triple, in closed form: it is the triple
parity times `icosaRadius ^ 3`, plus `3/5`. -/
theorem icosaDesign_cubicInvariant {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom first)
        * tracelessAtomMatrix 3 (icosaDesign.atom second)
        * tracelessAtomMatrix 3 (icosaDesign.atom third))
      = icosaOverlapSign first second * icosaOverlapSign second third
          * icosaOverlapSign third first * icosaRadius ^ 3 + 3 / 5 := by
  have hdecomp := atomPairing_product_eq_cubicInvariant_add (rank := 3) (by norm_num)
    (icosaDesign.atom first) (icosaDesign.atom second) (icosaDesign.atom third)
  rw [icosaDesign_tracelessPairing hfirstSecond, icosaDesign_tracelessPairing hfirstThird,
    icosaDesign_tracelessPairing hsecondThird, icosaDesign_leverage, icosaDesign_leverage,
    icosaDesign_leverage] at hdecomp
  have hone : icosaDesign.atom first ⬝ᵥ icosaDesign.atom second
      = icosaOverlapSign first second * icosaRadius := atomPairing_icosaDesign_of_ne hfirstSecond
  have htwo : icosaDesign.atom second ⬝ᵥ icosaDesign.atom third
      = icosaOverlapSign second third * icosaRadius := atomPairing_icosaDesign_of_ne hsecondThird
  have hthree : icosaDesign.atom third ⬝ᵥ icosaDesign.atom first
      = icosaOverlapSign third first * icosaRadius := atomPairing_icosaDesign_of_ne hfirstThird.symm
  rw [hone, htwo, hthree] at hdecomp
  linarith [hdecomp]

/-- **THE ONE NUMBER THE LIFT DISCARDS, MEASURED.**  The two triples of
`icosaDesign_lift_does_not_decide_domination` have cubic invariants differing by
exactly `2 * icosaRadius ^ 3 > 0`, and that difference is the whole of what
separates a dominating icosahedral triple from a non-dominating one. -/
theorem icosaDesign_cubicInvariant_separates :
    Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom 0)
          * tracelessAtomMatrix 3 (icosaDesign.atom 2)
          * tracelessAtomMatrix 3 (icosaDesign.atom 4))
        - Matrix.trace (tracelessAtomMatrix 3 (icosaDesign.atom 0)
          * tracelessAtomMatrix 3 (icosaDesign.atom 3)
          * tracelessAtomMatrix 3 (icosaDesign.atom 4))
      = 2 * icosaRadius ^ 3 := by
  rw [icosaDesign_cubicInvariant (first := 0) (second := 2) (third := 4)
      (by decide) (by decide) (by decide),
    icosaDesign_cubicInvariant (first := 0) (second := 3) (third := 4)
      (by decide) (by decide) (by decide)]
  simp only [icosaOverlapSign, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons]
  ring

end Gtz
