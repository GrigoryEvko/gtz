import Mathlib
import Gtz.Ties.ConicCaratheodory

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-
# The equality stratum of the rank-two hinge is EMPTY

`RankTwoEqualityStratum` was the sole remaining Prop hypothesis of the rank-two
four-direction hinge: the statement that the circuit bound's equality locus
`sum_c T_c p_c = 1` carries no four pairwise non-parallel atoms.  The sibling lane closed
the `nu = 1` half of it by a moment argument (`not_cornerHeaviness_of_pairCap`) and left
the `nu != 1` band open, measured strictly infeasible but not mechanised.  This file
closes the band -- and in doing so covers `nu = 1` too, because the mechanism turns out
not to see the shape matrix's determinant at all.

## What the band actually is

The equality locus carries a symmetric trace-one shape matrix `R` with
`p_c = <g_c, R g_c> / l_c` (the Caratheodory lane's
`exists_isSymm_shapeMatrix_traceOne_of_isTie`).  Writing `R`'s eigenvalues as
`(1 +- nu)/2`, the sibling's `nu = 1` case is `det R = 0`; the band is `det R != 0`.

## The Bloch chart, and why the band is not a second argument

An atom's UNIT PROJECTOR `g_c g_c^T / l_c` is a symmetric two by two matrix of trace one,
so it is a point `P_c = (u_c, v_c, 1)` of a three-dimensional space with `u^2 + v^2 = 1`.
Two bilinear forms live there:

    coneForm  C(P,Q) = P0 Q0 + P1 Q1 - P2 Q2          C(P_c,P_d) = 2 (B_cd - 1)
    shapeForm A(P,Q) = 2 (P . Q) - (P . k)(Q . k)     A(P_c,P_d) = 4 (B_cd - p_c p_d)

with `k = (R00 - R11, R01 + R10, 1)` the Bloch vector of `R`.  So the CONE form measures
PARALLELISM (it vanishes off-diagonal exactly on parallel atoms and vanishes on the
diagonal exactly because a unit projector has rank one) and the SHAPE form measures the
PAIR-CAP SLACK.  The whole dictionary is `ring`; no square root, no eigenvector, no
determinant hypothesis.

## The mechanism, in one line

At equality the Caratheodory reduction's three-atom sub-design ALSO attains `1`, so every
one of its pivot steps is tight and its three atoms SATURATE the cap pairwise
(`tight_of_sum_mass_mul_heaviness_eq_one`).  Saturation is exactly `A(P_j,P_k) = 0`: the
three Bloch points are a shape-ORTHOGONAL triple, hence a BASIS of the three-dimensional
space -- and linear independence from a diagonal Gram needs bilinearity alone, no
definiteness, which is why `det R` never enters.  A fourth atom's Bloch point expands in
that basis with coefficients `A(P_w,P_j)/A(P_j,P_j) >= 0` (the cap), and its own vanishing
cone form reads

    0 = C(P_w,P_w) = 2 sum_{j<k} x_j x_k C(P_j,P_k),

a sum of NONPOSITIVE terms, so every pairwise product `x_j x_k` vanishes.  At most one
coordinate survives, the last coordinates force it to be one, and the fourth atom IS one
of the three.  Four pairwise non-parallel atoms into three Bloch points is a pigeonhole
violation, and that is where the count FOUR acts.

## Why there is no margin to quote, and why that is the right shape

MEASURED, at exact rational and ninety-digit precision, outside Lean.  Maximising the
worst pair slack over four-direction designs on the equality locus returns a supremum of
ZERO at every `nu`, approached only as two directions MERGE -- the deficit is linear in
the smallest angular gap (at `nu = 0` it is `sqrt 3 / 12` times that gap, matching the
optimiser to five digits).  The dependence on the NUMBER of directions is exactly
`(N - 3)` times that unit deficit -- measured `0.1441 / 0.2879 / 0.4305` at `nu = 0` for
`N = 4 / 5 / 6`, and the same `1 : 2 : 3` ratio at `nu = 0.5` and `nu = 0.9` -- because a
configuration of `N` directions has `N - 3` atoms that the pigeonhole must push off the
tight triple.  So no floor-proportional margin exists and none is claimed;
the theorem is a RIGIDITY statement, and its Lean proof is correspondingly a
vanishing-sum argument rather than an estimate.  The ninety-digit run also confirms the
structural fact the proof rests on: fixing one cone point, its two shape-orthogonal cone
partners are automatically orthogonal TO EACH OTHER (measured `|A(P2,P3)| < 1e-60` at
every `nu` tested and every base point), and the resulting triple has masses summing to
two with zero barycentre -- it IS a design.  The invariant behind that is
`det(N - t G)` having no `t^2` term, identically in `nu`.

## What this closes

`rankTwoEqualityStratum_holds` is unconditional.  With the Caratheodory lane's
`rankTwoCircuitReduction_holds` it discharges both inputs of
`not_isTie_of_circuitReduction_of_equalityStratum`, so `not_isTie_of_fourNonParallel` --
the RANK-TWO four-direction hinge -- holds with no Prop hypotheses.
-/
/-! ## Part B1: the Bloch chart, and the two bilinear forms it carries -/

/-- The **cone form**.  A point of `Fin 3 -> R` codes the symmetric two by two matrix
whose traceless part is `(P 0, P 1)` and whose trace is `P 2`; `coneForm P P` is then
`-4 det` of that matrix, so the null cone of `coneForm` is exactly the rank-one locus. -/
def coneForm (leftPoint rightPoint : Fin 3 → ℝ) : ℝ :=
  leftPoint 0 * rightPoint 0 + leftPoint 1 * rightPoint 1 - leftPoint 2 * rightPoint 2

/-- The **shape form** attached to a Bloch vector.  Evaluated at the Bloch points of two
atoms it returns four times the pair-cap slack `unitPairGram - heaviness * heaviness`. -/
def shapeForm (shapeBloch leftPoint rightPoint : Fin 3 → ℝ) : ℝ :=
  2 * (leftPoint ⬝ᵥ rightPoint)
    - (leftPoint ⬝ᵥ shapeBloch) * (rightPoint ⬝ᵥ shapeBloch)

theorem coneForm_comm (leftPoint rightPoint : Fin 3 → ℝ) :
    coneForm leftPoint rightPoint = coneForm rightPoint leftPoint := by
  simp only [coneForm]; ring

theorem shapeForm_comm (shapeBloch leftPoint rightPoint : Fin 3 → ℝ) :
    shapeForm shapeBloch leftPoint rightPoint = shapeForm shapeBloch rightPoint leftPoint := by
  simp only [shapeForm, dotProduct, Fin.sum_univ_three]; ring

/-- The shape form is linear in its left slot: the coefficients of a three-term
combination come straight back out. -/
theorem shapeForm_combination_left (shapeBloch firstPoint secondPoint thirdPoint
    rightPoint : Fin 3 → ℝ) (firstCoeff secondCoeff thirdCoeff : ℝ) :
    shapeForm shapeBloch
        (firstCoeff • firstPoint + secondCoeff • secondPoint + thirdCoeff • thirdPoint)
        rightPoint
      = firstCoeff * shapeForm shapeBloch firstPoint rightPoint
        + secondCoeff * shapeForm shapeBloch secondPoint rightPoint
        + thirdCoeff * shapeForm shapeBloch thirdPoint rightPoint := by
  simp only [shapeForm, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The cone form of a three-term combination with itself, expanded.  This is the only
place the quadratic (as opposed to bilinear) behaviour of `coneForm` is used. -/
theorem coneForm_combination_self (firstPoint secondPoint thirdPoint : Fin 3 → ℝ)
    (firstCoeff secondCoeff thirdCoeff : ℝ) :
    coneForm (firstCoeff • firstPoint + secondCoeff • secondPoint + thirdCoeff • thirdPoint)
        (firstCoeff • firstPoint + secondCoeff • secondPoint + thirdCoeff • thirdPoint)
      = firstCoeff ^ 2 * coneForm firstPoint firstPoint
        + secondCoeff ^ 2 * coneForm secondPoint secondPoint
        + thirdCoeff ^ 2 * coneForm thirdPoint thirdPoint
        + 2 * firstCoeff * secondCoeff * coneForm firstPoint secondPoint
        + 2 * firstCoeff * thirdCoeff * coneForm firstPoint thirdPoint
        + 2 * secondCoeff * thirdCoeff * coneForm secondPoint thirdPoint := by
  simp only [coneForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Part B2: the orthogonal-triple engine

THE ENGINE, and it is design-free, matrix-free and square-root-free.  Three points of
`Fin 3 -> R` that are pairwise `shapeForm`-orthogonal with nonzero self-form are a BASIS
(bilinearity alone: no definiteness anywhere).  If in addition all three sit on the null
cone of `coneForm` and pair NEGATIVELY under it, then any fourth cone point pairing
NONNEGATIVELY with all three has nonnegative coordinates in that basis, and expanding its
own vanishing cone form leaves a sum of nonpositive terms which must therefore vanish
term by term.  All three pairwise coordinate products die, so at most one coordinate
survives -- the fourth point IS one of the three. -/

/-- Pairwise shape-orthogonal points with nonzero self-form are linearly independent.
Bilinearity is the whole proof; no positivity is needed. -/
theorem linearIndependent_of_shapeOrthogonal (shapeBloch firstPoint secondPoint
    thirdPoint : Fin 3 → ℝ)
    (horthFirstSecond : shapeForm shapeBloch firstPoint secondPoint = 0)
    (horthFirstThird : shapeForm shapeBloch firstPoint thirdPoint = 0)
    (horthSecondThird : shapeForm shapeBloch secondPoint thirdPoint = 0)
    (hselfFirst : shapeForm shapeBloch firstPoint firstPoint ≠ 0)
    (hselfSecond : shapeForm shapeBloch secondPoint secondPoint ≠ 0)
    (hselfThird : shapeForm shapeBloch thirdPoint thirdPoint ≠ 0) :
    LinearIndependent ℝ ![firstPoint, secondPoint, thirdPoint] := by
  rw [Fintype.linearIndependent_iff]
  intro coefficients hcombination index
  have hcombo : coefficients 0 • firstPoint + coefficients 1 • secondPoint
      + coefficients 2 • thirdPoint = 0 := by
    have hexpand := hcombination
    rw [Fin.sum_univ_three] at hexpand
    simpa using hexpand
  have hpair : ∀ probePoint : Fin 3 → ℝ,
      coefficients 0 * shapeForm shapeBloch firstPoint probePoint
        + coefficients 1 * shapeForm shapeBloch secondPoint probePoint
        + coefficients 2 * shapeForm shapeBloch thirdPoint probePoint = 0 := by
    intro probePoint
    rw [← shapeForm_combination_left shapeBloch firstPoint secondPoint thirdPoint probePoint,
      hcombo]
    simp only [shapeForm, dotProduct, Fin.sum_univ_three, Pi.zero_apply]
    ring
  have hfirstZero : coefficients 0 = 0 := by
    have hrow := hpair firstPoint
    rw [shapeForm_comm shapeBloch secondPoint firstPoint,
      shapeForm_comm shapeBloch thirdPoint firstPoint, horthFirstSecond,
      horthFirstThird] at hrow
    have hproduct : coefficients 0 * shapeForm shapeBloch firstPoint firstPoint = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hselfFirst
  have hsecondZero : coefficients 1 = 0 := by
    have hrow := hpair secondPoint
    rw [horthFirstSecond, shapeForm_comm shapeBloch thirdPoint secondPoint,
      horthSecondThird] at hrow
    have hproduct : coefficients 1 * shapeForm shapeBloch secondPoint secondPoint = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hselfSecond
  have hthirdZero : coefficients 2 = 0 := by
    have hrow := hpair thirdPoint
    rw [horthFirstThird, horthSecondThird] at hrow
    have hproduct : coefficients 2 * shapeForm shapeBloch thirdPoint thirdPoint = 0 := by
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_right hselfThird
  fin_cases index
  · exact hfirstZero
  · exact hsecondZero
  · exact hthirdZero

/-- Three linearly independent points of `Fin 3 -> R` expand every point. -/
theorem exists_combination_of_linearIndependent (firstPoint secondPoint thirdPoint
    probePoint : Fin 3 → ℝ)
    (hindependent : LinearIndependent ℝ ![firstPoint, secondPoint, thirdPoint]) :
    ∃ firstCoeff secondCoeff thirdCoeff : ℝ,
      probePoint = firstCoeff • firstPoint + secondCoeff • secondPoint
        + thirdCoeff • thirdPoint := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (Fin 3 → ℝ) := by
    simp
  let spanningBasis := basisOfLinearIndependentOfCardEqFinrank hindependent hcard
  have hcoe : ⇑spanningBasis = ![firstPoint, secondPoint, thirdPoint] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hindependent hcard
  refine ⟨spanningBasis.repr probePoint 0, spanningBasis.repr probePoint 1,
    spanningBasis.repr probePoint 2, ?_⟩
  have hsum := spanningBasis.sum_repr probePoint
  rw [Fin.sum_univ_three, hcoe] at hsum
  simpa using hsum.symm

/-- **THE ORTHOGONAL-TRIPLE ENGINE.**  A cone point pairing nonnegatively with a
shape-orthogonal triple of cone points that pair negatively among themselves IS one of
the triple.  The last coordinates normalise the scale; nothing else is assumed. -/
theorem eq_of_shapeNonneg_of_orthogonalConeTriple (shapeBloch firstPoint secondPoint
    thirdPoint probePoint : Fin 3 → ℝ)
    (hlastFirst : firstPoint 2 = 1) (hlastSecond : secondPoint 2 = 1)
    (hlastThird : thirdPoint 2 = 1) (hlastProbe : probePoint 2 = 1)
    (hconeFirst : coneForm firstPoint firstPoint = 0)
    (hconeSecond : coneForm secondPoint secondPoint = 0)
    (hconeThird : coneForm thirdPoint thirdPoint = 0)
    (hconeProbe : coneForm probePoint probePoint = 0)
    (hnegFirstSecond : coneForm firstPoint secondPoint < 0)
    (hnegFirstThird : coneForm firstPoint thirdPoint < 0)
    (hnegSecondThird : coneForm secondPoint thirdPoint < 0)
    (horthFirstSecond : shapeForm shapeBloch firstPoint secondPoint = 0)
    (horthFirstThird : shapeForm shapeBloch firstPoint thirdPoint = 0)
    (horthSecondThird : shapeForm shapeBloch secondPoint thirdPoint = 0)
    (hselfFirst : 0 < shapeForm shapeBloch firstPoint firstPoint)
    (hselfSecond : 0 < shapeForm shapeBloch secondPoint secondPoint)
    (hselfThird : 0 < shapeForm shapeBloch thirdPoint thirdPoint)
    (hprobeFirst : 0 ≤ shapeForm shapeBloch probePoint firstPoint)
    (hprobeSecond : 0 ≤ shapeForm shapeBloch probePoint secondPoint)
    (hprobeThird : 0 ≤ shapeForm shapeBloch probePoint thirdPoint) :
    probePoint = firstPoint ∨ probePoint = secondPoint ∨ probePoint = thirdPoint := by
  obtain ⟨firstCoeff, secondCoeff, thirdCoeff, hexpansion⟩ :=
    exists_combination_of_linearIndependent firstPoint secondPoint thirdPoint probePoint
      (linearIndependent_of_shapeOrthogonal shapeBloch firstPoint secondPoint thirdPoint
        horthFirstSecond horthFirstThird horthSecondThird (ne_of_gt hselfFirst)
        (ne_of_gt hselfSecond) (ne_of_gt hselfThird))
  have hcoordFirst : shapeForm shapeBloch probePoint firstPoint
      = firstCoeff * shapeForm shapeBloch firstPoint firstPoint := by
    rw [hexpansion, shapeForm_combination_left,
      shapeForm_comm shapeBloch secondPoint firstPoint,
      shapeForm_comm shapeBloch thirdPoint firstPoint, horthFirstSecond, horthFirstThird]
    ring
  have hcoordSecond : shapeForm shapeBloch probePoint secondPoint
      = secondCoeff * shapeForm shapeBloch secondPoint secondPoint := by
    rw [hexpansion, shapeForm_combination_left, horthFirstSecond,
      shapeForm_comm shapeBloch thirdPoint secondPoint, horthSecondThird]
    ring
  have hcoordThird : shapeForm shapeBloch probePoint thirdPoint
      = thirdCoeff * shapeForm shapeBloch thirdPoint thirdPoint := by
    rw [hexpansion, shapeForm_combination_left, horthFirstThird, horthSecondThird]
    ring
  have hfirstNonneg : 0 ≤ firstCoeff := by
    by_contra hnegative
    push Not at hnegative
    nlinarith [hprobeFirst, hcoordFirst, hselfFirst]
  have hsecondNonneg : 0 ≤ secondCoeff := by
    by_contra hnegative
    push Not at hnegative
    nlinarith [hprobeSecond, hcoordSecond, hselfSecond]
  have hthirdNonneg : 0 ≤ thirdCoeff := by
    by_contra hnegative
    push Not at hnegative
    nlinarith [hprobeThird, hcoordThird, hselfThird]
  have hcoeffTotal : firstCoeff + secondCoeff + thirdCoeff = 1 := by
    have hlast := congrFun hexpansion 2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hlastFirst, hlastSecond,
      hlastThird, hlastProbe, mul_one] at hlast
    linarith [hlast]
  have hconeExpansion : 2 * firstCoeff * secondCoeff * coneForm firstPoint secondPoint
      + 2 * firstCoeff * thirdCoeff * coneForm firstPoint thirdPoint
      + 2 * secondCoeff * thirdCoeff * coneForm secondPoint thirdPoint = 0 := by
    have hraw := hconeProbe
    rw [hexpansion, coneForm_combination_self, hconeFirst, hconeSecond, hconeThird] at hraw
    linarith [hraw]
  have hproductFirstSecond : firstCoeff * secondCoeff = 0 := by
    nlinarith [hconeExpansion, mul_nonneg hfirstNonneg hsecondNonneg,
      mul_nonneg hfirstNonneg hthirdNonneg, mul_nonneg hsecondNonneg hthirdNonneg,
      hnegFirstSecond, hnegFirstThird, hnegSecondThird]
  have hproductFirstThird : firstCoeff * thirdCoeff = 0 := by
    nlinarith [hconeExpansion, mul_nonneg hfirstNonneg hsecondNonneg,
      mul_nonneg hfirstNonneg hthirdNonneg, mul_nonneg hsecondNonneg hthirdNonneg,
      hnegFirstSecond, hnegFirstThird, hnegSecondThird]
  have hproductSecondThird : secondCoeff * thirdCoeff = 0 := by
    nlinarith [hconeExpansion, mul_nonneg hfirstNonneg hsecondNonneg,
      mul_nonneg hfirstNonneg hthirdNonneg, mul_nonneg hsecondNonneg hthirdNonneg,
      hnegFirstSecond, hnegFirstThird, hnegSecondThird]
  rcases eq_or_lt_of_le hfirstNonneg with hfirstZero | hfirstPos
  · rcases eq_or_lt_of_le hsecondNonneg with hsecondZero | hsecondPos
    · right; right
      have hthirdOne : thirdCoeff = 1 := by linarith [hcoeffTotal, hfirstZero, hsecondZero]
      rw [hexpansion, ← hfirstZero, ← hsecondZero, hthirdOne]
      simp
    · right; left
      have hthirdZero : thirdCoeff = 0 :=
        (mul_eq_zero.mp hproductSecondThird).resolve_left (ne_of_gt hsecondPos)
      have hsecondOne : secondCoeff = 1 := by linarith [hcoeffTotal, hfirstZero, hthirdZero]
      rw [hexpansion, ← hfirstZero, hsecondOne, hthirdZero]
      simp
  · left
    have hsecondZero : secondCoeff = 0 :=
      (mul_eq_zero.mp hproductFirstSecond).resolve_left (ne_of_gt hfirstPos)
    have hthirdZero : thirdCoeff = 0 :=
      (mul_eq_zero.mp hproductFirstThird).resolve_left (ne_of_gt hfirstPos)
    have hfirstOne : firstCoeff = 1 := by linarith [hcoeffTotal, hsecondZero, hthirdZero]
    rw [hexpansion, hfirstOne, hsecondZero, hthirdZero]
    simp

/-! ## Part B3: the Bloch chart of a rank-two design

The dictionary that turns the design into the engine's input.  An atom's unit projector
is a symmetric two by two matrix of trace one, so it is a point `(u, v, 1)` with
`u^2 + v^2 = 1` -- the Bloch chart.  Under that chart

    coneForm  (bloch a) (bloch b) = 2 * (unitPairGram a b - 1)
    shapeForm (bloch R) (bloch a) (bloch b) = 4 * (unitPairGram a b - heaviness a * heaviness b)

so the cone form measures PARALLELISM and the shape form measures the PAIR-CAP SLACK. -/

/-- The **Bloch point** of a plane vector: the traceless part of its unit projector,
with the trace appended. -/
noncomputable def blochPoint (vector : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![(vector 0 ^ 2 - vector 1 ^ 2) / leverageOf vector,
    2 * (vector 0 * vector 1) / leverageOf vector, 1]

/-- The **Bloch vector of a shape matrix** of trace one. -/
def shapeBlochOf (shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ) : Fin 3 → ℝ :=
  ![shapeMatrix 0 0 - shapeMatrix 1 1, shapeMatrix 0 1 + shapeMatrix 1 0, 1]

theorem leverageOf_two (vector : Fin 2 → ℝ) :
    leverageOf vector = vector 0 ^ 2 + vector 1 ^ 2 := by
  simp [leverageOf, Fin.sum_univ_two]

theorem blochPoint_apply_two (vector : Fin 2 → ℝ) : blochPoint vector 2 = 1 := by
  simp [blochPoint]

/-- **The cone form reads off parallelism.** -/
theorem coneForm_blochPoint (leftVector rightVector : Fin 2 → ℝ)
    (hleftPos : leverageOf leftVector ≠ 0) (hrightPos : leverageOf rightVector ≠ 0) :
    coneForm (blochPoint leftVector) (blochPoint rightVector)
      = 2 * ((leftVector ⬝ᵥ rightVector) ^ 2
          / (leverageOf leftVector * leverageOf rightVector)) - 2 := by
  rw [leverageOf_two] at hleftPos hrightPos
  simp only [coneForm, blochPoint, dotProduct, Fin.sum_univ_two, leverageOf_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  field_simp
  ring

/-- The Bloch point of a nonzero vector lies on the null cone. -/
theorem coneForm_blochPoint_self (vector : Fin 2 → ℝ) (hnonzero : leverageOf vector ≠ 0) :
    coneForm (blochPoint vector) (blochPoint vector) = 0 := by
  rw [coneForm_blochPoint vector vector hnonzero hnonzero]
  have hself : vector ⬝ᵥ vector = leverageOf vector := by
    simp [leverageOf_two, dotProduct, Fin.sum_univ_two]; ring
  rw [hself]
  field_simp
  norm_num

/-- Pairing a Bloch point against a trace-one shape matrix's Bloch vector returns twice
the shape matrix's quadratic form, normalised by the leverage. -/
theorem dotProduct_blochPoint_shapeBlochOf (vector : Fin 2 → ℝ)
    (shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ) (htrace : Matrix.trace shapeMatrix = 1)
    (hnonzero : leverageOf vector ≠ 0) :
    blochPoint vector ⬝ᵥ shapeBlochOf shapeMatrix
      = 2 * (vector ⬝ᵥ (shapeMatrix *ᵥ vector)) / leverageOf vector := by
  rw [Matrix.trace_fin_two] at htrace
  have hdiagonal : shapeMatrix 1 1 = 1 - shapeMatrix 0 0 := by linarith
  rw [leverageOf_two] at hnonzero
  simp only [blochPoint, shapeBlochOf, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Fin.sum_univ_three, leverageOf_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, hdiagonal]
  field_simp
  ring

/-- **The shape form reads off the pair-cap slack.** -/
theorem shapeForm_blochPoint (leftVector rightVector : Fin 2 → ℝ)
    (shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ) (htrace : Matrix.trace shapeMatrix = 1)
    (leftHeaviness rightHeaviness : ℝ)
    (hleftPos : leverageOf leftVector ≠ 0) (hrightPos : leverageOf rightVector ≠ 0)
    (hleftShape : leverageOf leftVector * leftHeaviness
      = leftVector ⬝ᵥ (shapeMatrix *ᵥ leftVector))
    (hrightShape : leverageOf rightVector * rightHeaviness
      = rightVector ⬝ᵥ (shapeMatrix *ᵥ rightVector)) :
    shapeForm (shapeBlochOf shapeMatrix) (blochPoint leftVector) (blochPoint rightVector)
      = 4 * ((leftVector ⬝ᵥ rightVector) ^ 2
          / (leverageOf leftVector * leverageOf rightVector)
        - leftHeaviness * rightHeaviness) := by
  have hleftPair : blochPoint leftVector ⬝ᵥ shapeBlochOf shapeMatrix = 2 * leftHeaviness := by
    rw [dotProduct_blochPoint_shapeBlochOf leftVector shapeMatrix htrace hleftPos,
      ← hleftShape]
    field_simp
  have hrightPair : blochPoint rightVector ⬝ᵥ shapeBlochOf shapeMatrix
      = 2 * rightHeaviness := by
    rw [dotProduct_blochPoint_shapeBlochOf rightVector shapeMatrix htrace hrightPos,
      ← hrightShape]
    field_simp
  have hcross : blochPoint leftVector ⬝ᵥ blochPoint rightVector
      = coneForm (blochPoint leftVector) (blochPoint rightVector) + 2 := by
    simp only [coneForm, dotProduct, Fin.sum_univ_three, blochPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [shapeForm, hleftPair, hrightPair, hcross,
    coneForm_blochPoint leftVector rightVector hleftPos hrightPos]
  ring

/-! ## Part B4: the equality case of the circuit bound

The shipped circuit bound stops at `<= 1`.  At EQUALITY it says much more, and the extra
content is the whole band argument: the support has exactly THREE labels, every pivot
step is tight, and every pair inside the support SATURATES the cap.  A saturating triple
is precisely a shape-orthogonal triple in the Bloch chart, which is what the engine of
Part B2 consumes. -/

/-- **THE CIRCUIT BOUND AT EQUALITY.**  Design-free and index-type-generic, exactly like
the bound it sharpens. -/
theorem tight_of_sum_mass_mul_heaviness_eq_one
    {label : Type*} [Fintype label] [DecidableEq label]
    (mass heaviness : label → ℝ) (cap : label → label → ℝ) (support : Finset label)
    (hmassNonneg : ∀ index, 0 ≤ mass index)
    (hmassVanishesOffSupport : ∀ index, index ∉ support → mass index = 0)
    (hmassTotal : ∑ index, mass index = 2)
    (hprobe : ∀ pivot ∈ support, ∑ index, mass index * cap pivot index = 1)
    (hcapDiagonal : ∀ pivot ∈ support, cap pivot pivot = 1)
    (hheavinessNonneg : ∀ index, 0 ≤ heaviness index)
    (hheavinessLtOne : ∀ index, heaviness index < 1)
    (hpairCap : ∀ pivot index, pivot ≠ index →
      heaviness pivot * heaviness index ≤ cap pivot index)
    (hsupportSmall : support.card ≤ 3)
    (hequality : ∑ index, mass index * heaviness index = 1) :
    support.card = 3
      ∧ (∀ pivot ∈ support, mass pivot * (1 + heaviness pivot) = 1)
      ∧ (∀ pivot ∈ support, ∀ partner ∈ support, pivot ≠ partner →
          heaviness pivot * heaviness partner = cap pivot partner) := by
  classical
  have hpivotIdentity : ∀ pivot ∈ support,
      (1 - heaviness pivot) * (1 - mass pivot * (1 + heaviness pivot))
        = ∑ index ∈ Finset.univ.erase pivot,
            mass index * (cap pivot index - heaviness pivot * heaviness index) := by
    intro pivot hpivotMem
    have hcapSplit : mass pivot * cap pivot pivot
        + ∑ index ∈ Finset.univ.erase pivot, mass index * cap pivot index = 1 := by
      rw [Finset.add_sum_erase _ (fun index => mass index * cap pivot index)
        (Finset.mem_univ pivot)]
      exact hprobe pivot hpivotMem
    rw [hcapDiagonal pivot hpivotMem] at hcapSplit
    have hheavySplit : mass pivot * heaviness pivot
        + ∑ index ∈ Finset.univ.erase pivot, mass index * heaviness index = 1 := by
      rw [Finset.add_sum_erase _ (fun index => mass index * heaviness index)
        (Finset.mem_univ pivot)]
      exact hequality
    have hexpand : ∑ index ∈ Finset.univ.erase pivot,
          mass index * (cap pivot index - heaviness pivot * heaviness index)
        = (∑ index ∈ Finset.univ.erase pivot, mass index * cap pivot index)
          - heaviness pivot
            * ∑ index ∈ Finset.univ.erase pivot, mass index * heaviness index := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun index _ => by ring
    rw [hexpand]
    linear_combination (-1 : ℝ) * hcapSplit + heaviness pivot * hheavySplit
  have htermNonneg : ∀ pivot : label, ∀ index ∈ Finset.univ.erase pivot,
      0 ≤ mass index * (cap pivot index - heaviness pivot * heaviness index) := by
    intro pivot index hindexMem
    have hdistinct : pivot ≠ index := fun heq => (Finset.mem_erase.mp hindexMem).1 heq.symm
    exact mul_nonneg (hmassNonneg index) (by linarith [hpairCap pivot index hdistinct])
  have hpivotStep : ∀ pivot ∈ support, mass pivot * (1 + heaviness pivot) ≤ 1 := by
    intro pivot hpivotMem
    have hsum := Finset.sum_nonneg (htermNonneg pivot)
    rw [← hpivotIdentity pivot hpivotMem] at hsum
    nlinarith [hsum, hheavinessLtOne pivot]
  have hsupportMass : ∑ pivot ∈ support, mass pivot = 2 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      fun index _ hindexOut => hmassVanishesOffSupport index hindexOut]
    exact hmassTotal
  have hsupportHeavy : ∑ pivot ∈ support, mass pivot * heaviness pivot = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support) fun index _ hindexOut => by
      rw [hmassVanishesOffSupport index hindexOut, zero_mul]]
    exact hequality
  have hcombined : ∑ pivot ∈ support, mass pivot * (1 + heaviness pivot) = 3 := by
    have hregroup : ∀ pivot : label, mass pivot * (1 + heaviness pivot)
        = mass pivot + mass pivot * heaviness pivot := fun pivot => by ring
    rw [Finset.sum_congr rfl fun pivot _ => hregroup pivot, Finset.sum_add_distrib,
      hsupportMass, hsupportHeavy]
    norm_num
  have hcardGe : (3 : ℝ) ≤ (support.card : ℝ) := by
    calc (3 : ℝ) = ∑ pivot ∈ support, mass pivot * (1 + heaviness pivot) := hcombined.symm
      _ ≤ ∑ _pivot ∈ support, (1 : ℝ) := Finset.sum_le_sum hpivotStep
      _ = (support.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcardThree : support.card = 3 :=
    le_antisymm hsupportSmall (by exact_mod_cast hcardGe)
  have hdeficitZero : ∀ pivot ∈ support, mass pivot * (1 + heaviness pivot) = 1 := by
    have hzeroSum : ∑ pivot ∈ support, (1 - mass pivot * (1 + heaviness pivot)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcombined,
        hcardThree]
      norm_num
    intro pivot hpivotMem
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun index hindexMem => by linarith [hpivotStep index hindexMem])).mp hzeroSum
    linarith [hall pivot hpivotMem]
  refine ⟨hcardThree, hdeficitZero, ?_⟩
  intro pivot hpivotMem partner hpartnerMem hdistinct
  have hidentity := hpivotIdentity pivot hpivotMem
  rw [hdeficitZero pivot hpivotMem] at hidentity
  have hzeroSum : ∑ index ∈ Finset.univ.erase pivot,
      mass index * (cap pivot index - heaviness pivot * heaviness index) = 0 := by
    simp only [sub_self, mul_zero] at hidentity
    exact hidentity.symm
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (htermNonneg pivot)).mp hzeroSum
  have hterm := hall partner
    (Finset.mem_erase.mpr ⟨Ne.symm hdistinct, Finset.mem_univ partner⟩)
  have hpartnerPos : 0 < mass partner := by
    by_contra hnonpos
    push Not at hnonpos
    nlinarith [hdeficitZero partner hpartnerMem, hheavinessNonneg partner, hnonpos]
  rcases mul_eq_zero.mp hterm with hzero | hzero
  · exact absurd hzero (ne_of_gt hpartnerPos)
  · linarith

/-- **On the equality locus no atom is short.**  Every atom of a rank-two design whose
mass-weighted heaviness attains `1` has leverage at least one -- in particular no atom
vanishes, so every atom has a Bloch point. -/
theorem one_le_leverageOf_of_designValue (D : WeightedDesign m 2)
    (hdesignValue : ∑ label, atomMass D label * atomHeaviness D label = 1)
    (label : Fin m) : 1 ≤ leverageOf (D.atom label) := by
  have htermwise : ∀ index : Fin m,
      D.weight index * (leverageOf (D.atom index) - 1)
        ≤ atomMass D index * atomHeaviness D index := by
    intro index
    rw [atomMass, atomHeaviness]
    split
    · rename_i hlight
      nlinarith [hlight, D.weight_pos index]
    · rename_i hheavy
      push Not at hheavy
      have hpositive : (0 : ℝ) < leverageOf (D.atom index) := lt_trans zero_lt_one hheavy
      have hcancel : D.weight index * leverageOf (D.atom index)
            * (1 - (leverageOf (D.atom index))⁻¹)
          = D.weight index * (leverageOf (D.atom index) - 1) := by field_simp
      linarith [hcancel]
  have htotal : ∑ index, D.weight index * (leverageOf (D.atom index) - 1) = 1 := by
    have hshipped := sum_weight_mul_leverage_sub_one D
    norm_num at hshipped
    exact hshipped
  have hpointwise := (Finset.sum_eq_sum_iff_of_le
    (fun index (_ : index ∈ Finset.univ) => htermwise index)).mp (htotal.trans hdesignValue.symm)
  have hlabelEq := hpointwise label (Finset.mem_univ label)
  by_contra hshort
  push Not at hshort
  have hclip : atomHeaviness D label = 0 := by
    rw [atomHeaviness, if_pos (le_of_lt hshort)]
  rw [hclip, mul_zero] at hlabelEq
  nlinarith [hlabelEq, D.weight_pos label, hshort]

/-! ## Part B5: the equality stratum is empty

Assembling.  On the equality locus the Caratheodory reduction produces a three-atom
sub-design whose mass-weighted heaviness also attains `1`, so by Part B4 its three atoms
SATURATE the cap pairwise.  In the Bloch chart that is a shape-orthogonal triple of cone
points pairing negatively, and the engine of Part B2 then forces EVERY atom's Bloch point
to be one of the three.  Four pairwise non-parallel atoms into three Bloch points is a
pigeonhole violation -- and that is where the count FOUR finally acts. -/

/-- Pigeonhole, four into three. -/
theorem exists_repeat_of_four_into_three {carrier : Type*}
    (firstItem secondItem thirdItem fourthItem targetOne targetTwo targetThree : carrier)
    (hfirst : firstItem = targetOne ∨ firstItem = targetTwo ∨ firstItem = targetThree)
    (hsecond : secondItem = targetOne ∨ secondItem = targetTwo ∨ secondItem = targetThree)
    (hthird : thirdItem = targetOne ∨ thirdItem = targetTwo ∨ thirdItem = targetThree)
    (hfourth : fourthItem = targetOne ∨ fourthItem = targetTwo ∨ fourthItem = targetThree) :
    firstItem = secondItem ∨ firstItem = thirdItem ∨ firstItem = fourthItem
      ∨ secondItem = thirdItem ∨ secondItem = fourthItem ∨ thirdItem = fourthItem := by
  rcases hfirst with hone | hone | hone <;> rcases hsecond with htwo | htwo | htwo <;>
    rcases hthird with hthree | hthree | hthree <;>
    rcases hfourth with hfour | hfour | hfour <;>
    first
      | exact Or.inl (hone.trans htwo.symm)
      | exact Or.inr (Or.inl (hone.trans hthree.symm))
      | exact Or.inr (Or.inr (Or.inl (hone.trans hfour.symm)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (htwo.trans hthree.symm))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (htwo.trans hfour.symm)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hthree.trans hfour.symm)))))

/-- **THE EQUALITY STRATUM IS EMPTY, UNCONDITIONALLY.**  No rank-two design carrying the
tie's pair cap and four pairwise non-parallel atoms attains mass-weighted heaviness `1`.
No hypothesis on the shape matrix's determinant: the `nu = 1` corner and the `nu != 1`
band are the same argument. -/
theorem rankTwoEqualityStratum_holds : RankTwoEqualityStratum := by
  classical
  intro size D firstLabel secondLabel thirdLabel fourthLabel _hone _htwo _hthree _hfour
    _hfive _hsix hgramOne hgramTwo hgramThree hgramFour hgramFive hgramSix hpairCap
    hdesignValue
  -- on the equality locus no atom is short, so every atom has a Bloch point
  have hleverageOne : ∀ label : Fin size, 1 ≤ leverageOf (D.atom label) :=
    one_le_leverageOf_of_designValue D hdesignValue
  have hleverageNonzero : ∀ label : Fin size, leverageOf (D.atom label) ≠ 0 := fun label =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (hleverageOne label))
  have hatomNonzero : ∀ label : Fin size, D.atom label ≠ 0 := by
    intro label hzero
    exact hleverageNonzero label (by rw [hzero]; simp [leverageOf])
  have hcapAll : ∀ pivot partner : Fin size,
      atomHeaviness D pivot * atomHeaviness D partner ≤ unitPairGram D pivot partner := by
    intro pivot partner
    by_cases hsame : pivot = partner
    · subst hsame
      rw [unitPairGram_self D (hatomNonzero pivot)]
      nlinarith [atomHeaviness_nonneg D pivot, atomHeaviness_lt_one D pivot]
    · exact hpairCap pivot partner hsame
  have hdesignValueFlat : ∑ label, D.weight label * leverageOf (D.atom label)
      * atomHeaviness D label = 1 := by
    simpa [atomMass] using hdesignValue
  -- the shipped circuit bound, at an arbitrary three-supported admissible mass vector
  have hthreeSupportBound : ∀ (subWeight : Fin size → ℝ) (support : Finset (Fin size)),
      (∀ label, 0 ≤ subWeight label) → (∀ label, label ∉ support → subWeight label = 0) →
      support.card ≤ 3 → (∑ label, subWeight label • atomMatrix (D.atom label) = 1) →
      ∑ label, subWeight label * leverageOf (D.atom label) * atomHeaviness D label ≤ 1 := by
    intro subWeight support hsubNonneg hsubOff hsubCard hsubParseval
    have hmassTotal : ∑ label, subWeight label * leverageOf (D.atom label) = 2 := by
      have hrank := sum_coefficient_mul_leverage D subWeight hsubParseval
      norm_num at hrank
      exact hrank
    exact sum_mass_mul_heaviness_le_one_of_support_card_le_three
      (fun label => subWeight label * leverageOf (D.atom label)) (atomHeaviness D)
      (unitPairGram D) support
      (fun label => mul_nonneg (hsubNonneg label) (leverageOf_nonneg _))
      (fun label hout => by rw [hsubOff label hout, zero_mul]) hmassTotal
      (fun pivot _ => sum_coefficientMass_mul_unitPairGram_eq_one D subWeight hsubParseval
        (hatomNonzero pivot))
      (fun pivot _ => unitPairGram_self D (hatomNonzero pivot))
      (atomHeaviness_nonneg D) (atomHeaviness_le_one D) hpairCap (by exact_mod_cast hsubCard)
  obtain ⟨shapeMatrix, _hsymmetric, hquadratic, htrace⟩ :=
    exists_isSymm_shapeMatrix_traceOne_of_threeSupportBound D (atomHeaviness D)
      hthreeSupportBound hdesignValueFlat
  -- the Caratheodory reduction, and its equality
  obtain ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard, hsubParseval, hmonotone⟩ :=
    rankTwoCircuitReduction_holds size D (atomHeaviness D)
  have hmassTotal : ∑ label, subWeight label * leverageOf (D.atom label) = 2 := by
    have hrank := sum_coefficient_mul_leverage D subWeight hsubParseval
    norm_num at hrank
    exact hrank
  have hreducedEquality : ∑ label, subWeight label * leverageOf (D.atom label)
      * atomHeaviness D label = 1 :=
    le_antisymm (hthreeSupportBound subWeight support hsubNonneg hsubOff hsubCard hsubParseval)
      (by rw [← hdesignValue]; exact hmonotone)
  obtain ⟨hcardThree, _hpivotTight, hpairTight⟩ :=
    tight_of_sum_mass_mul_heaviness_eq_one
      (fun label => subWeight label * leverageOf (D.atom label)) (atomHeaviness D)
      (unitPairGram D) support
      (fun label => mul_nonneg (hsubNonneg label) (leverageOf_nonneg _))
      (fun label hout => by rw [hsubOff label hout, zero_mul]) hmassTotal
      (fun pivot _ => sum_coefficientMass_mul_unitPairGram_eq_one D subWeight hsubParseval
        (hatomNonzero pivot))
      (fun pivot _ => unitPairGram_self D (hatomNonzero pivot))
      (atomHeaviness_nonneg D) (atomHeaviness_lt_one D) hpairCap hsubCard hreducedEquality
  obtain ⟨alphaLabel, betaLabel, gammaLabel, _hab, _hac, _hbc, hsupportEq⟩ :=
    Finset.card_eq_three.mp hcardThree
  have halphaMem : alphaLabel ∈ support := by rw [hsupportEq]; simp
  have hbetaMem : betaLabel ∈ support := by rw [hsupportEq]; simp
  have hgammaMem : gammaLabel ∈ support := by rw [hsupportEq]; simp
  -- the Bloch dictionary
  have hcone : ∀ leftLabel rightLabel : Fin size,
      coneForm (blochPoint (D.atom leftLabel)) (blochPoint (D.atom rightLabel))
        = 2 * unitPairGram D leftLabel rightLabel - 2 := fun leftLabel rightLabel =>
    coneForm_blochPoint (D.atom leftLabel) (D.atom rightLabel)
      (hleverageNonzero leftLabel) (hleverageNonzero rightLabel)
  have hshape : ∀ leftLabel rightLabel : Fin size,
      shapeForm (shapeBlochOf shapeMatrix) (blochPoint (D.atom leftLabel))
          (blochPoint (D.atom rightLabel))
        = 4 * (unitPairGram D leftLabel rightLabel
            - atomHeaviness D leftLabel * atomHeaviness D rightLabel) :=
    fun leftLabel rightLabel =>
      shapeForm_blochPoint (D.atom leftLabel) (D.atom rightLabel) shapeMatrix htrace
        (atomHeaviness D leftLabel) (atomHeaviness D rightLabel)
        (hleverageNonzero leftLabel) (hleverageNonzero rightLabel)
        (hquadratic leftLabel) (hquadratic rightLabel)
  -- the triple is shape-orthogonal, cone-negative and cone-null
  have horth : ∀ leftLabel ∈ support, ∀ rightLabel ∈ support, leftLabel ≠ rightLabel →
      shapeForm (shapeBlochOf shapeMatrix) (blochPoint (D.atom leftLabel))
        (blochPoint (D.atom rightLabel)) = 0 := by
    intro leftLabel hleftMem rightLabel hrightMem hdistinct
    rw [hshape leftLabel rightLabel, hpairTight leftLabel hleftMem rightLabel hrightMem hdistinct]
    ring
  have hnegative : ∀ leftLabel ∈ support, ∀ rightLabel ∈ support, leftLabel ≠ rightLabel →
      coneForm (blochPoint (D.atom leftLabel)) (blochPoint (D.atom rightLabel)) < 0 := by
    intro leftLabel hleftMem rightLabel hrightMem hdistinct
    rw [hcone leftLabel rightLabel,
      ← hpairTight leftLabel hleftMem rightLabel hrightMem hdistinct]
    nlinarith [atomHeaviness_nonneg D leftLabel, atomHeaviness_nonneg D rightLabel,
      atomHeaviness_lt_one D leftLabel, atomHeaviness_lt_one D rightLabel]
  have hselfPositive : ∀ label : Fin size,
      0 < shapeForm (shapeBlochOf shapeMatrix) (blochPoint (D.atom label))
        (blochPoint (D.atom label)) := by
    intro label
    rw [hshape label label, unitPairGram_self D (hatomNonzero label)]
    nlinarith [atomHeaviness_nonneg D label, atomHeaviness_lt_one D label]
  have hprobeNonneg : ∀ probeLabel partnerLabel : Fin size,
      0 ≤ shapeForm (shapeBlochOf shapeMatrix) (blochPoint (D.atom probeLabel))
        (blochPoint (D.atom partnerLabel)) := by
    intro probeLabel partnerLabel
    rw [hshape probeLabel partnerLabel]
    linarith [hcapAll probeLabel partnerLabel]
  -- every atom's Bloch point IS one of the triple's
  have hclassify : ∀ probeLabel : Fin size,
      blochPoint (D.atom probeLabel) = blochPoint (D.atom alphaLabel)
        ∨ blochPoint (D.atom probeLabel) = blochPoint (D.atom betaLabel)
        ∨ blochPoint (D.atom probeLabel) = blochPoint (D.atom gammaLabel) := by
    intro probeLabel
    have habDistinct : alphaLabel ≠ betaLabel := _hab
    have hacDistinct : alphaLabel ≠ gammaLabel := _hac
    have hbcDistinct : betaLabel ≠ gammaLabel := _hbc
    exact eq_of_shapeNonneg_of_orthogonalConeTriple (shapeBlochOf shapeMatrix)
      (blochPoint (D.atom alphaLabel)) (blochPoint (D.atom betaLabel))
      (blochPoint (D.atom gammaLabel)) (blochPoint (D.atom probeLabel))
      (blochPoint_apply_two _) (blochPoint_apply_two _) (blochPoint_apply_two _)
      (blochPoint_apply_two _)
      (coneForm_blochPoint_self _ (hleverageNonzero alphaLabel))
      (coneForm_blochPoint_self _ (hleverageNonzero betaLabel))
      (coneForm_blochPoint_self _ (hleverageNonzero gammaLabel))
      (coneForm_blochPoint_self _ (hleverageNonzero probeLabel))
      (hnegative alphaLabel halphaMem betaLabel hbetaMem habDistinct)
      (hnegative alphaLabel halphaMem gammaLabel hgammaMem hacDistinct)
      (hnegative betaLabel hbetaMem gammaLabel hgammaMem hbcDistinct)
      (horth alphaLabel halphaMem betaLabel hbetaMem habDistinct)
      (horth alphaLabel halphaMem gammaLabel hgammaMem hacDistinct)
      (horth betaLabel hbetaMem gammaLabel hgammaMem hbcDistinct)
      (hselfPositive alphaLabel) (hselfPositive betaLabel) (hselfPositive gammaLabel)
      (hprobeNonneg probeLabel alphaLabel) (hprobeNonneg probeLabel betaLabel)
      (hprobeNonneg probeLabel gammaLabel)
  -- equal Bloch points means parallel atoms
  have hparallel : ∀ leftLabel rightLabel : Fin size,
      blochPoint (D.atom leftLabel) = blochPoint (D.atom rightLabel) →
      unitPairGram D leftLabel rightLabel = 1 := by
    intro leftLabel rightLabel hsame
    have hzero : coneForm (blochPoint (D.atom leftLabel))
        (blochPoint (D.atom rightLabel)) = 0 := by
      rw [hsame]
      exact coneForm_blochPoint_self _ (hleverageNonzero rightLabel)
    rw [hcone leftLabel rightLabel] at hzero
    linarith
  -- pigeonhole: four pairwise non-parallel atoms into three Bloch points
  rcases exists_repeat_of_four_into_three (blochPoint (D.atom firstLabel))
    (blochPoint (D.atom secondLabel)) (blochPoint (D.atom thirdLabel))
    (blochPoint (D.atom fourthLabel)) (blochPoint (D.atom alphaLabel))
    (blochPoint (D.atom betaLabel)) (blochPoint (D.atom gammaLabel))
    (hclassify firstLabel) (hclassify secondLabel) (hclassify thirdLabel)
    (hclassify fourthLabel) with
      hcollide | hcollide | hcollide | hcollide | hcollide | hcollide
  · exact hgramOne (hparallel firstLabel secondLabel hcollide)
  · exact hgramTwo (hparallel firstLabel thirdLabel hcollide)
  · exact hgramThree (hparallel firstLabel fourthLabel hcollide)
  · exact hgramFour (hparallel secondLabel thirdLabel hcollide)
  · exact hgramFive (hparallel secondLabel fourthLabel hcollide)
  · exact hgramSix (hparallel thirdLabel fourthLabel hcollide)

/-! ## Part B6: the rank-two hinge, unconditionally

Both residual inputs of `not_isTie_of_circuitReduction_of_equalityStratum` are now bare
terms: `rankTwoCircuitReduction_holds` from the Caratheodory lane and
`rankTwoEqualityStratum_holds` above.  The rank-two four-direction hinge therefore holds
with NO hypotheses beyond the four labels' pairwise non-parallelism. -/

/-- **THE RANK-TWO FOUR-DIRECTION HINGE, HYPOTHESIS-FREE.**  A rank-two design with four
pairwise non-parallel atoms is not a tie -- equivalently, some pair dominates STRICTLY. -/
theorem not_isTie_of_fourNonParallel (D : WeightedDesign m 2)
    (firstLabel secondLabel thirdLabel fourthLabel : Fin m)
    (hone : firstLabel ≠ secondLabel) (htwo : firstLabel ≠ thirdLabel)
    (hthree : firstLabel ≠ fourthLabel) (hfour : secondLabel ≠ thirdLabel)
    (hfive : secondLabel ≠ fourthLabel) (hsix : thirdLabel ≠ fourthLabel)
    (hgramOne : unitPairGram D firstLabel secondLabel ≠ 1)
    (hgramTwo : unitPairGram D firstLabel thirdLabel ≠ 1)
    (hgramThree : unitPairGram D firstLabel fourthLabel ≠ 1)
    (hgramFour : unitPairGram D secondLabel thirdLabel ≠ 1)
    (hgramFive : unitPairGram D secondLabel fourthLabel ≠ 1)
    (hgramSix : unitPairGram D thirdLabel fourthLabel ≠ 1) :
    ¬ IsTie D :=
  not_isTie_of_equalityStratum rankTwoEqualityStratum_holds D
    firstLabel secondLabel thirdLabel fourthLabel hone htwo hthree hfour hfive hsix
    hgramOne hgramTwo hgramThree hgramFour hgramFive hgramSix

end Gtz
