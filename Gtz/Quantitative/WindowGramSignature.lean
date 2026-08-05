/-
# The window Gram: bordered inverse, Lorentzian signature, and a wall for trace one

The target was the residual left standing by the sibling lane's `TieBasisWindow`:

    at a tie, tr (S_Q − 1)⁻¹ = 1 + Σ over the insiders whose erasure is DEPENDENT
    of (q_c − 1);  in particular = 1 at every CIRCUIT window.

The route assigned was the window's own geometry: writing `Γ_Q` for the Gram of the
window's `rank + 1` atoms and `R = (Γ_Q − 1)⁻¹`, the claim is that `R` is Lorentzian with
the circuit dependency `alpha` as timelike axis, that the tie makes every `e_c`
non-timelike, and that the residual asks every `e_c` with `alpha_c` nonzero to be exactly
NULL — a boundary rigidity rather than another inequality.

The geometry is real and is landed here at arbitrary rank.  The rigidity is FALSE, and the
last section proves it with a model.

## The dictionary (arbitrary rank, arbitrary window size)

`windowMatrix` is the `rank × window` rectangle `B` of the window's atoms;
`subsetSum = B Bᵀ` is the moment and `windowGram = Bᵀ B` is the Gram.  Push-through gives
the bordered inverse in closed form, with no spectral theory and no cardinality hypothesis:

    Bᵀ (B Bᵀ − 1)⁻¹ B  =  1 + (Bᵀ B − 1)⁻¹        (`transpose_mul_gapInv_mul_rectangle`)

Reading the `(c, c)` entry and the trace of that one identity yields the whole dictionary:

    q_c            =  1 + R_cc                    (`pivot_eq_one_add_windowGramGapInv`)
    tr R           =  tr (S_Q − 1)⁻¹ − 1          (`trace_windowGramGapInv`)
    det (Γ_Q − 1)  =  (−1) ^ (|Q| + rank) · det (S_Q − 1)      (`det_gramGap`)

so at `|Q| = rank + 1` the Gram gap's determinant is exactly `−det (S_Q − 1) < 0`
(`det_windowGram_sub_one_of_card`): ONE extra negative direction.  The signature is pinned
by two definite pieces, each a two-line computation on the form
`⟨y, (Γ − 1) y⟩ = ‖B y‖² − ‖y‖²`, stated for an arbitrary index type so the rank-two lane
can use them unchanged:

* `gramGap_form_neg_of_kernel` — on `ker B` the form is `−‖·‖²`, the timelike piece;
* `gramGap_form_pos_of_range` — on `range Bᵀ` the form pulls back to
  `‖(S − 1) z‖² + ⟨z, (S − 1) z⟩ > 0`, the spacelike piece;
* `kernel_orthogonal_range` — the two are Euclidean-orthogonal.

Together: with a positive definite moment gap the Gram gap has signature
`(rank, |Q| − rank)`, hence `(rank, 1)` at a critical window.  `trace_eq_one_iff_forall_null`
then restates the residual: at a tie, trace one for the window IFF every standard basis
vector is null for `R`.

## What the tie does supply, and it is not local

`pivot_added_eq_one_of_singular_base`: if a base has SINGULAR gap and one further atom
restores definiteness, the added atom's pivot in the enlarged window is exactly one — the
kernel vector `v` of the base satisfies `(S_Q − 1) v = ⟨g, v⟩ g`, so
`(S_Q − 1)⁻¹ g = v / ⟨g, v⟩` and `q = 1` on the nose.  At a tie the existential half of
`IsTie` hands over a weak dominator, which is singular because it is not strict, so
`pivot_added_eq_one_of_isTie` verifies the residual AT ONE COORDINATE of every window built
over a tie's dominator; `windowGramGapInv_diag_added_eq_zero_of_isTie` is the same fact as a
nullity.  Note where the input came from: a subset of the design that the window does not
contain.  That is the shape the wall below says every proof must have.

## THE WALL

`no_window_local_trace_one`.  Four hypotheses — gate, critical cardinality, circuit, every
insider pivot at least one — are EXACTLY the tie's window-local content: a window of
`rank + 1` atoms has precisely its `rank + 1` erasures as `rank`-subsets, and about those
the tie says only that none dominates strictly, i.e. only `q_c ≥ 1`.  All four hold, and
the trace is not one, on the tetrahedron ray:

    rayDesign : a genuine (7,3) design for every scale in (1/2, 1) — four tetrahedron
    directions at that scale with weight (16 − 12 scale²)⁻¹, plus three doubled coordinate
    axes with weight 4(1 − scale²)/(16 − 12 scale²), Parseval and mass exact.

Its window `{0,1,2,3}` has moment `(4 scale²) · 1`, gap `(4 scale² − 1) · 1 ≻ 0`, every
insider pivot `3 scale² / (4 scale² − 1) ≥ 1`, every erasure independent (each erased
moment is `(4 scale²) · 1 − g gᵀ` with base pivot `3/4` at every scale, so the rank-one
Schur step keeps it definite) — and inverse-gap trace

    3 / (4 scale² − 1)   >  1  for every scale < 1,   = 1 only at scale = 1.

At `scale = 1` the four atoms ARE the `(4,3)` tetrahedron tie, where the trace is one.  So
the counterexample family runs right up to the tie: the trace-one locus on this ray is the
single tie point, approached through a region in which every window-local hypothesis
already holds.  No continuity or perturbation argument off the tie recovers the equation
either.  At `scale = 3/4` the numbers are `4/37` and `7/37` for the weights, `27/20` for
every insider pivot and `12/5` for the trace.

The witness is not a tie (`rayDesign_not_isTie`: its three doubled axes dominate strictly),
and it could not be — a window-local witness that were a tie would refute the residual
itself.  That is why this wall is optimal in its class: the strongest possible
window-confined counterexample is one that fails to be a tie only through atoms outside the
window.

## What the Lorentzian picture proves, and what it does not

It proves the CONVERSE of the residual, which is already shipped: a causal basis vector
(`R_cc ≤ 0`, i.e. `q_c ≤ 1`, i.e. the erasure dominates) is never orthogonal to a timelike
axis, so `alpha_c ≠ 0` and the erasure is independent — "a weak dominator is a basis".  The
residual is the other direction, and in a Lorentzian space spacelike vectors carry nonzero
coefficients of a timelike vector just as happily as null ones.  Non-timelike is the
UNCONSTRAINED regime; there is no boundary rigidity to harvest.  This is a different
mechanism from the sibling lane's wall, which surveys the outside sources of a reverse
inequality and finds them all same-signed: that argument rules out three routes, this one
rules out every argument whose hypotheses are confined to the window's atom geometry.

## What is left

The residual survives.  What this file changes is the search space: any proof must consume
the tie through atoms outside the window, and the only mechanism of that kind currently
known is the singular-base step above.  The natural next question is whether the base
supplied by `IsTie` can be moved: `pivot_added_eq_one_of_isTie` fixes the pivot of the
ADDED atom, and the remaining `rank` coordinates of that window would follow if each
`(C \ c) ∪ {x}` were itself known singular — which is the residual again, so the step does
not iterate on its own.  Breaking that circle, or finding a second non-local mechanism, is
the frontier.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.TraceIdentity
import Gtz.Design.CapSlack
import Gtz.Corner.CapDictionary
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Dot-product positivity at an arbitrary finite index -/

/-- The dot square is nonnegative, at any finite index type. -/
theorem dotProductSelf_nonneg {slot : Type*} [Fintype slot] (vector : slot → ℝ) :
    0 ≤ vector ⬝ᵥ vector :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- The dot square is strictly positive off zero, at any finite index type. -/
theorem dotProductSelf_pos_of_ne_zero {slot : Type*} [Fintype slot] {vector : slot → ℝ}
    (hnonzero : vector ≠ 0) : 0 < vector ⬝ᵥ vector := by
  obtain ⟨coord, hcoord⟩ := Function.ne_iff.mp hnonzero
  simp only [Pi.zero_apply] at hcoord
  exact Finset.sum_pos' (fun index _ => mul_self_nonneg (vector index))
    ⟨coord, Finset.mem_univ coord, mul_self_pos.mpr hcoord⟩

/-! ## The rectangular dictionary, at arbitrary rank and arbitrary window size -/

section Rectangle

variable {slot : Type*} [Fintype slot] [DecidableEq slot]

/-- **The intertwiner.**  `B (BᵀB − 1) = (BBᵀ − 1) B`: the moment gap and the Gram gap are
one operator read on the two sides of `B`. -/
theorem rectangle_mul_gramGap (rectangle : Matrix (Fin rank) slot ℝ) :
    rectangle * (rectangleᵀ * rectangle - 1)
      = (rectangle * rectangleᵀ - 1) * rectangle := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc]

/-- The intertwiner inverted: `(BBᵀ − 1)⁻¹ B = B (BᵀB − 1)⁻¹`. -/
theorem gapInv_mul_rectangle (rectangle : Matrix (Fin rank) slot ℝ)
    (hmoment : IsUnit (rectangle * rectangleᵀ - 1).det)
    (hgram : IsUnit (rectangleᵀ * rectangle - 1).det) :
    (rectangle * rectangleᵀ - 1)⁻¹ * rectangle
      = rectangle * (rectangleᵀ * rectangle - 1)⁻¹ := by
  have hcancel : (rectangle * rectangleᵀ - 1)⁻¹ * (rectangle * (rectangleᵀ * rectangle - 1))
      = rectangle := by
    rw [rectangle_mul_gramGap, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hmoment,
      Matrix.one_mul]
  calc (rectangle * rectangleᵀ - 1)⁻¹ * rectangle
      = (rectangle * rectangleᵀ - 1)⁻¹
          * (rectangle * ((rectangleᵀ * rectangle - 1) * (rectangleᵀ * rectangle - 1)⁻¹)) := by
        rw [Matrix.mul_nonsing_inv _ hgram, Matrix.mul_one]
    _ = ((rectangle * rectangleᵀ - 1)⁻¹ * (rectangle * (rectangleᵀ * rectangle - 1)))
          * (rectangleᵀ * rectangle - 1)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = rectangle * (rectangleᵀ * rectangle - 1)⁻¹ := by rw [hcancel]

/-- **THE BORDERED INVERSE, IN CLOSED FORM.**  Conjugating the moment gap's inverse back
through `B` returns the Gram gap's inverse shifted by the identity:

    Bᵀ (B Bᵀ − 1)⁻¹ B  =  1 + (Bᵀ B − 1)⁻¹.

Every pivot of the window is therefore a DIAGONAL ENTRY of `(Γ − 1)⁻¹` offset by one, and
the whole pivot vector is read off one `window × window` matrix.  Push-through only: no
spectral theory, no cardinality hypothesis, arbitrary rank. -/
theorem transpose_mul_gapInv_mul_rectangle (rectangle : Matrix (Fin rank) slot ℝ)
    (hmoment : IsUnit (rectangle * rectangleᵀ - 1).det)
    (hgram : IsUnit (rectangleᵀ * rectangle - 1).det) :
    rectangleᵀ * (rectangle * rectangleᵀ - 1)⁻¹ * rectangle
      = 1 + (rectangleᵀ * rectangle - 1)⁻¹ := by
  have hexpand : (rectangleᵀ * rectangle) * (rectangleᵀ * rectangle - 1)⁻¹
      = (rectangleᵀ * rectangle - 1) * (rectangleᵀ * rectangle - 1)⁻¹
        + 1 * (rectangleᵀ * rectangle - 1)⁻¹ := by
    rw [← Matrix.add_mul]
    congr 1
    abel
  rw [Matrix.mul_assoc, gapInv_mul_rectangle rectangle hmoment hgram, ← Matrix.mul_assoc,
    hexpand, Matrix.mul_nonsing_inv _ hgram, Matrix.one_mul]

/-- **THE SIGNATURE'S DETERMINANT SHADOW.**
`det (BᵀB − 1) = (−1) ^ (slots + rank) · det (BBᵀ − 1)`.  Weinstein–Aronszajn at a shift:
the Gram gap and the moment gap share every nonzero eigenvalue, and the Gram gap carries
`slots − rank` extra copies of `−1`.  At a window of `rank + 1` atoms the sign is exactly
`−1`: ONE extra negative direction. -/
theorem det_gramGap (rectangle : Matrix (Fin rank) slot ℝ) :
    (rectangleᵀ * rectangle - 1).det
      = (-1) ^ (Fintype.card slot + rank) * (rectangle * rectangleᵀ - 1).det := by
  have hleft : rectangleᵀ * rectangle - (1 : Matrix slot slot ℝ)
      = -(1 + rectangleᵀ * (-rectangle)) := by
    rw [Matrix.mul_neg]
    abel
  have hright : (1 : Matrix (Fin rank) (Fin rank) ℝ) + (-rectangle) * rectangleᵀ
      = -(rectangle * rectangleᵀ - 1) := by
    rw [Matrix.neg_mul]
    abel
  rw [hleft, Matrix.det_neg, Matrix.det_one_add_mul_comm rectangleᵀ (-rectangle), hright,
    Matrix.det_neg, Fintype.card_fin, ← mul_assoc, ← pow_add]

omit [Fintype slot] [DecidableEq slot] in
/-- The `(chosen, chosen)` entry of a conjugated matrix is the chosen column's quadratic
form: the bridge from the Gram gap's diagonal to the campaign's pivots. -/
theorem transpose_mul_mul_diag (rectangle : Matrix (Fin rank) slot ℝ)
    (middle : Matrix (Fin rank) (Fin rank) ℝ) (chosen : slot) :
    (rectangleᵀ * middle * rectangle) chosen chosen
      = (fun coord => rectangle coord chosen)
          ⬝ᵥ (middle *ᵥ fun coord => rectangle coord chosen) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### The Gram gap's quadratic form and its two definite pieces -/

/-- The Gram gap's quadratic form is the squared length of the image minus the squared
length of the probe. -/
theorem gramGap_form (rectangle : Matrix (Fin rank) slot ℝ) (probe : slot → ℝ) :
    probe ⬝ᵥ ((rectangleᵀ * rectangle - 1) *ᵥ probe)
      = (rectangle *ᵥ probe) ⬝ᵥ (rectangle *ᵥ probe) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **THE TIMELIKE PIECE.**  On the kernel of `B` the Gram gap is `−‖·‖²`, strictly
negative.  At a window of `rank + 1` atoms the kernel is the line of the circuit
dependency: its single negative direction. -/
theorem gramGap_form_neg_of_kernel (rectangle : Matrix (Fin rank) slot ℝ) {probe : slot → ℝ}
    (hkernel : rectangle *ᵥ probe = 0) (hnonzero : probe ≠ 0) :
    probe ⬝ᵥ ((rectangleᵀ * rectangle - 1) *ᵥ probe) < 0 := by
  rw [gramGap_form, hkernel, dotProduct_zero, zero_sub, neg_lt, neg_zero]
  exact dotProductSelf_pos_of_ne_zero hnonzero

omit [Fintype slot] [DecidableEq slot] in
/-- A positive definite gap makes the shifted square form strictly positive:
`‖(G + 1) z‖² − ⟨z, (G + 1) z⟩ = ‖G z‖² + ⟨z, G z⟩ > 0`. -/
theorem shifted_square_form_pos {gap : Matrix (Fin rank) (Fin rank) ℝ} (hgap : gap.PosDef)
    {probe : Fin rank → ℝ} (hnonzero : probe ≠ 0) :
    0 < ((gap + 1) *ᵥ probe) ⬝ᵥ ((gap + 1) *ᵥ probe) - probe ⬝ᵥ ((gap + 1) *ᵥ probe) := by
  have hshift : (gap + 1) *ᵥ probe = gap *ᵥ probe + probe := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hrayleigh : 0 < probe ⬝ᵥ (gap *ᵥ probe) := by
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hgap).2 hnonzero
    rwa [star_trivial] at hpos
  have hnorm : 0 ≤ (gap *ᵥ probe) ⬝ᵥ (gap *ᵥ probe) := dotProductSelf_nonneg _
  rw [hshift]
  simp only [dotProduct_add, add_dotProduct]
  rw [dotProduct_comm (gap *ᵥ probe) probe]
  linarith

/-- **THE SPACELIKE PIECE.**  On the row space of `B` the Gram gap is positive definite as
soon as the moment gap is: the form pulls back to `‖(S − 1) z‖² + ⟨z, (S − 1) z⟩`. -/
theorem gramGap_form_pos_of_range (rectangle : Matrix (Fin rank) slot ℝ)
    (hmoment : (rectangle * rectangleᵀ - 1).PosDef) {coprobe : Fin rank → ℝ}
    (hnonzero : rectangleᵀ *ᵥ coprobe ≠ 0) :
    0 < (rectangleᵀ *ᵥ coprobe)
      ⬝ᵥ ((rectangleᵀ * rectangle - 1) *ᵥ (rectangleᵀ *ᵥ coprobe)) := by
  have hcoNonzero : coprobe ≠ 0 := by
    intro hzero
    exact hnonzero (by rw [hzero, Matrix.mulVec_zero])
  have hshifted := shifted_square_form_pos hmoment hcoNonzero
  have hunshift : rectangle * rectangleᵀ - 1 + 1 = rectangle * rectangleᵀ := by abel
  rw [hunshift] at hshifted
  have hsquare : (rectangleᵀ *ᵥ coprobe) ⬝ᵥ (rectangleᵀ *ᵥ coprobe)
      = coprobe ⬝ᵥ ((rectangle * rectangleᵀ) *ᵥ coprobe) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      dotProduct_comm]
  rw [gramGap_form, Matrix.mulVec_mulVec, hsquare]
  exact hshifted

omit [DecidableEq slot] in
/-- The kernel of `B` and the row space of `B` are Euclidean-orthogonal, so the two
definite pieces sit on complementary subspaces: the Gram gap has signature
`(rank, slots − rank)` whenever the moment gap is positive definite. -/
theorem kernel_orthogonal_range (rectangle : Matrix (Fin rank) slot ℝ) {probe : slot → ℝ}
    (hkernel : rectangle *ᵥ probe = 0) (coprobe : Fin rank → ℝ) :
    probe ⬝ᵥ (rectangleᵀ *ᵥ coprobe) = 0 := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hkernel, zero_dotProduct]

end Rectangle

/-! ## The window matrix, the window Gram, and the pivot dictionary -/

/-- The `rank × window` matrix whose columns are the window's atoms. -/
def windowMatrix (design : WeightedDesign size rank) (window : Finset (Fin size)) :
    Matrix (Fin rank) {insider // insider ∈ window} ℝ :=
  Matrix.of fun coord insider => design.atom insider.val coord

/-- **THE WINDOW GRAM** `Γ_Q`: the `window × window` matrix of the atoms' inner products.
The moment `S_Q` is the other product of the same rectangle. -/
def windowGram (design : WeightedDesign size rank) (window : Finset (Fin size)) :
    Matrix {insider // insider ∈ window} {insider // insider ∈ window} ℝ :=
  (windowMatrix design window)ᵀ * windowMatrix design window

theorem windowGram_def (design : WeightedDesign size rank) (window : Finset (Fin size)) :
    windowGram design window
      = (windowMatrix design window)ᵀ * windowMatrix design window := rfl

/-- The window's moment is the rectangle times its transpose. -/
theorem windowMatrix_mul_transpose (design : WeightedDesign size rank)
    (window : Finset (Fin size)) :
    windowMatrix design window * (windowMatrix design window)ᵀ = subsetSum design window := by
  ext row col
  simp only [Matrix.mul_apply, Matrix.transpose_apply, windowMatrix, Matrix.of_apply,
    subsetSum, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]
  exact Finset.sum_coe_sort window fun insider =>
    design.atom insider row * design.atom insider col

/-- The Gram's entries are the atoms' inner products. -/
theorem windowGram_apply (design : WeightedDesign size rank) (window : Finset (Fin size))
    (left right : {insider // insider ∈ window}) :
    windowGram design window left right = design.atom left.val ⬝ᵥ design.atom right.val := by
  simp only [windowGram, Matrix.mul_apply, Matrix.transpose_apply, windowMatrix,
    Matrix.of_apply, dotProduct]

/-- **THE GRAM GAP'S DETERMINANT**, at any window size: the sign records how many extra
negative directions the Gram carries over the moment. -/
theorem det_windowGram_sub_one (design : WeightedDesign size rank)
    (window : Finset (Fin size)) :
    (windowGram design window - 1).det
      = (-1) ^ (window.card + rank) * (subsetSum design window - 1).det := by
  rw [windowGram_def, det_gramGap, windowMatrix_mul_transpose, Fintype.card_coe]

/-- **AT A WINDOW OF `rank + 1` ATOMS THE GRAM GAP FLIPS THE SIGN.**  Exactly one extra
negative direction: with a positive definite moment gap the Gram gap has signature
`(rank, 1)` — Lorentzian, with the circuit dependency as its timelike axis. -/
theorem det_windowGram_sub_one_of_card (design : WeightedDesign size rank)
    {window : Finset (Fin size)} (hcard : window.card = rank + 1) :
    (windowGram design window - 1).det = -(subsetSum design window - 1).det := by
  have hexponent : window.card + rank = 2 * rank + 1 := by omega
  rw [det_windowGram_sub_one, hexponent, pow_succ, pow_mul]
  norm_num

theorem isUnit_det_windowGram_sub_one (design : WeightedDesign size rank)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) : IsUnit (windowGram design window - 1).det := by
  rw [det_windowGram_sub_one_of_card design hcard]
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (ne_of_gt hgate.det_pos))

/-- **THE PIVOT DICTIONARY.**  With `R = (Γ_Q − 1)⁻¹`, every insider pivot is
`q_c = 1 + R_cc`.  The tie's whole window-local content, `q_c ≥ 1`, therefore says
exactly that every standard basis vector is NON-TIMELIKE for `R`; the residual says the
ones with nonzero dependency coefficient are exactly NULL. -/
theorem pivot_eq_one_add_windowGramGapInv (design : WeightedDesign size rank)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) (insider : {c // c ∈ window}) :
    pivot design window insider.val
      = 1 + (windowGram design window - 1)⁻¹ insider insider := by
  have hmomentEq := windowMatrix_mul_transpose design window
  have hmomentUnit : IsUnit (windowMatrix design window
      * (windowMatrix design window)ᵀ - 1).det := by
    rw [hmomentEq]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hgate.det_pos)
  have hgramUnit : IsUnit ((windowMatrix design window)ᵀ
      * windowMatrix design window - 1).det := by
    rw [← windowGram_def]
    exact isUnit_det_windowGram_sub_one design hgate hcard
  have hkey := transpose_mul_gapInv_mul_rectangle (windowMatrix design window)
    hmomentUnit hgramUnit
  rw [hmomentEq, ← windowGram_def] at hkey
  have hentry := congrFun (congrFun hkey insider) insider
  rw [transpose_mul_mul_diag] at hentry
  rw [Matrix.add_apply, Matrix.one_apply_eq] at hentry
  rw [pivot_eq_dot]
  exact hentry

/-- **THE TRACE BRIDGE.**  `tr (Γ_Q − 1)⁻¹ = tr (S_Q − 1)⁻¹ − 1` at a window of
`rank + 1` atoms: the scalar the residual is about, transported to the Gram side, where it
is the plain sum of the diagonal the tie signs. -/
theorem trace_windowGramGapInv (design : WeightedDesign size rank)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) :
    Matrix.trace ((windowGram design window - 1)⁻¹)
      = Matrix.trace ((subsetSum design window - 1)⁻¹) - 1 := by
  have hmomentEq := windowMatrix_mul_transpose design window
  have hmomentUnit : IsUnit (windowMatrix design window
      * (windowMatrix design window)ᵀ - 1).det := by
    rw [hmomentEq]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hgate.det_pos)
  have hgramUnit : IsUnit ((windowMatrix design window)ᵀ
      * windowMatrix design window - 1).det := by
    rw [← windowGram_def]
    exact isUnit_det_windowGram_sub_one design hgate hcard
  have hkey := transpose_mul_gapInv_mul_rectangle (windowMatrix design window)
    hmomentUnit hgramUnit
  rw [hmomentEq, ← windowGram_def] at hkey
  have htrace := congrArg Matrix.trace hkey
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hmomentEq,
    Matrix.trace_add, Matrix.trace_one, Fintype.card_coe, hcard] at htrace
  have hsplit : (subsetSum design window - 1)⁻¹ * subsetSum design window
      = (subsetSum design window - 1)⁻¹ * (subsetSum design window - 1)
        + (subsetSum design window - 1)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hsplit, Matrix.trace_add, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (ne_of_gt hgate.det_pos)), Matrix.trace_one,
    Fintype.card_fin] at htrace
  push_cast at htrace ⊢
  linarith

/-! ## What the tie does supply: the added atom over a tight base -/

/-- **THE ADDED ATOM'S PIVOT IS EXACTLY ONE OVER A SINGULAR BASE.**  If a base has singular
gap and one more atom makes the gap positive definite, then the new atom's pivot in the
enlarged window is one on the nose.  In the Gram picture: the new basis vector is NULL.
No tie, no domination, no cardinality — just the base's own singularity. -/
theorem pivot_added_eq_one_of_singular_base (design : WeightedDesign size rank)
    {base : Finset (Fin size)} {added : Fin size} (hnew : added ∉ base)
    (hgate : (subsetSum design (insert added base) - 1).PosDef)
    (hsingular : (subsetSum design base - 1).det = 0) :
    pivot design (insert added base) added = 1 := by
  refine boundary_pivot_eq_one design (insert added base) hgate
    (Finset.mem_insert_self added base) ?_
  rw [Finset.erase_insert hnew]
  exact hsingular

/-- **AT A TIE, EVERY WINDOW BUILT ON A WEAK DOMINATOR HAS PIVOT ONE AT THE ADDED ATOM.**
A tie's dominating `rank`-subset is weakly but not strictly dominating, hence has singular
gap; adding any atom that restores definiteness produces a window whose new atom sits
exactly on the boundary.

This is the residual's own conclusion, verified at ONE coordinate of the window, and it is
not window-local: the dominating subset comes from the tie's existential half, which is
information about the design outside any single window.  It is the shape any proof of the
residual must have — see the wall below. -/
theorem pivot_added_eq_one_of_isTie (design : WeightedDesign size rank) (htie : IsTie design)
    {base : Finset (Fin size)} (hcard : base.card = rank) (hdominates : Dominates design base)
    {added : Fin size} (hnew : added ∉ base)
    (hgate : (subsetSum design (insert added base) - 1).PosDef) :
    pivot design (insert added base) added = 1 := by
  refine pivot_added_eq_one_of_singular_base design hnew hgate ?_
  by_contra hnonzero
  exact htie.2 base hcard (hdominates.posDef_iff_det_ne_zero.mpr hnonzero)

/-- The Lorentzian reading of the previous theorem: over a tie's weak dominator the added
atom's basis vector is exactly NULL for the window's Gram gap inverse. -/
theorem windowGramGapInv_diag_added_eq_zero_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {base : Finset (Fin size)} (hcard : base.card = rank)
    (hdominates : Dominates design base) {added : Fin size} (hnew : added ∉ base)
    (hgate : (subsetSum design (insert added base) - 1).PosDef) :
    (windowGram design (insert added base) - 1)⁻¹
        ⟨added, Finset.mem_insert_self added base⟩
        ⟨added, Finset.mem_insert_self added base⟩ = 0 := by
  have hcardWindow : (insert added base).card = rank + 1 := by
    rw [Finset.card_insert_of_notMem hnew, hcard]
  have hdictionary := pivot_eq_one_add_windowGramGapInv design hgate hcardWindow
    ⟨added, Finset.mem_insert_self added base⟩
  have hone := pivot_added_eq_one_of_isTie design htie hcard hdominates hnew hgate
  rw [hone] at hdictionary
  linarith

/-! ## The residual, restated as a nullity -/

/-- At a tie no insider pivot of a critical window drops below one: a pivot below one is a
strictly dominating erasure, and a tie has none.  In the Gram picture: every standard basis
vector is NON-TIMELIKE. -/
theorem one_le_pivot_of_tie (design : WeightedDesign size rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) {dropped : Fin size} (hmem : dropped ∈ window) :
    1 ≤ pivot design window dropped := by
  by_contra hbelow
  rw [not_le] at hbelow
  refine htie.2 (window.erase dropped) ?_
    ((erase_strictDominates_iff_pivot_lt_one design window hgate hmem).mpr hbelow)
  rw [Finset.card_erase_of_mem hmem, hcard]
  omega

/-- **THE RESIDUAL IS A NULLITY STATEMENT.**  At a tie, a critical window's inverse moment
gap has trace one exactly when EVERY standard basis vector is null for the window's Gram
gap inverse — one scalar equation per window, restated as `rank + 1` scalar equations that
the tie already pins from one side.

Against `no_window_local_trace_one` below, this is the sharp form of what is left: the
Lorentzian data says every `e_c` is non-timelike and the dependency `alpha` is timelike, and
the residual asks that every `e_c` with `alpha_c` nonzero be exactly null.  The witness
below satisfies the first and violates the second. -/
theorem trace_eq_one_iff_forall_null (design : WeightedDesign size rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) :
    Matrix.trace ((subsetSum design window - 1)⁻¹) = 1
      ↔ ∀ insider : {c // c ∈ window},
          (windowGram design window - 1)⁻¹ insider insider = 0 := by
  have hbridge := trace_windowGramGapInv design hgate hcard
  have hdiagSum : Matrix.trace ((windowGram design window - 1)⁻¹)
      = ∑ insider : {c // c ∈ window}, (windowGram design window - 1)⁻¹ insider insider := rfl
  have hnonneg : ∀ insider : {c // c ∈ window},
      0 ≤ (windowGram design window - 1)⁻¹ insider insider := by
    intro insider
    have hdictionary := pivot_eq_one_add_windowGramGapInv design hgate hcard insider
    have hlower := one_le_pivot_of_tie design htie hgate hcard insider.2
    linarith
  constructor
  · intro htrace insider
    have hzero : ∑ other : {c // c ∈ window},
        (windowGram design window - 1)⁻¹ other other = 0 := by
      rw [← hdiagSum, hbridge, htrace]
      ring
    exact (Finset.sum_eq_zero_iff_of_nonneg fun other _ => hnonneg other).mp hzero insider
      (Finset.mem_univ insider)
  · intro hnull
    have hzero : Matrix.trace ((windowGram design window - 1)⁻¹) = 0 := by
      rw [hdiagSum]
      exact Finset.sum_eq_zero fun insider _ => hnull insider
    linarith

/-! ## The wall: window-local data does not decide the trace -/

section Wall

/-- A scalar multiple of the identity, written as a diagonal. -/
theorem smul_one_eq_diagonal (dimension : ℕ) (scalar : ℝ) :
    scalar • (1 : Matrix (Fin dimension) (Fin dimension) ℝ)
      = Matrix.diagonal (fun _ : Fin dimension => scalar) := by
  ext rowIndex colIndex
  simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hdiagonal : rowIndex = colIndex <;> simp [hdiagonal]

/-- Erasing an insider subtracts its atom from the moment. -/
theorem subsetSum_erase (design : WeightedDesign size rank) {window : Finset (Fin size)}
    {dropped : Fin size} (hmem : dropped ∈ window) :
    subsetSum design (window.erase dropped)
      = subsetSum design window - atomMatrix (design.atom dropped) := by
  have hsum := Finset.sum_erase_add window (fun c => atomMatrix (design.atom c)) hmem
  rw [subsetSum, subsetSum, ← hsum]
  abel

/-! ### The tetrahedron ray inside a genuine `(7,3)` design

Four tetrahedron directions at a common scale, plus three doubled coordinate axes carrying
the Parseval remainder.  At `scale = 1` the four are the `(4,3)` TIE; below one they are a
circuit window with every window-local shadow of a tie intact and a trace above one. -/

/-- The atoms: four scaled tetrahedron directions, then three doubled axes. -/
noncomputable def rayAtom (scale : ℝ) : Fin 7 → (Fin 3 → ℝ)
  | 0 => ![scale, scale, scale]
  | 1 => ![scale, -scale, -scale]
  | 2 => ![-scale, scale, -scale]
  | 3 => ![-scale, -scale, scale]
  | 4 => ![2, 0, 0]
  | 5 => ![0, 2, 0]
  | 6 => ![0, 0, 2]

/-- The weights forced by Parseval and by summing to one: the tetrahedron carries
`4 scale² / (16 − 12 scale²)` of the identity and the axes the rest. -/
noncomputable def rayWeight (scale : ℝ) (atomIndex : Fin 7) : ℝ :=
  if atomIndex.val < 4 then (16 - 12 * scale ^ 2)⁻¹
  else 4 * (1 - scale ^ 2) / (16 - 12 * scale ^ 2)

section RayFamily

variable {scale : ℝ}

theorem ray_denom_pos (hlow : 1/2 < scale) (hhigh : scale < 1) : 0 < 16 - 12 * scale ^ 2 := by
  nlinarith [mul_pos (sub_pos.mpr hhigh) (show (0:ℝ) < 1 + scale by linarith)]

/-- The window's gap scalar `4 scale² − 1` is positive above half scale. -/
theorem ray_gap_pos (hlow : 1/2 < scale) : 0 < 4 * scale ^ 2 - 1 := by nlinarith

theorem ray_moment_pos (hlow : 1/2 < scale) : 0 < 4 * scale ^ 2 := by nlinarith

theorem ray_weight_pos (hlow : 1/2 < scale) (hhigh : scale < 1) (atomIndex : Fin 7) :
    0 < rayWeight scale atomIndex := by
  have hdenom := ray_denom_pos hlow hhigh
  have hslack : 0 < 1 - scale ^ 2 := by nlinarith
  unfold rayWeight
  split_ifs
  · exact inv_pos.mpr hdenom
  · exact div_pos (by linarith) hdenom

theorem ray_weight_sum (hlow : 1/2 < scale) (hhigh : scale < 1) :
    ∑ atomIndex : Fin 7, rayWeight scale atomIndex = 1 := by
  have hdenom := ray_denom_pos hlow hhigh
  simp only [rayWeight, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  field_simp
  ring

theorem ray_parseval (hlow : 1/2 < scale) (hhigh : scale < 1) :
    ∑ atomIndex : Fin 7, rayWeight scale atomIndex • atomMatrix (rayAtom scale atomIndex)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hdenom := ray_denom_pos hlow hhigh
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [rayAtom, rayWeight, atomMatrix, Fin.sum_univ_succ] <;> field_simp <;> ring

/-- **A GENUINE `(7,3)` DESIGN** for every scale strictly between a half and one. -/
noncomputable def rayDesign (hlow : 1/2 < scale) (hhigh : scale < 1) : WeightedDesign 7 3 where
  atom := rayAtom scale
  weight := rayWeight scale
  weight_pos := ray_weight_pos hlow hhigh
  weight_sum_one := ray_weight_sum hlow hhigh
  isParseval := ray_parseval hlow hhigh

/-- The window: the four scaled tetrahedron directions. -/
def rayWindow : Finset (Fin 7) := {0, 1, 2, 3}

theorem rayWindow_card : rayWindow.card = 3 + 1 := by decide

theorem rayWindow_dotSelf (hlow : 1/2 < scale) (hhigh : scale < 1) {dropped : Fin 7}
    (hmem : dropped ∈ rayWindow) :
    (rayDesign hlow hhigh).atom dropped ⬝ᵥ (rayDesign hlow hhigh).atom dropped
      = 3 * scale ^ 2 := by
  fin_cases hmem <;> simp [rayDesign, rayAtom, dotProduct, Fin.sum_univ_succ] <;> ring

theorem rayWindow_leverage (hlow : 1/2 < scale) (hhigh : scale < 1) {dropped : Fin 7}
    (hmem : dropped ∈ rayWindow) :
    leverageOf ((rayDesign hlow hhigh).atom dropped) = 3 * scale ^ 2 := by
  fin_cases hmem <;> simp [rayDesign, rayAtom, leverageOf, Fin.sum_univ_succ] <;> ring

/-- The window's moment is `(4 scale²) · 1`: the tetrahedron's own `4 · 1` rescaled. -/
theorem rayWindow_subsetSum (hlow : 1/2 < scale) (hhigh : scale < 1) :
    subsetSum (rayDesign hlow hhigh) rayWindow
      = (4 * scale ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [subsetSum, show rayWindow = insert 0 (insert 1 (insert 2 {3})) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [rayDesign, rayAtom, atomMatrix] <;> ring

theorem rayWindow_gap (hlow : 1/2 < scale) (hhigh : scale < 1) :
    subsetSum (rayDesign hlow hhigh) rayWindow - 1
      = (4 * scale ^ 2 - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [rayWindow_subsetSum]
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hdiagonal : rowIndex = colIndex
  · simp [hdiagonal]
  · simp [hdiagonal]

theorem rayWindow_gate (hlow : 1/2 < scale) (hhigh : scale < 1) :
    (subsetSum (rayDesign hlow hhigh) rayWindow - 1).PosDef := by
  rw [rayWindow_gap, smul_one_eq_diagonal]
  exact Matrix.PosDef.diagonal fun _ => ray_gap_pos hlow

theorem rayWindow_gap_inv (hlow : 1/2 < scale) (hhigh : scale < 1) :
    (subsetSum (rayDesign hlow hhigh) rayWindow - 1)⁻¹
      = (4 * scale ^ 2 - 1)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [rayWindow_gap]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
    inv_mul_cancel₀ (ne_of_gt (ray_gap_pos hlow)), one_smul]

/-- **THE TRACE ALONG THE RAY IS `3 / (4 scale² − 1)`** — one only at `scale = 1`, which is
exactly the `(4,3)` tetrahedron tie, and strictly above one everywhere below it. -/
theorem rayWindow_trace_inverse (hlow : 1/2 < scale) (hhigh : scale < 1) :
    Matrix.trace ((subsetSum (rayDesign hlow hhigh) rayWindow - 1)⁻¹)
      = 3 / (4 * scale ^ 2 - 1) := by
  rw [rayWindow_gap_inv, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

theorem rayWindow_trace_gt_one (hlow : 1/2 < scale) (hhigh : scale < 1) :
    1 < Matrix.trace ((subsetSum (rayDesign hlow hhigh) rayWindow - 1)⁻¹) := by
  rw [rayWindow_trace_inverse, lt_div_iff₀ (ray_gap_pos hlow)]
  nlinarith

/-- **EVERY INSIDER PIVOT IS `3 scale² / (4 scale² − 1)`, AT LEAST ONE** — the window
satisfies everything a tie can say about it from the inside, at every scale below one. -/
theorem rayWindow_pivot (hlow : 1/2 < scale) (hhigh : scale < 1) {dropped : Fin 7}
    (hmem : dropped ∈ rayWindow) :
    pivot (rayDesign hlow hhigh) rayWindow dropped = 3 * scale ^ 2 / (4 * scale ^ 2 - 1) := by
  rw [pivot, rayWindow_gap_inv, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    trace_atomMatrix, rayWindow_leverage hlow hhigh hmem, smul_eq_mul]
  field_simp

theorem rayWindow_one_le_pivot (hlow : 1/2 < scale) (hhigh : scale < 1) {dropped : Fin 7}
    (hmem : dropped ∈ rayWindow) : 1 ≤ pivot (rayDesign hlow hhigh) rayWindow dropped := by
  rw [rayWindow_pivot hlow hhigh hmem, le_div_iff₀ (ray_gap_pos hlow)]
  nlinarith

/-- **THE WINDOW IS A CIRCUIT**: each erasure's moment is `(4 scale²) · 1 − g gᵀ` with
`‖g‖² = 3 scale²`, whose base pivot is `3/4` at every scale, so the rank-one Schur step
leaves it positive definite.  Every erasure is an independent triple, the dependency has
full support, and the residual predicts trace one. -/
theorem rayWindow_isCircuit (hlow : 1/2 < scale) (hhigh : scale < 1) {dropped : Fin 7}
    (hmem : dropped ∈ rayWindow) :
    0 < (subsetSum (rayDesign hlow hhigh) (rayWindow.erase dropped)).det := by
  have hmomentPos := ray_moment_pos hlow
  have hbaseDiag : ((4 * scale ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
    rw [smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => hmomentPos
  have hbaseInv : ((4 * scale ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹
      = (4 * scale ^ 2)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hmomentPos), one_smul]
  rw [subsetSum_erase _ hmem, rayWindow_subsetSum, atomMatrix]
  refine Matrix.PosDef.det_pos ?_
  refine (posDef_sub_vecMulVec_iff _ hbaseDiag _).mpr ?_
  rw [hbaseInv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    rayWindow_dotSelf hlow hhigh hmem, smul_eq_mul]
  rw [inv_mul_eq_div, div_lt_one hmomentPos]
  nlinarith

/-- The witness is NOT a tie: its three doubled axes dominate strictly.  It could not be —
a window-local witness that were a tie would refute the residual outright, and the point is
that the residual survives every window-local test. -/
theorem rayDesign_not_isTie (hlow : 1/2 < scale) (hhigh : scale < 1) :
    ¬ IsTie (rayDesign hlow hhigh) := by
  intro htie
  refine htie.2 {4, 5, 6} (by decide) ?_
  have hmoment : subsetSum (rayDesign hlow hhigh) {4, 5, 6} - 1
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [subsetSum, show ({4, 5, 6} : Finset (Fin 7)) = insert 4 (insert 5 {6}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [rayDesign, rayAtom, atomMatrix] <;> norm_num
  rw [hmoment, smul_one_eq_diagonal]
  exact Matrix.PosDef.diagonal fun _ => by norm_num

end RayFamily

/-- **THE WALL.  NO WINDOW-LOCAL THEOREM PRODUCES THE TRACE-ONE EQUATION.**

The four hypotheses below are exactly the data a Lorentzian argument on one window has: the
gate, so the Gram gap has signature `(rank, 1)`; the critical cardinality; the circuit
condition, so the timelike dependency has full support; and every insider pivot at least
one, so every standard basis vector is non-timelike — the tie's ENTIRE window-local content
(a window of `rank + 1` atoms has exactly its `rank + 1` erasures as `rank`-subsets, and the
tie says nothing else about them).  The tetrahedron ray inside a genuine `(7,3)` design
satisfies all four at every scale in `(1/2, 1)` and has trace `3 / (4 scale² − 1) > 1`.

So the reverse inequality cannot come from the window.  Two further readings:

* The failure is a NEIGHBOURHOOD, not a point.  The counterexample family runs right up to
  the tetrahedron tie at `scale = 1`, where the trace becomes one; so no continuity or
  perturbation argument off the tie recovers the equation either — the trace-one locus on
  this ray is the single tie point, approached from a region where every window-local
  hypothesis already holds.
* The Lorentzian geometry is real — `gramGap_form_neg_of_kernel` and
  `gramGap_form_pos_of_range` pin the signature at every rank — but non-timelike plus a
  full-support timelike axis is NOT a rigidity: spacelike basis vectors carry nonzero
  dependency coefficients as happily as null ones.  What the geometry does prove is the
  CONVERSE, already shipped: a causal basis vector forces a nonzero coefficient, which is
  "a weak dominator is a basis".

This is a different mechanism from the sibling lane's wall.  That one surveys the outside
sources of a reverse inequality and finds them all same-signed; this one is a model, and it
rules out arguments of every shape whose hypotheses are confined to the window's atom
geometry.  The tie must be consumed through atoms the window does not contain — as
`pivot_added_eq_one_of_isTie` above does, and as any complete proof must. -/
theorem no_window_local_trace_one :
    ¬ ∀ (ambient : ℕ) (design : WeightedDesign ambient 3) (window : Finset (Fin ambient)),
        (subsetSum design window - 1).PosDef →
        window.card = 3 + 1 →
        (∀ dropped ∈ window, 0 < (subsetSum design (window.erase dropped)).det) →
        (∀ insider ∈ window, 1 ≤ pivot design window insider) →
        Matrix.trace ((subsetSum design window - 1)⁻¹) = 1 := by
  intro hclaim
  have hlow : (1:ℝ)/2 < 3/4 := by norm_num
  have hhigh : (3:ℝ)/4 < 1 := by norm_num
  have hforced := hclaim 7 (rayDesign hlow hhigh) rayWindow (rayWindow_gate hlow hhigh)
    rayWindow_card (fun _ hmem => rayWindow_isCircuit hlow hhigh hmem)
    (fun _ hmem => rayWindow_one_le_pivot hlow hhigh hmem)
  have hstrict := rayWindow_trace_gt_one hlow hhigh
  rw [hforced] at hstrict
  exact absurd hstrict (lt_irrefl 1)

end Wall

end Gtz
