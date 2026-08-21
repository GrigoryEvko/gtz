/-
# The corner axis law: a corank-two dominator prices every outside pair

At a corank-two corner `S_C - 1 = lam·u uᵀ` the three inside atoms are an
UNWEIGHTED tight frame stretched along the axis, so every aggregate over `C` is
computable with NO weights.  This module spends that on the third Sylvester
minor and lands a scalar law that the campaign's weighted moment cannot reach.

## 1. The identity

Fix a pair of labels `d`, `e` OUTSIDE the corner.  Write `q := pairGapMinor g_d g_e`
and `L := l_d + l_e - 2`.  Then, with no hypothesis beyond the corner,

  `∑_{a ∈ C} tripleGapDet g_d g_e g_a
      = (lam - 2)·q - L + lam·tripleGapDet g_d g_e u`

(`Gtz.corner_sum_tripleGapDet_outsidePair`).  The axis enters as a THIRD ATOM of
unit leverage, so the whole corner correction is one more triple minor, read at
`u` itself.  Three steps carry it: the rank-one determinant update prices each
summand as an adjugate reading of the pair gap
(`Gtz.adjugate_pairGapMatrix_reading`), the corner resolves any form
(`Gtz.corner_form_reading_total`), and the adjugate trace of a pair gap is the
pair minor less the leverage excess (`Gtz.trace_adjugate_pairGapMatrix`).

## 2. The law

At a TIE with a heavy admissible pair the tree's gate says every third minor
through that pair is nonpositive (`Gtz.tripleGapDet_nonpos_of_isTie`), so the
corner total is nonpositive and the identity reads

  `(lam - 2)·q + lam·tripleGapDet g_d g_e u  ≤  L`

(`Gtz.corner_axisPair_law_of_isTie`).  The axis minor is NONPOSITIVE at an
admissible heavy pair (`Gtz.tripleGapDet_axisProbe_nonpos`), because it is minus
the adjugate form of the pair gap read at the two axis readings.  So with
`T := -tripleGapDet g_d g_e u ≥ 0` the law is

  `(lam - 2)·q  ≤  lam·T + L` .

**It bites exactly when `lam > 2`.**  Below `lam = 2` the left side is
nonpositive and the law is free.  A pair blind to the axis has `T = 0` and pays
the sharpest form, `(lam - 2)·q ≤ L` (`Gtz.corner_blindPair_law_of_isTie`), which
caps the corner eigenvalue outright: `lam ≤ 2 + L / q`.

## 3. Why this is not the weighted moment

`Gtz.sum_outside_weight_mul_tripleGapDet_corner` is a NO-GO: at a corner the
WEIGHTED outside total of the same minor is an identity, both sides agreeing in
sign.  The total above is the UNWEIGHTED INSIDE one, and the corner supplies it
in closed form for exactly the same reason the weighted one is vacuous — the
inside triple is a tight frame.  The two aggregates are independent: the weighted
one reproduces the landed area ceiling `Gtz.crossNormSq_le_of_isTie`, the
unweighted one does not.

[MEASURED, in an exact eleven-parameter corner chart in which Parseval and
`S_C - 1 = lam·u uᵀ` both hold by construction.  The chart writes the design in
the basis of the inside triple: the inside atoms are the coordinate vectors, the
inside Gram is `1 + lam v vᵀ`, and Parseval is
`∑_d t_d x_d x_dᵀ = (1 + lam v vᵀ)⁻¹ - diag(t_C)`.  Parseval residual `1e-15` and
corner corank two to `1e-16` at every sample.  The identity above was checked in
C and again in an independent Julia implementation on the near-optimal
configurations of three weight floors, at all three outside pairs: relative error
between `0` and `7e-12`.  The law FIRES — it certifies "no tie" — at two of those
three configurations, at the pair whose two atoms carry the smallest weights.

The same chart says the corner stratum of `(6,3)` carries no all-heavy tie, but
with NO uniform margin: minimising `∑_T max(lambda_min(S_T - 1), 0)^2` under a
hard weight floor `tau` gives largest strict eigenvalue `2.6e-3` at `tau = 0.05`,
`3.7e-4` at `0.02`, `3.0e-5` at `0.005` and `5.3e-6` at `0.0012`.  The degenerate
direction is always the same: two OUTSIDE atoms run to weight `tau` and leverage
`0.66/tau`, so their shares stay near `2/3` and the design leaves the open
simplex.  At every such near-optimum the corner eigenvalue sits in `2.1 ≤ lam ≤ 2.8`
— against the threshold `lam = 2` at which this law starts to bite.]
-/
import Gtz.Wave.PlaneShadowPairBridge
import Gtz.Wave.CellHDowndateLaws
import Gtz.Design.PlaneBranchComplementSelector

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1 — the pair gap and its adjugate, in Sylvester vocabulary

Four polynomial identities on three vectors of `R^3`.  No design, no hypothesis. -/

/-- The ambient gap of a PAIR of vectors: `g_a g_aᵀ + g_b g_bᵀ - 1`. -/
noncomputable def pairGapMatrix (a b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix a + atomMatrix b - 1

/-- **THE PAIR GAP DETERMINANT IS MINUS THE PAIR MINOR.**  A pair gap always has
one eigenvalue `-1`, and the other two multiply to the pair minor. -/
theorem det_pairGapMatrix (a b : Fin 3 → ℝ) :
    (pairGapMatrix a b).det = -pairGapMinor a b := by
  rw [pairGapMatrix, Matrix.det_fin_three, pairGapMinor]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- **THE TRIPLE GAP DETERMINANT, ON RAW VECTORS.**  The tree carries this for
three atoms of a design (`Gtz.det_subsetSum_tripleGap_eq_tripleGapDet`); the axis
of a corner is not an atom, so the vector form is what this module needs. -/
theorem det_tripleAtomGap (a b c : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1).det = tripleGapDet a b c := by
  rw [Matrix.det_fin_three, tripleGapDet]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- **THE ADJUGATE READING OF A PAIR GAP IS THE TRIPLE MINOR, SHIFTED.**  The
rank-one determinant update prices a third vector by the adjugate form, and the
two determinants are Sylvester minors. -/
theorem adjugate_pairGapMatrix_reading (a b c : Fin 3 → ℝ) :
    c ⬝ᵥ ((pairGapMatrix a b).adjugate *ᵥ c) = tripleGapDet a b c + pairGapMinor a b := by
  have hupdate := det_add_atomMatrix_fin_three (pairGapMatrix a b) c
  have hshape : pairGapMatrix a b + atomMatrix c
      = atomMatrix a + atomMatrix b + atomMatrix c - 1 := by
    rw [pairGapMatrix]; abel
  rw [hshape, det_tripleAtomGap, det_pairGapMatrix] at hupdate
  linarith

/-- **THE ADJUGATE TRACE AT SIZE THREE.**  For every `3 x 3` form the adjugate
trace is the second coefficient of the characteristic polynomial, read at one. -/
theorem trace_adjugate_eq_shifted_det_fin_three (form : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace form.adjugate = (form + 1).det - form.det - Matrix.trace form - 1 := by
  simp only [Matrix.trace_fin_three, Matrix.adjugate_fin_three, Matrix.det_fin_three,
    Matrix.add_apply, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- A pair of rank-one forms is singular at rank three. -/
theorem det_atomMatrix_add_atomMatrix (a b : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b).det = 0 := by
  simp only [Matrix.det_fin_three, atomMatrix, Matrix.add_apply, Matrix.vecMulVec_apply]
  ring

/-- The trace of a pair gap is the leverage total less the rank. -/
theorem trace_pairGapMatrix (a b : Fin 3 → ℝ) :
    Matrix.trace (pairGapMatrix a b) = leverageOf a + leverageOf b - 3 := by
  rw [pairGapMatrix, Matrix.trace_fin_three]
  simp only [Matrix.sub_apply, Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue]
  norm_num [Fin.ext_iff]
  ring

/-- **THE ADJUGATE TRACE OF A PAIR GAP.**  The pair minor less the leverage
excess.  This is the term the corner identity spends. -/
theorem trace_adjugate_pairGapMatrix (a b : Fin 3 → ℝ) :
    Matrix.trace (pairGapMatrix a b).adjugate
      = pairGapMinor a b - leverageOf a - leverageOf b + 2 := by
  have hshift : pairGapMatrix a b + 1 = atomMatrix a + atomMatrix b := by
    rw [pairGapMatrix]; abel
  rw [trace_adjugate_eq_shifted_det_fin_three, hshift, det_atomMatrix_add_atomMatrix, det_pairGapMatrix,
    trace_pairGapMatrix]
  ring

/-! ## Part 2 — the axis minor, and its sign at an admissible heavy pair -/

/-- **THE AXIS MINOR.**  A unit third vector kills the leading term of the triple
minor, and what is left is minus the adjugate form of the pair's `2 x 2` gap read
at the two axis readings. -/
theorem tripleGapDet_axisProbe (a b u : Fin 3 → ℝ) (hunit : u ⬝ᵥ u = 1) :
    tripleGapDet a b u
      = 2 * (a ⬝ᵥ b) * ((a ⬝ᵥ u) * (b ⬝ᵥ u))
        - (leverageOf a - 1) * (b ⬝ᵥ u) ^ 2 - (leverageOf b - 1) * (a ⬝ᵥ u) ^ 2 := by
  have hlev : leverageOf u = 1 := by rw [leverageOf_eq_dotProduct]; exact hunit
  rw [tripleGapDet, hlev]
  ring

/-- **THE AXIS MINOR IS NONPOSITIVE AT AN ADMISSIBLE HEAVY PAIR.**  The adjugate
of a positive definite `2 x 2` gap is positive definite, so the axis form it reads
is nonnegative and the minor is its negative.  Cleared of denominators by the
leverage excess of the heavy atom. -/
theorem tripleGapDet_axisProbe_nonpos {a b : Fin 3 → ℝ} (u : Fin 3 → ℝ)
    (hunit : u ⬝ᵥ u = 1) (hheavy : 1 < leverageOf a) (hadmissible : 0 < pairGapMinor a b) :
    tripleGapDet a b u ≤ 0 := by
  have hexcess : 0 < leverageOf a - 1 := by linarith
  have hminor : (a ⬝ᵥ b) ^ 2 ≤ (leverageOf a - 1) * (leverageOf b - 1) := by
    rw [pairGapMinor] at hadmissible; linarith
  rw [tripleGapDet_axisProbe a b u hunit]
  have hclear : (leverageOf a - 1) * (2 * (a ⬝ᵥ b) * ((a ⬝ᵥ u) * (b ⬝ᵥ u))
        - (leverageOf a - 1) * (b ⬝ᵥ u) ^ 2 - (leverageOf b - 1) * (a ⬝ᵥ u) ^ 2)
      = -(((leverageOf a - 1) * (b ⬝ᵥ u) - (a ⬝ᵥ b) * (a ⬝ᵥ u)) ^ 2)
        - ((leverageOf a - 1) * (leverageOf b - 1) - (a ⬝ᵥ b) ^ 2) * (a ⬝ᵥ u) ^ 2 := by
    ring
  nlinarith [hclear, sq_nonneg ((leverageOf a - 1) * (b ⬝ᵥ u) - (a ⬝ᵥ b) * (a ⬝ᵥ u)),
    mul_nonneg (sub_nonneg.mpr hminor) (sq_nonneg (a ⬝ᵥ u)), hexcess]

/-! ## Part 3 — the corner resolves an arbitrary form -/

/-- **THE CORNER READS ANY FORM.**  The three inside atoms of a corank-two corner
total, at any `3 x 3` form, that form's trace plus `lam` times its axis reading.
The tree carries the `A⁻¹` instance (`Gtz.corner_inverse_reading_total`); the
adjugate of a pair gap is not an inverse — a pair gap is indefinite and its
adjugate is the object with no denominator — so the general form is what this
module needs. -/
theorem corner_form_reading_total (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ c ∈ C, D.atom c ⬝ᵥ (A *ᵥ D.atom c) = Matrix.trace A + lam * (u ⬝ᵥ (A *ᵥ u)) := by
  have hC : subsetSum D C = 1 + lam • atomMatrix u := by rw [← hgap]; abel
  have hsum : ∑ c ∈ C, D.atom c ⬝ᵥ (A *ᵥ D.atom c) = Matrix.trace (A * subsetSum D C) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun c _ =>
      dotProduct_mulVec_eq_trace_mul_atomMatrix A (D.atom c)
  have haxis : Matrix.trace (A * atomMatrix u) = u ⬝ᵥ (A *ᵥ u) :=
    (dotProduct_mulVec_eq_trace_mul_atomMatrix A u).symm
  rw [hsum, hC, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Matrix.mul_smul,
    Matrix.trace_smul, haxis, smul_eq_mul]

/-! ## Part 4 — the corner axis identity, and the law -/

/-- **THE CORNER AXIS IDENTITY.**  The unweighted total of the third Sylvester
minor over the inside triple, through any pair, in closed form.  The corner
correction is ONE MORE triple minor, read at the axis.  No tie, no heaviness, no
admissibility: only the corner and `C.card = 3`. -/
theorem corner_sum_tripleGapDet_outsidePair (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (d e : Fin m) :
    ∑ a ∈ C, tripleGapDet (D.atom d) (D.atom e) (D.atom a)
      = (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
        - (leverageOf (D.atom d) + leverageOf (D.atom e) - 2)
        + lam * tripleGapDet (D.atom d) (D.atom e) u := by
  have hterm : ∀ a ∈ C, tripleGapDet (D.atom d) (D.atom e) (D.atom a)
      = D.atom a ⬝ᵥ ((pairGapMatrix (D.atom d) (D.atom e)).adjugate *ᵥ D.atom a)
        - pairGapMinor (D.atom d) (D.atom e) := by
    intro a _
    rw [adjugate_pairGapMatrix_reading]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const, hcard,
    corner_form_reading_total D hgap, trace_adjugate_pairGapMatrix,
    adjugate_pairGapMatrix_reading]
  ring

/-- **THE CORNER AXIS LAW.**  A tie whose corner is priced against a heavy
admissible pair OUTSIDE the corner pays one scalar inequality.  Every summand of
the corner total is nonpositive by the tree's gate, so the identity of
`Gtz.corner_sum_tripleGapDet_outsidePair` becomes a bound on the corner
eigenvalue. -/
theorem corner_axisPair_law_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hde : d ≠ e) (hd : d ∉ C) (he : e ∉ C)
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e)) :
    (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
        + lam * tripleGapDet (D.atom d) (D.atom e) u
      ≤ leverageOf (D.atom d) + leverageOf (D.atom e) - 2 := by
  have hnonpos : ∑ a ∈ C, tripleGapDet (D.atom d) (D.atom e) (D.atom a) ≤ 0 := by
    refine Finset.sum_nonpos fun a ha => ?_
    exact tripleGapDet_nonpos_of_isTie D htie hde (fun hcon => hd (hcon ▸ ha))
      (fun hcon => he (hcon ▸ ha)) hheavy hadmissible
  rw [corner_sum_tripleGapDet_outsidePair D hcard hgap d e] at hnonpos
  linarith

/-- **THE LAW BITES ONLY ABOVE `lam = 2`.**  With the axis minor's sign spent, the
law says the corner eigenvalue excess above two is paid for by the axis minor and
the leverage excess of the pair. -/
theorem corner_axisPair_excess_le_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hde : d ≠ e) (hd : d ∉ C) (he : e ∉ C)
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e)) :
    (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
      ≤ lam * (-tripleGapDet (D.atom d) (D.atom e) u)
        + (leverageOf (D.atom d) + leverageOf (D.atom e) - 2) := by
  have hlaw := corner_axisPair_law_of_isTie D htie hcard hgap hde hd he hheavy hadmissible
  linarith

/-- **A PAIR BLIND TO THE AXIS PAYS THE SHARPEST FORM.**  When both atoms of the
pair read the axis at zero the axis minor vanishes and the law caps the corner
eigenvalue outright. -/
theorem corner_blindPair_law_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hde : d ≠ e) (hd : d ∉ C) (he : e ∉ C)
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e))
    (hdaxis : D.atom d ⬝ᵥ u = 0) (heaxis : D.atom e ⬝ᵥ u = 0) :
    (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
      ≤ leverageOf (D.atom d) + leverageOf (D.atom e) - 2 := by
  have hlaw := corner_axisPair_law_of_isTie D htie hcard hgap hde hd he hheavy hadmissible
  have haxis : tripleGapDet (D.atom d) (D.atom e) u = 0 := by
    rw [tripleGapDet_axisProbe (D.atom d) (D.atom e) u hunit, hdaxis, heaxis]
    ring
  rw [haxis, mul_zero, add_zero] at hlaw
  exact hlaw

/-- **THE CORNER EIGENVALUE CAP.**  Divided form of the blind-pair law. -/
theorem corner_lam_le_of_blindPair (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hde : d ≠ e) (hd : d ∉ C) (he : e ∉ C)
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e))
    (hdaxis : D.atom d ⬝ᵥ u = 0) (heaxis : D.atom e ⬝ᵥ u = 0) :
    lam ≤ 2 + (leverageOf (D.atom d) + leverageOf (D.atom e) - 2)
        / pairGapMinor (D.atom d) (D.atom e) := by
  have hlaw := corner_blindPair_law_of_isTie D htie hcard hunit hgap hde hd he hheavy
    hadmissible hdaxis heaxis
  have hpos : 0 < pairGapMinor (D.atom d) (D.atom e) := hadmissible
  have hstep : lam - 2 ≤ (leverageOf (D.atom d) + leverageOf (D.atom e) - 2)
      / pairGapMinor (D.atom d) (D.atom e) := by
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-! ## Part 5 — the `(6,3)` reading

At `(6,3)` the complement of a corner is again a triple, so the pairs the law can
price are exactly the three pairs of the complement.  Everything below is the law
with that census spelled out. -/

/-- Membership in the complement is non-membership in the corner. -/
theorem notMem_of_mem_compl {C : Finset (Fin m)} {d : Fin m}
    (hd : d ∈ (Cᶜ : Finset (Fin m))) : d ∉ C := Finset.mem_compl.mp hd

/-- **THE `(6,3)` CORNER AXIS LAW.**  Every admissible heavy pair of the
complement of a corank-two corner pays the law. -/
theorem corner_axisPair_law_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {C : Finset (Fin 6)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin 6} (hde : d ≠ e) (hd : d ∈ (Cᶜ : Finset (Fin 6)))
    (he : e ∈ (Cᶜ : Finset (Fin 6)))
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e)) :
    (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
        + lam * tripleGapDet (D.atom d) (D.atom e) u
      ≤ leverageOf (D.atom d) + leverageOf (D.atom e) - 2 :=
  corner_axisPair_law_of_isTie D htie hcard hgap hde (notMem_of_mem_compl hd)
    (notMem_of_mem_compl he) hheavy hadmissible

/-- **THE CORNER TOTAL IS THE OBSTRUCTION.**  Contrapositive form: a corner whose
inside total through some outside pair is STRICTLY POSITIVE carries a strictly
dominating triple, so it is not a tie.  This is the shape a search reports. -/
theorem not_isTie_of_corner_sum_pos (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {d e : Fin m} (hde : d ≠ e) (hd : d ∉ C) (he : e ∉ C)
    (hheavy : 1 < leverageOf (D.atom d))
    (hadmissible : AdmissiblePair (D.atom d) (D.atom e))
    (hpos : leverageOf (D.atom d) + leverageOf (D.atom e) - 2
      < (lam - 2) * pairGapMinor (D.atom d) (D.atom e)
        + lam * tripleGapDet (D.atom d) (D.atom e) u) :
    ¬ IsTie D := by
  intro htie
  have hlaw := corner_axisPair_law_of_isTie D htie hcard hgap hde hd he hheavy hadmissible
  linarith

/-! ## Part 6 — the `K1` minor ratio

A `K1` dominating triple is a corank-one dominator with EXACTLY ONE vanishing
inside pair minor.  Its two surviving minors are not free: they are proportional,
with the ratio of the two leverage excesses of the vanishing pair.

The two hypotheses below are exactly what the campaign's `K1` normal form
supplies — the vanishing minor itself, and the pivot row that the Sylvester
chain reads off a corank-one dominator.  Nothing here restates that chain. -/

/-- **THE `K1` MINOR RATIO.**  At a vanishing pair minor with the pivot row of a
corank-one dominator, the two remaining pair minors are proportional to the
leverage excesses of the vanishing pair:

  `(l_a - 1)·q_bc = (l_b - 1)·q_ac` .

So the two survive or vanish TOGETHER, and the corner — all three minors zero —
is the only way either of them can vanish. -/
theorem pairGapMinor_ratio_of_pivotRow {a b c : Fin 3 → ℝ}
    (hheavy : 1 < leverageOf a) (hvanish : pairGapMinor a b = 0)
    (hpivot : (leverageOf a - 1) * (b ⬝ᵥ c) = (a ⬝ᵥ b) * (a ⬝ᵥ c)) :
    (leverageOf a - 1) * pairGapMinor b c = (leverageOf b - 1) * pairGapMinor a c := by
  have hexcess : 0 < leverageOf a - 1 := by linarith
  have hprod : (leverageOf a - 1) * (leverageOf b - 1) = (a ⬝ᵥ b) ^ 2 := by
    rw [pairGapMinor] at hvanish; linarith
  have hsquare : ((leverageOf a - 1) * (b ⬝ᵥ c)) ^ 2 = ((a ⬝ᵥ b) * (a ⬝ᵥ c)) ^ 2 := by
    rw [hpivot]
  have hclear : (leverageOf a - 1)
      * ((leverageOf a - 1) * pairGapMinor b c - (leverageOf b - 1) * pairGapMinor a c) = 0 := by
    rw [pairGapMinor, pairGapMinor]
    linear_combination (a ⬝ᵥ c) ^ 2 * hprod - hsquare
  have hne : (leverageOf a - 1) ≠ 0 := ne_of_gt hexcess
  have := (mul_eq_zero.mp hclear).resolve_left hne
  linarith

/-- **THE TWO SURVIVING `K1` MINORS SHARE A SIGN.**  At an all-heavy `K1` triple a
positive minor at one of the two atoms of the vanishing pair forces a positive
minor at the other. -/
theorem pairGapMinor_pos_of_pairGapMinor_pos_of_pivotRow {a b c : Fin 3 → ℝ}
    (hheavyA : 1 < leverageOf a) (hheavyB : 1 < leverageOf b)
    (hvanish : pairGapMinor a b = 0)
    (hpivot : (leverageOf a - 1) * (b ⬝ᵥ c) = (a ⬝ᵥ b) * (a ⬝ᵥ c))
    (hac : 0 < pairGapMinor a c) :
    0 < pairGapMinor b c := by
  have hratio := pairGapMinor_ratio_of_pivotRow hheavyA hvanish hpivot
  have hexcessA : 0 < leverageOf a - 1 := by linarith
  have hexcessB : 0 < leverageOf b - 1 := by linarith
  nlinarith [hratio, mul_pos hexcessB hac, hexcessA]

/-- **AND CONVERSELY.**  A vanishing minor at one of them is a vanishing minor at
the other, so a `K1` triple never has exactly two vanishing minors — the
trichotomy, read through the ratio. -/
theorem pairGapMinor_eq_zero_of_pairGapMinor_eq_zero_of_pivotRow {a b c : Fin 3 → ℝ}
    (hheavyA : 1 < leverageOf a) (hvanish : pairGapMinor a b = 0)
    (hpivot : (leverageOf a - 1) * (b ⬝ᵥ c) = (a ⬝ᵥ b) * (a ⬝ᵥ c))
    (hac : pairGapMinor a c = 0) :
    pairGapMinor b c = 0 := by
  have hratio := pairGapMinor_ratio_of_pivotRow hheavyA hvanish hpivot
  have hexcessA : 0 < leverageOf a - 1 := by linarith
  rw [hac, mul_zero] at hratio
  exact (mul_eq_zero.mp hratio).resolve_left (ne_of_gt hexcessA)

/-! ## Part 7 — the same identity at a pair that MEETS the corner

`Gtz.corner_sum_tripleGapDet_outsidePair` is stated for arbitrary labels, so it
may be read at a pair whose first member is an INSIDE atom.  One summand of the
corner total is then the repeated-atom minor, which is a pair quantity and not a
refusal.  Peeling it off leaves the two genuine refusals and a SHARPER law: the
right side is one leverage excess, not two. -/

/-- The repeated-atom minor in pair-minor vocabulary.  The tree carries it in
squared-area vocabulary (`Gtz.tripleGapDet_repeat_left`); the pair minor is what
the corner identity speaks. -/
theorem tripleGapDet_repeat_left_pairMinor (a b : Fin 3 → ℝ) :
    tripleGapDet a b a = -2 * pairGapMinor a b - leverageOf b + 1 := by
  rw [tripleGapDet_repeat_left, pairGapMinor_eq_crossNormSq]
  ring

/-- **THE CORNER AXIS IDENTITY AT A PAIR THROUGH THE CORNER.**  With `a0` inside
the corner and `d` any other label, the two remaining inside atoms total

  `lam·q - (l_{a0} - 1) + lam·tripleGapDet g_{a0} g_d u` .

The pair minor now carries the FULL factor `lam`, not `lam - 2`, and the leverage
term is a single excess. -/
theorem corner_sum_tripleGapDet_insidePair (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {a0 : Fin m} (ha0 : a0 ∈ C) (d : Fin m) :
    ∑ a ∈ C.erase a0, tripleGapDet (D.atom a0) (D.atom d) (D.atom a)
      = lam * pairGapMinor (D.atom a0) (D.atom d) - (leverageOf (D.atom a0) - 1)
        + lam * tripleGapDet (D.atom a0) (D.atom d) u := by
  have hsplit : ∑ a ∈ C.erase a0, tripleGapDet (D.atom a0) (D.atom d) (D.atom a)
      + tripleGapDet (D.atom a0) (D.atom d) (D.atom a0)
      = ∑ a ∈ C, tripleGapDet (D.atom a0) (D.atom d) (D.atom a) :=
    Finset.sum_erase_add _ _ ha0
  rw [corner_sum_tripleGapDet_outsidePair D hcard hgap a0 d,
    tripleGapDet_repeat_left_pairMinor] at hsplit
  linarith

/-- **THE CORNER AXIS LAW AT A PAIR THROUGH THE CORNER.**  A tie prices an
admissible heavy pair whose first atom is INSIDE the corner and whose second is
outside it, against one leverage excess. -/
theorem corner_insidePair_law_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {a0 d : Fin m} (ha0 : a0 ∈ C) (hd : d ∉ C)
    (hheavy : 1 < leverageOf (D.atom a0))
    (hadmissible : AdmissiblePair (D.atom a0) (D.atom d)) :
    lam * pairGapMinor (D.atom a0) (D.atom d)
        + lam * tripleGapDet (D.atom a0) (D.atom d) u
      ≤ leverageOf (D.atom a0) - 1 := by
  have hne : a0 ≠ d := fun hcon => hd (hcon ▸ ha0)
  have hnonpos : ∑ a ∈ C.erase a0, tripleGapDet (D.atom a0) (D.atom d) (D.atom a) ≤ 0 := by
    refine Finset.sum_nonpos fun a ha => ?_
    have haC : a ∈ C := Finset.mem_of_mem_erase ha
    have hane : a ≠ a0 := Finset.ne_of_mem_erase ha
    exact tripleGapDet_nonpos_of_isTie D htie hne (Ne.symm hane)
      (fun hcon => hd (hcon ▸ haC)) hheavy hadmissible
  rw [corner_sum_tripleGapDet_insidePair D hcard hgap ha0 d] at hnonpos
  linarith

/-- **THE PAIR MINOR CAP AT A CORNER.**  Divided form: at a genuine corner the
pair minor of an admissible heavy pair through the corner is capped by the axis
minor and by the SQUARED AXIS READING of the inside atom, because
`(l_{a0} - 1)/lam` is exactly that reading. -/
theorem corner_insidePair_minor_le_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {a0 d : Fin m} (ha0 : a0 ∈ C) (hd : d ∉ C)
    (hheavy : 1 < leverageOf (D.atom a0))
    (hadmissible : AdmissiblePair (D.atom a0) (D.atom d)) :
    pairGapMinor (D.atom a0) (D.atom d) + tripleGapDet (D.atom a0) (D.atom d) u
      ≤ (leverageOf (D.atom a0) - 1) / lam := by
  have hlaw := corner_insidePair_law_of_isTie D htie hcard hgap ha0 hd hheavy hadmissible
  rw [le_div_iff₀ hlam]
  linarith

end Gtz
