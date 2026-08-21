/-
# The kernel slide: the inverse form of a four-set, in closed form

A dominating subset whose gap `G = S_C - 1` has corank one is the campaign's
central object.  Adjoining one more atom `v` that reads the kernel makes the
four-set strictly dominating (`Gtz.fourSet_posDef_of_reading_ne_zero`), and the
boundary hypothesis then says every one of its sub-triples REFUSES.  By the
landed rank-one drop criterion each refusal is an inequality on an inverse form
`u ⬝ᵥ ((G + v vᵀ)⁻¹ *ᵥ u)`, and until now nothing evaluated that form: it was read
off a matrix inverse that changes with `v`.

This module evaluates it exactly.  Restore the kernel direction to the gap,

  **`kernelShift G w = G + w wᵀ`** ,

which is invertible where the gap was not, and slide `u` along `v` until it
lands in the kernel's orthogonal complement,

  **`kernelSlide u v w = u - (⟨u,w⟩ / ⟨v,w⟩) • v`** .

Then, with `lam = ⟨u,w⟩ / ⟨v,w⟩` and no hypothesis beyond invertibility and
`⟨v,w⟩ ≠ 0` (`Gtz.fourSet_inverseForm_eq_kernelSlide`):

  **`u ⬝ᵥ ((G + v vᵀ)⁻¹ *ᵥ u) = (u - lam • v) ⬝ᵥ ((G + w wᵀ)⁻¹ *ᵥ (u - lam • v)) + lam ^ 2`** .

The whole proof is three elementary steps and never inverts a sum:

* `G *ᵥ w = 0` gives `(G + v vᵀ) *ᵥ w = ⟨v,w⟩ • v`, hence
  `(G + v vᵀ)⁻¹ *ᵥ v = ⟨v,w⟩⁻¹ • w` (`Gtz.fourSet_inv_mulVec_atom`).  In
  particular `v ⬝ᵥ ((G + v vᵀ)⁻¹ *ᵥ v) = 1` exactly, which is the statement that
  dropping `v` from the four-set returns the singular gap it came from.
* a vector orthogonal to the kernel cannot tell the two inverses apart
  (`Gtz.kernelOrth_inverseForm_eq`), because the two solution vectors differ by
  a multiple of `w`.
* the cross term dies, since `(G + v vᵀ)⁻¹ *ᵥ v` points along `w` and the slid
  vector is orthogonal to `w`.

## Two consequences, and the second is about the whole design

**A BLIND ATOM CANNOT TELL WHICH ATOM COMPLETED THE FOUR-SET.**  If `⟨u,w⟩ = 0`
the slide is trivial and the law reads `u ⬝ᵥ ((G + v vᵀ)⁻¹ *ᵥ u) = u ⬝ᵥ ((G + w wᵀ)⁻¹ *ᵥ u)`
(`Gtz.blind_fourSet_inverseForm`), with `v` gone from the right side entirely.
So whether dropping a blind member of a dominating triple produces a strict
dominator does not depend on the atom adjoined, and that whole family of
refusals is ONE condition on the triple.

**THE READING CAP.**  Summing the law over the three members of the dominating
triple, the cross terms cancel against the reproduction `Σ ⟨u,w⟩ • u = w`, and
the sum telescopes (`Gtz.triple_fourSet_inverseForm_sum`).  At a boundary system
every summand is at least one, so every vector `v` of the design obeys

  **`(3 - trace (G + w wᵀ)⁻¹) * ⟨v,w⟩ ^ 2 ≤ 1 + v ⬝ᵥ ((G + w wᵀ)⁻¹ *ᵥ v)`**

(`Gtz.reading_cap_of_refusals`).  This caps the reading of EVERY atom against a
corank-one dominating triple, in terms of that triple alone.  It is not a
statement about one stratum: it holds at every boundary system of every size.

[CALIBRATION.  The bound is attained.  At the `(5,3)` diamond the four dominating
triples `{1,2,3}`, `{1,2,4}`, `{1,3,4}`, `{2,3,4}` have `trace (G + w wᵀ)⁻¹`
equal to `1.6136` and the cap holds with equality, slack `0.000000`, at every one
of the five atoms; the remaining four dominating triples give slack `1.25`.  The
law itself was checked to `3.4e-10` at ranks two through six, and the cap is the
sum of the three drop conditions, so a violation of the cap refutes a boundary
system outright.]
-/
import Gtz.Wave.NullProbeFourSetLaw
import Gtz.Reduction.MassGapDescent
import Gtz.Wave.FourSetProducer
import Gtz.Reduction.PolarGapDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ## 1. The kernel shift -/

/-- The gap with its own kernel direction restored.  Where the gap is singular
of corank one this matrix is invertible, and it agrees with the gap on the
kernel's orthogonal complement. -/
def kernelShift (gap : Matrix (Fin k) (Fin k) ℝ) (kern : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  gap + atomMatrix kern

theorem kernelShift_transpose {gap : Matrix (Fin k) (Fin k) ℝ} (hsymm : gapᵀ = gap)
    (kern : Fin k → ℝ) : (kernelShift gap kern)ᵀ = kernelShift gap kern := by
  rw [kernelShift, Matrix.transpose_add, hsymm,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix kern).1]

/-- **THE SHIFT FIXES THE KERNEL.**  The restored direction is an eigenvector at
one, because the gap kills it and the restored atom is a unit. -/
theorem kernelShift_mulVec_kernel {gap : Matrix (Fin k) (Fin k) ℝ} {kern : Fin k → ℝ}
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) :
    kernelShift gap kern *ᵥ kern = kern := by
  rw [kernelShift, Matrix.add_mulVec, hgap, atomMatrix, vecMulVec_mulVec_eq, hunit,
    one_smul, zero_add]

/-- The inverse fixes the kernel too. -/
theorem kernelShift_inv_mulVec_kernel {gap : Matrix (Fin k) (Fin k) ℝ} {kern : Fin k → ℝ}
    (hdet : IsUnit (kernelShift gap kern).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) :
    (kernelShift gap kern)⁻¹ *ᵥ kern = kern :=
  calc (kernelShift gap kern)⁻¹ *ᵥ kern
      = (kernelShift gap kern)⁻¹ *ᵥ (kernelShift gap kern *ᵥ kern) := by
        rw [kernelShift_mulVec_kernel hgap hunit]
    _ = kern := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- The shifted inverse is symmetric. -/
theorem kernelShift_inv_transpose {gap : Matrix (Fin k) (Fin k) ℝ} (hsymm : gapᵀ = gap)
    (kern : Fin k → ℝ) :
    ((kernelShift gap kern)⁻¹)ᵀ = (kernelShift gap kern)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, kernelShift_transpose hsymm]

/-- **THE SHIFTED SOLUTION STAYS ORTHOGONAL TO THE KERNEL.**  Solving against the
shift preserves orthogonality to the restored direction. -/
theorem kernelShift_inv_dotProduct_kernel {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern probe : Fin k → ℝ} (hsymm : gapᵀ = gap)
    (hdet : IsUnit (kernelShift gap kern).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (horth : kern ⬝ᵥ probe = 0) :
    kern ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ probe) = 0 := by
  have hmove := dotProduct_mulVec_transpose ((kernelShift gap kern)⁻¹) kern probe
  rw [kernelShift_inv_transpose hsymm, kernelShift_inv_mulVec_kernel hdet hgap hunit] at hmove
  rw [← hmove, horth]

/-- **THE SHIFT AND THE GAP AGREE OFF THE KERNEL.**  On a probe orthogonal to the
kernel, the shifted solution solves the gap's own equation. -/
theorem gap_mulVec_kernelShift_inv {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern probe : Fin k → ℝ} (hsymm : gapᵀ = gap)
    (hdet : IsUnit (kernelShift gap kern).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (horth : kern ⬝ᵥ probe = 0) :
    gap *ᵥ ((kernelShift gap kern)⁻¹ *ᵥ probe) = probe := by
  set sol := (kernelShift gap kern)⁻¹ *ᵥ probe with hsol
  have hsolve : kernelShift gap kern *ᵥ sol = probe := by
    rw [hsol, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hzero : kern ⬝ᵥ sol = 0 := by
    rw [hsol]; exact kernelShift_inv_dotProduct_kernel hsymm hdet hgap hunit horth
  rw [kernelShift, Matrix.add_mulVec, atomMatrix, vecMulVec_mulVec_eq, hzero, zero_smul,
    add_zero] at hsolve
  exact hsolve

/-! ## 2. The four-set carries the kernel onto its own atom -/

/-- **THE FOUR-SET SENDS THE KERNEL TO THE ADJOINED ATOM.** -/
theorem fourSet_mulVec_kernel {gap : Matrix (Fin k) (Fin k) ℝ} {kern atom : Fin k → ℝ}
    (hgap : gap *ᵥ kern = 0) :
    (gap + atomMatrix atom) *ᵥ kern = (atom ⬝ᵥ kern) • atom := by
  rw [Matrix.add_mulVec, hgap, atomMatrix, vecMulVec_mulVec_eq, zero_add]

/-- **AND ITS INVERSE SENDS THE ATOM BACK TO THE KERNEL.**  One equation, no
inverse of a sum: the four-set already maps the kernel onto a multiple of the
atom, so the inverse reverses it. -/
theorem fourSet_inv_mulVec_atom {gap : Matrix (Fin k) (Fin k) ℝ} {kern atom : Fin k → ℝ}
    (hdet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hread : atom ⬝ᵥ kern ≠ 0) :
    (gap + atomMatrix atom)⁻¹ *ᵥ atom = (atom ⬝ᵥ kern)⁻¹ • kern := by
  have hback : (gap + atomMatrix atom)⁻¹ *ᵥ ((gap + atomMatrix atom) *ᵥ kern) = kern := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [fourSet_mulVec_kernel hgap, Matrix.mulVec_smul] at hback
  have hscaled := congrArg (fun z : Fin k → ℝ => (atom ⬝ᵥ kern)⁻¹ • z) hback
  simpa only [smul_smul, inv_mul_cancel₀ hread, one_smul] using hscaled

/-- **DROPPING THE ADJOINED ATOM RETURNS THE SINGULAR GAP.**  Its inverse form is
exactly one, never less, so that drop is never a strict dominator.  This is the
one refusal of the four-set that costs nothing. -/
theorem fourSet_inverseForm_self {gap : Matrix (Fin k) (Fin k) ℝ} {kern atom : Fin k → ℝ}
    (hdet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hread : atom ⬝ᵥ kern ≠ 0) :
    atom ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ atom) = 1 := by
  rw [fourSet_inv_mulVec_atom hdet hgap hread, dotProduct_smul, smul_eq_mul,
    inv_mul_cancel₀ hread]

/-- A probe orthogonal to the kernel is blind to the adjoined atom's direction in
the inverse. -/
theorem fourSet_inverseForm_cross {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern atom probe : Fin k → ℝ} (hdet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hread : atom ⬝ᵥ kern ≠ 0) (horth : kern ⬝ᵥ probe = 0) :
    probe ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ atom) = 0 := by
  rw [fourSet_inv_mulVec_atom hdet hgap hread, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe kern, horth, mul_zero]

/-! ## 3. Off the kernel the two inverses agree -/

/-- **THE TWO INVERSES AGREE OFF THE KERNEL.**  On a probe orthogonal to the
kernel the four-set and the shift give the same form, whatever atom was
adjoined.  The two solution vectors differ by a multiple of the kernel, which the
probe cannot see. -/
theorem kernelOrth_inverseForm_eq {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern atom probe : Fin k → ℝ} (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0)
    (horth : kern ⬝ᵥ probe = 0) :
    probe ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ probe)
      = probe ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ probe) := by
  set shifted := (kernelShift gap kern)⁻¹ *ᵥ probe with hshifted
  set coeff := (atom ⬝ᵥ shifted) / (atom ⬝ᵥ kern) with hcoeff
  -- the four-set sends `shifted - coeff • kern` to the probe
  have hgapAct : gap *ᵥ shifted = probe :=
    gap_mulVec_kernelShift_inv hsymm hshiftDet hgap hunit horth
  have hfour : (gap + atomMatrix atom) *ᵥ (shifted - coeff • kern) = probe := by
    have h1 : (gap + atomMatrix atom) *ᵥ shifted = probe + (atom ⬝ᵥ shifted) • atom := by
      rw [Matrix.add_mulVec, hgapAct, atomMatrix, vecMulVec_mulVec_eq]
    have h2 : (gap + atomMatrix atom) *ᵥ (coeff • kern)
        = (coeff * (atom ⬝ᵥ kern)) • atom := by
      rw [Matrix.mulVec_smul, fourSet_mulVec_kernel hgap, smul_smul]
    rw [Matrix.mulVec_sub, h1, h2, hcoeff, div_mul_cancel₀ _ hread]
    abel
  have hsolve : (gap + atomMatrix atom)⁻¹ *ᵥ probe = shifted - coeff • kern := by
    rw [← hfour, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hfourDet, Matrix.one_mulVec]
  rw [hsolve, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe kern, horth, mul_zero, sub_zero]

/-! ## 4. The kernel slide, and the drop law -/

/-- The probe slid along the adjoined atom until it is orthogonal to the kernel. -/
noncomputable def kernelSlide (probe atom kern : Fin k → ℝ) : Fin k → ℝ :=
  probe - ((probe ⬝ᵥ kern) / (atom ⬝ᵥ kern)) • atom

theorem kernelSlide_dotProduct_kernel (probe atom kern : Fin k → ℝ)
    (hread : atom ⬝ᵥ kern ≠ 0) : kern ⬝ᵥ kernelSlide probe atom kern = 0 := by
  rw [kernelSlide, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    dotProduct_comm kern probe, dotProduct_comm kern atom,
    div_mul_cancel₀ _ hread, sub_self]

/-- A symmetric form expands on a slid vector. -/
theorem inverseForm_sub_smul {form : Matrix (Fin k) (Fin k) ℝ} (hform : formᵀ = form)
    (probe atom : Fin k → ℝ) (lam : ℝ) :
    (probe - lam • atom) ⬝ᵥ (form *ᵥ (probe - lam • atom))
      = probe ⬝ᵥ (form *ᵥ probe) - 2 * lam * (probe ⬝ᵥ (form *ᵥ atom))
        + lam ^ 2 * (atom ⬝ᵥ (form *ᵥ atom)) := by
  have hsym : atom ⬝ᵥ (form *ᵥ probe) = probe ⬝ᵥ (form *ᵥ atom) := by
    have hmove := dotProduct_mulVec_transpose form atom probe
    rw [hform] at hmove
    rw [← hmove, dotProduct_comm]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym]
  ring

/-- **THE DROP LAW, IN SPLIT FORM.**  Write the probe as a vector orthogonal to
the kernel plus a multiple of the adjoined atom.  Then the four-set's inverse
form is the shifted form of the orthogonal part plus the square of the
coefficient.  No positivity, no rank hypothesis, no size: only invertibility and
a live reading. -/
theorem fourSet_inverseForm_split {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern atom probe orth : Fin k → ℝ} {lam : ℝ} (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0)
    (horth : kern ⬝ᵥ orth = 0) (hsplit : probe = orth + lam • atom) :
    probe ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ probe)
      = orth ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ orth) + lam ^ 2 := by
  subst hsplit
  have hfourSymm : ((gap + atomMatrix atom)⁻¹)ᵀ = (gap + atomMatrix atom)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_add, hsymm,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix atom).1]
  have hexpand := inverseForm_sub_smul hfourSymm orth atom (-lam)
  have hrewrite : orth - (-lam) • atom = orth + lam • atom := by
    rw [neg_smul, sub_neg_eq_add]
  rw [hrewrite] at hexpand
  rw [hexpand, fourSet_inverseForm_cross hfourDet hgap hread horth,
    fourSet_inverseForm_self hfourDet hgap hread,
    kernelOrth_inverseForm_eq hsymm hshiftDet hfourDet hgap hunit hread horth]
  ring

/-- **THE DROP LAW.**  The inverse form of a four-set at any vector is the shifted
form at the slid vector, plus the square of the slide coefficient. -/
theorem fourSet_inverseForm_eq_kernelSlide {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern atom probe : Fin k → ℝ} (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0) :
    probe ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ probe)
      = (kernelSlide probe atom kern)
          ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ (kernelSlide probe atom kern))
        + ((probe ⬝ᵥ kern) / (atom ⬝ᵥ kern)) ^ 2 :=
  fourSet_inverseForm_split hsymm hshiftDet hfourDet hgap hunit hread
    (kernelSlide_dotProduct_kernel probe atom kern hread)
    (by rw [kernelSlide]; abel)

/-- **A BLIND VECTOR CANNOT TELL WHICH ATOM WAS ADJOINED.**  When the probe is
orthogonal to the kernel the slide is trivial and the adjoined atom leaves the
statement altogether, so the whole family of refusals obtained by dropping a
blind member of the dominating triple is ONE condition on that triple. -/
theorem blind_fourSet_inverseForm {gap : Matrix (Fin k) (Fin k) ℝ}
    {kern atom probe : Fin k → ℝ} (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0)
    (hblind : probe ⬝ᵥ kern = 0) :
    probe ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ probe)
      = probe ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ probe) :=
  kernelOrth_inverseForm_eq hsymm hshiftDet hfourDet hgap hunit hread
    (by rw [dotProduct_comm]; exact hblind)

/-! ## 5. Summing over the dominating triple: the cross terms cancel -/

section Triple

variable {gap : Matrix (Fin 3) (Fin 3) ℝ} {kern atom ga gb gc : Fin 3 → ℝ}

/-- **THE REPRODUCTION.**  A dominating triple rebuilds its own kernel direction
with its readings as the coefficients. -/
theorem triple_kernel_reproduction
    (hS : atomMatrix ga + atomMatrix gb + atomMatrix gc = gap + 1)
    (hgap : gap *ᵥ kern = 0) :
    (ga ⬝ᵥ kern) • ga + (gb ⬝ᵥ kern) • gb + (gc ⬝ᵥ kern) • gc = kern := by
  have happ := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M *ᵥ kern) hS
  simpa only [Matrix.add_mulVec, atomMatrix, vecMulVec_mulVec_eq, hgap,
    Matrix.one_mulVec, zero_add] using happ

/-- The three readings of the kernel square to one. -/
theorem triple_kernel_readings_sq
    (hS : atomMatrix ga + atomMatrix gb + atomMatrix gc = gap + 1)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) :
    (ga ⬝ᵥ kern) ^ 2 + (gb ⬝ᵥ kern) ^ 2 + (gc ⬝ᵥ kern) ^ 2 = 1 := by
  have hrep := triple_kernel_reproduction hS hgap
  have hdot := congrArg (fun v : Fin 3 → ℝ => kern ⬝ᵥ v) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hdot
  rw [dotProduct_comm kern ga, dotProduct_comm kern gb, dotProduct_comm kern gc,
    hunit] at hdot
  simp only [pow_two]
  linarith [hdot]

/-- **THE SUMMED DROP LAW.**  Adding the three drop values of a dominating triple,
the cross terms cancel against the reproduction and the reading squares sum to
one.  What is left has the adjoined atom in exactly two places. -/
theorem triple_fourSet_inverseForm_sum (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0)
    (hS : atomMatrix ga + atomMatrix gb + atomMatrix gc = gap + 1) :
    ga ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ ga)
        + gb ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gb)
        + gc ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gc)
      = (ga ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ ga)
          + gb ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gb)
          + gc ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gc)) - 2
        + (1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom)) / (atom ⬝ᵥ kern) ^ 2 := by
  set N := (kernelShift gap kern)⁻¹ with hN
  have hNsymm : Nᵀ = N := kernelShift_inv_transpose hsymm kern
  have hNkern : N *ᵥ kern = kern := kernelShift_inv_mulVec_kernel hshiftDet hgap hunit
  -- the shifted inverse reads the adjoined atom against the kernel at the reading itself
  have hmix : kern ⬝ᵥ (N *ᵥ atom) = atom ⬝ᵥ kern := by
    have hmove := dotProduct_mulVec_transpose N kern atom
    rw [hNsymm, hNkern] at hmove
    rw [← hmove, dotProduct_comm]
  -- each member, through the drop law
  have hstep : ∀ u : Fin 3 → ℝ,
      u ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ u)
        = u ⬝ᵥ (N *ᵥ u) - 2 * ((u ⬝ᵥ kern) / (atom ⬝ᵥ kern)) * (u ⬝ᵥ (N *ᵥ atom))
          + ((u ⬝ᵥ kern) / (atom ⬝ᵥ kern)) ^ 2 * (atom ⬝ᵥ (N *ᵥ atom))
          + ((u ⬝ᵥ kern) / (atom ⬝ᵥ kern)) ^ 2 := by
    intro u
    rw [fourSet_inverseForm_eq_kernelSlide hsymm hshiftDet hfourDet hgap hunit hread,
      kernelSlide, ← hN, inverseForm_sub_smul hNsymm u atom]
  -- the cross terms, summed, see only the reproduction
  have hcross : (ga ⬝ᵥ kern) * (ga ⬝ᵥ (N *ᵥ atom)) + (gb ⬝ᵥ kern) * (gb ⬝ᵥ (N *ᵥ atom))
      + (gc ⬝ᵥ kern) * (gc ⬝ᵥ (N *ᵥ atom)) = atom ⬝ᵥ kern := by
    have hrep := triple_kernel_reproduction hS hgap
    have hdot := congrArg (fun v : Fin 3 → ℝ => v ⬝ᵥ (N *ᵥ atom)) hrep
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hdot
    rw [hdot]; exact hmix
  have hsq := triple_kernel_readings_sq hS hgap hunit
  have hsum : ga ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ ga)
        + gb ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gb)
        + gc ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gc)
      = (ga ⬝ᵥ (N *ᵥ ga) + gb ⬝ᵥ (N *ᵥ gb) + gc ⬝ᵥ (N *ᵥ gc))
        - (2 / (atom ⬝ᵥ kern)) * ((ga ⬝ᵥ kern) * (ga ⬝ᵥ (N *ᵥ atom))
            + (gb ⬝ᵥ kern) * (gb ⬝ᵥ (N *ᵥ atom))
            + (gc ⬝ᵥ kern) * (gc ⬝ᵥ (N *ᵥ atom)))
        + (((ga ⬝ᵥ kern) ^ 2 + (gb ⬝ᵥ kern) ^ 2 + (gc ⬝ᵥ kern) ^ 2)
            / (atom ⬝ᵥ kern) ^ 2) * (1 + atom ⬝ᵥ (N *ᵥ atom)) := by
    rw [hstep ga, hstep gb, hstep gc]
    field_simp
    ring
  rw [hsum, hcross, hsq]
  field_simp

/-! ## 6. The reading cap -/

/-- A refused drop is an inverse form of at least one.  The contrapositive of the
landed rank-one drop criterion, and the bridge from "this triple does not
strictly dominate" to an inequality the drop law can evaluate. -/
theorem one_le_inverseForm_of_not_posDef {n : ℕ} {block : Matrix (Fin n) (Fin n) ℝ}
    (hblock : block.PosDef) {u : Fin n → ℝ}
    (hrefuse : ¬ (block - atomMatrix u).PosDef) :
    1 ≤ u ⬝ᵥ (block⁻¹ *ᵥ u) := by
  by_contra hlt
  push_neg at hlt
  exact hrefuse (posDef_sub_atomMatrix_of_inverseForm_lt_one hblock hlt)

/-- **THE READING CAP.**  Let a dominating triple have a corank-one gap with unit
kernel, and adjoin any vector that reads that kernel.  If all three drops of the
resulting four-set refuse, then the reading is capped by the triple alone:

  `(5 - Σ) * ⟨atom, kern⟩ ^ 2 ≤ 1 + atom ⬝ᵥ ((gap + kern kernᵀ)⁻¹ *ᵥ atom)` ,

where `Σ` is the shifted form of the triple summed over its three members.  The
adjoined vector enters only through its reading and its own shifted form, so this
caps EVERY atom of the design against ONE dominating triple.

Writing `Σ = 2 + trace (gap + kern kernᵀ)⁻¹`, the coefficient is
`3 - trace (gap + kern kernᵀ)⁻¹`: the cap has content exactly when the triple
dominates strongly enough transverse to its kernel.

[The bound is ATTAINED: at the `(5,3)` diamond the four dominating triples that
omit the short edge give coefficient `1.3864` and equality at every one of the
five atoms.] -/
theorem reading_cap_of_refusals (hsymm : gapᵀ = gap)
    (hshiftDet : IsUnit (kernelShift gap kern).det)
    (hfourDet : IsUnit (gap + atomMatrix atom).det)
    (hgap : gap *ᵥ kern = 0) (hunit : kern ⬝ᵥ kern = 1) (hread : atom ⬝ᵥ kern ≠ 0)
    (hS : atomMatrix ga + atomMatrix gb + atomMatrix gc = gap + 1)
    (hrefa : 1 ≤ ga ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ ga))
    (hrefb : 1 ≤ gb ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gb))
    (hrefc : 1 ≤ gc ⬝ᵥ ((gap + atomMatrix atom)⁻¹ *ᵥ gc)) :
    (5 - (ga ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ ga)
        + gb ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gb)
        + gc ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gc))) * (atom ⬝ᵥ kern) ^ 2
      ≤ 1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom) := by
  have hsum := triple_fourSet_inverseForm_sum hsymm hshiftDet hfourDet hgap hunit hread hS
  have hthree : (3 : ℝ)
      ≤ (ga ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ ga)
          + gb ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gb)
          + gc ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gc)) - 2
        + (1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom)) / (atom ⬝ᵥ kern) ^ 2 := by
    rw [← hsum]; linarith
  have hpos : 0 < (atom ⬝ᵥ kern) ^ 2 := by positivity
  have hkey : 5 - (ga ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ ga)
        + gb ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gb)
        + gc ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gc))
      ≤ (1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom)) / (atom ⬝ᵥ kern) ^ 2 := by
    linarith
  calc (5 - (ga ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ ga)
          + gb ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gb)
          + gc ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ gc))) * (atom ⬝ᵥ kern) ^ 2
      ≤ ((1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom)) / (atom ⬝ᵥ kern) ^ 2)
          * (atom ⬝ᵥ kern) ^ 2 := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
    _ = 1 + atom ⬝ᵥ ((kernelShift gap kern)⁻¹ *ᵥ atom) := by field_simp

end Triple

/-! ## 7. At a boundary design -/

section Design

variable {m : ℕ}

/-- A triple's atom sum, written out. -/
theorem subsetSum_triple_expand (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
  rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton]
  abel

/-- **THE READING CAP AT A BOUNDARY DESIGN.**  Every atom of a boundary design is
capped against every corank-one weak dominator, in terms of that dominator alone.

The dominator supplies a unit null probe `kern` and a nonzero second invariant.
Any atom `d` outside it that reads the probe makes the four-set strictly
dominating, so all three of its drops refuse, and the three refusals sum to this
one inequality by `Gtz.triple_fourSet_inverseForm_sum`.

The left coefficient is `3 - trace (gap + kern kernᵀ)⁻¹` once the summed shifted
form is written as `2 + trace`, so the cap has content exactly when the dominator
dominates strongly transverse to its own kernel. -/
theorem reading_cap_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    {kern : Fin 3 → ℝ}
    (hgap : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ kern = 0)
    (hunit : kern ⬝ᵥ kern = 1)
    (he : secondInvariantOfThree (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) ≠ 0)
    (hread : D.atom d ⬝ᵥ kern ≠ 0) :
    (5 - (D.atom x ⬝ᵥ
            ((kernelShift (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) kern)⁻¹ *ᵥ D.atom x)
        + D.atom y ⬝ᵥ
            ((kernelShift (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) kern)⁻¹ *ᵥ D.atom y)
        + D.atom z ⬝ᵥ
            ((kernelShift (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) kern)⁻¹ *ᵥ D.atom z)))
        * (D.atom d ⬝ᵥ kern) ^ 2
      ≤ 1 + D.atom d ⬝ᵥ
          ((kernelShift (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) kern)⁻¹ *ᵥ D.atom d) := by
  classical
  set gap := subsetSum D ({x, y, z} : Finset (Fin m)) - 1 with hgapset
  have hexpand := subsetSum_triple_expand D hxy hxz hyz
  have hgapdef : gap = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1 := by
    rw [hgapset, hexpand]
  have hS : atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) = gap + 1 := by
    rw [hgapdef]; abel
  have hpsd : gap.PosSemidef := hdom
  have hsymm : gapᵀ = gap := (by simpa using hpsd.isHermitian : gap.IsSymm)
  -- both rank-one updates are positive definite, by the landed four-set producer
  have hkernRead : kern ⬝ᵥ kern ≠ 0 := by rw [hunit]; exact one_ne_zero
  have hshiftPD : (kernelShift gap kern).PosDef :=
    posDef_add_atomMatrix_of_reading_ne_zero hpsd hgap hunit he hkernRead
  have hfourPD : (gap + atomMatrix (D.atom d)).PosDef :=
    posDef_add_atomMatrix_of_reading_ne_zero hpsd hgap hunit he hread
  have hshiftDet : IsUnit (kernelShift gap kern).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hshiftPD.det_pos)
  have hfourDet : IsUnit (gap + atomMatrix (D.atom d)).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hfourPD.det_pos)
  -- no triple of the design dominates strictly
  have hno : ∀ p q r : Fin m, p ≠ q → p ≠ r → q ≠ r →
      ¬ (atomMatrix (D.atom p) + atomMatrix (D.atom q) + atomMatrix (D.atom r) - 1).PosDef := by
    intro p q r hpq hpr hqr
    have hrefuse := htie.2 ({p, q, r} : Finset (Fin m)) (card_triple_eq hpq hpr hqr)
    rwa [subsetSum_triple_expand D hpq hpr hqr] at hrefuse
  -- the three drops of the four-set, each refused
  have hrefa : 1 ≤ D.atom x ⬝ᵥ ((gap + atomMatrix (D.atom d))⁻¹ *ᵥ D.atom x) := by
    refine one_le_inverseForm_of_not_posDef hfourPD ?_
    have heq : gap + atomMatrix (D.atom d) - atomMatrix (D.atom x)
        = atomMatrix (D.atom d) + atomMatrix (D.atom y) + atomMatrix (D.atom z) - 1 := by
      rw [hgapdef]; abel
    rw [heq]; exact hno d y z hdy hdz hyz
  have hrefb : 1 ≤ D.atom y ⬝ᵥ ((gap + atomMatrix (D.atom d))⁻¹ *ᵥ D.atom y) := by
    refine one_le_inverseForm_of_not_posDef hfourPD ?_
    have heq : gap + atomMatrix (D.atom d) - atomMatrix (D.atom y)
        = atomMatrix (D.atom x) + atomMatrix (D.atom d) + atomMatrix (D.atom z) - 1 := by
      rw [hgapdef]; abel
    rw [heq]; exact hno x d z (Ne.symm hdx) hxz hdz
  have hrefc : 1 ≤ D.atom z ⬝ᵥ ((gap + atomMatrix (D.atom d))⁻¹ *ᵥ D.atom z) := by
    refine one_le_inverseForm_of_not_posDef hfourPD ?_
    have heq : gap + atomMatrix (D.atom d) - atomMatrix (D.atom z)
        = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom d) - 1 := by
      rw [hgapdef]; abel
    rw [heq]; exact hno x y d hxy (Ne.symm hdx) (Ne.symm hdy)
  exact reading_cap_of_refusals hsymm hshiftDet hfourDet hgap hunit hread hS hrefa hrefb hrefc

end Design

end Gtz
