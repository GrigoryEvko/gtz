import Gtz.Wave.OneAxisZeroWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The anchor caps of the one-zero corner: the axis and erased readings are
# budgeted, and the outside readings obey an exact window

Every landed law of the `Z1` stratum bounds the anchor readings from BELOW:
the pair floors, the per-atom tie floor, and the exchange reading all push
readings of `B⁻¹` UP.  This module supplies the missing other side: exact
upper bounds and exact identities, with no tie hypothesis.

The engine is the erased over-coverage (`Gtz.corner_oneAxisZero_outside_overCoverage`):
the `x`-resolution makes the weighted outside mass an exact multiple of the
erased direction, so after the weight cap `ms` the UNWEIGHTED outside atoms
over-cover the erased atom by the factor `(1 − t_x)/ms > 1`.  Feeding the
over-coverage into the frame pair gives the anchor a Loewner floor
(`Gtz.corner_oneAxisZero_anchor_loewner`):

  `B ⪰ lam • u uᵀ + ((1 − t_x − ms)/ms) • g_x g_xᵀ` ,

and the floor caps the two readings the tie-side laws cannot see
(`Gtz.corner_oneAxisZero_anchor_axis_cap`, with the joint Gram form):

  `lam · uᵀB⁻¹u ≤ 1`,  `(1 − t_x − ms) · g_xᵀB⁻¹g_x ≤ ms` .

The general instrument is `Gtz.psd_pair_gram_cap`: a matrix that dominates two
rank-one atoms in the Loewner order caps their inverse Gram at the identity —
the two-vector sharpening of `Gtz.posSemidef_sub_vecMulVec_iff`.

## The exact window of the outside readings

Tracing the frame pair against `B⁻¹` collapses the outside anchor readings to
three scalars (`Gtz.corner_oneAxisZero_anchor_outside_total`):

  `Σ_{d ∈ Cᶜ} R_dd = 3 + X − lam·U` ,  `U = uᵀB⁻¹u`, `X = g_xᵀB⁻¹g_x`,

with the trace companion `tr B⁻¹ = R_yy + R_zz + X − lam·U`
(`Gtz.corner_oneAxisZero_anchor_trace_identity`).  With the axis cap the
identity becomes the window `2 + X ≤ Σ R_dd ≤ 3 + X`
(`Gtz.corner_oneAxisZero_anchor_outside_window`): the three outside atoms
always over-read the anchor.  The coweight reading cap of the stratum is the
identity's shadow: at the `Z1` anchor it carries no information beyond
`U + W ≥ 0`.

## The trace pinch of a tie

At a tie the pair floors meet the full weighted Parseval trace and pinch every
anchored atom against the whole trace (`Gtz.tie_fiveSet_trace_pinch`, any
five-set, any size):

  `(Σ_{d ∈ F, d ≠ e} t_d)(1 − R_ee) + t_e R_ee + Σ_{b ∉ F} t_b R_bb ≤ tr B⁻¹`.

At the `Z1` anchor of a `(6,3)` tie the excluded sum is the single erased
reading `t_x X` (`Gtz.corner_oneAxisZero_anchor_pinch`).  In the heavy-inside
cell the failed four-set forces `R_yy ≥ 1` with no tie
(`Gtz.corner_oneAxisZero_heavyInside_anchor_reading`), so the pinch at `e = z`
runs against the capped trace while the failure holds `R_yy` at one — the
quantitative tension of the cell, kernel on both sides.

Measured: all caps and the window hold at 6.45·10⁶ fresh `Z1` samples with the
caps saturating (max `lam·U = 0.9999990`, max `(1−t_x−ms)X/ms = 0.9999998`),
and the witness saturates the erased cap exactly (`κ·X = 1` at
`ms = 44/201`); the outside total at the witness is `292/93 = 3 + X − lam·U`
in exact rationals.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The PSD pair Gram cap -/

/-- **THE PSD PAIR GRAM CAP.**  A positive definite matrix that dominates two
rank-one atoms in the Loewner order caps their inverse-metric Gram at the
identity: both self-readings stay at most one, and the cross-reading is
dominated by the product of the two complements.  The one-vector case is
`Gtz.posSemidef_sub_vecMulVec_iff`; the pair case follows from one exact
factorization of the domination form at one well-chosen probe. -/
theorem psd_pair_gram_cap {k : ℕ} {B : Matrix (Fin k) (Fin k) ℝ} (hB : B.PosDef)
    (q r : Fin k → ℝ)
    (hpsd : (B - Matrix.vecMulVec q q - Matrix.vecMulVec r r).PosSemidef) :
    q ⬝ᵥ (B⁻¹ *ᵥ q) ≤ 1 ∧ r ⬝ᵥ (B⁻¹ *ᵥ r) ≤ 1
      ∧ (q ⬝ᵥ (B⁻¹ *ᵥ r)) ^ 2
        ≤ (1 - q ⬝ᵥ (B⁻¹ *ᵥ q)) * (1 - r ⬝ᵥ (B⁻¹ *ᵥ r)) := by
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hB.det_pos)
  have hInv : (B⁻¹).PosSemidef := hB.inv.posSemidef
  set Q : ℝ := q ⬝ᵥ (B⁻¹ *ᵥ q) with hQdef
  set R : ℝ := r ⬝ᵥ (B⁻¹ *ᵥ r) with hRdef
  set Cc : ℝ := q ⬝ᵥ (B⁻¹ *ᵥ r) with hCdef
  -- symmetry of the inverse metric
  have hBsym : Bᵀ = B := transpose_eq_of_isHermitian hB.1
  have hIsym : (B⁻¹)ᵀ = B⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hBsym]
  have hcross : r ⬝ᵥ (B⁻¹ *ᵥ q) = Cc := by
    rw [hCdef, dotProduct_mulVec q B⁻¹ r, ← hIsym, Matrix.vecMul_transpose,
      dotProduct_comm, hIsym]
  -- the one-vector caps through the landed rank-one criterion
  have hQr : (Matrix.vecMulVec r r).PosSemidef := posSemidef_atomMatrix r
  have hQq : (Matrix.vecMulVec q q).PosSemidef := posSemidef_atomMatrix q
  have hBq : (B - Matrix.vecMulVec q q).PosSemidef := by
    have hsum : B - Matrix.vecMulVec q q
        = (B - Matrix.vecMulVec q q - Matrix.vecMulVec r r)
          + Matrix.vecMulVec r r := by abel
    rw [hsum]
    exact hpsd.add hQr
  have hBr : (B - Matrix.vecMulVec r r).PosSemidef := by
    have hsum : B - Matrix.vecMulVec r r
        = (B - Matrix.vecMulVec q q - Matrix.vecMulVec r r)
          + Matrix.vecMulVec q q := by abel
    rw [hsum]
    exact hpsd.add hQq
  have hQ1 : Q ≤ 1 := (posSemidef_sub_vecMulVec_iff B hB q).mp hBq
  have hR1 : R ≤ 1 := (posSemidef_sub_vecMulVec_iff B hB r).mp hBr
  have hR0 : 0 ≤ R := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hInv).2 r
    rwa [star_trivial] at h
  refine ⟨hQ1, hR1, ?_⟩
  -- the domination form at the probe B⁻¹(α q + β r)
  have hprobe : ∀ α β : ℝ,
      0 ≤ (α ^ 2 * Q + 2 * (α * β) * Cc + β ^ 2 * R)
        - (α * Q + β * Cc) ^ 2 - (α * Cc + β * R) ^ 2 := by
    intro α β
    set s : Fin k → ℝ := α • q + β • r with hs
    set mv : Fin k → ℝ := B⁻¹ *ᵥ s with hmv
    have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 mv
    rw [star_trivial] at hread
    have hBm : B *ᵥ mv = s := by
      rw [hmv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hdet,
        Matrix.one_mulVec]
    have hsm : s ⬝ᵥ mv = α ^ 2 * Q + 2 * (α * β) * Cc + β ^ 2 * R := by
      rw [hmv, hs, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        add_dotProduct, smul_dotProduct, smul_dotProduct,
        dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
        dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← hQdef, ← hRdef, ← hCdef, hcross]
      ring
    have hqm : q ⬝ᵥ mv = α * Q + β * Cc := by
      rw [hmv, hs, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        dotProduct_add, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← hQdef, ← hCdef]
    have hrm : r ⬝ᵥ mv = α * Cc + β * R := by
      rw [hmv, hs, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        dotProduct_add, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← hRdef, hcross]
    have hexp : mv ⬝ᵥ ((B - Matrix.vecMulVec q q - Matrix.vecMulVec r r) *ᵥ mv)
        = s ⬝ᵥ mv - (q ⬝ᵥ mv) ^ 2 - (r ⬝ᵥ mv) ^ 2 := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub,
        hBm, vecMulVec_mulVec_eq, vecMulVec_mulVec_eq, dotProduct_smul,
        dotProduct_smul]
      simp only [smul_eq_mul]
      rw [dotProduct_comm mv q, dotProduct_comm mv r, dotProduct_comm mv s]
      ring
    rw [hexp, hsm, hqm, hrm] at hread
    linarith
  -- the exact factorization at the probe (Cc, 1 − Q)
  have hfact : (Cc ^ 2 * Q + 2 * (Cc * (1 - Q)) * Cc + (1 - Q) ^ 2 * R)
        - (Cc * Q + (1 - Q) * Cc) ^ 2 - (Cc * Cc + (1 - Q) * R) ^ 2
      = ((1 - Q) * (1 - R) - Cc ^ 2) * ((1 - Q) * R + Cc ^ 2) := by
    ring
  have hval := hprobe Cc (1 - Q)
  rw [hfact] at hval
  by_cases hdeg : (1 - Q) * R + Cc ^ 2 = 0
  · have hQR : 0 ≤ (1 - Q) * R := mul_nonneg (by linarith) hR0
    have hC0 : Cc ^ 2 = 0 := by nlinarith [sq_nonneg Cc]
    rw [hC0]
    have : 0 ≤ (1 - Q) * (1 - R) := mul_nonneg (by linarith) (by linarith)
    linarith
  · have hpos : 0 < (1 - Q) * R + Cc ^ 2 := by
      have hQR : 0 ≤ (1 - Q) * R := mul_nonneg (by linarith) hR0
      have : 0 ≤ (1 - Q) * R + Cc ^ 2 := by nlinarith [sq_nonneg Cc]
      exact lt_of_le_of_ne this (Ne.symm hdeg)
    nlinarith [hval, hpos]

/-! ## 2. The erased over-coverage of the outside family -/

/-- **THE ERASED OVER-COVERAGE.**  At a `Z1` corner the unweighted outside
atoms over-cover the erased direction by the inverse weight cap: the
`x`-resolution and the `x`-mass make the weighted outside second moment exact
in the erased direction, and the cap `ms` prices the unweighted excess.  No
tie, any size. -/
theorem corner_oneAxisZero_outside_overCoverage (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {ms : ℝ} (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (v : Fin 3 → ℝ) :
    (1 - D.weight x) * (D.atom x ⬝ᵥ v) ^ 2
      ≤ ms * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
  classical
  set ξ : ℝ := D.atom x ⬝ᵥ v with hxi
  set v' : Fin 3 → ℝ := v - ξ • D.atom x with hv'
  have hread : ∀ d : Fin m, D.atom d ⬝ᵥ v' = D.atom d ⬝ᵥ v - ξ * (D.atom d ⬝ᵥ D.atom x) := by
    intro d
    rw [hv', dotProduct_sub, dotProduct_smul, smul_eq_mul]
  -- the weighted outside form at the deflated vector is nonnegative
  have hnn : 0 ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (D.atom d ⬝ᵥ v') ^ 2 :=
    Finset.sum_nonneg fun d _ =>
      mul_nonneg (D.weight_pos d).le (sq_nonneg _)
  -- the middle moment: the x-resolution read at v
  have hres := corner_oneAxisZero_outside_xResolve D hxy hxz hyz hlam hunit hgap hax
  have hmid : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v) = (1 - D.weight x) * ξ := by
    have hdot := congrArg (fun wv : Fin 3 → ℝ => wv ⬝ᵥ v) hres
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at hdot
    rw [hxi]
    exact hdot
  -- the closing moment: the x-mass
  have hmass := corner_oneAxisZero_outside_xMass D hxy hxz hyz hlam hunit hgap hax
  -- expand the deflated form
  have hexp : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * (D.atom d ⬝ᵥ v') ^ 2
      = ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
        - 2 * ξ * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d * (D.atom d ⬝ᵥ D.atom x) * (D.atom d ⬝ᵥ v)
        + ξ ^ 2 * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d * (D.atom d ⬝ᵥ D.atom x) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hread d]
    ring
  rw [hexp, hmid, hmass] at hnn
  -- the weighted form is exactly the outside form minus the erased mass
  have hweighted : (1 - D.weight x) * ξ ^ 2
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * (D.atom d ⬝ᵥ v) ^ 2 := by
    nlinarith [hnn]
  have hcap : ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d * (D.atom d ⬝ᵥ v) ^ 2
      ≤ ms * ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd =>
      mul_le_mul_of_nonneg_right (hmd d hd) (sq_nonneg _)
  linarith

/-! ## 3. The Loewner floor of the anchor -/

/-- The erase-`x` five-set splits into the two axis-carrying inside atoms and
the outside triple. -/
theorem erase_eq_insert_insert_compl {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (univ : Finset (Fin m)).erase x
      = insert y (insert z (({x, y, z} : Finset (Fin m))ᶜ)) := by
  ext a
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
    Finset.mem_compl, Finset.mem_singleton]
  constructor
  · intro hax
    by_cases hay : a = y
    · exact Or.inl hay
    by_cases haz : a = z
    · exact Or.inr (Or.inl haz)
    refine Or.inr (Or.inr ?_)
    intro hmem
    rcases hmem with h | h | h
    · exact hax h
    · exact hay h
    · exact haz h
  · rintro (rfl | rfl | h)
    · exact Ne.symm hxy
    · exact Ne.symm hxz
    · intro hax
      exact h (Or.inl hax)

/-- The anchor gap is the frame boost plus the outside gap of the erased
direction. -/
theorem corner_oneAxisZero_anchor_split (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D ((univ : Finset (Fin m)).erase x)
      = atomMatrix (D.atom y) + atomMatrix (D.atom z)
        + subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) := by
  classical
  have hyC : y ∉ insert z (({x, y, z} : Finset (Fin m))ᶜ) := by
    simp [hyz]
  have hzC : z ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  rw [subsetSum, subsetSum, erase_eq_insert_insert_compl hxy hxz hyz,
    Finset.sum_insert hyC, Finset.sum_insert hzC]
  abel

/-- **THE LOEWNER FLOOR OF THE ANCHOR.**  At a `Z1` corner the anchor gap
dominates the stretched axis atom and the coweighted erased atom together:
`ms·B ⪰ ms·lam·uuᵀ + (1 − t_x − ms)·g_x g_xᵀ`, read at every direction.  The
frame pair pays the two inside atoms, the erased over-coverage pays the
outside, and the orthonormal resolution closes the square. -/
theorem corner_oneAxisZero_anchor_loewner (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (v : Fin 3 → ℝ) :
    ms * lam * (u ⬝ᵥ v) ^ 2 + (1 - D.weight x - ms) * (D.atom x ⬝ᵥ v) ^ 2
      ≤ ms * (v ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1) *ᵥ v)) := by
  classical
  obtain ⟨w, hwunit, hwu, hwx, hframe⟩ :=
    corner_oneAxisZero_frame_pair D hxy hxz hyz hlam hunit hgap hax haz
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  -- the quadratic form of the anchor through the split and the frame pair
  have hquad := quadForm_subsetSum_sub_one D ((univ : Finset (Fin m)).erase x) v
  have hframe_read : (D.atom y ⬝ᵥ v) ^ 2 + (D.atom z ⬝ᵥ v) ^ 2
      = (1 + lam) * (u ⬝ᵥ v) ^ 2 + (w ⬝ᵥ v) ^ 2 := by
    have hread := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => v ⬝ᵥ (M *ᵥ v)) hframe
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul] at hread
    rw [show atomMatrix (D.atom y) = Matrix.vecMulVec (D.atom y) (D.atom y) from rfl,
      show atomMatrix (D.atom z) = Matrix.vecMulVec (D.atom z) (D.atom z) from rfl,
      show atomMatrix u = Matrix.vecMulVec u u from rfl,
      show atomMatrix w = Matrix.vecMulVec w w from rfl,
      quadForm_atomMatrix, quadForm_atomMatrix, quadForm_atomMatrix,
      quadForm_atomMatrix] at hread
    exact hread
  have hsum_read : ∑ a ∈ (univ : Finset (Fin m)).erase x, (D.atom a ⬝ᵥ v) ^ 2
      = (D.atom y ⬝ᵥ v) ^ 2 + (D.atom z ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    have hyC : y ∉ insert z (({x, y, z} : Finset (Fin m))ᶜ) := by
      simp [hyz]
    have hzC : z ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
    rw [erase_eq_insert_insert_compl hxy hxz hyz, Finset.sum_insert hyC,
      Finset.sum_insert hzC]
    try ring
  -- the orthonormal resolution of the squared length
  have hxu : u ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hax
  have hwx' : w ⬝ᵥ D.atom x = 0 := by rw [dotProduct_comm]; exact hwx
  have hres := read_sq_orthonormal_resolution hunit hwunit hlev hwu hxu hwx' v
  -- the over-coverage of the erased direction
  have hcover := corner_oneAxisZero_outside_overCoverage D hxy hxz hyz hlam hunit
    hgap hax hmd v
  -- assemble
  have hquad' : v ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1) *ᵥ v)
      = lam * (u ⬝ᵥ v) ^ 2 - (D.atom x ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2 := by
    rw [hquad, hsum_read, hframe_read]
    have hvv : v ⬝ᵥ v = (u ⬝ᵥ v) ^ 2 + (w ⬝ᵥ v) ^ 2 + (D.atom x ⬝ᵥ v) ^ 2 :=
      hres.symm
    rw [hvv]
    ring
  have hchain : ms * (lam * (u ⬝ᵥ v) ^ 2 - (D.atom x ⬝ᵥ v) ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), (D.atom d ⬝ᵥ v) ^ 2)
      ≥ ms * lam * (u ⬝ᵥ v) ^ 2 - ms * (D.atom x ⬝ᵥ v) ^ 2
        + (1 - D.weight x) * (D.atom x ⬝ᵥ v) ^ 2 := by
    nlinarith [hcover]
  rw [hquad']
  nlinarith [hchain]

/-! ## 4. The axis and erased caps -/

/-- **THE AXIS AND ERASED CAPS OF THE ANCHOR.**  The anchor's inverse gap
reads the axis at most at `1/lam` and the erased atom at most at
`ms/(1 − t_x − ms)`, jointly: the Loewner floor caps the two-vector Gram at
the identity.  Tie-free.  At the witness the erased cap is exact:
`κ·X = 1` at `ms = 44/201`. -/
theorem corner_oneAxisZero_anchor_axis_cap (D : WeightedDesign m 3) (hm : 3 ≤ m)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (hmx : D.weight x + ms < 1) :
    lam * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹ *ᵥ u)) ≤ 1
    ∧ (1 - D.weight x - ms)
        * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom x)) ≤ ms
    ∧ lam * (1 - D.weight x - ms)
        * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom x)) ^ 2
      ≤ (1 - lam * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ u)))
        * (ms - (1 - D.weight x - ms)
            * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
                *ᵥ D.atom x))) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin m)).erase x) - 1 with hB
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : B.PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  set κ : ℝ := (1 - D.weight x - ms) / ms with hκ
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    have : 0 ≤ 1 - D.weight x - ms := by linarith
    positivity
  set q : Fin 3 → ℝ := Real.sqrt lam • u with hq
  set r : Fin 3 → ℝ := Real.sqrt κ • D.atom x with hr
  have hqq : Matrix.vecMulVec q q = lam • atomMatrix u := by
    rw [hq, show Matrix.vecMulVec (Real.sqrt lam • u) (Real.sqrt lam • u)
      = atomMatrix (Real.sqrt lam • u) from rfl, atomMatrix_smul,
      Real.sq_sqrt hlam]
  have hrr : Matrix.vecMulVec r r = κ • atomMatrix (D.atom x) := by
    rw [hr, show Matrix.vecMulVec (Real.sqrt κ • D.atom x) (Real.sqrt κ • D.atom x)
      = atomMatrix (Real.sqrt κ • D.atom x) from rfl, atomMatrix_smul,
      Real.sq_sqrt hκ0]
  -- the Loewner floor gives PSD of the double downdate
  have hpsd : (B - Matrix.vecMulVec q q - Matrix.vecMulVec r r).PosSemidef := by
    rw [hqq, hrr]
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun v => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_smul,
        Matrix.transpose_smul, hB, transpose_subsetSum_sub_one D _,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix u).1,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom x)).1]
    · rw [star_trivial, Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub,
        dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul,
        dotProduct_smul]
      simp only [smul_eq_mul]
      rw [show atomMatrix u = Matrix.vecMulVec u u from rfl,
        show atomMatrix (D.atom x) = Matrix.vecMulVec (D.atom x) (D.atom x) from rfl,
        quadForm_atomMatrix, quadForm_atomMatrix]
      have hfloor := corner_oneAxisZero_anchor_loewner D hxy hxz hyz hlam hunit
        hgap hax haz hmd v
      rw [← hB] at hfloor
      have hκval : κ * ms = 1 - D.weight x - ms := by
        rw [hκ]
        field_simp
      nlinarith [hfloor, hms]
  obtain ⟨hQ, hR, hcross⟩ := psd_pair_gram_cap hPD q r hpsd
  -- rewrite the readings
  have hlam2 : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam
  have hκ2 : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ0
  have hread_q : q ⬝ᵥ (B⁻¹ *ᵥ q) = lam * (u ⬝ᵥ (B⁻¹ *ᵥ u)) := by
    rw [hq, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hlam2]
  have hread_r : r ⬝ᵥ (B⁻¹ *ᵥ r) = κ * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) := by
    rw [hr, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hκ2]
  have hread_c : (q ⬝ᵥ (B⁻¹ *ᵥ r)) ^ 2
      = lam * κ * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) ^ 2 := by
    rw [hq, hr, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    calc (Real.sqrt lam * (Real.sqrt κ * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)))) ^ 2
        = Real.sqrt lam * Real.sqrt lam * (Real.sqrt κ * Real.sqrt κ)
          * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) ^ 2 := by ring
      _ = lam * κ * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) ^ 2 := by rw [hlam2, hκ2]
  rw [hread_q] at hQ
  rw [hread_r] at hR
  rw [hread_c, hread_q, hread_r] at hcross
  have hκms : κ * ms = 1 - D.weight x - ms := by
    rw [hκ]
    field_simp
  refine ⟨hQ, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hR hms.le
    calc (1 - D.weight x - ms) * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x))
        = κ * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) * ms := by
          rw [mul_right_comm, hκms]
      _ ≤ 1 * ms := by linarith
      _ = ms := one_mul ms
  · have hstep := mul_le_mul_of_nonneg_right hcross hms.le
    calc lam * (1 - D.weight x - ms) * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) ^ 2
        = (lam * κ * (u ⬝ᵥ (B⁻¹ *ᵥ D.atom x)) ^ 2) * ms := by
          rw [← hκms]
          ring
      _ ≤ ((1 - lam * (u ⬝ᵥ (B⁻¹ *ᵥ u)))
            * (1 - κ * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x)))) * ms := hstep
      _ = (1 - lam * (u ⬝ᵥ (B⁻¹ *ᵥ u)))
            * (ms - κ * ms * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x))) := by
          ring
      _ = (1 - lam * (u ⬝ᵥ (B⁻¹ *ᵥ u)))
            * (ms - (1 - D.weight x - ms)
                * (D.atom x ⬝ᵥ (B⁻¹ *ᵥ D.atom x))) := by
          rw [hκms]

/-! ## 5. The exact reading identities of the anchor -/

/-- **THE OUTSIDE READING TOTAL.**  At the `Z1` anchor the three outside
readings total exactly `3 + X − lam·U`: the outside atom sum is the anchor gap
plus the erased atom minus the stretched axis.  An identity — no tie, no
cap. -/
theorem corner_oneAxisZero_anchor_outside_total (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
        D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
          *ᵥ D.atom d)
      = 3 + D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom x)
        - lam * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ u)) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin m)).erase x) - 1 with hB
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : B.PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  obtain ⟨w, hwunit, hwu, hwx, hframe⟩ :=
    corner_oneAxisZero_frame_pair D hxy hxz hyz hlam hunit hgap hax haz
  -- the outside atom sum in anchor coordinates
  have hres := atomMatrix_orthonormal_resolution hunit hwunit hlev hwu
    (by rw [dotProduct_comm]; exact hax) (by rw [dotProduct_comm]; exact hwx)
  have hsplit := corner_oneAxisZero_anchor_split D hxy hxz hyz
  have hMo : subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
      = B + atomMatrix (D.atom x) - lam • atomMatrix u := by
    have hstep : subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
        = subsetSum D ((univ : Finset (Fin m)).erase x)
          - (atomMatrix (D.atom y) + atomMatrix (D.atom z)) := by
      rw [hsplit]
      abel
    rw [hstep, hframe]
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ)
        = atomMatrix u + atomMatrix w + atomMatrix (D.atom x) := hres.symm
    have hBS : subsetSum D ((univ : Finset (Fin m)).erase x) = B + 1 := by
      rw [hB]
      abel
    rw [hBS, hone, add_smul, one_smul]
    abel
  -- trace both sides against the inverse gap
  have htr : ∀ (s : Finset (Fin m)),
      Matrix.trace (B⁻¹ * subsetSum D s)
        = ∑ a ∈ s, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) := by
    intro s
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun a _ => trace_mul_atomMatrix B⁻¹ (D.atom a)
  have htrace := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ
    => Matrix.trace (B⁻¹ * M)) hMo
  rw [htr] at htrace
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.mul_smul, Matrix.trace_smul] at htrace
  rw [Matrix.nonsing_inv_mul B hdet, Matrix.trace_one, trace_mul_atomMatrix,
    trace_mul_atomMatrix] at htrace
  rw [htrace, Fintype.card_fin]
  simp only [smul_eq_mul]
  norm_num

/-- **THE TRACE IDENTITY OF THE ANCHOR.**  The whole inverse-gap trace is the
two inside readings plus the erased reading minus the stretched axis reading:
`tr B⁻¹ = R_yy + R_zz + X − lam·U`.  An identity — no tie. -/
theorem corner_oneAxisZero_anchor_trace_identity (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    Matrix.trace (subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
      = D.atom y ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
          *ᵥ D.atom y)
        + D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom z)
        + D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom x)
        - lam * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ u)) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin m)).erase x) - 1 with hB
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : B.PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  have hdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have htr : ∀ (s : Finset (Fin m)),
      Matrix.trace (B⁻¹ * subsetSum D s)
        = ∑ a ∈ s, D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) := by
    intro s
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun a _ => trace_mul_atomMatrix B⁻¹ (D.atom a)
  -- the five-set trace: members total three plus the trace
  have hfive : ∑ a ∈ (univ : Finset (Fin m)).erase x,
      D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a) = 3 + Matrix.trace B⁻¹ := by
    have hBS : subsetSum D ((univ : Finset (Fin m)).erase x) = B + 1 := by
      rw [hB]
      abel
    have h := htr ((univ : Finset (Fin m)).erase x)
    rw [hBS, Matrix.mul_add, Matrix.trace_add, Matrix.nonsing_inv_mul B hdet,
      Matrix.trace_one, Matrix.mul_one, Fintype.card_fin] at h
    rw [← h]
    norm_num
  -- the five-set splits into the two inside atoms and the outside
  have hyC : y ∉ insert z (({x, y, z} : Finset (Fin m))ᶜ) := by
    simp [hyz]
  have hzC : z ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  have hsum : ∑ a ∈ (univ : Finset (Fin m)).erase x,
      D.atom a ⬝ᵥ (B⁻¹ *ᵥ D.atom a)
      = D.atom y ⬝ᵥ (B⁻¹ *ᵥ D.atom y) + D.atom z ⬝ᵥ (B⁻¹ *ᵥ D.atom z)
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom d) := by
    rw [erase_eq_insert_insert_compl hxy hxz hyz, Finset.sum_insert hyC,
      Finset.sum_insert hzC]
    try ring
  have houtside := corner_oneAxisZero_anchor_outside_total D hm hxy hxz hyz
    hlam hunit hgap hax haz
  rw [← hB] at houtside
  rw [hsum, houtside] at hfive
  linarith

/-- **THE OUTSIDE READING WINDOW.**  With the axis cap, the outside reading
total sits in the exact window `[2 + X, 3 + X]`: the three outside atoms
always over-read the anchor by at least two plus the whole erased reading. -/
theorem corner_oneAxisZero_anchor_outside_window (D : WeightedDesign m 3)
    (hm : 3 ≤ m) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    {ms : ℝ} (hms : 0 < ms)
    (hmd : ∀ d ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight d ≤ ms)
    (hmx : D.weight x + ms < 1) :
    2 + D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
          *ᵥ D.atom x)
      ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom d)
    ∧ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
          D.atom d ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
            *ᵥ D.atom d)
      ≤ 3 + D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
          *ᵥ D.atom x) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin m)).erase x) - 1 with hB
  have hlev := corner_oneAxisZero_unit D _ (card_triple_eq hxy hxz hyz) hlam
    hunit hgap (by simp : x ∈ ({x, y, z} : Finset (Fin m))) hax
  have hPD : B.PosDef :=
    complement_erase_posDef_of_leverage_le_one D hm hlev.le
  have htotal := corner_oneAxisZero_anchor_outside_total D hm hxy hxz hyz
    hlam hunit hgap hax haz
  rw [← hB] at htotal
  obtain ⟨hcap, -, -⟩ := corner_oneAxisZero_anchor_axis_cap D hm hxy hxz hyz
    hlam hunit hgap hax haz hms hmd hmx
  rw [← hB] at hcap
  have hU0 : 0 ≤ u ⬝ᵥ (B⁻¹ *ᵥ u) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hPD.inv.posSemidef).2 u
    rwa [star_trivial] at h
  constructor
  · rw [htotal]
    nlinarith [hcap]
  · rw [htotal]
    nlinarith [mul_nonneg hlam hU0]

/-! ## 6. The trace pinch of a tie -/

/-- **THE FIVE-SET TRACE PINCH.**  At a tie, the pair floors of a strictly
dominating five-set meet the full weighted Parseval trace: every member atom
is pinched against the whole inverse-gap trace,

  `(Σ_{d ∈ F, d ≠ e} t_d)(1 − R_e) + t_e R_e + Σ_{b ∉ F} t_b R_b ≤ tr B⁻¹`.

Any size, any five-set. -/
theorem tie_fiveSet_trace_pinch (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 5)
    (hPD : (subsetSum D F - 1).PosDef) {e : Fin m} (he : e ∈ F) :
    (∑ d ∈ F.erase e, D.weight d)
        * (1 - D.atom e ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom e))
      + D.weight e * (D.atom e ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom e))
      + ∑ b ∈ Fᶜ, D.weight b * (D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b))
      ≤ Matrix.trace (subsetSum D F - 1)⁻¹ := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  -- the full weighted Parseval trace
  have hfull : ∑ c, D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c))
      = Matrix.trace B⁻¹ := by
    have htr : Matrix.trace (B⁻¹ * ∑ c, D.weight c • atomMatrix (D.atom c))
        = ∑ c, D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
    rw [← htr, D.isParseval, Matrix.mul_one]
  -- split the trace over the five-set and its complement, then off the pivot
  have hsplit := Finset.sum_add_sum_compl F
    (fun c => D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)))
  rw [hfull] at hsplit
  have hpivot := Finset.add_sum_erase F
    (fun c => D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c))) he
  -- the pair floors at the pivot
  have hpairs : ∀ d ∈ F.erase e,
      D.weight d ≤ D.weight d * (D.atom e ⬝ᵥ (B⁻¹ *ᵥ D.atom e))
        + D.weight d * (D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom d)) := by
    intro d hd
    have hdF := Finset.mem_of_mem_erase hd
    have hde : d ≠ e := Finset.ne_of_mem_erase hd
    have hfloor := tie_fiveSet_pair_floor D htie F hF hPD hdF he hde
    rw [← hB] at hfloor
    nlinarith [D.weight_pos d, hfloor]
  have hpairsum := Finset.sum_le_sum hpairs
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hpairsum
  linarith [hsplit, hpivot, hpairsum]

/-- **THE ANCHOR PINCH OF THE `Z1` STRATUM.**  At a `(6,3)` tie with a `Z1`
corner, every anchored atom `e` is pinched against the anchor trace with the
erased reading riding along:

  `(1 − t_x − t_e)(1 − R_e) + t_e R_e + t_x X ≤ tr B⁻¹`. -/
theorem corner_oneAxisZero_anchor_pinch (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    {e : Fin 6} (he : e ∈ (univ : Finset (Fin 6)).erase x) :
    (1 - D.weight x - D.weight e)
        * (1 - D.atom e ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom e))
      + D.weight e
        * (D.atom e ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom e))
      + D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom x))
      ≤ Matrix.trace (subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ := by
  classical
  set F : Finset (Fin 6) := (univ : Finset (Fin 6)).erase x with hF
  have hFcard : F.card = 5 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hPD : (subsetSum D F - 1).PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  have hcompl : (Fᶜ : Finset (Fin 6)) = {x} := by
    rw [hF, Finset.compl_erase, Finset.compl_univ]
    rfl
  have hpinch := tie_fiveSet_trace_pinch D htie F hFcard hPD he
  rw [hcompl, Finset.sum_singleton] at hpinch
  -- the erased-weight total of the five-set
  have hweights : ∑ d ∈ F.erase e, D.weight d
      = 1 - D.weight x - D.weight e := by
    have h1 := Finset.add_sum_erase (univ : Finset (Fin 6)) D.weight
      (Finset.mem_univ x)
    rw [D.weight_sum_one] at h1
    have h2 := Finset.add_sum_erase F D.weight he
    rw [hF] at h2 ⊢
    linarith
  rw [hweights] at hpinch
  exact hpinch

/-- **THE OUTSIDE PINCH OF THE `Z1` ANCHOR.**  At a `(6,3)` tie with a `Z1`
corner, pairing an axis-carrying inside atom `e` against the three outside
atoms only — and keeping both inside readings explicit — sharpens the anchor
pinch: with `τ = Σ_{d ∈ Cᶜ} t_d`,

  `τ(1 − R_ee) + t_x X + t_y R_yy + t_z R_zz ≤ tr B⁻¹`.

The general pinch at `e = z` is this law weakened through the `y`-`z` pair
floor. -/
theorem corner_oneAxisZero_outside_pinch (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) {e : Fin 6} (he : e = y ∨ e = z) :
    (∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d)
        * (1 - D.atom e ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom e))
      + D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom x))
      + D.weight y
        * (D.atom y ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom y))
      + D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom z))
      ≤ Matrix.trace (subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ := by
  classical
  set F : Finset (Fin 6) := (univ : Finset (Fin 6)).erase x with hF
  set B : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hB
  have hFcard : F.card = 5 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hPD : B.PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  have heC : e ∈ ({x, y, z} : Finset (Fin 6)) := by
    rcases he with rfl | rfl <;> simp
  have heF : e ∈ F := by
    rw [hF]
    rcases he with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hxz, Finset.mem_univ _⟩
  -- the full weighted Parseval trace, split at the corner
  have hfull : ∑ c, D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c))
      = Matrix.trace B⁻¹ := by
    have htr : Matrix.trace (B⁻¹ * ∑ c, D.weight c • atomMatrix (D.atom c))
        = ∑ c, D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)) := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
    rw [← htr, D.isParseval, Matrix.mul_one]
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
    (fun c => D.weight c * (D.atom c ⬝ᵥ (B⁻¹ *ᵥ D.atom c)))
  rw [hfull, sum_triple_eq hxy hxz hyz] at hsplit
  -- the pair floors of e against the outside atoms
  have hpairs : ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      D.weight d ≤ D.weight d * (D.atom e ⬝ᵥ (B⁻¹ *ᵥ D.atom e))
        + D.weight d * (D.atom d ⬝ᵥ (B⁻¹ *ᵥ D.atom d)) := by
    intro d hd
    have hdC : d ∉ ({x, y, z} : Finset (Fin 6)) := Finset.mem_compl.mp hd
    have hdF : d ∈ F := by
      rw [hF]
      exact Finset.mem_erase.mpr ⟨fun h => hdC (h ▸ by simp), Finset.mem_univ d⟩
    have hde : d ≠ e := fun h => hdC (h ▸ heC)
    have hfloor := tie_fiveSet_pair_floor D htie F hFcard hPD hdF heF hde
    rw [← hB] at hfloor
    nlinarith [D.weight_pos d, hfloor]
  have hpairsum := Finset.sum_le_sum hpairs
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hpairsum
  linarith [hsplit, hpairsum]

/-! ## 7. The heavy-inside cell at the anchor -/

/-- **THE HEAVY-INSIDE ANCHOR READING.**  When the four-set through `z`
fails, the kept inside atom `y` reads the anchor's inverse gap at least at
one — with no tie: the anchor minus the kept atom IS the failed four-set. -/
theorem corner_oneAxisZero_heavyInside_anchor_reading (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    1 ≤ D.atom y ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom y) := by
  classical
  set B : Matrix (Fin 3) (Fin 3) ℝ :=
    subsetSum D ((univ : Finset (Fin 6)).erase x) - 1 with hB
  have hPD : B.PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  have hyF : y ∈ (univ : Finset (Fin 6)).erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_univ y⟩
  have hset : ((univ : Finset (Fin 6)).erase x).erase y
      = insert z (({x, y, z} : Finset (Fin 6))ᶜ) := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert,
      Finset.mem_compl, Finset.mem_singleton]
    constructor
    · rintro ⟨hay, hax'⟩
      by_cases haz : a = z
      · exact Or.inl haz
      refine Or.inr ?_
      intro hmem
      rcases hmem with h | h | h
      · exact hax' h
      · exact hay h
      · exact haz h
    · rintro (rfl | h)
      · exact ⟨Ne.symm hyz, Ne.symm hxz⟩
      · exact ⟨fun hay => h (Or.inr (Or.inl hay)),
          fun hax' => h (Or.inl hax')⟩
  have hdown : subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1
      = B - Matrix.vecMulVec (D.atom y) (D.atom y) := by
    rw [← hset, ← subsetSum_erase_sub_one_rankOne D ((univ : Finset (Fin 6)).erase x) hyF]
  by_contra hlt
  push Not at hlt
  exact hnotz (by
    rw [hdown]
    exact (posDef_sub_vecMulVec_iff B hPD (D.atom y)).mpr hlt)

/-- **The heavy-inside anchor reading, `y` and `z` exchanged.** -/
theorem corner_oneAxisZero_heavyInside_anchor_reading' (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hnoty : ¬ (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    1 ≤ D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom z) := by
  have hset : ({x, z, y} : Finset (Fin 6)) = ({x, y, z} : Finset (Fin 6)) := by
    ext c
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  exact corner_oneAxisZero_heavyInside_anchor_reading D hxz hxy (Ne.symm hyz)
    hlam hunit (by rw [hset]; exact hgap) hax (by rw [hset]; exact hnoty)

/-- **THE ANCHOR TENSION OF A `Z1` TIE.**  The outside pinch at `e = z` runs
against the trace identity: with `τ = Σ_{d ∈ Cᶜ} t_d`,

  `τ(1 − R_zz) + t_x X + t_y R_yy + t_z R_zz + lam·U ≤ R_yy + R_zz + X`.

In the heavy-inside cell the geometry holds `R_yy ≥ 1` for free
(`Gtz.corner_oneAxisZero_heavyInside_anchor_reading`); measured on 1.6·10⁵
fresh heavy-inside samples the tension already fails at 76.5% of them, so the
cell is refuted exactly when the geometry drives the right side below the
left on the remaining share. -/
theorem corner_oneAxisZero_anchor_tension (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0) :
    (∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d)
        * (1 - D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom z))
      + D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom x))
      + D.weight y
        * (D.atom y ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom y))
      + D.weight z
        * (D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom z))
      + lam * (u ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹ *ᵥ u))
      ≤ D.atom y ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
          *ᵥ D.atom y)
        + D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom z)
        + D.atom x ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom x) := by
  have hpinch := corner_oneAxisZero_outside_pinch D htie hxy hxz hyz hlam hunit
    hgap hax (Or.inr rfl)
  have hid := corner_oneAxisZero_anchor_trace_identity D (by norm_num)
    hxy hxz hyz hlam hunit hgap hax haz
  linarith [hpinch, hid]

end Gtz
