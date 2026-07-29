/-
# The `(7,3)` caps-and-gates layer: single-clause domination, determinant caps,
# battlefield polynomials

Everything here lives on the uniform-share stratum of rank-three designs, where the
direction Gram obeys `Gamma^2 = shareValue⁻¹ • Gamma`
(`Gtz.directionGramMatrix_sq_of_uniformShare`).  At `(7,3)` the share is `3/7` and the
scale is `7/3`.

**The one-line cap.**  From the quadratic law and symmetry,
`scale • 1 - Gamma = scale⁻¹ • (scale • 1 - Gamma)^2 ⪰ 0` — no eigenvalues, no
interlacing (`Gtz.posSemidef_smul_one_sub_of_mul_self_eq_smul`).  Compressed at a
triple this is the spectral cap `(shareValue⁻¹ - 1) • 1 - M[T] ⪰ 0` on the hollow
block of the three direction cosines; at `(7,3)` the cap is `4/3`, exactly the hinge
value `cap = 2 * level` of the shipped criterion
`Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds`.

**(C1-IFF), the single-clause criterion.**  Feeding the cap into the shipped
criterion and the shipped free-weight dictionary
`Gtz.dominates_triple_iff_posSemidef_slackHollowThree` collapses the seven-clause
domination test to ONE inequality on a leverage-three triple of a uniform-share
design with `3/7 ≤ shareValue` (equivalently size at most seven, the hinge boundary
`Gtz.uniformStratumCap_le_hinge_iff_size_le_seven`):

    Dominates {a,b,c}  ↔  sigma_T - 3 P_T ≤ 4/9,

stated through the shipped scalar `Gtz.orientedTripleResidual`.  The pairwise clauses
`w ≤ 4/9` are consequences (`Gtz.edgeWeight_le_four_ninths_of_dominates_triple`), not
extra conjuncts.  Both residual cells instantiate: `(6,3)` at share `1/2` and `(7,3)`
at share `3/7`.

**The two determinant caps.**  `det Gamma[T] ≥ 0` reads
`sigma ≤ 1 + 2P` (share-free; for frustrated triples `sigma + 2|P| ≤ 1`), and
`det((4/3) • 1 - M[T]) ≥ 0` reads `sigma + (3/2) P ≤ 16/9` — the coherent cap.  Their
positive combination `3 · det + 4 · coherent` kills the product term and pins the
`(7,3)` triple mass cap `sigma_T ≤ 13/9`, confirming the campaign's previously
UNVERIFIED chart maximum: the corner `(sigma, P) = (13/9, 2/9)` saturates both caps
and fails the criterion (`residual = 7/9 > 4/9`), so `13/9` is exact on the
`(sigma, P)` chart (`Gtz.failingChartCorner_thirteen_ninths`).  The corner is realised
by unit vectors (a parallel pair plus a third at squared cosine `2/9`); whether a full
`(7,3)`-uniform design attains it is open.

**The gates.**  Light per-triple gate: three edges of weight at most `1/9` force
`residual ≤ 1/3 + 1/9 = 4/9`, hence domination, with equality exactly at the
tetrahedral tie `gamma ≡ -1/3`.  Heavy gate, RIGID: three edges of weight at least
`4/9` are frozen — the caps force `w ≡ 4/9` and `P = +8/27` exactly, hence
`residual = 4/9`, a tie; so `m ≥ 4/9` (some triple with min-edge `≥ 4/9`) closes with
margin zero.  Both tie blocks are landed as PSD matrices with vanishing determinant.
Every failing triple therefore has min-edge `< 4/9` AND max-edge `> 1/9` — the open
middle band `(1/9, 4/9)` of the endpoint cubic
`rho(m) = 9m^3 - 9m^2 + (8/3)m - 16/81 = 9(m - 1/9)(m - 4/9)^2`.

**The battlefield polynomials.**  `rho`'s factorisation (simple root at the light
gate, double root at the heavy gate) and the `(6,3)` non-transfer certificate
`Psi(r) = 16/9 - 4r^3 - 16r^4 + (81/4)r^6 + (27/2)r^7`.  `Psi` factors as
`(r - 2/3)^2 · q(r)` with `q` of ALL POSITIVE coefficients — so `Psi(2/3) = 0` is a
DOUBLE root (`Psi'(2/3) = 0`, sharper than the campaign note recorded) and `Psi > 0`
on the whole of `[0, ∞) \ {2/3}`, not merely on `(0, 2/3)`: the U6 squeeze constant
is an isolated tangency.

**Not landed here** (recorded so silence is not mistaken for closure): the light
SQUEEZE (`max-min edge ≤ 1/9` forces coverage — a global covering argument, not
per-triple), design-side attainment of the `13/9` chart corner, and any statement at
free weights.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.WeightedTripleCriterion
import Gtz.Quantitative.GTransformGate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The battlefield polynomials, exactly -/

/-- **The band endpoint cubic factors.**  `rho(m) = 9m^3 - 9m^2 + (8/3)m - 16/81`
has a simple root at the light gate `1/9` and a DOUBLE root at the heavy gate `4/9`;
the open middle band `(1/9, 4/9)` between them is exactly the regime the per-triple
gates below do not close. -/
theorem bandGateCubic_factorisation (edgeValue : ℝ) :
    9 * edgeValue ^ 3 - 9 * edgeValue ^ 2 + (8 / 3) * edgeValue - 16 / 81
      = 9 * (edgeValue - 1 / 9) * (edgeValue - 4 / 9) ^ 2 := by
  ring

/-- The light gate `m = 1/9` is a root of the endpoint cubic. -/
theorem bandGateCubic_vanishes_at_lightGate :
    9 * ((1 : ℝ) / 9) ^ 3 - 9 * ((1 : ℝ) / 9) ^ 2 + (8 / 3) * ((1 : ℝ) / 9) - 16 / 81 = 0 := by
  norm_num

/-- The heavy gate `m = 4/9` is a (double) root of the endpoint cubic. -/
theorem bandGateCubic_vanishes_at_heavyGate :
    9 * ((4 : ℝ) / 9) ^ 3 - 9 * ((4 : ℝ) / 9) ^ 2 + (8 / 3) * ((4 : ℝ) / 9) - 16 / 81 = 0 := by
  norm_num

/-- **The `(6,3)` non-transfer certificate factors with a DOUBLE root at `2/3`.**
`Psi(r) = 16/9 - 4r^3 - 16r^4 + (81/4)r^6 + (27/2)r^7` is `(r - 2/3)^2` times a
quintic with all positive coefficients.  The campaign note recorded only the simple
vanishing `Psi(2/3) = 0`; the factorisation shows the tangency is second order
(`Psi'(2/3) = 0` as well), which is the sharp form of "the U6 squeeze provably does
not transport". -/
theorem squeezeNonTransferSeptic_factorisation (ratio : ℝ) :
    16 / 9 - 4 * ratio ^ 3 - 16 * ratio ^ 4 + (81 / 4) * ratio ^ 6 + (27 / 2) * ratio ^ 7
      = (ratio - 2 / 3) ^ 2
        * ((27 / 2) * ratio ^ 5 + (153 / 4) * ratio ^ 4 + 45 * ratio ^ 3
            + 27 * ratio ^ 2 + 12 * ratio + 4) := by
  ring

/-- `Psi(2/3) = 0`, exactly. -/
theorem squeezeNonTransferSeptic_vanishes_at_twoThirds :
    16 / 9 - 4 * ((2 : ℝ) / 3) ^ 3 - 16 * ((2 : ℝ) / 3) ^ 4 + (81 / 4) * ((2 : ℝ) / 3) ^ 6
      + (27 / 2) * ((2 : ℝ) / 3) ^ 7 = 0 := by
  norm_num

/-- **`Psi > 0` away from its unique nonnegative root.**  On `[0, ∞)` the certificate
vanishes only at `2/3`: the square factor is positive off the root and the quintic
factor is at least its constant term `4`.  This subsumes the briefed statement
"`Psi > 0` on `(0, 2/3)`". -/
theorem squeezeNonTransferSeptic_pos_of_ne_twoThirds {ratio : ℝ} (hnonneg : 0 ≤ ratio)
    (hoffRoot : ratio ≠ 2 / 3) :
    0 < 16 / 9 - 4 * ratio ^ 3 - 16 * ratio ^ 4 + (81 / 4) * ratio ^ 6
      + (27 / 2) * ratio ^ 7 := by
  rw [squeezeNonTransferSeptic_factorisation]
  have hgap : ratio - 2 / 3 ≠ 0 := sub_ne_zero_of_ne hoffRoot
  have hsquare : 0 < (ratio - 2 / 3) ^ 2 := by
    rcases lt_or_gt_of_ne hgap with hbelow | habove
    · nlinarith [hbelow]
    · nlinarith [habove]
  have hquintic : 0 < (27 / 2) * ratio ^ 5 + (153 / 4) * ratio ^ 4 + 45 * ratio ^ 3
      + 27 * ratio ^ 2 + 12 * ratio + 4 := by
    have hcubePow : (0 : ℝ) ≤ ratio ^ 3 := pow_nonneg hnonneg 3
    have hquartPow : (0 : ℝ) ≤ ratio ^ 4 := pow_nonneg hnonneg 4
    have hquintPow : (0 : ℝ) ≤ ratio ^ 5 := pow_nonneg hnonneg 5
    have hsquarePow : (0 : ℝ) ≤ ratio ^ 2 := sq_nonneg ratio
    linarith [hcubePow, hquartPow, hquintPow, hsquarePow, hnonneg]
  exact mul_pos hsquare hquintic

/-- The briefed interval form: `Psi > 0` on the open interval `(0, 2/3)`. -/
theorem squeezeNonTransferSeptic_pos_of_lt_twoThirds {ratio : ℝ} (hlower : 0 < ratio)
    (hupper : ratio < 2 / 3) :
    0 < 16 / 9 - 4 * ratio ^ 3 - 16 * ratio ^ 4 + (81 / 4) * ratio ^ 6
      + (27 / 2) * ratio ^ 7 :=
  squeezeNonTransferSeptic_pos_of_ne_twoThirds hlower.le (ne_of_lt hupper)

/-! ## 2. The one-line spectral caps

A symmetric matrix with `form * form = scale • form` is a scaled projection; both
`form ⪰ 0` and `scale • 1 - form ⪰ 0` are one-line consequences.  The design instance
is the uniform-share direction Gram. -/

/-- **A symmetric scaled projection is positive semidefinite**:
`form = scale⁻¹ • (form * form)` and `form * form = formᵀ * form` is a Gram square. -/
theorem posSemidef_of_mul_self_eq_smul {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    {scale : ℝ} (hsymmetric : formᵀ = form) (hsquare : form * form = scale • form)
    (hpositive : 0 < scale) : form.PosSemidef := by
  have hgram : (form * formᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose form
  rw [hsymmetric] at hgram
  have hscaled : form = scale⁻¹ • (form * form) := by
    rw [hsquare, smul_smul, inv_mul_cancel₀ hpositive.ne', one_smul]
  rw [hscaled]
  exact (posSemidef_smul_iff (inv_pos.mpr hpositive)).mpr hgram

/-- **THE ONE-LINE CAP.**  For a symmetric scaled projection the complementary gap
`scale • 1 - form` is itself a scaled projection, hence positive semidefinite:
`(scale • 1 - form)^2 = scale • (scale • 1 - form)`.  Every principal compression
inherits the bound — no interlacing, no spectral theorem. -/
theorem posSemidef_smul_one_sub_of_mul_self_eq_smul {size : ℕ}
    {form : Matrix (Fin size) (Fin size) ℝ} {scale : ℝ} (hsymmetric : formᵀ = form)
    (hsquare : form * form = scale • form) (hpositive : 0 < scale) :
    (scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form).PosSemidef := by
  have hgapSymmetric : (scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form)ᵀ
      = scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsymmetric]
  have hgapSquare : (scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form)
        * (scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form)
      = scale • (scale • (1 : Matrix (Fin size) (Fin size) ℝ) - form) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [hsquare, smul_sub]
    abel
  exact posSemidef_of_mul_self_eq_smul hgapSymmetric hgapSquare hpositive

/-- **The design cap**: on a uniform-share design,
`shareValue⁻¹ • 1 - Gamma ⪰ 0`.  At `(7,3)` this is `(7/3) • 1 - Gamma ⪰ 0`, so every
principal block of the direction Gram has `lambda_max ≤ 7/3` and every hollow block
has `lambda_max ≤ 4/3`.  (A statement-identical twin is being landed concurrently as
`Gtz.posSemidef_smul_one_sub_directionGramMatrix_of_uniformShare` in
`Gtz.Quantitative.SevenThreeInvolution`; this private copy carries a different name
so that no silent duplicate global is created — integrator: keep one.) -/
theorem posSemidef_smul_one_sub_directionGramMatrix_of_atomShare_eq (D : WeightedDesign m k)
    {shareValue : ℝ} (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) :
    (shareValue⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) - directionGramMatrix D).PosSemidef := by
  have hsymmetric : (directionGramMatrix D)ᵀ = directionGramMatrix D := by
    ext rowIndex colIndex
    exact directionGram_comm D colIndex rowIndex
  exact posSemidef_smul_one_sub_of_mul_self_eq_smul hsymmetric
    (directionGramMatrix_sq_of_uniformShare D hshare hpositive) (inv_pos.mpr hpositive)

/-- **The Gram compression at a triple** IS the unit-diagonal correlation matrix of
its three direction cosines.  Triple-local nondegeneracy only, and no distinctness:
if two slots coincide, both sides carry the same self-correlation `1`.  (The shipped
`Gtz.correlationInvolution_submatrix_three_eq_hollowMatrixThree` is the hollow-part
reading under a GLOBAL nondegeneracy hypothesis; this is the local repair.) -/
theorem directionGramMatrix_submatrix_three_eq_correlationMatrixThree (D : WeightedDesign m k)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third)) :
    (directionGramMatrix D).submatrix ![first, second, third] ![first, second, third]
      = correlationMatrixThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Matrix.submatrix_apply, correlationMatrixThree] <;>
    first
      | exact directionGram_self D hfirst
      | exact directionGram_self D hsecond
      | exact directionGram_self D hthird
      | rfl
      | exact directionGram_comm D second first
      | exact directionGram_comm D third first
      | exact directionGram_comm D third second

/-- **The compressed cap**: at a triple of distinct atoms of a uniform-share design,
`(shareValue⁻¹ - 1) • 1 - M[T] ⪰ 0` where `M[T]` is the hollow block of the three
direction cosines.  At `(7,3)` the cap value is `7/3 - 1 = 4/3`. -/
theorem posSemidef_smul_one_sub_hollowSymmetricThree_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ((shareValue⁻¹ - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third)).PosSemidef := by
  have hlevPos : ∀ atomIndex : Fin m, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [hshare atomIndex]; exact hpositive)
  have hpick : Function.Injective ![first, second, third] :=
    injective_three_of_ne hfirstSecond hfirstThird hsecondThird
  have hcap := (posSemidef_smul_one_sub_directionGramMatrix_of_atomShare_eq D hshare
    hpositive).submatrix ![first, second, third]
  have hsplit : (shareValue⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)
        - directionGramMatrix D).submatrix ![first, second, third] ![first, second, third]
      = shareValue⁻¹ • ((1 : Matrix (Fin m) (Fin m) ℝ).submatrix ![first, second, third]
            ![first, second, third])
        - (directionGramMatrix D).submatrix ![first, second, third] ![first, second, third] :=
    rfl
  rw [hsplit, Matrix.submatrix_one _ hpick,
    directionGramMatrix_submatrix_three_eq_correlationMatrixThree D (hlevPos first)
      (hlevPos second) (hlevPos third),
    correlationMatrixThree_eq_one_add_hollowSymmetricThree] at hcap
  have hshape : shareValue⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ((1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
          + hollowSymmetricThree (directionGram D first second) (directionGram D first third)
              (directionGram D second third))
      = (shareValue⁻¹ - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree (directionGram D first second) (directionGram D first third)
            (directionGram D second third) := by
    rw [sub_smul, one_smul]
    abel
  rw [hshape] at hcap
  exact hcap

/-- **The `4/3` cap, padded across the hinge.**  As soon as the uniform share is at
least `3/7` — equivalently the size is at most seven — the compressed cap
`shareValue⁻¹ - 1 ≤ 4/3` upgrades to the exact hypothesis the shipped `(7,3)`
criterion instance consumes.  At `(6,3)` share `1/2` this pads a cap of `1` up to
`4/3`; at `(7,3)` share `3/7` the padding is zero. -/
theorem posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_of_uniformShare
    (D : WeightedDesign m k) {shareValue : ℝ}
    (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hfloor : 3 / 7 ≤ shareValue) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (((4 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (directionGram D first second) (directionGram D first third)
          (directionGram D second third)).PosSemidef := by
  have hpositive : (0 : ℝ) < shareValue := lt_of_lt_of_le (by norm_num) hfloor
  have hbase := posSemidef_smul_one_sub_hollowSymmetricThree_of_uniformShare D hshare hpositive
    hfirstSecond hfirstThird hsecondThird
  have hinv : shareValue⁻¹ ≤ 7 / 3 := by
    nlinarith [mul_inv_cancel₀ hpositive.ne', hfloor, hpositive,
      inv_pos.mpr hpositive]
  have hgap : (0 : ℝ) ≤ 4 / 3 - (shareValue⁻¹ - 1) := by linarith
  have hsum := hbase.add (Matrix.PosSemidef.one.smul hgap)
  have hscalar : (shareValue⁻¹ - 1) + (4 / 3 - (shareValue⁻¹ - 1)) = (4 : ℝ) / 3 := by ring
  have hshape : ((shareValue⁻¹ - 1) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree (directionGram D first second) (directionGram D first third)
            (directionGram D second third))
        + (4 / 3 - (shareValue⁻¹ - 1)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = ((4 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree (directionGram D first second) (directionGram D first third)
            (directionGram D second third) := by
    rw [sub_add_eq_add_sub, ← add_smul, hscalar]
  rw [hshape] at hsum
  exact hsum

/-! ## 3. (C1-IFF): the single-clause domination criterion -/

/-- The oriented criterion value in the two triple scalars:
`orientedTripleResidual = sigma_T - 3 P_T`. -/
theorem orientedTripleResidual_eq_sigma_sub_three_mul_product (D : WeightedDesign m k)
    (first second third : Fin m) :
    orientedTripleResidual D first second third
      = directionTripleSigma D first second third
        - 3 * directionTripleProduct D first second third := by
  rw [orientedTripleResidual, directionTripleSigma, directionTripleProduct, edgeWeight,
    edgeWeight, edgeWeight]

/-- **(C1-IFF), the master form.**  On a rank-three design of uniform share at least
`3/7` (the hinge: size at most seven), a triple of distinct leverage-three atoms
dominates IF AND ONLY IF its oriented criterion value is at most `4/9`:

    Dominates {a,b,c}  ↔  sigma_T - 3 P_T ≤ 4/9.

One inequality replaces the seven-clause test: forward is the determinant sign of the
PSD shift, backward is the rogue-branch kill supplied by the `4/3` cap through the
shipped hinge criterion.  Instantiates at `(6,3)` share `1/2` and `(7,3)` share
`3/7`; at larger sizes the share hypothesis is unsatisfiable, so nothing is claimed.
Leverage three is required only on the TRIPLE; the other atoms are free. -/
theorem dominates_triple_iff_orientedTripleResidual_le_four_ninths_of_uniformShare
    (D : WeightedDesign m 3) {shareValue : ℝ}
    (hshare : ∀ atomIndex, atomShare D atomIndex = shareValue) (hfloor : 3 / 7 ≤ shareValue)
    {first second third : Fin m} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ orientedTripleResidual D first second third ≤ 4 / 9 := by
  have hfirstPos : 0 < leverageOf (D.atom first) := by rw [hlevFirst]; norm_num
  have hsecondPos : 0 < leverageOf (D.atom second) := by rw [hlevSecond]; norm_num
  have hthirdPos : 0 < leverageOf (D.atom third) := by rw [hlevThird]; norm_num
  have hslackFirst : weightSlack D first = 2 / 3 := by rw [weightSlack, hlevFirst]; norm_num
  have hslackSecond : weightSlack D second = 2 / 3 := by rw [weightSlack, hlevSecond]; norm_num
  have hslackThird : weightSlack D third = 2 / 3 := by rw [weightSlack, hlevThird]; norm_num
  have hcap := posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_of_uniformShare D hshare
    hfloor hfirstSecond hfirstThird hsecondThird
  rw [dominates_triple_iff_posSemidef_slackHollowThree D hfirstPos hsecondPos hthirdPos
      hfirstSecond hfirstThird hsecondThird, hslackFirst, hslackSecond, hslackThird,
    slackHollowThree_self, hollowMatrixThree_eq_hollowSymmetricThree,
    posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds
      (le_refl ((2 : ℝ) / 3)) hcap,
    orientedTripleResidual, edgeWeight, edgeWeight, edgeWeight]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- **(C1-IFF) at `(7,3)`.**  On a `(7,3)` design of uniform share `3/7`, a triple of
distinct leverage-three atoms dominates iff `sigma_T - 3 P_T ≤ 4/9`. -/
theorem dominates_triple_iff_orientedTripleResidual_le_four_ninths_sevenThree
    (D : WeightedDesign 7 3) (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third : Fin 7} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates D {first, second, third}
      ↔ orientedTripleResidual D first second third ≤ 4 / 9 :=
  dominates_triple_iff_orientedTripleResidual_le_four_ninths_of_uniformShare D hshare
    (le_refl _) hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird

/-- **The theta-parametric criterion at `(7,3)`.**  For every threshold
`theta ≥ 2/3` (no upper bound needed — the brief's `theta ≤ 4/3` is not required),
the shifted hollow block of a distinct triple of a `(7,3)`-uniform design is positive
semidefinite iff the cubic clause holds:

    (theta • 1 + M[T]) ⪰ 0  ↔  theta sigma_T - 2 P_T ≤ theta^3.

No leverage hypothesis: this is a statement about the direction cosines alone. -/
theorem posSemidef_smul_one_add_hollowSymmetricThree_iff_sevenThree (D : WeightedDesign 7 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7) {level : ℝ}
    (hlevel : 2 / 3 ≤ level) {first second third : Fin 7} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree (directionGram D first second) (directionGram D first third)
            (directionGram D second third)).PosSemidef
      ↔ level * directionTripleSigma D first second third
          - 2 * directionTripleProduct D first second third ≤ level ^ 3 := by
  rw [posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds hlevel
      (posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_of_uniformShare D hshare
        (le_refl _) hfirstSecond hfirstThird hsecondThird),
    directionTripleSigma, directionTripleProduct]

/-- **The pairwise consequence.**  A dominating triple of leverage-three atoms has
every edge weight at most `4/9` — the `2x2` minors of the PSD shift, read off the
shipped seven-clause criterion.  Share-free and size-free: only the triple's
leverages enter. -/
theorem edgeWeight_le_four_ninths_of_dominates_triple (D : WeightedDesign m 3)
    {first second third : Fin m} (hlevFirst : leverageOf (D.atom first) = 3)
    (hlevSecond : leverageOf (D.atom second) = 3) (hlevThird : leverageOf (D.atom third) = 3)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) (hdominates : Dominates D {first, second, third}) :
    edgeWeight D first second ≤ 4 / 9 ∧ edgeWeight D first third ≤ 4 / 9
      ∧ edgeWeight D second third ≤ 4 / 9 := by
  have hfirstPos : 0 < leverageOf (D.atom first) := by rw [hlevFirst]; norm_num
  have hsecondPos : 0 < leverageOf (D.atom second) := by rw [hlevSecond]; norm_num
  have hthirdPos : 0 < leverageOf (D.atom third) := by rw [hlevThird]; norm_num
  have hslackFirst : weightSlack D first = 2 / 3 := by rw [weightSlack, hlevFirst]; norm_num
  have hslackSecond : weightSlack D second = 2 / 3 := by rw [weightSlack, hlevSecond]; norm_num
  have hslackThird : weightSlack D third = 2 / 3 := by rw [weightSlack, hlevThird]; norm_num
  obtain ⟨-, -, -, hpairOne, hpairTwo, hpairThree, -⟩ :=
    (dominates_triple_iff_slackClauses D hfirstPos hsecondPos hthirdPos hfirstSecond
      hfirstThird hsecondThird).mp hdominates
  rw [hslackFirst, hslackSecond] at hpairOne
  rw [hslackFirst, hslackThird] at hpairTwo
  rw [hslackSecond, hslackThird] at hpairThree
  exact ⟨by nlinarith [hpairOne], by nlinarith [hpairTwo], by nlinarith [hpairThree]⟩

/-! ## 4. The two determinant caps and the triple mass cap -/

/-- **The Gram-determinant cap** `sigma_T ≤ 1 + 2 P_T`, at EVERY design, every rank,
every weight vector: `det Gamma[T] = 1 - sigma + 2P ≥ 0` because the direction Gram
is positive semidefinite.  Not even distinctness is needed. -/
theorem directionTripleSigma_le_one_add_two_mul_directionTripleProduct (D : WeightedDesign m k)
    {first second third : Fin m} (hfirst : 0 < leverageOf (D.atom first))
    (hsecond : 0 < leverageOf (D.atom second)) (hthird : 0 < leverageOf (D.atom third)) :
    directionTripleSigma D first second third
      ≤ 1 + 2 * directionTripleProduct D first second third := by
  have hdet := ((posSemidef_directionGramMatrix D).submatrix ![first, second, third]).det_nonneg
  rw [directionGramMatrix_submatrix_three_eq_correlationMatrixThree D hfirst hsecond hthird,
    det_correlationMatrixThree, elliptopeBracket] at hdet
  rw [directionTripleSigma, directionTripleProduct]
  linarith [hdet]

/-- **(C2-FRUST), the frustrated cap**: on a frustrated triple (`P_T ≤ 0`),
`sigma_T + 2 |P_T| ≤ 1`. -/
theorem directionTripleSigma_add_two_mul_abs_directionTripleProduct_le_one_of_nonpos
    (D : WeightedDesign m k) {first second third : Fin m}
    (hfirst : 0 < leverageOf (D.atom first)) (hsecond : 0 < leverageOf (D.atom second))
    (hthird : 0 < leverageOf (D.atom third))
    (hfrustrated : directionTripleProduct D first second third ≤ 0) :
    directionTripleSigma D first second third
      + 2 * |directionTripleProduct D first second third| ≤ 1 := by
  have hcap := directionTripleSigma_le_one_add_two_mul_directionTripleProduct D hfirst hsecond
    hthird
  rw [abs_of_nonpos hfrustrated]
  linarith

/-- **(C2-COH), the coherent cap at `(7,3)`**: `sigma_T + (3/2) P_T ≤ 16/9`,
unconditionally on the uniform stratum — the determinant of the compressed `4/3` cap.
The heavy-gate tie (`w ≡ 4/9`, `P = 8/27`) saturates it exactly. -/
theorem directionTripleSigma_add_three_halves_mul_product_le_sevenThree
    (D : WeightedDesign 7 3) (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third : Fin 7} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    directionTripleSigma D first second third
      + (3 / 2) * directionTripleProduct D first second third ≤ 16 / 9 := by
  have hdet := (posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_of_uniformShare D
    hshare (le_refl _) hfirstSecond hfirstThird hsecondThird).det_nonneg
  rw [det_smul_one_sub_hollowSymmetricThree] at hdet
  rw [directionTripleSigma, directionTripleProduct]
  nlinarith [hdet]

/-- **THE TRIPLE MASS CAP at `(7,3)`**: every triple of a `(7,3)`-uniform design has
edge mass `sigma_T ≤ 13/9`.  The positive combination `3 · (Gram cap) + 4 ·
(coherent cap)` cancels the product term: `7 sigma ≤ 3 + 64/9 = 91/9`.  This
CONFIRMS the campaign's previously unverified `13/9` chart maximum, and
`Gtz.failingChartCorner_thirteen_ninths` shows the constant is exact on the
`(sigma, P)` chart even within the failing region. -/
theorem directionTripleSigma_le_thirteen_ninths_of_uniformShare_sevenThree
    (D : WeightedDesign 7 3) (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {first second third : Fin 7} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    directionTripleSigma D first second third ≤ 13 / 9 := by
  have hlevPos : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [hshare atomIndex]; norm_num)
  have hdetCap := directionTripleSigma_le_one_add_two_mul_directionTripleProduct D
    (hlevPos first) (hlevPos second) (hlevPos third)
  have hcohCap := directionTripleSigma_add_three_halves_mul_product_le_sevenThree D hshare
    hfirstSecond hfirstThird hsecondThird
  linarith

/-! ## 5. The gates -/

/-- **THE LIGHT PER-TRIPLE GATE at `(7,3)`.**  Three edges of weight at most `1/9`
force `sigma ≤ 1/3` and `P ≥ -1/27`, hence `residual ≤ 4/9`: the triple dominates.
Equality holds exactly at the tetrahedral tie `gamma ≡ -1/3`
(`Gtz.posSemidef_lightGateTie`). -/
theorem dominates_triple_of_lightEdges_sevenThree (D : WeightedDesign 7 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7) {first second third : Fin 7}
    (hlevFirst : leverageOf (D.atom first) = 3) (hlevSecond : leverageOf (D.atom second) = 3)
    (hlevThird : leverageOf (D.atom third) = 3) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hlightOne : edgeWeight D first second ≤ 1 / 9)
    (hlightTwo : edgeWeight D first third ≤ 1 / 9)
    (hlightThree : edgeWeight D second third ≤ 1 / 9) :
    Dominates D {first, second, third} := by
  refine (dominates_triple_iff_orientedTripleResidual_le_four_ninths_sevenThree D hshare
    hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird).mpr ?_
  have hprodSq : (directionGram D first second * directionGram D first third
        * directionGram D second third) ^ 2
      = edgeWeight D first second * edgeWeight D first third * edgeWeight D second third := by
    rw [edgeWeight, edgeWeight, edgeWeight]
    ring
  have hpairBound : edgeWeight D first second * edgeWeight D first third ≤ 1 / 9 * (1 / 9) :=
    mul_le_mul hlightOne hlightTwo (edgeWeight_nonneg D first third) (by norm_num)
  have htripleBound : edgeWeight D first second * edgeWeight D first third
      * edgeWeight D second third ≤ 1 / 9 * (1 / 9) * (1 / 9) :=
    mul_le_mul hpairBound hlightThree (edgeWeight_nonneg D second third) (by norm_num)
  have hprodFloor : -(1 / 27) ≤ directionGram D first second * directionGram D first third
      * directionGram D second third := by
    nlinarith [hprodSq, htripleBound,
      sq_nonneg (directionGram D first second * directionGram D first third
        * directionGram D second third + 1 / 27)]
  rw [orientedTripleResidual]
  linarith [hlightOne, hlightTwo, hlightThree, hprodFloor]

/-- **THE HEAVY GATE IS RIGID at `(7,3)`.**  A triple whose three edges all weigh at
least `4/9` is FROZEN: the Gram-determinant cap forces `P > 0`, the product of the
three weights forces `P ≥ 8/27`, and the coherent cap then pins `sigma = 4/3` —
whence every edge is EXACTLY `4/9` and `P` is exactly `+8/27`.  No leverage
hypothesis: this is a statement about the cosines alone. -/
theorem heavyEdges_rigid_of_uniformShare_sevenThree (D : WeightedDesign 7 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7) {first second third : Fin 7}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hheavyOne : 4 / 9 ≤ edgeWeight D first second)
    (hheavyTwo : 4 / 9 ≤ edgeWeight D first third)
    (hheavyThree : 4 / 9 ≤ edgeWeight D second third) :
    edgeWeight D first second = 4 / 9 ∧ edgeWeight D first third = 4 / 9
      ∧ edgeWeight D second third = 4 / 9
      ∧ directionTripleProduct D first second third = 8 / 27 := by
  have hlevPos : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [hshare atomIndex]; norm_num)
  have hdetCap := directionTripleSigma_le_one_add_two_mul_directionTripleProduct D
    (hlevPos first) (hlevPos second) (hlevPos third)
  have hcohCap := directionTripleSigma_add_three_halves_mul_product_le_sevenThree D hshare
    hfirstSecond hfirstThird hsecondThird
  have hsigmaSplit : directionTripleSigma D first second third
      = edgeWeight D first second + edgeWeight D first third + edgeWeight D second third := by
    rw [directionTripleSigma, edgeWeight, edgeWeight, edgeWeight]
  have hprodSq : directionTripleProduct D first second third ^ 2
      = edgeWeight D first second * edgeWeight D first third * edgeWeight D second third := by
    rw [directionTripleProduct, edgeWeight, edgeWeight, edgeWeight]
    ring
  have hpairBound : 4 / 9 * (4 / 9) ≤ edgeWeight D first second * edgeWeight D first third :=
    mul_le_mul hheavyOne hheavyTwo (by norm_num) (le_trans (by norm_num) hheavyOne)
  have htripleBound : 4 / 9 * (4 / 9) * (4 / 9)
      ≤ edgeWeight D first second * edgeWeight D first third * edgeWeight D second third :=
    mul_le_mul hpairBound hheavyThree (by norm_num)
      (mul_nonneg (edgeWeight_nonneg D first second) (edgeWeight_nonneg D first third))
  have hprodPos : 0 < directionTripleProduct D first second third := by
    linarith [hdetCap, hsigmaSplit, hheavyOne, hheavyTwo, hheavyThree]
  have hprodFloor : 8 / 27 ≤ directionTripleProduct D first second third := by
    nlinarith [hprodPos, hprodSq, htripleBound]
  have hsigmaCeil : directionTripleSigma D first second third ≤ 4 / 3 := by
    linarith [hcohCap, hprodFloor]
  have honeEq : edgeWeight D first second = 4 / 9 := by
    linarith [hsigmaCeil, hsigmaSplit, hheavyOne, hheavyTwo, hheavyThree]
  have htwoEq : edgeWeight D first third = 4 / 9 := by
    linarith [hsigmaCeil, hsigmaSplit, hheavyOne, hheavyTwo, hheavyThree]
  have hthreeEq : edgeWeight D second third = 4 / 9 := by
    linarith [hsigmaCeil, hsigmaSplit, hheavyOne, hheavyTwo, hheavyThree]
  have hprodCeil : directionTripleProduct D first second third ≤ 8 / 27 := by
    linarith [hcohCap, hsigmaSplit, honeEq, htwoEq, hthreeEq]
  exact ⟨honeEq, htwoEq, hthreeEq, le_antisymm hprodCeil hprodFloor⟩

/-- **THE HEAVY PER-TRIPLE GATE at `(7,3)`**: a leverage-three triple with all three
edges of weight at least `4/9` dominates — and by the rigidity it dominates with
margin exactly zero (`residual = 4/3 - 8/9 = 4/9`, the double root of the endpoint
cubic).  So `min-edge ≥ 4/9` at any single triple closes the covering. -/
theorem dominates_triple_of_heavyEdges_sevenThree (D : WeightedDesign 7 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7) {first second third : Fin 7}
    (hlevFirst : leverageOf (D.atom first) = 3) (hlevSecond : leverageOf (D.atom second) = 3)
    (hlevThird : leverageOf (D.atom third) = 3) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hheavyOne : 4 / 9 ≤ edgeWeight D first second)
    (hheavyTwo : 4 / 9 ≤ edgeWeight D first third)
    (hheavyThree : 4 / 9 ≤ edgeWeight D second third) :
    Dominates D {first, second, third} := by
  obtain ⟨honeEq, htwoEq, hthreeEq, hprodEq⟩ := heavyEdges_rigid_of_uniformShare_sevenThree D
    hshare hfirstSecond hfirstThird hsecondThird hheavyOne hheavyTwo hheavyThree
  refine (dominates_triple_iff_orientedTripleResidual_le_four_ninths_sevenThree D hshare
    hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird).mpr ?_
  have hresidual : orientedTripleResidual D first second third
      = edgeWeight D first second + edgeWeight D first third + edgeWeight D second third
        - 3 * directionTripleProduct D first second third := by
    rw [orientedTripleResidual, directionTripleProduct]
  rw [hresidual, honeEq, htwoEq, hthreeEq, hprodEq]
  norm_num

/-- **THE MIDDLE-BAND FENCE.**  Every FAILING triple of the `(7,3)` uniform
leverage-three stratum satisfies `residual > 4/9`, has some edge strictly below the
heavy gate `4/9`, and some edge strictly above the light gate `1/9`: the battlefield
is exactly the open band `(1/9, 4/9)` of the endpoint cubic.  (It also obeys the two
caps and the mass cap `sigma ≤ 13/9`, which hold for ALL triples — see above.) -/
theorem middleBandEdges_of_not_dominates_sevenThree (D : WeightedDesign 7 3)
    (hshare : ∀ atomIndex, atomShare D atomIndex = 3 / 7) {first second third : Fin 7}
    (hlevFirst : leverageOf (D.atom first) = 3) (hlevSecond : leverageOf (D.atom second) = 3)
    (hlevThird : leverageOf (D.atom third) = 3) (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hfails : ¬ Dominates D {first, second, third}) :
    4 / 9 < orientedTripleResidual D first second third
      ∧ (edgeWeight D first second < 4 / 9 ∨ edgeWeight D first third < 4 / 9
          ∨ edgeWeight D second third < 4 / 9)
      ∧ (1 / 9 < edgeWeight D first second ∨ 1 / 9 < edgeWeight D first third
          ∨ 1 / 9 < edgeWeight D second third) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hle
    rw [not_lt] at hle
    exact hfails ((dominates_triple_iff_orientedTripleResidual_le_four_ninths_sevenThree D
      hshare hlevFirst hlevSecond hlevThird hfirstSecond hfirstThird hsecondThird).mpr hle)
  · by_contra hcontra
    rw [not_or, not_or, not_lt, not_lt, not_lt] at hcontra
    obtain ⟨honeGe, htwoGe, hthreeGe⟩ := hcontra
    exact hfails (dominates_triple_of_heavyEdges_sevenThree D hshare hlevFirst hlevSecond
      hlevThird hfirstSecond hfirstThird hsecondThird honeGe htwoGe hthreeGe)
  · by_contra hcontra
    rw [not_or, not_or, not_lt, not_lt, not_lt] at hcontra
    obtain ⟨honeLe, htwoLe, hthreeLe⟩ := hcontra
    exact hfails (dominates_triple_of_lightEdges_sevenThree D hshare hlevFirst hlevSecond
      hlevThird hfirstSecond hfirstThird hsecondThird honeLe htwoLe hthreeLe)

/-- **The chart corner `(sigma, P) = (13/9, 2/9)` is sharp.**  It saturates the
Gram-determinant cap (`det Gamma[T] = 0`), saturates the coherent cap, and FAILS the
single clause (`residual = 7/9 > 4/9`): so the mass cap `sigma ≤ 13/9` cannot be
improved on the `(sigma, P)` chart, even restricted to failing triples.  The corner
is realised by unit vectors (an exactly parallel pair plus a third atom at squared
cosine `2/9` to both); design-side attainment inside a full `(7,3)`-uniform frame is
open. -/
theorem failingChartCorner_thirteen_ninths :
    (1 : ℝ) - 13 / 9 + 2 * (2 / 9) = 0 ∧ (13 : ℝ) / 9 + (3 / 2) * (2 / 9) = 16 / 9
      ∧ (4 : ℝ) / 9 < 13 / 9 - 3 * (2 / 9) := by
  norm_num

/-! ## 6. The two tie blocks

Both gate endpoints are TIES of the single clause: the light (tetrahedral) block
`gamma ≡ -1/3` and the heavy (coherent) block `gamma ≡ 2/3` both satisfy
`sigma - 3P = 4/9` exactly, and their shifted hollow blocks `(2/3) • 1 + M[T]` are
positive semidefinite with vanishing determinant — domination with margin zero. -/

/-- **The light-gate tie block is PSD**: `(2/3) • 1 + M` at `gamma ≡ -1/3` (the
tetrapod triple of the basis-plus-tetrapod witness; `sigma = 1/3`, `P = -1/27`,
`residual = 4/9` exactly). -/
theorem posSemidef_lightGateTie :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (-(1 / 3)) (-(1 / 3)) (-(1 / 3))).PosSemidef := by
  rw [smul_one_add_hollowSymmetricThree]
  refine posSemidef_three_of_principalMinors ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> rfl
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]

/-- The light-gate tie block is singular: the tie sits exactly on the PSD boundary
(`lambda_min(M) = -2/3` attained). -/
theorem det_lightGateTie_eq_zero :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (-(1 / 3)) (-(1 / 3)) (-(1 / 3))).det = 0 := by
  rw [det_smul_one_add_hollowSymmetricThree]
  norm_num

/-- **The heavy-gate tie block is PSD**: `(2/3) • 1 + M` at `gamma ≡ 2/3` — the rigid
configuration of `Gtz.heavyEdges_rigid_of_uniformShare_sevenThree` (`sigma = 4/3`,
`P = 8/27`, `residual = 4/9` exactly; it also saturates the `4/3` spectral cap and
the coherent cap simultaneously). -/
theorem posSemidef_heavyGateTie :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (2 / 3) (2 / 3) (2 / 3)).PosSemidef := by
  rw [smul_one_add_hollowSymmetricThree]
  refine posSemidef_three_of_principalMinors ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> rfl
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]
  · rw [Matrix.det_fin_three]
    norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.of_apply]

/-- The heavy-gate tie block is singular: the heavy gate lands exactly on the PSD
boundary — the double root `m = 4/9` of the endpoint cubic in matrix form. -/
theorem det_heavyGateTie_eq_zero :
    (((2 : ℝ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + hollowSymmetricThree (2 / 3) (2 / 3) (2 / 3)).det = 0 := by
  rw [det_smul_one_add_hollowSymmetricThree]
  norm_num

end Gtz
