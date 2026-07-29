/-
# The `(7,3)` uniform quadratic layer, its one-line spectral caps, and the witness

The `(7,3)` uniform-share stratum is the campaign's frontier (residual R3): rank-three
GTZ at every size is equivalent to the all-heavy `(7,3)` statement
(`Gtz.discriminantCovering_seven_iff_rank_three`), and its uniform-share slice carries
the quadratic law `Gamma^2 = (7/3) Gamma` (landed as
`Gtz.directionGramMatrix_sq_of_uniformShare`).  This file lands the design-side reading
of that law and the stratum's witness.

**The quadratic package** (pen brief P1/P2).  On `M = Gamma - 1` the square law reads
`M^2 = (1/3) M + (4/3) 1` — landed here parametrically at every uniform share as
`M^2 = (1/s - 2) M + (1/s - 1) 1`, so every future cell inherits it — with the cube law
`M^3 = (13/9) M + (4/9) 1`, the trace laws `tr M^2 = 28/3` and `tr M^3 = 28/9`, the row
law `sum_{b /= a} w_ab = 4/3`, the positive supply chain
`sum_{c /= a,b} gamma_ac gamma_cb = (1/3) gamma_ab` (where `(6,3)` has zero), and the
doubled edge total `28/3` (unordered pair total `14/3`).

**The one-line caps** (pen brief P1/P4).  From `form^2 = scale . form` and symmetry,
`(scale 1 - form) = scale^{-1} (scale 1 - form)^2 ⪰ 0` — no interlacing, no spectral
theory.  At `(7,3)`: `(7/3) 1 - Gamma ⪰ 0`, and compressing to any triple of distinct
atoms, `(4/3) 1 - M[T] ⪰ 0`, which is exactly the `hcap` feeder of the landed
`Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds`.  Its
determinant is the coherent cap `sigma_T + (3/2) P_T <= 16/9` (C2-COH); the Gram block's
own determinant is the frustrated cap `0 <= 1 - sigma_T + 2 P_T` (C2-FRUST); and the
cap plus the leverage-three dictionary collapses domination to ONE inequality
(C1-IFF): on the `(7,3)` stratum with uniform share `3/7` and uniform leverage `3`,
`T` dominates iff `sigma_T - 3 P_T <= 4/9` — the pairwise clauses are consequences,
not extra conjuncts.

**The witness** `Gtz.sevenThreeBasisTetrapodDesign`: three axis atoms `sqrt 3 e_i` plus
the four even-sign tetrapod atoms `(+-1, +-1, +-1)` (the shipped `Gtz.tetraAtom`), all
at weight `1/7` and leverage `3`.  It is `IsEqualShare`, all-heavy, has every share
`3/7`, and de-vacuates at one stroke every landed theorem conditioned on
`forall c, atomShare D c = 3/7` — the non-vacuity gap wf3's audit named.  Gram pattern:
basis-basis `0`, basis-tetrapod `+-1/sqrt 3` (edge weight `1/3`), tetrapod-tetrapod
`-1/3`.  Calibration: the tetrapod triple `{3,4,5}` has `sigma = 1/3`, `P = -1/27`,
`sigma - 3P = 4/9` EXACTLY — the tetrahedral tie, its slack determinant vanishing —
and it dominates; the BASIS triple `{0,1,2}` has Gram determinant `1`, the maximum any
triple of unit directions can attain (`2P <= sigma`, hypothesis-free), and dominates
STRICTLY with gap exactly `2 . 1`.  (The brief's earlier draft called the tetrapod
triple max-volume; that is false — `16/27 < 1` — and the true calibration is stated
here.  This feeds conjecture M7: the max-volume triple of the witness dominates
strictly, the tie sits on a non-maximal triple.)

`Gtz.GtzUniformShareSevenThree` is the R3 statement as a `Prop`, mirroring the landed
`Gtz.GtzUniformShareSixThree`, and the witness inhabits its hypothesis stratum and its
conclusion.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.FrameConservation
import Gtz.Design.StressCertificate
import Gtz.Design.DominationGates
import Gtz.Reduction.Reductions
import Gtz.Reduction.RayleighCertificate
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.WeightedTripleCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The quadratic law package at a uniform share

`Gamma^2 = s^{-1} Gamma` is landed; everything here is its `M = Gamma - 1` reading.
The parametric square law is size- and rank-generic so that the `(6,3)` involution
(`s = 1/2`: `M^2 = 1`) and the `(7,3)` law (`s = 3/7`: `M^2 = (1/3)M + (4/3)1`) are two
instances of one identity. -/

/-- **The parametric hollow square law.**  At uniform share `s` the correlation matrix
`M = Gamma - 1` satisfies `M^2 = (1/s - 2) M + (1/s - 1) 1`.  At `s = 1/2` this is the
`(6,3)` involution `M^2 = 1`; at `s = 3/7` it is the `(7,3)` law; no other hypothesis —
in particular no uniform weight and no uniform leverage. -/
theorem correlationInvolution_sq_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue) :
    correlationInvolution D * correlationInvolution D
      = (shareValue⁻¹ - 2) • correlationInvolution D
        + (shareValue⁻¹ - 1) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have hsquare := directionGramMatrix_sq_of_uniformShare D huniform hpositive
  rw [correlationInvolution, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, hsquare]
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  split_ifs <;> ring

/-- `Gamma^2 = (7/3) Gamma` at the `(7,3)` uniform-share stratum. -/
theorem directionGramMatrix_sq_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    directionGramMatrix D * directionGramMatrix D = (7 / 3 : ℝ) • directionGramMatrix D := by
  have hsquare := directionGramMatrix_sq_of_uniformShare D huniform (by norm_num)
  rwa [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hsquare

/-- **The `(7,3)` square law**: `M^2 = (1/3) M + (4/3) 1`. -/
theorem correlationInvolution_sq_uniformSevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    correlationInvolution D * correlationInvolution D
      = (1 / 3 : ℝ) • correlationInvolution D
        + (4 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  have hsquare := correlationInvolution_sq_of_uniformShare D huniform (by norm_num)
  rwa [show ((3 : ℝ) / 7)⁻¹ - 2 = 1 / 3 by norm_num,
    show ((3 : ℝ) / 7)⁻¹ - 1 = 4 / 3 by norm_num] at hsquare

/-- **The `(7,3)` cube law**: `M^3 = (13/9) M + (4/9) 1`, obtained by multiplying the
square law once more — `M^3 = (1/3) M^2 + (4/3) M`. -/
theorem correlationInvolution_cube_uniformSevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    correlationInvolution D * correlationInvolution D * correlationInvolution D
      = (13 / 9 : ℝ) • correlationInvolution D
        + (4 / 9 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  have hsquare := correlationInvolution_sq_uniformSevenThree D huniform
  rw [hsquare, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hsquare]
  ext rowIndex colIndex
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> ring

/-- The correlation matrix `M = Gamma - 1` is traceless at every positive uniform
share: the Gram diagonal is all ones (`trace Gamma = m`). -/
theorem trace_correlationInvolution_of_uniformShare (D : WeightedDesign m k) {shareValue : ℝ}
    (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue) (hpositive : 0 < shareValue) :
    Matrix.trace (correlationInvolution D) = 0 := by
  rw [correlationInvolution, Matrix.trace_sub,
    trace_directionGramMatrix_of_uniformShare D huniform hpositive, Matrix.trace_one]
  simp

/-- **The `(7,3)` second trace law**: `tr M^2 = 28/3` — equivalently the doubled total
edge weight, cross-checked below by summing the row law. -/
theorem trace_correlationInvolution_sq_uniformSevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    Matrix.trace (correlationInvolution D * correlationInvolution D) = 28 / 3 := by
  rw [correlationInvolution_sq_uniformSevenThree D huniform, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_correlationInvolution_of_uniformShare D huniform (by norm_num),
    Matrix.trace_one]
  norm_num

/-- **The `(7,3)` third trace law**: `tr M^3 = 28/9` — the total coherent supply, six
times the pen's triple-product total `14/27`. -/
theorem trace_correlationInvolution_cube_uniformSevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    Matrix.trace (correlationInvolution D * correlationInvolution D * correlationInvolution D)
      = 28 / 9 := by
  rw [correlationInvolution_cube_uniformSevenThree D huniform, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_correlationInvolution_of_uniformShare D huniform (by norm_num),
    Matrix.trace_one]
  norm_num

/-- **The `(7,3)` row law**: `sum_{b /= a} w_ab = 4/3` at every atom — the diagonal of
`M^2 = (1/3) M + (4/3) 1`, instantiated from the landed vertex-sum law. -/
theorem sum_erase_edgeWeight_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex = 4 / 3 := by
  have hpositive : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq D huniform hpositive]
  norm_num

/-- **The `(7,3)` doubled edge total**: the ordered off-diagonal weight total is `28/3`,
so the unordered total over the twenty-one pairs is `14/3` — the constant that feeds
`tr M^2 = 28/3` and the landed determinant total `343/27`. -/
theorem sum_sum_erase_edgeWeight_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∑ atomIndex : Fin 7, ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        edgeWeight D atomIndex otherIndex = 28 / 3 := by
  rw [Finset.sum_congr rfl fun atomIndex _ => sum_erase_edgeWeight_sevenThree D huniform
    atomIndex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **The `(7,3)` POSITIVE supply chain**:
`sum_{c /= a,b} gamma_ac gamma_cb = (1/3) gamma_ab` — the off-diagonal of
`M^2 = (1/3) M + (4/3) 1`.  At `(6,3)` the same sum vanishes
(`Gtz.sum_sdiff_directionGram_mul_of_isEqualShare`); the surviving `1/3` is the
structural difference between the two cells and the engine of the `(7,3)`
starve-feed transfer. -/
theorem sum_sdiff_directionGram_mul_directionGram_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex
      = (1 / 3 : ℝ) * directionGram D firstIndex secondIndex := by
  have hfirstPositive : 0 < leverageOf (D.atom firstIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform firstIndex]; norm_num)
  have hsecondPositive : 0 < leverageOf (D.atom secondIndex) :=
    leverageOf_pos_of_atomShare_pos D (by rw [huniform secondIndex]; norm_num)
  have hchain := sum_sdiff_atomShare_mul_directionGram_mul_directionGram D hdistinct
    hfirstPositive hsecondPositive
  have hpull : ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        atomShare D otherIndex
          * (directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex)
      = (3 / 7 : ℝ) * ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
          directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex]
  rw [hpull, huniform firstIndex, huniform secondIndex] at hchain
  linarith [hchain]

/-! ## 2. The one-line spectral caps

`(scale 1 - form)^2 = scale (scale 1 - form)` whenever `form^2 = scale form`, so the
cap is a nonnegative multiple of a square — positive semidefinite with no eigenvalue
argument at all.  Compression to a triple produces exactly the `hcap` hypothesis of the
landed `(7,3)` cubic criterion. -/

/-- **The one-line cap, abstractly.**  A symmetric scaled projection is bounded above
by its scale: `form^2 = scale form` with `scale > 0` forces `scale 1 - form ⪰ 0`,
because `scale 1 - form = scale^{-1} (scale 1 - form)^2` is a scaled square. -/
theorem posSemidef_smul_one_sub_of_sq_eq_smul {size : ℕ} {form : Matrix (Fin size) (Fin size) ℝ}
    {scaleValue : ℝ} (hsymmetric : formᵀ = form)
    (hsquare : form * form = scaleValue • form) (hpositive : 0 < scaleValue) :
    (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form).PosSemidef := by
  have hcapSymmetric : (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)ᵀ
      = scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsymmetric]
  have hcapSquare : (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)
        * (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)
      = scaleValue • (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hsquare, smul_sub, smul_smul]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  have hgram : ((scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)ᵀ
      * (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self
      (scaleValue • (1 : Matrix (Fin size) (Fin size) ℝ) - form)
  rw [hcapSymmetric, hcapSquare] at hgram
  exact (posSemidef_smul_iff hpositive).mp hgram

/-- **The design-side cap at every uniform share**: `s^{-1} 1 - Gamma ⪰ 0`, hence every
principal block of the direction Gram has largest eigenvalue at most `1/s`. -/
theorem posSemidef_smul_one_sub_directionGramMatrix_of_uniformShare (D : WeightedDesign m k)
    {shareValue : ℝ} (huniform : ∀ atomIndex, atomShare D atomIndex = shareValue)
    (hpositive : 0 < shareValue) :
    (shareValue⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) - directionGramMatrix D).PosSemidef := by
  have hsymmetric : (directionGramMatrix D)ᵀ = directionGramMatrix D := by
    ext rowIndex colIndex
    exact directionGram_comm D colIndex rowIndex
  exact posSemidef_smul_one_sub_of_sq_eq_smul hsymmetric
    (directionGramMatrix_sq_of_uniformShare D huniform hpositive) (inv_pos.mpr hpositive)

/-- **The `(7,3)` cap**: `(7/3) 1 - Gamma ⪰ 0` on the uniform-share stratum. -/
theorem posSemidef_sevenThirds_smul_one_sub_directionGramMatrix (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D).PosSemidef := by
  have hcap := posSemidef_smul_one_sub_directionGramMatrix_of_uniformShare D huniform
    (by norm_num)
  rwa [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hcap

/-- **The `(7,3)` triple cap** `(4/3) 1 - M[T] ⪰ 0` for every triple of distinct atoms:
the compression of `(7/3) 1 - Gamma ⪰ 0`, written on the hollow block of the three
direction cosines.  This is verbatim the `hcap` hypothesis of the landed
`Gtz.posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds`. -/
theorem posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_sevenThree
    (D : WeightedDesign 7 3) (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex thirdIndex : Fin 7} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    ((4 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex)
          (directionGram D secondIndex thirdIndex)).PosSemidef := by
  have hpositive : ∀ atomIndex : Fin 7, 0 < leverageOf (D.atom atomIndex) := fun atomIndex =>
    leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsub : (correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex] - 1 := by
    rw [correlationInvolution, show (directionGramMatrix D - 1).submatrix
        ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
        = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex]
          - (1 : Matrix (Fin 7) (Fin 7) ℝ).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex] from rfl,
      Matrix.submatrix_one _ hpick]
  have hshape : (4 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree (directionGram D firstIndex secondIndex)
            (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex)
      = ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D).submatrix
          ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex] := by
    rw [← hollowMatrixThree_eq_hollowSymmetricThree,
      ← correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive hfirstSecond
        hfirstThird hsecondThird, hsub]
    ext rowIndex colIndex
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs with hslotEqual hpickEqual hpickEqual
    · ring
    · exact absurd (by rw [hslotEqual]) hpickEqual
    · exact absurd (hpick hpickEqual) hslotEqual
    · ring
  rw [hshape]
  exact (posSemidef_sevenThirds_smul_one_sub_directionGramMatrix D huniform).submatrix _

/-- **(C2-COH) The coherent cap at `(7,3)`**: `sigma_T + (3/2) P_T <= 16/9` for every
triple of distinct atoms of the uniform-share stratum — the determinant of the triple
cap `(4/3) 1 - M[T] ⪰ 0`. -/
theorem directionTripleSigma_add_three_halves_mul_directionTripleProduct_le_sevenThree
    (D : WeightedDesign 7 3) (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex thirdIndex : Fin 7} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    directionTripleSigma D firstIndex secondIndex thirdIndex
        + (3 / 2 : ℝ) * directionTripleProduct D firstIndex secondIndex thirdIndex
      ≤ 16 / 9 := by
  have hdet := (posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_sevenThree D huniform
    hfirstSecond hfirstThird hsecondThird).det_nonneg
  rw [det_smul_one_sub_hollowSymmetricThree] at hdet
  rw [directionTripleSigma, directionTripleProduct]
  linarith [hdet]

/-- **(C2-FRUST) The frustrated cap**: `0 <= 1 - sigma_T + 2 P_T` — the Gram block's
own determinant, nonnegative because the direction Gram is positive semidefinite.
Share-free: it holds on EVERY design with nondegenerate atoms, at every size and rank;
for a frustrated triple (`P_T < 0`) it reads `sigma_T + 2 |P_T| <= 1`. -/
theorem nonneg_one_sub_directionTripleSigma_add_two_mul_directionTripleProduct
    (D : WeightedDesign m k) (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    {firstIndex secondIndex thirdIndex : Fin m} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    0 ≤ 1 - directionTripleSigma D firstIndex secondIndex thirdIndex
        + 2 * directionTripleProduct D firstIndex secondIndex thirdIndex := by
  have hpick : Function.Injective ![firstIndex, secondIndex, thirdIndex] := by
    intro leftSlot rightSlot hvalue
    fin_cases leftSlot <;> fin_cases rightSlot <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsub : (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree (directionGram D firstIndex secondIndex)
            (directionGram D firstIndex thirdIndex)
            (directionGram D secondIndex thirdIndex) := by
    have hcompress := correlationInvolution_submatrix_three_eq_hollowMatrixThree D hpositive
      hfirstSecond hfirstThird hsecondThird
    rw [hollowMatrixThree_eq_hollowSymmetricThree] at hcompress
    have hsplit : (correlationInvolution D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]
        = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
            ![firstIndex, secondIndex, thirdIndex] - 1 := by
      rw [correlationInvolution, show (directionGramMatrix D - 1).submatrix
          ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex]
          = (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex]
            - (1 : Matrix (Fin m) (Fin m) ℝ).submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex] from rfl,
        Matrix.submatrix_one _ hpick]
    rw [hsplit, sub_eq_iff_eq_add] at hcompress
    rw [one_smul, hcompress]
    exact add_comm _ _
  have hdet := ((posSemidef_directionGramMatrix D).submatrix
    ![firstIndex, secondIndex, thirdIndex]).det_nonneg
  rw [hsub, det_smul_one_add_hollowSymmetricThree] at hdet
  rw [directionTripleSigma, directionTripleProduct]
  linarith [hdet]

/-- **The bracket ceiling, hypothesis-free**: `2 P_T <= sigma_T` for every triple of
every design — equivalently `det Gamma[T] <= 1`, since
`det Gamma[T] = 1 - sigma_T + 2 P_T` on nondegenerate triples.  Certificate:
`sigma - 2P = (gamma_ab - gamma_ac gamma_bc)^2 + gamma_ac^2 (1 - gamma_bc^2)
+ gamma_bc^2`, using only `|gamma_bc| <= 1`.  An orthonormal triple attains equality
in the det reading; this is the max-volume ceiling the witness's basis triple hits. -/
theorem two_mul_directionTripleProduct_le_directionTripleSigma (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    2 * directionTripleProduct D firstIndex secondIndex thirdIndex
      ≤ directionTripleSigma D firstIndex secondIndex thirdIndex := by
  have habs := abs_directionGram_le_one D secondIndex thirdIndex
  have hnonneg := abs_nonneg (directionGram D secondIndex thirdIndex)
  have hsqLe : directionGram D secondIndex thirdIndex ^ 2 ≤ 1 := by
    nlinarith [sq_abs (directionGram D secondIndex thirdIndex)]
  rw [directionTripleProduct, directionTripleSigma]
  nlinarith [sq_nonneg (directionGram D firstIndex secondIndex
      - directionGram D firstIndex thirdIndex * directionGram D secondIndex thirdIndex),
    mul_nonneg (sq_nonneg (directionGram D firstIndex thirdIndex)) (sub_nonneg.mpr hsqLe),
    sq_nonneg (directionGram D secondIndex thirdIndex)]

/-- The bracket ceiling in determinant coordinates: `1 - sigma_T + 2 P_T <= 1`. -/
theorem one_sub_directionTripleSigma_add_two_mul_directionTripleProduct_le_one
    (D : WeightedDesign m k) (firstIndex secondIndex thirdIndex : Fin m) :
    1 - directionTripleSigma D firstIndex secondIndex thirdIndex
        + 2 * directionTripleProduct D firstIndex secondIndex thirdIndex ≤ 1 := by
  have hceiling := two_mul_directionTripleProduct_le_directionTripleSigma D firstIndex
    secondIndex thirdIndex
  linarith

/-- **(C1-IFF) The single-clause domination criterion at the `(7,3)` equal-share
stratum.**  With uniform share `3/7` AND uniform leverage `3` (both load-bearing:
share feeds the cap, leverage feeds the dictionary), a triple of distinct atoms
dominates IFF `sigma_T - 3 P_T <= 4/9`.  One inequality — the pairwise clauses
`w <= 4/9` of the seven-clause criterion are CONSEQUENCES here, not extra conjuncts.
The tetrahedral tie sits exactly on the boundary `sigma - 3P = 4/9`. -/
theorem dominates_triple_iff_sigma_sub_three_mul_product_sevenThree (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin 7} (hfirstSecond : firstIndex ≠ secondIndex)
    (hfirstThird : firstIndex ≠ thirdIndex) (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ directionTripleSigma D firstIndex secondIndex thirdIndex
          - 3 * directionTripleProduct D firstIndex secondIndex thirdIndex ≤ 4 / 9 := by
  rw [dominates_triple_iff_posSemidef_hollowShift D hleverage hfirstSecond hfirstThird
      hsecondThird, hollowMatrixThree_eq_hollowSymmetricThree,
    add_comm (hollowSymmetricThree (directionGram D firstIndex secondIndex)
      (directionGram D firstIndex thirdIndex) (directionGram D secondIndex thirdIndex))
      ((2 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)),
    posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds
      (by norm_num : (2 : ℝ) / 3 ≤ 2 / 3)
      (posSemidef_fourThirds_smul_one_sub_hollowSymmetricThree_sevenThree D huniform
        hfirstSecond hfirstThird hsecondThird),
    directionTripleSigma, directionTripleProduct]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-! ## 3. The witness: basis plus tetrapod

Three axis atoms `sqrt 3 . e_i` and the four even-sign tetrapod atoms
(the shipped `Gtz.tetraAtom`), all at weight `1/7`.  The tetrapod block alone sums to
`4 . 1` and the basis block to `3 . 1`, so Parseval is exact.  This inhabits the
`(7,3)` uniform-share stratum — the non-vacuity wf3's audit flagged as missing. -/

/-- The seven atoms: `sqrt 3` times the standard basis, then the four even-sign
tetrapod vertices `(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)`. -/
noncomputable def sevenThreeBasisTetrapodAtom : Fin 7 → Fin 3 → ℝ :=
  ![![Real.sqrt 3, 0, 0], ![0, Real.sqrt 3, 0], ![0, 0, Real.sqrt 3],
    tetraAtom 0, tetraAtom 1, tetraAtom 2, tetraAtom 3]

@[simp] theorem sevenThreeBasisTetrapodAtom_zero :
    sevenThreeBasisTetrapodAtom 0 = ![Real.sqrt 3, 0, 0] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_one :
    sevenThreeBasisTetrapodAtom 1 = ![0, Real.sqrt 3, 0] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_two :
    sevenThreeBasisTetrapodAtom 2 = ![0, 0, Real.sqrt 3] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_three :
    sevenThreeBasisTetrapodAtom 3 = ![1, 1, 1] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_four :
    sevenThreeBasisTetrapodAtom 4 = ![1, -1, -1] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_five :
    sevenThreeBasisTetrapodAtom 5 = ![-1, 1, -1] := rfl

@[simp] theorem sevenThreeBasisTetrapodAtom_six :
    sevenThreeBasisTetrapodAtom 6 = ![-1, -1, 1] := rfl

/-- **THE `(7,3)` EQUAL-SHARE WITNESS**: basis plus tetrapod at uniform weight `1/7`.
Every leverage is `3`, every share is `3/7`, and the design is all-heavy — so every
landed theorem conditioned on `forall c, atomShare D c = 3/7` (the minor-sum total
`343/27`, the sigma mirror correction, the whole `(7,3)` tau-order-statistics block,
and this file's quadratic layer) is non-vacuous. -/
noncomputable def sevenThreeBasisTetrapodDesign : WeightedDesign 7 3 where
  atom := sevenThreeBasisTetrapodAtom
  weight := fun _ => (7 : ℝ)⁻¹
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_seven, smul_eq_mul, sevenThreeBasisTetrapodAtom, tetraAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

@[simp] theorem sevenThreeBasisTetrapodDesign_atom :
    sevenThreeBasisTetrapodDesign.atom = sevenThreeBasisTetrapodAtom := rfl

@[simp] theorem sevenThreeBasisTetrapodDesign_weight (atomIndex : Fin 7) :
    sevenThreeBasisTetrapodDesign.weight atomIndex = (7 : ℝ)⁻¹ := rfl

/-- Every atom of the witness has leverage exactly `3`. -/
theorem leverageOf_sevenThreeBasisTetrapodDesign (atomIndex : Fin 7) :
    leverageOf (sevenThreeBasisTetrapodDesign.atom atomIndex) = 3 := by
  fin_cases atomIndex <;>
    norm_num [sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom, tetraAtom,
      leverageOf, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]

/-- The witness sits on the equal-share stratum: weight `1/7` and leverage `3`. -/
theorem isEqualShare_sevenThreeBasisTetrapodDesign :
    IsEqualShare sevenThreeBasisTetrapodDesign where
  weight_eq := fun _ => by norm_num
  leverage_eq := fun atomIndex => by
    rw [leverageOf_sevenThreeBasisTetrapodDesign]
    norm_num

/-- **NON-VACUITY OF THE `(7,3)` UNIFORM-SHARE STRATUM**: the witness has every share
equal to `3/7`. -/
theorem atomShare_sevenThreeBasisTetrapodDesign (atomIndex : Fin 7) :
    atomShare sevenThreeBasisTetrapodDesign atomIndex = 3 / 7 := by
  rw [isEqualShare_sevenThreeBasisTetrapodDesign.atomShare_eq atomIndex]
  norm_num

/-- The witness is all-heavy: every leverage is `3 > 1`. -/
theorem allHeavy_sevenThreeBasisTetrapodDesign : AllHeavy sevenThreeBasisTetrapodDesign :=
  isEqualShare_sevenThreeBasisTetrapodDesign.allHeavy (by norm_num)

/-- Every atom of the witness has weight slack (capacity) `2/3`. -/
theorem weightSlack_sevenThreeBasisTetrapodDesign (atomIndex : Fin 7) :
    weightSlack sevenThreeBasisTetrapodDesign atomIndex = 2 / 3 :=
  weightSlack_eq_two_thirds_of_isEqualShare isEqualShare_sevenThreeBasisTetrapodDesign atomIndex

/-- The witness's direction Gram in raw coordinates: every cosine is one third of the
raw pairing, because every leverage is `3`. -/
theorem directionGram_sevenThreeBasisTetrapodDesign (firstIndex secondIndex : Fin 7) :
    directionGram sevenThreeBasisTetrapodDesign firstIndex secondIndex
      = 3⁻¹ * (sevenThreeBasisTetrapodAtom firstIndex ⬝ᵥ sevenThreeBasisTetrapodAtom
          secondIndex) := by
  rw [directionGram_eq_scaled_atomPairing sevenThreeBasisTetrapodDesign firstIndex secondIndex,
    leverageOf_sevenThreeBasisTetrapodDesign firstIndex,
    leverageOf_sevenThreeBasisTetrapodDesign secondIndex, ← mul_inv,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3), sevenThreeBasisTetrapodDesign_atom]

/-! ### The Gram pattern: basis-basis `0`, tetrapod-tetrapod `-1/3`,
basis-tetrapod `+-1/sqrt 3` (edge weight `1/3`) -/

theorem directionGram_sevenThreeBasisTetrapodDesign_zero_one :
    directionGram sevenThreeBasisTetrapodDesign 0 1 = 0 := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_zero,
    sevenThreeBasisTetrapodAtom_one]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_zero_two :
    directionGram sevenThreeBasisTetrapodDesign 0 2 = 0 := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_zero,
    sevenThreeBasisTetrapodAtom_two]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_one_two :
    directionGram sevenThreeBasisTetrapodDesign 1 2 = 0 := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_one,
    sevenThreeBasisTetrapodAtom_two]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_three_four :
    directionGram sevenThreeBasisTetrapodDesign 3 4 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_three,
    sevenThreeBasisTetrapodAtom_four]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_three_five :
    directionGram sevenThreeBasisTetrapodDesign 3 5 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_three,
    sevenThreeBasisTetrapodAtom_five]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_three_six :
    directionGram sevenThreeBasisTetrapodDesign 3 6 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_three,
    sevenThreeBasisTetrapodAtom_six]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_four_five :
    directionGram sevenThreeBasisTetrapodDesign 4 5 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_four,
    sevenThreeBasisTetrapodAtom_five]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_four_six :
    directionGram sevenThreeBasisTetrapodDesign 4 6 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_four,
    sevenThreeBasisTetrapodAtom_six]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem directionGram_sevenThreeBasisTetrapodDesign_five_six :
    directionGram sevenThreeBasisTetrapodDesign 5 6 = -(1 / 3) := by
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_five,
    sevenThreeBasisTetrapodAtom_six]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- A basis-tetrapod cosine: `gamma_{0,3} = 1/sqrt 3`.  (The twelve mixed pairs carry
`+-1/sqrt 3` according to the tetrapod signs; the squared value `1/3` below is
sign-free.) -/
theorem directionGram_sevenThreeBasisTetrapodDesign_zero_three :
    directionGram sevenThreeBasisTetrapodDesign 0 3 = (Real.sqrt 3)⁻¹ := by
  have hmul : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hnonzero : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  rw [directionGram_sevenThreeBasisTetrapodDesign, sevenThreeBasisTetrapodAtom_zero,
    sevenThreeBasisTetrapodAtom_three]
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  field_simp
  linear_combination hmul

/-- Every mixed pair carries edge weight exactly `1/3`, sample `(0,3)`. -/
theorem edgeWeight_sevenThreeBasisTetrapodDesign_zero_three :
    edgeWeight sevenThreeBasisTetrapodDesign 0 3 = 1 / 3 := by
  rw [edgeWeight, directionGram_sevenThreeBasisTetrapodDesign_zero_three, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-! ### Calibration: the tetrapod triple is the tie, the basis triple is max-volume -/

/-- The tetrapod triple `{3,4,5}` has `sigma = 1/3`. -/
theorem directionTripleSigma_tetrapodTriple_sevenThreeBasisTetrapodDesign :
    directionTripleSigma sevenThreeBasisTetrapodDesign 3 4 5 = 1 / 3 := by
  rw [directionTripleSigma, directionGram_sevenThreeBasisTetrapodDesign_three_four,
    directionGram_sevenThreeBasisTetrapodDesign_three_five,
    directionGram_sevenThreeBasisTetrapodDesign_four_five]
  norm_num

/-- The tetrapod triple `{3,4,5}` has oriented product `P = -1/27`. -/
theorem directionTripleProduct_tetrapodTriple_sevenThreeBasisTetrapodDesign :
    directionTripleProduct sevenThreeBasisTetrapodDesign 3 4 5 = -(1 / 27) := by
  rw [directionTripleProduct, directionGram_sevenThreeBasisTetrapodDesign_three_four,
    directionGram_sevenThreeBasisTetrapodDesign_three_five,
    directionGram_sevenThreeBasisTetrapodDesign_four_five]
  norm_num

/-- **THE TETRAHEDRAL TIE**: the tetrapod triple sits exactly on the single-clause
boundary, `sigma - 3P = 4/9`. -/
theorem tetrapodTriple_tie_sevenThreeBasisTetrapodDesign :
    directionTripleSigma sevenThreeBasisTetrapodDesign 3 4 5
        - 3 * directionTripleProduct sevenThreeBasisTetrapodDesign 3 4 5 = 4 / 9 := by
  rw [directionTripleSigma_tetrapodTriple_sevenThreeBasisTetrapodDesign,
    directionTripleProduct_tetrapodTriple_sevenThreeBasisTetrapodDesign]
  norm_num

/-- The tetrapod triple's Gram determinant: `1 - sigma + 2P = 16/27` (spectrum
`(1/3, 4/3, 4/3)` — domination with margin zero). -/
theorem gramBracket_tetrapodTriple_sevenThreeBasisTetrapodDesign :
    1 - directionTripleSigma sevenThreeBasisTetrapodDesign 3 4 5
        + 2 * directionTripleProduct sevenThreeBasisTetrapodDesign 3 4 5 = 16 / 27 := by
  rw [directionTripleSigma_tetrapodTriple_sevenThreeBasisTetrapodDesign,
    directionTripleProduct_tetrapodTriple_sevenThreeBasisTetrapodDesign]
  norm_num

/-- The tie's determinant clause vanishes EXACTLY: at capacity `2/3` and the
tetrahedral cosines `-1/3` the slack determinant is zero — the scalar form of "the
tetrapod triple dominates with margin zero". -/
theorem slackDeterminantThree_tetrapodTriple_eq_zero :
    slackDeterminantThree (2 / 3) (2 / 3) (2 / 3) (-(1 / 3)) (-(1 / 3)) (-(1 / 3)) = 0 := by
  simp only [slackDeterminantThree]
  norm_num

/-- **The tetrapod triple DOMINATES** — through the landed seven-clause slack
criterion, with the determinant clause holding with equality (the tie). -/
theorem dominates_tetrapodTriple_sevenThreeBasisTetrapodDesign :
    Dominates sevenThreeBasisTetrapodDesign {3, 4, 5} := by
  have hpositive : ∀ atomIndex : Fin 7,
      0 < leverageOf (sevenThreeBasisTetrapodDesign.atom atomIndex) := fun atomIndex => by
    rw [leverageOf_sevenThreeBasisTetrapodDesign]
    norm_num
  refine (dominates_triple_iff_slackClauses sevenThreeBasisTetrapodDesign (hpositive 3)
    (hpositive 4) (hpositive 5) (by decide) (by decide) (by decide)).mpr ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [weightSlack_sevenThreeBasisTetrapodDesign, edgeWeight,
      directionGram_sevenThreeBasisTetrapodDesign_three_four,
      directionGram_sevenThreeBasisTetrapodDesign_three_five,
      directionGram_sevenThreeBasisTetrapodDesign_four_five, slackDeterminantThree] <;>
    norm_num

/-- The basis triple has `sigma = 0` — three orthogonal directions. -/
theorem directionTripleSigma_basisTriple_sevenThreeBasisTetrapodDesign :
    directionTripleSigma sevenThreeBasisTetrapodDesign 0 1 2 = 0 := by
  rw [directionTripleSigma, directionGram_sevenThreeBasisTetrapodDesign_zero_one,
    directionGram_sevenThreeBasisTetrapodDesign_zero_two,
    directionGram_sevenThreeBasisTetrapodDesign_one_two]
  norm_num

/-- The basis triple has oriented product `P = 0`. -/
theorem directionTripleProduct_basisTriple_sevenThreeBasisTetrapodDesign :
    directionTripleProduct sevenThreeBasisTetrapodDesign 0 1 2 = 0 := by
  rw [directionTripleProduct, directionGram_sevenThreeBasisTetrapodDesign_zero_one,
    directionGram_sevenThreeBasisTetrapodDesign_zero_two,
    directionGram_sevenThreeBasisTetrapodDesign_one_two]
  norm_num

/-- **The basis triple is max-volume**: its Gram determinant `1 - sigma + 2P` equals
`1`, the ceiling no triple of unit directions can exceed
(`Gtz.one_sub_directionTripleSigma_add_two_mul_directionTripleProduct_le_one`).  The
tetrapod triple's `16/27` is strictly below it: the brief's earlier claim that the
TETRAPOD triple is max-volume is FALSE, and this is the corrected calibration — at
this witness the max-volume selector picks a strictly dominating triple while the tie
sits on a non-maximal one (the M7-relevant reading). -/
theorem gramBracket_basisTriple_sevenThreeBasisTetrapodDesign :
    1 - directionTripleSigma sevenThreeBasisTetrapodDesign 0 1 2
        + 2 * directionTripleProduct sevenThreeBasisTetrapodDesign 0 1 2 = 1 := by
  rw [directionTripleSigma_basisTriple_sevenThreeBasisTetrapodDesign,
    directionTripleProduct_basisTriple_sevenThreeBasisTetrapodDesign]
  norm_num

/-- **The basis triple DOMINATES** — through the landed orthogonal-triple gate. -/
theorem dominates_basisTriple_sevenThreeBasisTetrapodDesign :
    Dominates sevenThreeBasisTetrapodDesign {0, 1, 2} := by
  refine dominates_of_orthogonalTriple_of_one_le sevenThreeBasisTetrapodDesign
    (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [leverageOf_sevenThreeBasisTetrapodDesign]; norm_num
  · rw [leverageOf_sevenThreeBasisTetrapodDesign]; norm_num
  · rw [leverageOf_sevenThreeBasisTetrapodDesign]; norm_num
  · rw [atomPairing, sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom_zero,
      sevenThreeBasisTetrapodAtom_one]
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · rw [atomPairing, sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom_zero,
      sevenThreeBasisTetrapodAtom_two]
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · rw [atomPairing, sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom_one,
      sevenThreeBasisTetrapodAtom_two]
    norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- The basis triple's domination gap along any probe is exactly `2 |probe|^2`:
`S_{{0,1,2}} - 1 = 2 . 1`. -/
theorem basisTripleGap_form_sevenThreeBasisTetrapodDesign (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum sevenThreeBasisTetrapodDesign {0, 1, 2} - 1) *ᵥ probe)
      = 2 * (probe ⬝ᵥ probe) := by
  have hsqrt : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [dominationGap_form, show ({0, 1, 2} : Finset (Fin 7)) = insert 0 (insert 1 {2}) from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (probe 0 ^ 2 + probe 1 ^ 2 + probe 2 ^ 2) * hsqrt

/-- **The basis triple dominates STRICTLY**: the gap is positive definite (margin
exactly `2`).  So the witness is NOT a tie through its max-volume triple; only the
tetrapod triples tie. -/
theorem posDef_basisTripleGap_sevenThreeBasisTetrapodDesign :
    (subsetSum sevenThreeBasisTetrapodDesign {0, 1, 2} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 7)) fun memberIndex _ =>
      posSemidef_atomMatrix (sevenThreeBasisTetrapodDesign.atom memberIndex)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, basisTripleGap_form_sevenThreeBasisTetrapodDesign]
    have hnormPositive := dotProduct_self_pos hprobe
    linarith

/-! ## 4. The R3 statement and its non-vacuity -/

/-- **THE `(7,3)` UNIFORM-SHARE STATEMENT** — residual R3, the frontier this workflow
serves.  Every weighted `(7,3)` design whose atoms all carry share `3/7` and are all
heavy has a dominating triple.  Mirrors the landed `Gtz.GtzUniformShareSixThree`; by
`Gtz.discriminantCovering_seven_iff_rank_three` the free-weight `(7,3)` statement is
all of rank-three GTZ, and this Prop is its uniform-share slice. -/
def GtzUniformShareSevenThree : Prop :=
  ∀ D : WeightedDesign 7 3, (∀ atomIndex, atomShare D atomIndex = 3 / 7) → AllHeavy D →
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates D C

/-- The witness satisfies the CONCLUSION of the `(7,3)` uniform-share statement: its
basis triple dominates. -/
theorem exists_dominating_triple_sevenThreeBasisTetrapodDesign :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates sevenThreeBasisTetrapodDesign C :=
  ⟨{0, 1, 2}, by decide, dominates_basisTriple_sevenThreeBasisTetrapodDesign⟩

/-- **NON-VACUITY OF R3, in one statement**: the witness inhabits the hypothesis
stratum of `Gtz.GtzUniformShareSevenThree` (uniform share `3/7`, all-heavy) AND its
conclusion (a dominating triple exists).  Before this file no design in the tree
satisfied `forall c, atomShare D c = 3/7`; every landed theorem carrying that
hypothesis was potentially vacuous, as wf3's audit recorded. -/
theorem sevenThreeBasisTetrapodDesign_witnesses_gtzUniformShareSevenThree :
    (∀ atomIndex, atomShare sevenThreeBasisTetrapodDesign atomIndex = 3 / 7)
      ∧ AllHeavy sevenThreeBasisTetrapodDesign
      ∧ ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates sevenThreeBasisTetrapodDesign C :=
  ⟨atomShare_sevenThreeBasisTetrapodDesign, allHeavy_sevenThreeBasisTetrapodDesign,
    exists_dominating_triple_sevenThreeBasisTetrapodDesign⟩

end Gtz
