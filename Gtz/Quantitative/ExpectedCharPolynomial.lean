/-
# The expected characteristic polynomial: coefficients, the rank-three sign criterion,
# the tetrahedron computed exactly, and the tilt family named

The volume-sampling mixture `Gtz.mixedCharPoly` (`Gtz/Reduction/MixedCharPolynomial.lean`)
is the expected characteristic polynomial of the subset atom sums under the
projection determinantal measure `π(C) = det P_C`.  Writing
`q = X^rank − c₁ X^(rank−1) + c₂ X^(rank−2) − …`, its coefficients are the
DPP-averaged elementary symmetric functions of the selected Gram,

    c_j  =  E_π[e_j(Gram_C)]  =  ∑_{|J| = j} (det P_J)² / ∏_{c ∈ J} t_c,

weighted sums of FOURTH powers of `j`-dimensional volumes.  This file supplies
what the campaign's expected-polynomial instrument needs and can actually prove.

## What is PROVED here

  * **The coefficients.**  `expectedElementary D j` is the displayed sum, with
    `expectedElementary_zero = 1` and — the only one the rest of the file uses —
    `expectedElementary_one = ∑_c t_c ℓ_c²`, via the singleton minor
    `shadowDeterminant_singleton = t_c ℓ_c`.
  * **B4, unconditional.**  `sq_rank_le_expectedElementary_one` : `rank² ≤ c₁`.
    One line of Jensen (`Gtz.sq_weightedMean_le_weightedMean_sq`) on the trace
    identity `∑_c t_c ℓ_c = rank`.  So at rank three `c₁ ≥ 9` with slack at least
    `6` over the `c₁ ≥ 3` that `q''(1) ≤ 0` needs: that Taylor leg is FREE and can
    never bind.
  * **The rank-three coefficient of `X^(rank−1)` in closed form**, unconditional:
    `coeff_mixedCharPoly_pred_rank = −expectedSubsetTrace`, the DPP average of
    `trace S_C`.
  * **B6, the sign criterion**, standalone real algebra with no reference to GTZ:
    `nonneg_of_elementarySymmetric_nonneg` (three reals whose three elementary
    symmetric functions are nonnegative are themselves nonnegative) and its
    polynomial wrapper `forall_root_one_le_of_taylorSigns` — for a monic cubic
    that splits over ℝ, all roots are `≥ 1` iff `q(1) ≤ 0`, `q'(1) ≥ 0`,
    `q''(1) ≤ 0`.  Reusable, and used below.
  * **B3, total ties.**  `mixedCharPoly_eval_one_eq_zero_of_totalTieSupported` :
    if every positively-weighted `rank`-subset has `det(1 − S_C) = 0` then
    `q(1) = 0`.  The mechanism is measure-independent — it holds for ANY weighting
    of the bases, which is why the tie boundary is free for the whole instrument
    and is NOT where the difficulty lives.  Companion:
    `not_posDef_gap_of_shadowDeterminant_eq_zero`, so a weightless subset can never
    dominate strictly either.
  * **B5, the tetrahedron, exactly.**  `mixedCharPoly_tetraDesign = (X − 1)(X − 4)²`
    with `mixedCharPoly_tetraDesign_expanded = X³ − 9X² + 24X − 16`, so
    `(c₁, c₂, c₃) = (9, 24, 16)`; `expectedElementary_one_tetraDesign = 9`, which is
    exactly `rank² = 9`, so **B4's Jensen step is TIGHT at the tetrahedron**.  The
    sign criterion is then applied for real:
    `forall_root_tetraDesign_one_le` derives "every root is `≥ 1`" from the three
    Taylor signs `(0, 9, −12)`.  `Gtz.tetraDesign_isTie` is shipped, so this is a
    tie where the expected polynomial is rooted exactly at one — zero margin.
  * **The tilt family, named and reparametrised honestly.**  `tiltedMixture` is
    the unnormalised tilted mixture, `tiltedMixture_one = mixedCharPoly` pins the
    uniform tilt, and `EcpStar` states the conjecture.  One theorem of content:
    `exists_root_tiltedMixture_one_rootKillDesign_lt_one` — the UNIFORM tilt fails
    at `(6,3)`, so if `EcpStar` holds at all it needs a genuinely non-constant
    tilt.

## Reparametrisation of the tilt, recorded so the statement is not misread

The brief's tilt is `μ^y(C) ∝ (∏_{c ∈ C} y_c) · det Γ_C` against the ATOM Gram
`Γ = Gram(g)`.  Since `det P_C = (∏_{c ∈ C} t_c) · det Γ_C`
(`Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum` at selection size the
rank), that measure is `(∏_{c ∈ C} y_c/t_c) · det P_C`.  So `tiltedMixture D tilt`
below is the brief's family with `tilt = y/t`, and `tilt ≡ 1` is the brief's
`y = t`, i.e. `π` itself.  The tilt ranges over all positive vectors either way, so
`EcpStar` is the brief's statement; only the coordinate changed.

## What is NOT proved, and why each is named rather than buried

  * **`c_j` is the `j`-th coefficient of `q`, for `j ≥ 1`.**  This needs the DPP
    one-point (and, for `j ≥ 2`, the `j`-point) inclusion identity
    `∑_{C ⊇ J} det P_C = det P_J`, which is not in Mathlib and not in this
    repository.  It ships as `Gtz.IsProjectionOnePointMarginal`
    (`Gtz/Design/VolumeSamplingAverage.lean`) with its construction plan, and the
    `j = 1` bridge is proved CONDITIONALLY on it:
    `expectedSubsetTrace_eq_expectedElementary_one_of_marginal`, hence
    `coeff_mixedCharPoly_pred_rank_of_marginal` and the rank-three Taylor
    consequence `coeff_mixedCharPoly_two_le_neg_nine_of_marginal`.  Nothing
    unconditional in this file depends on the marginal.
  * **`q` is real-rooted.**  CITED (Anari–Oveis Gharan arXiv:1412.1143 Cor 3.2 for
    strongly Rayleigh measures; the projection DPP is strongly Rayleigh by
    Borcea–Brändén–Liggett), MEASURED with zero counterexamples in ~1500 exact
    rational designs at ranks 2, 3 and 4, and NOT mechanized.  It ships as
    `IsRealRootedCubic` used only as a hypothesis, never asserted.  Note that
    real-rootedness does not follow pointwise: the average of the real-rooted
    `X² − 1` and `X² + 10X + 25` is `X² + 5X + 12`, discriminant `−23`.
  * **`EcpStar` itself.**  OPEN as a mechanized statement.  The exact evidence, so
    the campaign can stop re-deriving it: at the ICOSAHEDRON (`(6,3)`, six
    diagonals, uniform weight) the uniform tilt gives `q(1) = 16/25 > 0` and
    `minroot(q) = 0.910432248…`, the root of the irreducible `25X³ − 225X² + 540X
    − 324` [EXACT, not mechanized here]; the icosahedron's signed-Gram automorphism
    group has order 60 and acts TRANSITIVELY on the six atoms, so every
    isomorphism-equivariant tilt formula returns the uniform tilt there and
    therefore fails [EXACT, not mechanized].  Separately
    `sup over positive tilts of minroot(q_tilt) = max_C λ_min(Gram_C)` exactly, so
    the bare existential `∃ tilt` is GtzWeighted restated and cannot prove it
    [EXACT-BY-HAND, not mechanized].  The only mechanized fragment is the uniform
    tilt's failure at `(6,3)`, below.
  * **The pocket has a fat margin.**  REFUTED, exactly, off-Lean: a `(6,3)` design
    with `q(1) > 0` and `max_C λ_min(Gram_C)` certified in
    `[17638/15625, 1128833/1000000)`, and the K4 graphic design at conductances
    `(1, s, s, s, s, 1)`, `s = (√17 − 3)/2`, with `q(1) > 0` and
    `max_C λ_min = 3(7 − √17)/8 = 1.078835…`.  So "inside the pocket GTZ has
    slack ≥ 1.4" is FALSE; the available slack is at most `(13 − 3√17)/8 ≈ 0.0788`.
    Not mechanized here — both are rational-frame witnesses and so mechanizable
    without radicals, which is the recommended next step.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressCertificate
import Gtz.Design.VolumeSamplingAverage
import Gtz.LinAlg.ProjectionForm
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.MixedCharPolynomial
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The coefficients `c_j` -/

/-- **The expected elementary symmetric coefficient**
`c_j = ∑_{|J| = j} (det P_J)² / ∏_{c ∈ J} t_c`.  Equivalently
`∑_{|J| = j} (∏_{c ∈ J} t_c) · det(Gram_J)²`, a weighted sum of fourth powers of
`j`-dimensional volumes.  Under the DPP inclusion identity this is
`E_π[e_j(Gram_C)]`, hence the `j`-th coefficient of `Gtz.mixedCharPoly` up to
sign; that identification is NOT available (see the module header) and is never
used. -/
noncomputable def expectedElementary (D : WeightedDesign m k) (level : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard level,
    shadowDeterminant D selected ^ 2 / ∏ atomIndex ∈ selected, D.weight atomIndex

/-- The empty minor of the projection chart is one: an empty determinant. -/
theorem shadowDeterminant_empty (D : WeightedDesign m k) :
    shadowDeterminant D ∅ = 1 := by
  rw [shadowDeterminant]
  refine Matrix.det_eq_one_of_card_eq_zero ?_
  rw [Fintype.card_coe, Finset.card_empty]

/-- `c₀ = 1`: the only zero-element subset is empty, and both its minor and its
weight product are one. -/
theorem expectedElementary_zero (D : WeightedDesign m k) :
    expectedElementary D 0 = 1 := by
  rw [expectedElementary, Finset.powersetCard_zero, Finset.sum_singleton,
    shadowDeterminant_empty, Finset.prod_empty]
  norm_num

/-- **The singleton minor of the projection chart is the share** `P_cc = t_c ℓ_c`.
A `1 × 1` determinant read off `Gtz.projectionOfDesign_diagonal`. -/
theorem shadowDeterminant_singleton (D : WeightedDesign m k) (atomIndex : Fin m) :
    shadowDeterminant D {atomIndex} = D.weight atomIndex * leverageOf (D.atom atomIndex) := by
  classical
  haveI : Unique { member // member ∈ ({atomIndex} : Finset (Fin m)) } :=
    ⟨⟨⟨atomIndex, Finset.mem_singleton_self atomIndex⟩⟩,
      fun member => Subtype.ext (Finset.mem_singleton.mp member.2)⟩
  rw [shadowDeterminant, Matrix.det_unique, Matrix.submatrix_apply]
  have hdefault : (default : { member // member ∈ ({atomIndex} : Finset (Fin m)) }).val
      = atomIndex := Finset.mem_singleton.mp (default :
        { member // member ∈ ({atomIndex} : Finset (Fin m)) }).2
  rw [hdefault, projectionOfDesign_diagonal]

/-- **`c₁ = ∑_c t_c ℓ_c²`.**  The `1`-element subsets are the singletons, whose
minor is the share `t_c ℓ_c`, so each term is `(t_c ℓ_c)²/t_c = t_c ℓ_c²`.  This
is the quantity `Gtz.trace_leverageWeightedAtomSum` computes as the trace of the
B1 average. -/
theorem expectedElementary_one (D : WeightedDesign m k) :
    expectedElementary D 1
      = ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2 := by
  classical
  rw [expectedElementary, Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  have hsingleton : (⟨singleton, Finset.singleton_injective⟩ :
      Fin m ↪ Finset (Fin m)) atomIndex = {atomIndex} := rfl
  rw [hsingleton, shadowDeterminant_singleton, Finset.prod_singleton]
  rw [div_eq_iff (D.weight_pos atomIndex).ne']
  ring

/-! ## B4: `rank² ≤ c₁`, and why the second-derivative leg can never bind -/

/-- **B4.**  `rank² ≤ c₁`.  Jensen on the probability weights `t` applied to the
leverages, whose `t`-mean is the rank by the trace identity
`Gtz.sum_weight_mul_leverage`.  At rank three this reads `c₁ ≥ 9`, while the
Taylor leg `q''(1) ≤ 0` needs only `c₁ ≥ 3` — slack at least `6`, so that leg is
free.  Tight at the tetrahedron (`expectedElementary_one_tetraDesign`). -/
theorem sq_rank_le_expectedElementary_one (D : WeightedDesign m k) :
    (k : ℝ) ^ 2 ≤ expectedElementary D 1 := by
  have hjensen := sq_weightedMean_le_weightedMean_sq_design D
    fun atomIndex => leverageOf (D.atom atomIndex)
  rw [sum_weight_mul_leverage D] at hjensen
  rw [expectedElementary_one]
  exact hjensen

/-- The same bound in the raw share form, for consumers holding the sum rather
than the coefficient. -/
theorem sq_rank_le_sum_weight_mul_leverage_sq (D : WeightedDesign m k) :
    (k : ℝ) ^ 2 ≤ ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2 := by
  rw [← expectedElementary_one]
  exact sq_rank_le_expectedElementary_one D

/-! ## The coefficient of `X^(rank−1)`, unconditionally

`coeff (rank − 1) (charpoly M) = −trace M`, so the mixture's subleading
coefficient is minus the DPP average of the subset traces.  Turning that average
into `c₁` is exactly the one-point marginal, and is done separately below. -/

/-- The trace of a subset atom sum is the sum of its leverages. -/
theorem trace_subsetSum (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    Matrix.trace (subsetSum D selected)
      = ∑ atomIndex ∈ selected, leverageOf (D.atom atomIndex) := by
  rw [subsetSum, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun atomIndex _ => trace_atomMatrix (D.atom atomIndex)

/-- The volume-sampling average of the subset traces. -/
noncomputable def expectedSubsetTrace (D : WeightedDesign m k) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    shadowDeterminant D selected * Matrix.trace (subsetSum D selected)

/-- **The subleading coefficient of the mixture, in closed form and
unconditionally**: `coeff (rank − 1) q = −E_π[trace S_C]`.  Termwise from
`Matrix.trace_eq_neg_charpoly_coeff`; no inclusion identity is used. -/
theorem coeff_mixedCharPoly_pred_rank (D : WeightedDesign m k) (hrank : 0 < k) :
    (mixedCharPoly D).coeff (k - 1) = -expectedSubsetTrace D := by
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hrank
  rw [mixedCharPoly, Polynomial.finsetSum_coeff, expectedSubsetTrace, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun selected _ => ?_
  have hcoeff : (subsetSum D selected).charpoly.coeff (k - 1)
      = -Matrix.trace (subsetSum D selected) := by
    have htrace := Matrix.trace_eq_neg_charpoly_coeff (subsetSum D selected)
    rw [Fintype.card_fin] at htrace
    linarith [htrace]
  rw [Polynomial.coeff_smul, smul_eq_mul, hcoeff]
  ring

/-- **The `j = 1` inclusion bridge, CONDITIONAL on the DPP one-point marginal.**
Exchanging the two summations turns the average of the subset traces into
`∑_c ℓ_c · Pr_π[c ∈ C]`, and the marginal supplies `Pr_π[c ∈ C] = t_c ℓ_c`. -/
theorem expectedSubsetTrace_eq_expectedElementary_one_of_marginal (D : WeightedDesign m k)
    (hmarginal : IsProjectionOnePointMarginal D) :
    expectedSubsetTrace D = expectedElementary D 1 := by
  classical
  have hexchange : expectedSubsetTrace D
      = ∑ atomIndex, leverageOf (D.atom atomIndex)
        * ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            if atomIndex ∈ selected then shadowDeterminant D selected else 0 := by
    rw [expectedSubsetTrace]
    have hinner : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        shadowDeterminant D selected * Matrix.trace (subsetSum D selected)
          = ∑ atomIndex, leverageOf (D.atom atomIndex)
            * (if atomIndex ∈ selected then shadowDeterminant D selected else 0) := by
      intro selected _
      rw [trace_subsetSum, Finset.mul_sum,
        ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun atomIndex => atomIndex ∈ selected)]
      have hleft : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => atomIndex ∈ selected),
            leverageOf (D.atom atomIndex)
              * (if atomIndex ∈ selected then shadowDeterminant D selected else 0)
          = ∑ atomIndex ∈ selected,
              shadowDeterminant D selected * leverageOf (D.atom atomIndex) := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.sum_congr rfl fun atomIndex hmem => by rw [if_pos hmem]; ring
      have hright : ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => atomIndex ∉ selected),
            leverageOf (D.atom atomIndex)
              * (if atomIndex ∈ selected then shadowDeterminant D selected else 0)
          = 0 := by
        refine Finset.sum_eq_zero fun atomIndex hmem => ?_
        rw [if_neg (Finset.mem_filter.mp hmem).2, mul_zero]
      rw [hleft, hright, add_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    exact Finset.sum_congr rfl fun atomIndex _ => (Finset.mul_sum _ _ _).symm
  rw [hexchange, expectedElementary_one]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [hmarginal atomIndex]
  ring

/-- The subleading coefficient IS `−c₁`, conditional on the marginal. -/
theorem coeff_mixedCharPoly_pred_rank_of_marginal (D : WeightedDesign m k) (hrank : 0 < k)
    (hmarginal : IsProjectionOnePointMarginal D) :
    (mixedCharPoly D).coeff (k - 1) = -expectedElementary D 1 := by
  rw [coeff_mixedCharPoly_pred_rank D hrank,
    expectedSubsetTrace_eq_expectedElementary_one_of_marginal D hmarginal]

/-- **B4's Taylor consequence at rank three, conditional on the marginal.**  For a
monic cubic, `q''(1)/2 = 3 + coeff 2 q`, so `coeff 2 q = −c₁ ≤ −9` forces
`q''(1) ≤ −12 < 0`.  Stated on the coefficient rather than on
`Polynomial.derivative` twice, since the coefficient is what the closed form
delivers. -/
theorem coeff_mixedCharPoly_two_le_neg_nine_of_marginal (D : WeightedDesign m 3)
    (hmarginal : IsProjectionOnePointMarginal D) :
    (mixedCharPoly D).coeff 2 ≤ -9 := by
  have hcoeff := coeff_mixedCharPoly_pred_rank_of_marginal D (by norm_num) hmarginal
  have hbound := sq_rank_le_expectedElementary_one D
  norm_num at hcoeff hbound
  linarith

/-! ## B6: the rank-three sign criterion

Pure real algebra, independent of GTZ, designs and measures.  Shift `y = x − 1`:
for a monic cubic that splits, all roots are `≥ 1` exactly when the three
elementary symmetric functions of the SHIFTED roots are nonnegative, and those
three are `−q(1)`, `q'(1)` and `−q''(1)/2`. -/

/-- **The core.**  Three reals whose three elementary symmetric functions are all
nonnegative are themselves all nonnegative.  Proof: if `first < 0` then
`first³ = e₁ first² − e₂ first + e₃`, whose right side is a sum of three
nonnegative terms while its left side is strictly negative. -/
theorem nonneg_of_elementarySymmetric_nonneg (first second third : ℝ)
    (hfirstSymmetric : 0 ≤ first + second + third)
    (hsecondSymmetric : 0 ≤ first * second + first * third + second * third)
    (hthirdSymmetric : 0 ≤ first * second * third) :
    0 ≤ first ∧ 0 ≤ second ∧ 0 ≤ third := by
  have hgeneric : ∀ candidate other another : ℝ,
      0 ≤ candidate + other + another →
      0 ≤ candidate * other + candidate * another + other * another →
      0 ≤ candidate * other * another → 0 ≤ candidate := by
    intro candidate other another hone htwo hthree
    by_contra hnegative
    push Not at hnegative
    nlinarith [hone, htwo, hthree, hnegative, sq_nonneg candidate, mul_pos
      (neg_pos.mpr hnegative) (neg_pos.mpr hnegative)]
  refine ⟨hgeneric first second third hfirstSymmetric hsecondSymmetric hthirdSymmetric,
    hgeneric second first third (by linarith) (by linarith) (by linarith),
    hgeneric third first second (by linarith) (by linarith) (by linarith)⟩

/-- A monic cubic that SPLITS over the reals, with its three roots exhibited.
Used only as a hypothesis: real-rootedness of the volume-sampling mixture is
CITED and MEASURED, never asserted here (see the module header). -/
def IsRealRootedCubic (target : Polynomial ℝ) : Prop :=
  ∃ firstRoot secondRoot thirdRoot : ℝ,
    target = (Polynomial.X - Polynomial.C firstRoot)
      * (Polynomial.X - Polynomial.C secondRoot)
      * (Polynomial.X - Polynomial.C thirdRoot)

/-- The value at one of a split monic cubic. -/
theorem eval_one_of_splitCubic (firstRoot secondRoot thirdRoot : ℝ) :
    ((Polynomial.X - Polynomial.C firstRoot) * (Polynomial.X - Polynomial.C secondRoot)
        * (Polynomial.X - Polynomial.C thirdRoot)).eval 1
      = -((firstRoot - 1) * (secondRoot - 1) * (thirdRoot - 1)) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-- The first derivative at one of a split monic cubic: the second elementary
symmetric function of the SHIFTED roots. -/
theorem eval_one_derivative_of_splitCubic (firstRoot secondRoot thirdRoot : ℝ) :
    (Polynomial.derivative ((Polynomial.X - Polynomial.C firstRoot)
        * (Polynomial.X - Polynomial.C secondRoot)
        * (Polynomial.X - Polynomial.C thirdRoot))).eval 1
      = (firstRoot - 1) * (secondRoot - 1) + (firstRoot - 1) * (thirdRoot - 1)
        + (secondRoot - 1) * (thirdRoot - 1) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_zero]
  ring

/-- The second derivative at one of a split monic cubic: minus twice the first
elementary symmetric function of the SHIFTED roots. -/
theorem eval_one_secondDerivative_of_splitCubic (firstRoot secondRoot thirdRoot : ℝ) :
    (Polynomial.derivative (Polynomial.derivative
        ((Polynomial.X - Polynomial.C firstRoot) * (Polynomial.X - Polynomial.C secondRoot)
          * (Polynomial.X - Polynomial.C thirdRoot)))).eval 1
      = -2 * ((firstRoot - 1) + (secondRoot - 1) + (thirdRoot - 1)) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  ring

/-- **B6 — THE SIGN CRITERION.**  For a monic cubic that splits over the reals, if
`q(1) ≤ 0`, `q'(1) ≥ 0` and `q''(1) ≤ 0` then EVERY root is at least one.  Purely
about polynomials: no design, no measure, no GTZ.  This is the analogue at rank
three of "all Taylor coefficients at one alternate", and it is exactly the shape
in which the campaign's expected-polynomial instrument is stated. -/
theorem forall_root_one_le_of_taylorSigns {target : Polynomial ℝ}
    (hsplit : IsRealRootedCubic target)
    (hvalue : target.eval 1 ≤ 0)
    (hderivative : 0 ≤ (Polynomial.derivative target).eval 1)
    (hsecondDerivative : (Polynomial.derivative (Polynomial.derivative target)).eval 1 ≤ 0) :
    ∀ root : ℝ, target.IsRoot root → 1 ≤ root := by
  obtain ⟨firstRoot, secondRoot, thirdRoot, hfactor⟩ := hsplit
  subst hfactor
  rw [eval_one_of_splitCubic] at hvalue
  rw [eval_one_derivative_of_splitCubic] at hderivative
  rw [eval_one_secondDerivative_of_splitCubic] at hsecondDerivative
  obtain ⟨hfirstNonneg, hsecondNonneg, hthirdNonneg⟩ :=
    nonneg_of_elementarySymmetric_nonneg (firstRoot - 1) (secondRoot - 1) (thirdRoot - 1)
      (by linarith) (by linarith) (by linarith)
  intro root hroot
  rw [Polynomial.IsRoot] at hroot
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hroot
  rcases mul_eq_zero.mp hroot with hleft | hthird
  · rcases mul_eq_zero.mp hleft with hfirst | hsecond
    · have : root = firstRoot := by linarith [sub_eq_zero.mp hfirst]
      rw [this]; linarith
    · have : root = secondRoot := by linarith [sub_eq_zero.mp hsecond]
      rw [this]; linarith
  · have : root = thirdRoot := by linarith [sub_eq_zero.mp hthird]
    rw [this]; linarith

/-! ## B3: at a total tie the expected polynomial is rooted exactly at one

The mechanism is measure-independent: if every subset carrying positive mass has
`1` in its spectrum then the mixture vanishes at one for ANY weighting of the
bases.  So the TIE BOUNDARY IS FREE for the whole expected-polynomial instrument;
the difficulty lives elsewhere (`Gtz.not_mixedRootAtLeastOne_sixThree`). -/

/-- **A total tie, in the form the mixture consumes.**  Every `rank`-subset either
carries no volume-sampling mass or has determinant zero at level one, i.e. has `1`
in the spectrum of its Gram.

This is STRICTLY STRONGER than `Gtz.IsTie`, and deliberately so: `IsTie` asks only
that SOME subset dominate and none dominate strictly, which permits positively
weighted subsets that do not dominate at all — as happens at the icosahedron,
where ten of the twenty triples fail to dominate.  Conversely a total tie has no
strict dominator (`not_posDef_gap_of_totalTieSupported`) but need not have a weak
one without a separate GTZ input. -/
def IsTotalTieSupported (D : WeightedDesign m k) : Prop :=
  ∀ selected : Finset (Fin m), selected.card = k →
    shadowDeterminant D selected = 0
      ∨ (Matrix.scalar (Fin k) (1 : ℝ) - subsetSum D selected).det = 0

/-- **B3.**  At a total tie the expected characteristic polynomial vanishes at one
— zero margin, exactly.  Every summand of `Gtz.mixedCharPoly_eval` is a product
one of whose two factors is zero. -/
theorem mixedCharPoly_eval_one_eq_zero_of_totalTieSupported (D : WeightedDesign m k)
    (htie : IsTotalTieSupported D) : (mixedCharPoly D).eval 1 = 0 := by
  rw [mixedCharPoly_eval]
  refine Finset.sum_eq_zero fun selected hmem => ?_
  rcases htie selected (Finset.mem_powersetCard.mp hmem).2 with hmass | hlevel
  · rw [hmass, zero_mul]
  · rw [hlevel, mul_zero]

/-- A subset with zero volume-sampling mass is linearly dependent, so its Gram is
singular and its gap can never be positive definite: the weightless subsets are
not silently excluded from the tie statement, they genuinely cannot dominate
strictly. -/
theorem not_posDef_gap_of_shadowDeterminant_eq_zero (D : WeightedDesign m k)
    {selected : Finset (Fin m)} (hcard : selected.card = k)
    (hmass : shadowDeterminant D selected = 0) :
    ¬ (subsetSum D selected - 1).PosDef := by
  intro hposDef
  have hgram : (subsetSum D selected).det = 0 := by
    have hfactor := shadowDeterminant_eq_weightProduct_mul_detSubsetSum D hcard
    rw [hmass] at hfactor
    have hweights : (0 : ℝ) < ∏ atomIndex ∈ selected, D.weight atomIndex :=
      Finset.prod_pos fun atomIndex _ => D.weight_pos atomIndex
    rcases mul_eq_zero.mp hfactor.symm with hzero | hdet
    · exact absurd hzero hweights.ne'
    · exact hdet
  have hsplit : subsetSum D selected = (subsetSum D selected - 1) + 1 := by abel
  have hpos : (0 : ℝ) < (subsetSum D selected).det := by
    rw [hsplit]
    exact (hposDef.add_posSemidef Matrix.PosSemidef.one).det_pos
  rw [hgram] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **A total tie has no strict dominator.**  Half of `Gtz.IsTie` for free; the
other half (existence of a weak dominator) is exactly a GTZ input at that design
and is not implied. -/
theorem not_posDef_gap_of_totalTieSupported (D : WeightedDesign m k)
    (htie : IsTotalTieSupported D) (selected : Finset (Fin m)) (hcard : selected.card = k) :
    ¬ (subsetSum D selected - 1).PosDef := by
  rcases htie selected hcard with hmass | hlevel
  · exact not_posDef_gap_of_shadowDeterminant_eq_zero D hcard hmass
  · intro hposDef
    have hgapDet : (subsetSum D selected - 1).det = 0 := by
      have hscalarOne : Matrix.scalar (Fin k) (1 : ℝ) = 1 := map_one _
      have hnegate : Matrix.scalar (Fin k) (1 : ℝ) - subsetSum D selected
          = -(subsetSum D selected - 1) := by
        rw [hscalarOne, neg_sub]
      rw [hnegate, Matrix.det_neg, Fintype.card_fin] at hlevel
      rcases mul_eq_zero.mp hlevel with hsign | hdet
      · exact absurd hsign (pow_ne_zero k (by norm_num : (-1 : ℝ) ≠ 0))
      · exact hdet
    have hdetPos := hposDef.det_pos
    rw [hgapDet] at hdetPos
    exact absurd hdetPos (lt_irrefl 0)

/-! ## B5: the tetrahedron, exactly

`Gtz.tetraDesign` is the `(4,3)` regular tetrahedron at uniform weight `1/4`.  Its
four triples are exactly the complements of the four directions, so every one has
atom sum `4·I − d_j d_jᵀ` with spectrum `(1, 4, 4)`; the mixture is that single
polynomial.  `Gtz.tetraDesign_isTie` is shipped, so this is a genuine tie at which
the expected polynomial is rooted exactly at one. -/

/-- Every triple of the tetrahedron is a rank-one deficit of `4·I`: its complement
in `Fin 4` is a singleton, and the four directions resolve `4·I`. -/
theorem subsetSum_tetraDesign_of_card_three {selected : Finset (Fin 4)}
    (hcard : selected.card = 3) :
    ∃ missingDirection : Fin 4, subsetSum tetraDesign selected
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (tetraAtom missingDirection) := by
  classical
  have hcomplCard : selectedᶜ.card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  obtain ⟨missingDirection, hmissing⟩ := Finset.card_eq_one.mp hcomplCard
  refine ⟨missingDirection, ?_⟩
  have hsplit := Finset.sum_add_sum_compl selected
    (fun dirIndex : Fin 4 => atomMatrix (tetraAtom dirIndex))
  rw [hmissing, Finset.sum_singleton, sum_tetraAtomMatrix_eq_fourSmulOne] at hsplit
  exact eq_sub_of_add_eq hsplit

/-- **B5, THE CALIBRATION WITNESS.**  At the regular tetrahedron the expected
characteristic polynomial is `(X − 1)(X − 4)²` on the nose.  No enumeration: every
triple carries the same characteristic polynomial and
`Gtz.mixedCharPoly_eq_of_classes` aggregates through
`Gtz.sum_shadowDeterminant_eq_one`. -/
theorem mixedCharPoly_tetraDesign :
    mixedCharPoly tetraDesign = (Polynomial.X - 1) * (Polynomial.X - 4) ^ 2 := by
  refine mixedCharPoly_eq_of_classes tetraDesign _ fun selected hcard => ?_
  obtain ⟨missingDirection, hsum⟩ := subsetSum_tetraDesign_of_card_three hcard
  exact Or.inr (by rw [hsum, charpoly_four_smul_sub_tetraAtom])

/-- **B5's coefficients: `(c₁, c₂, c₃) = (9, 24, 16)`.**  The expanded form of
`(X − 1)(X − 4)²`. -/
theorem mixedCharPoly_tetraDesign_expanded :
    mixedCharPoly tetraDesign
      = Polynomial.X ^ 3 - 9 * Polynomial.X ^ 2 + 24 * Polynomial.X - 16 := by
  rw [mixedCharPoly_tetraDesign]
  ring

/-- **B4 is TIGHT at the tetrahedron**: `c₁ = 9 = rank²` exactly, because every
leverage is `3` and every weight is `1/4`.  So the Jensen step of
`sq_rank_le_expectedElementary_one` has zero slack here — there is no room to
strengthen it. -/
theorem expectedElementary_one_tetraDesign : expectedElementary tetraDesign 1 = 9 := by
  rw [expectedElementary_one]
  have hterm : ∀ atomIndex : Fin 4,
      tetraDesign.weight atomIndex * leverageOf (tetraDesign.atom atomIndex) ^ 2 = 9 / 4 := by
    intro atomIndex
    have hleverage : leverageOf (tetraAtom atomIndex) = 3 := by
      rw [leverageOf]
      fin_cases atomIndex <;>
        norm_num [tetraAtom, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_cons]
    show tetraDesign.weight atomIndex * leverageOf (tetraAtom atomIndex) ^ 2 = 9 / 4
    rw [hleverage]
    show (1 : ℝ) / 4 * 3 ^ 2 = 9 / 4
    norm_num
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hterm atomIndex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- The tetrahedron's mixture splits, with roots `1, 4, 4`. -/
theorem isRealRootedCubic_mixedCharPoly_tetraDesign :
    IsRealRootedCubic (mixedCharPoly tetraDesign) := by
  refine ⟨1, 4, 4, ?_⟩
  rw [mixedCharPoly_tetraDesign]
  simp only [Polynomial.C_1, map_ofNat]
  ring

/-- The three Taylor signs at the tetrahedron: `q(1) = 0`, `q'(1) = 9`,
`q''(1) = −12`.  The first is B3 with zero margin; the second and third are the
free legs. -/
theorem mixedCharPoly_tetraDesign_taylorAtOne :
    (mixedCharPoly tetraDesign).eval 1 = 0
      ∧ (Polynomial.derivative (mixedCharPoly tetraDesign)).eval 1 = 9
      ∧ (Polynomial.derivative (Polynomial.derivative (mixedCharPoly tetraDesign))).eval 1
        = -12 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [mixedCharPoly_tetraDesign] <;>
    simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.derivative_ofNat,
      Polynomial.derivative_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
      Polynomial.eval_zero] <;>
    norm_num

/-- **The sign criterion applied for real.**  From the three Taylor signs at the
tetrahedron, `forall_root_one_le_of_taylorSigns` concludes that every root of the
expected characteristic polynomial is at least one — with `1` itself attained
(`Gtz.tetraDesign_isTie` is a shipped tie), so the bound is exactly saturated. -/
theorem forall_root_tetraDesign_one_le :
    ∀ root : ℝ, (mixedCharPoly tetraDesign).IsRoot root → 1 ≤ root := by
  obtain ⟨hvalue, hderivative, hsecondDerivative⟩ := mixedCharPoly_tetraDesign_taylorAtOne
  exact forall_root_one_le_of_taylorSigns isRealRootedCubic_mixedCharPoly_tetraDesign
    (by rw [hvalue]) (by rw [hderivative]; norm_num) (by rw [hsecondDerivative]; norm_num)

/-- The tetrahedron IS a total tie in the sense `IsTotalTieSupported`: every triple
has `det(I − S_C) = (1−1)(1−4)(1−4) = 0`, because the spectrum is `(1, 4, 4)`.  So
B3 applies to it, and independently `Gtz.tetraDesign_isTie` records that it is a
tie in the campaign's own vocabulary. -/
theorem isTotalTieSupported_tetraDesign : IsTotalTieSupported tetraDesign := by
  intro selected hcard
  refine Or.inr ?_
  obtain ⟨missingDirection, hsum⟩ := subsetSum_tetraDesign_of_card_three hcard
  have hcharpoly : (subsetSum tetraDesign selected).charpoly
      = (Polynomial.X - 1) * (Polynomial.X - 4) ^ 2 := by
    rw [hsum, charpoly_four_smul_sub_tetraAtom]
  have hdet : (Matrix.scalar (Fin 3) (1 : ℝ) - subsetSum tetraDesign selected).det
      = (subsetSum tetraDesign selected).charpoly.eval 1 := (Matrix.eval_charpoly _ 1).symm
  rw [hdet, hcharpoly]
  simp

/-! ## The tilt family, and ECP-STAR named

`tiltedMixture D tilt` is the UNNORMALISED tilted mixture: scaling a polynomial by
a positive constant does not move its roots, so no normalisation is carried and no
positivity side condition on the total mass is needed.  See the module header for
the reparametrisation `tilt = y/t` against the brief's own tilt. -/

/-- The tilted volume-sampling mixture, unnormalised. -/
noncomputable def tiltedMixture (D : WeightedDesign m k) (tilt : Fin m → ℝ) : Polynomial ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    ((∏ atomIndex ∈ selected, tilt atomIndex) * shadowDeterminant D selected)
      • (subsetSum D selected).charpoly

/-- **The uniform tilt is `π` itself**: `tiltedMixture D 1 = mixedCharPoly D`.  This
is the point of the family the brief calls `y = t`. -/
theorem tiltedMixture_one (D : WeightedDesign m k) :
    tiltedMixture D (fun _ => 1) = mixedCharPoly D := by
  rw [tiltedMixture, mixedCharPoly]
  exact Finset.sum_congr rfl fun selected _ => by rw [Finset.prod_const_one, one_mul]

/-- **ECP-STAR, NAMED not proved.**  For every weighted design there is a positive
tilt whose tilted mixture has no root strictly below one.  Stated root-free, in
the repository's convention (`Gtz.HasMixedRootAtLeastOne`), so that no
existence-of-a-real-root claim is smuggled in.

Status: OPEN as a mechanized statement, and the module header records the exact
off-Lean evidence — the icosahedron kills every equivariant tilt formula, and the
bare existential is `GtzWeighted` restated because
`sup over tilts of minroot = max_C λ_min`.  The one mechanized fragment is that
the UNIFORM tilt does not witness it at `(6,3)`
(`exists_root_tiltedMixture_one_rootKillDesign_lt_one`), so any witness must be a
genuinely non-constant tilt. -/
def EcpStar (m k : ℕ) : Prop :=
  ∀ D : WeightedDesign m k, ∃ tilt : Fin m → ℝ, (∀ atomIndex, 0 < tilt atomIndex) ∧
    ∀ level : ℝ, level < 1 → (tiltedMixture D tilt).eval level ≠ 0

/-- **The uniform tilt FAILS at `(6,3)`.**  Transporting
`Gtz.exists_root_rootKillDesign_lt_one` through `tiltedMixture_one`: at the `D₃`
root system the tilted mixture at `tilt ≡ 1` has a root strictly inside `(0,1)`.
So the constant tilt is not a witness for `EcpStar 6 3`, and the campaign's tilt
question is not vacuous at the uniform point — it is refuted there. -/
theorem exists_root_tiltedMixture_one_rootKillDesign_lt_one :
    ∃ level : ℝ, 0 < level ∧ level < 1
      ∧ (tiltedMixture rootKillDesign (fun _ => 1)).eval level = 0 := by
  obtain ⟨level, hpositive, hbelow, hroot⟩ := exists_root_rootKillDesign_lt_one
  exact ⟨level, hpositive, hbelow, by rw [tiltedMixture_one]; exact hroot⟩

/-- The same statement in the `EcpStar`-witness shape: the constant tilt does not
discharge the `(6,3)` instance. -/
theorem not_uniformTilt_witnesses_ecpStar_sixThree :
    ¬ ∀ level : ℝ, level < 1
        → (tiltedMixture rootKillDesign (fun _ => 1)).eval level ≠ 0 := by
  intro hnoRoot
  obtain ⟨level, -, hbelow, hroot⟩ := exists_root_tiltedMixture_one_rootKillDesign_lt_one
  exact hnoRoot level hbelow hroot

end Gtz
