/-
# The real fourth-moment bound: the sharpest identified quantum of realness

For a weighted design write `s_c = t_c |g_c|^2` for the share of atom `c`
(`Gtz.atomShare`) and `u_c = g_c / |g_c|` for its direction (`Gtz.unitAtom`), so
that `sum_c s_c u_c u_c^T = I_k` and `sum_c s_c = k`
(`Gtz.sum_atomShare_eq_rank`).  This file mechanizes the projective-2-design
lower bound on the share-weighted fourth moment of the direction Gram
`gamma_cd = <u_c, u_d>` (`Gtz.directionGram`), together with the field-blind
bound it is to be compared against.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* **The real floor, at every rank and every size, UNCONDITIONALLY**
  (`realMomentFloor_le_shareWeightedFourthMoment`):

      3k/(k+2)  <=  sum_{c,d} s_c s_d gamma_cd^4.

  No all-heavy hypothesis, no uniform-share hypothesis, no nondegeneracy
  hypothesis: a degenerate atom has share zero and contributes nothing, which is
  what `atomShare_mul_leverageOf_unitAtom` makes unconditional.  At rank three
  the constant is `9/5` (`nine_fifths_le_shareWeightedFourthMoment`).

* **The field-blind floor** (`hermitianMomentFloor_le_shareWeightedFourthMoment`):
  `2k/(k+1) <= sum_{c,d} s_c s_d gamma_cd^4`, at rank three `3/2`.  It is proved
  from the SAME tensor by the SAME certificate with one summand deleted, and in
  particular WITHOUT `sum_veroneseMomentTensor_swap`.

* **The gap between them is strict for every rank at least two**
  (`hermitianMomentFloor_lt_realMomentFloor`):
  `3k/(k+2) - 2k/(k+1) = k(k-1)/((k+1)(k+2)) > 0`.  At rank three, `9/5` against
  `3/2`.  THAT GAP IS THE REALNESS, and it is now a theorem rather than a remark.

* **The cross-check against the shipped syzygy floor**
  (`fourth_moment_ge_of_uniformShare_viaRealMomentFloor`).  Specialised to a
  `(7,3)` design on the uniform-share stratum `s_c = 3/7`, the general bound
  reads `(3/7)^2 sum_{a,b} gamma_ab^4 >= 9/5`, i.e.
  `sum_{a,b} gamma_ab^4 >= 49/5` — EXACTLY the constant of the shipped
  `Gtz.fourth_moment_ge_of_uniformShare`, which is proved by a completely
  different route (the Veronese syzygy and the explicit test matrix
  `Y_ab = 14 N [a=b] + 3N - 14 theta_a theta_b`).  The two constants agree on
  the nose, so neither is a plausible-but-wrong constant.  Calibration: on
  `Gtz.sevenThreeBasisTetrapodDesign` the shipped total is `265/27`
  (`Gtz.fourth_moment_sevenThreeBasisTetrapodDesign`), so the share-weighted
  value there is `265/147`, clearing `9/5` by exactly `2/735`.

* **Per-row refinements**, the form a crux argument consumes.  For a
  nondegenerate atom `a`, `1/k <= sum_d s_d gamma_ad^4`
  (`inv_rank_le_rowFourthMoment`); and, splitting off the diagonal,
  `s_a + (1 - s_a)^2/(k - s_a) <= sum_d s_d gamma_ad^4`
  (`sharpRowFourthMoment_ge`).  The second is strictly sharper wherever
  `s_a /= 1/k`: at `(7,3)` uniform share it gives `5/9` against `1/3`.  Both ride
  the shipped row law `Gtz.sum_atomShare_mul_sq_directionGram` (`sum_d s_d
  gamma_ad^2 = 1`) and its diagonal split, so unlike the global bound they DO use
  the Parseval identity and not merely `sum_c s_c = k`.

## WHERE REALNESS IS CONSUMED — one step, named

The moment tensor is `A(i,j,p,q) = sum_c s_c (u_c)_i (u_c)_j (u_c)_p (u_c)_q`
(`veroneseMomentTensor`), and the certificate is the single square

    0 <= sum_{i,j,p,q} ( A(i,j,p,q) - N(i,j,p,q)/(k+2) )^2,

where `N` is the isotropic four-tensor `isotropicMomentNumerator`

    N(i,j,p,q) = [i=p][j=q] + [i=q][j=p] + [i=j][p=q].

Expanding needs exactly two numbers: `sum A*N = 3k`, from three contractions
each equal to the rank, and `sum N^2 = 3k(k+2)`, which is the SAME three
contractions applied to `N` itself.  The three contractions are

* `sum_veroneseMomentTensor_direct` — `sum_{i,j} A(i,j,i,j) = k`;
* `sum_veroneseMomentTensor_trace`  — `sum_{i,p} A(i,i,p,p) = k`;
* `sum_veroneseMomentTensor_swap`   — `sum_{i,j} A(i,j,j,i) = k`.  **THIS ONE.**

The swap contraction holds because `A(i,j,p,q)` is invariant under exchanging
`i` and `j` — that is, because the rank-one atom `u u^T` is a SYMMETRIC matrix.
Its proof is literally a `ring` step after unfolding `Gtz.atomMatrix`, since
`u_i u_j = u_j u_i`.  Over the complex numbers the rank-one atom is `u u*`, which
is Hermitian but NOT symmetric, and the middle summand `[i=q][j=p]` of `N` is
unavailable.  Deleting exactly that summand gives `hermitianMomentNumerator`,
whose self-pairing is `2k(k+1)` instead of `3k(k+2)`, and the floor drops from
`3k/(k+2)` to `2k/(k+1)`.

The dimension reading of the same step: `N/(k+2)` is `(2 Sym + I (x) I)/(k+2)`,
and the trace of the symmetriser `Sym` is `dim Sym(R^k) = k(k+1)/2`, which is
`6` at `k = 3`; the Hermitian analogue has `k^2 = 9`.  On the trace-free part
that is `5` against `8`, which is why five-versus-eight is load-bearing.  In the
shipped traceless chart the same `5` appears as
`Gtz.finrank_symmetricTracelessSubmodule_atRankThree`, and the common length
`2/3` of the traceless directions as
`Gtz.frobeniusNormSq_veroneseTracelessPart`; this file does not route through
either, because the dimension enters through the swap contraction rather than
through a rank bound.

For the same reason the Veronese factorisation is NOT a dependency here.  It is
in any case already shipped, at every size, as
`Gtz.hadamardSquareGram_eq_veroneseRows_mul_transpose` and
`Gtz.rank_hadamardSquareGram_le_six`.

## NOT PROVED — the honest boundary

* **Nothing over the complex numbers is formalised here.**  No complex design,
  no Hermitian moment tensor, no complex 2-design exists in this development.
  What is mechanized is that deleting the swap summand from the certificate
  costs exactly `3k/(k+2) - 2k/(k+1)`.  The identification of `2k/(k+1)` as THE
  complex constant is cited from the campaign ledger, not proved, and the name
  `hermitianMomentNumerator` records that analogy — it is a real tensor.

* **Sharpness is not proved.**  Equality in the certificate holds exactly when
  `A = N/(k+2)`, i.e. when the design is a projective 2-design; that
  characterisation is not mechanized, and no attainment claim is made.  The
  `2/735` calibration above shows the floor is nearly attained at `(7,3)`, which
  is evidence of sharpness, not a proof of it.

* **No domination consequence.**  Nothing here produces a dominating triple, and
  the bound is not connected to `Gtz.Dominates`.  It is a constraint on the
  direction Gram of an arbitrary weighted design, offered as substrate.

* The field-blind bound is strictly weaker than the real one and is landed only
  as the comparison object; it is never used to prove anything.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Reduction.BranchTransferConstants
import Gtz.Quantitative.SevenThreeSyzygy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. Toolkit -/

private theorem sum_swap_atomOutward (values : Fin k → Fin k → Fin m → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ atomIndex, values rowFirst rowSecond atomIndex
      = ∑ atomIndex, ∑ rowFirst, ∑ rowSecond, values rowFirst rowSecond atomIndex := by
  rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
    (Finset.sum_comm : ∑ rowSecond, ∑ atomIndex, values rowFirst rowSecond atomIndex
      = ∑ atomIndex, ∑ rowSecond, values rowFirst rowSecond atomIndex)]
  exact Finset.sum_comm

private theorem sum_atomPairOutward (values : Fin k → Fin m → Fin m → ℝ) :
    ∑ rowIndex, ∑ firstAtom, ∑ secondAtom, values rowIndex firstAtom secondAtom
      = ∑ firstAtom, ∑ secondAtom, ∑ rowIndex, values rowIndex firstAtom secondAtom := by
  rw [(Finset.sum_comm : ∑ rowIndex, ∑ firstAtom, ∑ secondAtom, values rowIndex firstAtom secondAtom
    = ∑ firstAtom, ∑ rowIndex, ∑ secondAtom, values rowIndex firstAtom secondAtom)]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem sum_double_atomMatrix_mul (leftVector rightVector : Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond,
        atomMatrix leftVector rowFirst rowSecond * atomMatrix rightVector rowFirst rowSecond
      = (leftVector ⬝ᵥ rightVector) ^ 2 := by
  simp only [atomMatrix, Matrix.vecMulVec_apply, dotProduct]
  rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
    Finset.sum_congr rfl fun rowSecond (_ : rowSecond ∈ Finset.univ) =>
      show leftVector rowFirst * leftVector rowSecond
            * (rightVector rowFirst * rightVector rowSecond)
        = (leftVector rowFirst * rightVector rowFirst)
            * (leftVector rowSecond * rightVector rowSecond) from by ring]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private theorem sum_tensor_sq_sub_scaled
    (leftTensor rightTensor : Fin k → Fin k → Fin k → Fin k → ℝ) (scale : ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        (leftTensor rowFirst rowSecond colFirst colSecond
          - scale * rightTensor rowFirst rowSecond colFirst colSecond) ^ 2
      = (∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
            leftTensor rowFirst rowSecond colFirst colSecond ^ 2)
        - 2 * scale * (∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
            leftTensor rowFirst rowSecond colFirst colSecond
              * rightTensor rowFirst rowSecond colFirst colSecond)
        + scale ^ 2 * ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
            rightTensor rowFirst rowSecond colFirst colSecond ^ 2 := by
  have hpointwise : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      (leftTensor rowFirst rowSecond colFirst colSecond
          - scale * rightTensor rowFirst rowSecond colFirst colSecond) ^ 2
        = leftTensor rowFirst rowSecond colFirst colSecond ^ 2
          - 2 * scale * (leftTensor rowFirst rowSecond colFirst colSecond
              * rightTensor rowFirst rowSecond colFirst colSecond)
          + scale ^ 2 * rightTensor rowFirst rowSecond colFirst colSecond ^ 2 := by
    intro _ _ _ _; ring
  simp only [hpointwise, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The share kills the degenerate directions, so the direction's leverage may be
cancelled against the share with no hypothesis. -/
theorem atomShare_mul_leverageOf_unitAtom (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomShare D atomIndex * leverageOf (unitAtom D atomIndex) = atomShare D atomIndex := by
  have hnonneg : 0 ≤ leverageOf (D.atom atomIndex) := by rw [leverageOf]; positivity
  rcases eq_or_lt_of_le hnonneg with hvanishes | hpositive
  · have hshare : atomShare D atomIndex = 0 := by rw [atomShare, ← hvanishes, mul_zero]
    rw [hshare, zero_mul]
  · rw [leverageOf_unitAtom D hpositive, mul_one]

private theorem atomShare_nonneg (D : WeightedDesign m k) (atomIndex : Fin m) :
    0 ≤ atomShare D atomIndex := by
  rw [atomShare]
  have hlev : 0 ≤ leverageOf (D.atom atomIndex) := by rw [leverageOf]; positivity
  exact mul_nonneg (D.weight_pos atomIndex).le hlev

/-! ## 2. The Veronese fourth-moment tensor -/

/-- The share-weighted fourth-moment tensor. -/
noncomputable def veroneseMomentTensor (D : WeightedDesign m k)
    (rowFirst rowSecond colFirst colSecond : Fin k) : ℝ :=
  ∑ atomIndex, atomShare D atomIndex
    * (atomMatrix (unitAtom D atomIndex) rowFirst rowSecond
        * atomMatrix (unitAtom D atomIndex) colFirst colSecond)

private theorem sum_atomShare_mul_leverage_sq (D : WeightedDesign m k) :
    ∑ atomIndex, atomShare D atomIndex
        * (leverageOf (unitAtom D atomIndex) * leverageOf (unitAtom D atomIndex))
      = (k : ℝ) := by
  rw [← sum_atomShare_eq_rank D]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [← mul_assoc, atomShare_mul_leverageOf_unitAtom, atomShare_mul_leverageOf_unitAtom]

/-- **THE DIRECT CONTRACTION**: `sum_{i,j} A(i,j,i,j) = k`.  Field-blind — it is
the Frobenius norm of each atom, `|u_c u_c^T|^2 = 1`, weighted by the shares. -/
theorem sum_veroneseMomentTensor_direct (D : WeightedDesign m k) :
    ∑ rowFirst, ∑ rowSecond, veroneseMomentTensor D rowFirst rowSecond rowFirst rowSecond
      = (k : ℝ) := by
  rw [show (∑ rowFirst, ∑ rowSecond,
        veroneseMomentTensor D rowFirst rowSecond rowFirst rowSecond)
      = ∑ atomIndex, ∑ rowFirst, ∑ rowSecond, atomShare D atomIndex
          * (atomMatrix (unitAtom D atomIndex) rowFirst rowSecond
              * atomMatrix (unitAtom D atomIndex) rowFirst rowSecond) from
    sum_swap_atomOutward _, ← sum_atomShare_mul_leverage_sq D]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  simp only [atomMatrix, Matrix.vecMulVec_apply, leverageOf]
  rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
    Finset.sum_congr rfl fun rowSecond (_ : rowSecond ∈ Finset.univ) =>
      show atomShare D atomIndex
            * (unitAtom D atomIndex rowFirst * unitAtom D atomIndex rowSecond
                * (unitAtom D atomIndex rowFirst * unitAtom D atomIndex rowSecond))
        = atomShare D atomIndex * unitAtom D atomIndex rowFirst ^ 2
            * unitAtom D atomIndex rowSecond ^ 2 from by ring]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- **THE SWAP CONTRACTION**: `sum_{i,j} A(i,j,j,i) = k`.  **THIS IS THE STEP
WHERE REALNESS IS CONSUMED.**  It reduces to the direct contraction because
`A(i,j,p,q)` is unchanged when `i` and `j` are exchanged, i.e. because the atom
`u u^T` is a SYMMETRIC matrix — the proof is a `ring` step on `u_i u_j = u_j u_i`.
Over the complex numbers the atom `u u*` is Hermitian, not symmetric, and this
contraction is unavailable; the field-blind bound below is exactly what survives
its deletion. -/
theorem sum_veroneseMomentTensor_swap (D : WeightedDesign m k) :
    ∑ rowFirst, ∑ rowSecond, veroneseMomentTensor D rowFirst rowSecond rowSecond rowFirst
      = (k : ℝ) := by
  rw [← sum_veroneseMomentTensor_direct D]
  refine Finset.sum_congr rfl fun rowFirst _ => Finset.sum_congr rfl fun rowSecond _ => ?_
  simp only [veroneseMomentTensor, atomMatrix, Matrix.vecMulVec_apply]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **THE TRACE CONTRACTION**: `sum_{i,p} A(i,i,p,p) = k`.  Field-blind — it is
the squared trace of each atom, `(tr u_c u_c^T)^2 = 1`, weighted by the shares. -/
theorem sum_veroneseMomentTensor_trace (D : WeightedDesign m k) :
    ∑ rowFirst, ∑ colFirst, veroneseMomentTensor D rowFirst rowFirst colFirst colFirst
      = (k : ℝ) := by
  rw [show (∑ rowFirst, ∑ colFirst,
        veroneseMomentTensor D rowFirst rowFirst colFirst colFirst)
      = ∑ atomIndex, ∑ rowFirst, ∑ colFirst, atomShare D atomIndex
          * (atomMatrix (unitAtom D atomIndex) rowFirst rowFirst
              * atomMatrix (unitAtom D atomIndex) colFirst colFirst) from
    sum_swap_atomOutward _, ← sum_atomShare_mul_leverage_sq D]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  simp only [atomMatrix, Matrix.vecMulVec_apply, leverageOf]
  rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
    Finset.sum_congr rfl fun colFirst (_ : colFirst ∈ Finset.univ) =>
      show atomShare D atomIndex
            * (unitAtom D atomIndex rowFirst * unitAtom D atomIndex rowFirst
                * (unitAtom D atomIndex colFirst * unitAtom D atomIndex colFirst))
        = atomShare D atomIndex * unitAtom D atomIndex rowFirst ^ 2
            * unitAtom D atomIndex colFirst ^ 2 from by ring]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The share-weighted fourth moment of the direction Gram. -/
noncomputable def shareWeightedFourthMoment (D : WeightedDesign m k) : ℝ :=
  ∑ firstAtom, ∑ secondAtom, atomShare D firstAtom * atomShare D secondAtom
    * directionGram D firstAtom secondAtom ^ 4

/-- **THE NORM IDENTITY**: the squared Frobenius norm of the moment tensor IS the
share-weighted fourth moment, `sum_{i,j,p,q} A^2 = sum_{c,d} s_c s_d gamma_cd^4`.
Unconditional; the two inner double sums each collapse to `gamma_cd^2`. -/
theorem sum_sq_veroneseMomentTensor (D : WeightedDesign m k) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        veroneseMomentTensor D rowFirst rowSecond colFirst colSecond ^ 2
      = shareWeightedFourthMoment D := by
  have hexpand : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      veroneseMomentTensor D rowFirst rowSecond colFirst colSecond ^ 2
        = ∑ firstAtom, ∑ secondAtom,
            (atomShare D firstAtom * (atomMatrix (unitAtom D firstAtom) rowFirst rowSecond
                * atomMatrix (unitAtom D firstAtom) colFirst colSecond))
              * (atomShare D secondAtom * (atomMatrix (unitAtom D secondAtom) rowFirst rowSecond
                  * atomMatrix (unitAtom D secondAtom) colFirst colSecond)) := by
    intro _ _ _ _
    rw [pow_two, veroneseMomentTensor, Finset.sum_mul_sum]
  have hinner : ∀ firstAtom secondAtom : Fin m,
      ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
          (atomShare D firstAtom * (atomMatrix (unitAtom D firstAtom) rowFirst rowSecond
              * atomMatrix (unitAtom D firstAtom) colFirst colSecond))
            * (atomShare D secondAtom * (atomMatrix (unitAtom D secondAtom) rowFirst rowSecond
                * atomMatrix (unitAtom D secondAtom) colFirst colSecond))
        = atomShare D firstAtom * atomShare D secondAtom
            * directionGram D firstAtom secondAtom ^ 4 := by
    intro firstAtom secondAtom
    rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
      Finset.sum_congr rfl fun rowSecond (_ : rowSecond ∈ Finset.univ) =>
        Finset.sum_congr rfl fun colFirst (_ : colFirst ∈ Finset.univ) =>
          Finset.sum_congr rfl fun colSecond (_ : colSecond ∈ Finset.univ) =>
            show (atomShare D firstAtom * (atomMatrix (unitAtom D firstAtom) rowFirst rowSecond
                  * atomMatrix (unitAtom D firstAtom) colFirst colSecond))
                * (atomShare D secondAtom * (atomMatrix (unitAtom D secondAtom) rowFirst rowSecond
                    * atomMatrix (unitAtom D secondAtom) colFirst colSecond))
              = atomShare D firstAtom * atomShare D secondAtom
                  * ((atomMatrix (unitAtom D firstAtom) rowFirst rowSecond
                        * atomMatrix (unitAtom D secondAtom) rowFirst rowSecond)
                      * (atomMatrix (unitAtom D firstAtom) colFirst colSecond
                          * atomMatrix (unitAtom D secondAtom) colFirst colSecond)) from by ring]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [sum_double_atomMatrix_mul, directionGram]
    ring
  simp only [hexpand]
  rw [Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
      Finset.sum_congr rfl fun rowSecond (_ : rowSecond ∈ Finset.univ) =>
        Finset.sum_congr rfl fun colFirst (_ : colFirst ∈ Finset.univ) =>
          sum_atomPairOutward _,
    Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
      Finset.sum_congr rfl fun rowSecond (_ : rowSecond ∈ Finset.univ) =>
        sum_atomPairOutward _,
    Finset.sum_congr rfl fun rowFirst (_ : rowFirst ∈ Finset.univ) =>
      sum_atomPairOutward _,
    sum_atomPairOutward _, shareWeightedFourthMoment]
  exact Finset.sum_congr rfl fun firstAtom _ =>
    Finset.sum_congr rfl fun secondAtom _ => hinner firstAtom secondAtom

/-! ## 3. The two test tensors -/

/-- The REAL isotropic four-tensor numerator: THREE Kronecker terms. -/
def isotropicMomentNumerator (rowFirst rowSecond colFirst colSecond : Fin k) : ℝ :=
  (if rowFirst = colFirst then (1:ℝ) else 0) * (if rowSecond = colSecond then (1:ℝ) else 0)
    + (if rowFirst = colSecond then (1:ℝ) else 0) * (if rowSecond = colFirst then (1:ℝ) else 0)
    + (if rowFirst = rowSecond then (1:ℝ) else 0) * (if colFirst = colSecond then (1:ℝ) else 0)

/-- The FIELD-BLIND numerator: the same tensor with the swap term deleted. -/
def hermitianMomentNumerator (rowFirst rowSecond colFirst colSecond : Fin k) : ℝ :=
  (if rowFirst = colFirst then (1:ℝ) else 0) * (if rowSecond = colSecond then (1:ℝ) else 0)
    + (if rowFirst = rowSecond then (1:ℝ) else 0) * (if colFirst = colSecond then (1:ℝ) else 0)

private theorem sum_tensor_mul_kroneckerDirect (tensor : Fin k → Fin k → Fin k → Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        tensor rowFirst rowSecond colFirst colSecond
          * ((if rowFirst = colFirst then (1:ℝ) else 0)
              * (if rowSecond = colSecond then (1:ℝ) else 0))
      = ∑ rowFirst, ∑ rowSecond, tensor rowFirst rowSecond rowFirst rowSecond := by
  simp

private theorem sum_tensor_mul_kroneckerSwap (tensor : Fin k → Fin k → Fin k → Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        tensor rowFirst rowSecond colFirst colSecond
          * ((if rowFirst = colSecond then (1:ℝ) else 0)
              * (if rowSecond = colFirst then (1:ℝ) else 0))
      = ∑ rowFirst, ∑ rowSecond, tensor rowFirst rowSecond rowSecond rowFirst := by
  simp

private theorem sum_tensor_mul_kroneckerTrace (tensor : Fin k → Fin k → Fin k → Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        tensor rowFirst rowSecond colFirst colSecond
          * ((if rowFirst = rowSecond then (1:ℝ) else 0)
              * (if colFirst = colSecond then (1:ℝ) else 0))
      = ∑ rowFirst, ∑ colFirst, tensor rowFirst rowFirst colFirst colFirst := by
  simp

/-- Pairing ANY four-tensor against the isotropic numerator is the sum of its three
contractions.  Stated for an arbitrary tensor so that it computes both `sum A*N`
(with the design contractions) and `sum N^2` (with `N` in place of `A`). -/
theorem sum_tensor_mul_isotropicMomentNumerator (tensor : Fin k → Fin k → Fin k → Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        tensor rowFirst rowSecond colFirst colSecond
          * isotropicMomentNumerator rowFirst rowSecond colFirst colSecond
      = (∑ rowFirst, ∑ rowSecond, tensor rowFirst rowSecond rowFirst rowSecond)
        + (∑ rowFirst, ∑ rowSecond, tensor rowFirst rowSecond rowSecond rowFirst)
        + ∑ rowFirst, ∑ colFirst, tensor rowFirst rowFirst colFirst colFirst := by
  have hsplit : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      tensor rowFirst rowSecond colFirst colSecond
          * isotropicMomentNumerator rowFirst rowSecond colFirst colSecond
        = tensor rowFirst rowSecond colFirst colSecond
              * ((if rowFirst = colFirst then (1:ℝ) else 0)
                  * (if rowSecond = colSecond then (1:ℝ) else 0))
            + tensor rowFirst rowSecond colFirst colSecond
              * ((if rowFirst = colSecond then (1:ℝ) else 0)
                  * (if rowSecond = colFirst then (1:ℝ) else 0))
            + tensor rowFirst rowSecond colFirst colSecond
              * ((if rowFirst = rowSecond then (1:ℝ) else 0)
                  * (if colFirst = colSecond then (1:ℝ) else 0)) := by
    intro _ _ _ _; rw [isotropicMomentNumerator]; ring
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_tensor_mul_kroneckerDirect, sum_tensor_mul_kroneckerSwap, sum_tensor_mul_kroneckerTrace]

/-- The field-blind analogue: only the direct and trace contractions appear, the
swap contraction being absent by construction. -/
theorem sum_tensor_mul_hermitianMomentNumerator (tensor : Fin k → Fin k → Fin k → Fin k → ℝ) :
    ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        tensor rowFirst rowSecond colFirst colSecond
          * hermitianMomentNumerator rowFirst rowSecond colFirst colSecond
      = (∑ rowFirst, ∑ rowSecond, tensor rowFirst rowSecond rowFirst rowSecond)
        + ∑ rowFirst, ∑ colFirst, tensor rowFirst rowFirst colFirst colFirst := by
  have hsplit : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      tensor rowFirst rowSecond colFirst colSecond
          * hermitianMomentNumerator rowFirst rowSecond colFirst colSecond
        = tensor rowFirst rowSecond colFirst colSecond
              * ((if rowFirst = colFirst then (1:ℝ) else 0)
                  * (if rowSecond = colSecond then (1:ℝ) else 0))
            + tensor rowFirst rowSecond colFirst colSecond
              * ((if rowFirst = rowSecond then (1:ℝ) else 0)
                  * (if colFirst = colSecond then (1:ℝ) else 0)) := by
    intro _ _ _ _; rw [hermitianMomentNumerator]; ring
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_tensor_mul_kroneckerDirect, sum_tensor_mul_kroneckerTrace]

private theorem sum_double_kronecker :
    ∑ rowFirst : Fin k, ∑ rowSecond : Fin k,
      (if rowFirst = rowSecond then (1:ℝ) else 0) = (k : ℝ) := by
  simp

private theorem sum_double_one : ∑ _rowFirst : Fin k, ∑ _rowSecond : Fin k, (1:ℝ) = (k:ℝ)^2 := by
  simp [sq]

private theorem sum_isotropic_direct :
    ∑ rowFirst : Fin k, ∑ rowSecond : Fin k,
        isotropicMomentNumerator rowFirst rowSecond rowFirst rowSecond
      = (k:ℝ)^2 + 2 * (k:ℝ) := by
  have hpoint : ∀ rowFirst rowSecond : Fin k,
      isotropicMomentNumerator rowFirst rowSecond rowFirst rowSecond
        = 1 + 2 * (if rowFirst = rowSecond then (1:ℝ) else 0) := by
    intro rowFirst rowSecond
    rw [isotropicMomentNumerator]
    by_cases hequal : rowFirst = rowSecond
    · subst hequal; norm_num
    · simp [hequal, Ne.symm hequal]
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_double_kronecker, sum_double_one]

private theorem sum_isotropic_swap :
    ∑ rowFirst : Fin k, ∑ rowSecond : Fin k,
        isotropicMomentNumerator rowFirst rowSecond rowSecond rowFirst
      = (k:ℝ)^2 + 2 * (k:ℝ) := by
  have hpoint : ∀ rowFirst rowSecond : Fin k,
      isotropicMomentNumerator rowFirst rowSecond rowSecond rowFirst
        = 1 + 2 * (if rowFirst = rowSecond then (1:ℝ) else 0) := by
    intro rowFirst rowSecond
    rw [isotropicMomentNumerator]
    by_cases hequal : rowFirst = rowSecond
    · subst hequal; norm_num
    · simp [hequal, Ne.symm hequal]
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_double_kronecker, sum_double_one]

private theorem sum_isotropic_trace :
    ∑ rowFirst : Fin k, ∑ colFirst : Fin k,
        isotropicMomentNumerator rowFirst rowFirst colFirst colFirst
      = (k:ℝ)^2 + 2 * (k:ℝ) := by
  have hpoint : ∀ rowFirst colFirst : Fin k,
      isotropicMomentNumerator rowFirst rowFirst colFirst colFirst
        = 1 + 2 * (if rowFirst = colFirst then (1:ℝ) else 0) := by
    intro rowFirst colFirst
    rw [isotropicMomentNumerator]
    by_cases hequal : rowFirst = colFirst
    · subst hequal; norm_num
    · simp [hequal]
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_double_kronecker, sum_double_one]

private theorem sum_hermitian_direct :
    ∑ rowFirst : Fin k, ∑ rowSecond : Fin k,
        hermitianMomentNumerator rowFirst rowSecond rowFirst rowSecond
      = (k:ℝ)^2 + (k:ℝ) := by
  have hpoint : ∀ rowFirst rowSecond : Fin k,
      hermitianMomentNumerator rowFirst rowSecond rowFirst rowSecond
        = 1 + (if rowFirst = rowSecond then (1:ℝ) else 0) := by
    intro rowFirst rowSecond
    rw [hermitianMomentNumerator]
    by_cases hequal : rowFirst = rowSecond
    · subst hequal; norm_num
    · simp [hequal]
  simp only [hpoint, Finset.sum_add_distrib]
  rw [sum_double_kronecker, sum_double_one]

private theorem sum_hermitian_trace :
    ∑ rowFirst : Fin k, ∑ colFirst : Fin k,
        hermitianMomentNumerator rowFirst rowFirst colFirst colFirst
      = (k:ℝ)^2 + (k:ℝ) := by
  have hpoint : ∀ rowFirst colFirst : Fin k,
      hermitianMomentNumerator rowFirst rowFirst colFirst colFirst
        = 1 + (if rowFirst = colFirst then (1:ℝ) else 0) := by
    intro rowFirst colFirst
    rw [hermitianMomentNumerator]
    by_cases hequal : rowFirst = colFirst
    · subst hequal; norm_num
    · simp [hequal]
  simp only [hpoint, Finset.sum_add_distrib]
  rw [sum_double_kronecker, sum_double_one]

/-- `sum_{i,j,p,q} N^2 = 3k(k+2)`, obtained by pairing `N` against itself.  The
three self-contractions are `k^2 + 2k` each. -/
theorem sum_sq_isotropicMomentNumerator :
    ∑ rowFirst : Fin k, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        isotropicMomentNumerator rowFirst rowSecond colFirst colSecond ^ 2
      = 3 * (k:ℝ) * ((k:ℝ) + 2) := by
  have hsq : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      isotropicMomentNumerator rowFirst rowSecond colFirst colSecond ^ 2
        = isotropicMomentNumerator rowFirst rowSecond colFirst colSecond
            * isotropicMomentNumerator rowFirst rowSecond colFirst colSecond :=
    fun _ _ _ _ => pow_two _
  simp only [hsq]
  rw [sum_tensor_mul_isotropicMomentNumerator, sum_isotropic_direct, sum_isotropic_swap,
    sum_isotropic_trace]
  ring

/-- `sum_{i,j,p,q} H^2 = 2k(k+1)`, the field-blind counterpart, with two
self-contractions of `k^2 + k` each. -/
theorem sum_sq_hermitianMomentNumerator :
    ∑ rowFirst : Fin k, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
        hermitianMomentNumerator rowFirst rowSecond colFirst colSecond ^ 2
      = 2 * (k:ℝ) * ((k:ℝ) + 1) := by
  have hsq : ∀ rowFirst rowSecond colFirst colSecond : Fin k,
      hermitianMomentNumerator rowFirst rowSecond colFirst colSecond ^ 2
        = hermitianMomentNumerator rowFirst rowSecond colFirst colSecond
            * hermitianMomentNumerator rowFirst rowSecond colFirst colSecond :=
    fun _ _ _ _ => pow_two _
  simp only [hsq]
  rw [sum_tensor_mul_hermitianMomentNumerator, sum_hermitian_direct, sum_hermitian_trace]
  ring

/-! ## 4. The two bounds -/

/-- **THE REAL FOURTH-MOMENT BOUND.** -/
theorem realMomentFloor_le_shareWeightedFourthMoment (D : WeightedDesign m k) :
    3 * (k:ℝ) / ((k:ℝ) + 2) ≤ shareWeightedFourthMoment D := by
  have hpositive : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hcertificate : 0 ≤ ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
      (veroneseMomentTensor D rowFirst rowSecond colFirst colSecond
        - ((k:ℝ) + 2)⁻¹ * isotropicMomentNumerator rowFirst rowSecond colFirst colSecond) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_tensor_sq_sub_scaled, sum_sq_veroneseMomentTensor,
    sum_tensor_mul_isotropicMomentNumerator, sum_veroneseMomentTensor_direct,
    sum_veroneseMomentTensor_swap, sum_veroneseMomentTensor_trace,
    sum_sq_isotropicMomentNumerator] at hcertificate
  have hkey : (((k:ℝ) + 2)⁻¹) ^ 2 * (3 * (k:ℝ) * ((k:ℝ) + 2))
      = 3 * (k:ℝ) / ((k:ℝ) + 2) := by
    field_simp
  have hlinear : 2 * ((k:ℝ) + 2)⁻¹ * ((k:ℝ) + (k:ℝ) + (k:ℝ))
      = 2 * (3 * (k:ℝ) / ((k:ℝ) + 2)) := by
    field_simp
    ring
  rw [hkey, hlinear] at hcertificate
  linarith

/-- **THE FIELD-BLIND BOUND.**  Proved WITHOUT the swap contraction. -/
theorem hermitianMomentFloor_le_shareWeightedFourthMoment (D : WeightedDesign m k) :
    2 * (k:ℝ) / ((k:ℝ) + 1) ≤ shareWeightedFourthMoment D := by
  have hpositive : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hcertificate : 0 ≤ ∑ rowFirst, ∑ rowSecond, ∑ colFirst, ∑ colSecond,
      (veroneseMomentTensor D rowFirst rowSecond colFirst colSecond
        - ((k:ℝ) + 1)⁻¹ * hermitianMomentNumerator rowFirst rowSecond colFirst colSecond) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_tensor_sq_sub_scaled, sum_sq_veroneseMomentTensor,
    sum_tensor_mul_hermitianMomentNumerator, sum_veroneseMomentTensor_direct,
    sum_veroneseMomentTensor_trace, sum_sq_hermitianMomentNumerator] at hcertificate
  have hkey : (((k:ℝ) + 1)⁻¹) ^ 2 * (2 * (k:ℝ) * ((k:ℝ) + 1))
      = 2 * (k:ℝ) / ((k:ℝ) + 1) := by
    field_simp
  have hlinear : 2 * ((k:ℝ) + 1)⁻¹ * ((k:ℝ) + (k:ℝ))
      = 2 * (2 * (k:ℝ) / ((k:ℝ) + 1)) := by
    field_simp
    ring
  rw [hkey, hlinear] at hcertificate
  linarith

/-- **THE REALNESS GAP.** -/
theorem hermitianMomentFloor_lt_realMomentFloor {rank : ℕ} (hrank : 2 ≤ rank) :
    2 * (rank:ℝ) / ((rank:ℝ) + 1) < 3 * (rank:ℝ) / ((rank:ℝ) + 2) := by
  have hcast : (2:ℝ) ≤ (rank:ℝ) := by exact_mod_cast hrank
  have hgap : 3 * (rank:ℝ) / ((rank:ℝ) + 2) - 2 * (rank:ℝ) / ((rank:ℝ) + 1)
      = (rank:ℝ) * ((rank:ℝ) - 1) / (((rank:ℝ) + 1) * ((rank:ℝ) + 2)) := by
    field_simp
    ring
  have hstrict : 0 < (rank:ℝ) * ((rank:ℝ) - 1) / (((rank:ℝ) + 1) * ((rank:ℝ) + 2)) :=
    div_pos (by nlinarith [hcast]) (by nlinarith [hcast])
  linarith [hgap, hstrict]

/-- **RANK THREE**: the floor is `9/5`, against the field-blind `3/2`.  This is the
constant the campaign needs. -/
theorem nine_fifths_le_shareWeightedFourthMoment (D : WeightedDesign m 3) :
    9 / 5 ≤ shareWeightedFourthMoment D := by
  have hbound := realMomentFloor_le_shareWeightedFourthMoment D
  norm_num at hbound
  exact hbound

/-- **THE CROSS-CHECK.**  The general bound, specialised to `(7,3)` on the
uniform-share stratum, re-derives the shipped `Gtz.fourth_moment_ge_of_uniformShare`
with the SAME constant `49/5`, by an independent route: this proof uses only the
three tensor contractions, where the shipped one uses the Veronese syzygy and an
explicit test matrix.  Agreement of the two constants is the guard against a
plausible-but-wrong constant, and it is exact — `(3/7)^2 * 49/5 = 9/5`. -/
theorem fourth_moment_ge_of_uniformShare_viaRealMomentFloor (design : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare design atomIndex = 3 / 7) :
    49 / 5 ≤ ∑ firstIndex, ∑ secondIndex,
      hadamardSquareGram design firstIndex secondIndex ^ 2 := by
  have hbound := nine_fifths_le_shareWeightedFourthMoment design
  have hrewrite : shareWeightedFourthMoment design
      = 9 / 49 * ∑ firstIndex, ∑ secondIndex,
          hadamardSquareGram design firstIndex secondIndex ^ 2 := by
    rw [shareWeightedFourthMoment, Finset.mul_sum]
    refine Finset.sum_congr rfl fun firstIndex _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun secondIndex _ => ?_
    rw [huniform firstIndex, huniform secondIndex, hadamardSquareGram_apply]
    ring
  rw [hrewrite] at hbound
  linarith

/-! ## 5. Per-row refinements -/

/-- **THE PER-ROW FLOOR**: `1/k <= sum_d s_d gamma_ad^4` for every nondegenerate
atom `a`.  Unlike the global bound this DOES use the Parseval identity, through
the shipped row law `sum_d s_d gamma_ad^2 = 1`; the certificate is the single
square `sum_d s_d (gamma_ad^2 - 1/k)^2 >= 0`. -/
theorem inv_rank_le_rowFourthMoment (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    ((k:ℝ))⁻¹ ≤ ∑ otherIndex, atomShare D otherIndex
      * directionGram D atomIndex otherIndex ^ 4 := by
  have hsharePositive : 0 < atomShare D atomIndex := mul_pos (D.weight_pos atomIndex) hpositive
  have hrankPositive : (0:ℝ) < (k:ℝ) := by
    rw [← sum_atomShare_eq_rank D]
    exact lt_of_lt_of_le hsharePositive
      (Finset.single_le_sum (fun index _ => atomShare_nonneg D index) (Finset.mem_univ atomIndex))
  have hrow := sum_atomShare_mul_sq_directionGram D hpositive
  have htotal := sum_atomShare_eq_rank D
  have hcertificate : 0 ≤ ∑ otherIndex, atomShare D otherIndex
      * (directionGram D atomIndex otherIndex ^ 2 - ((k:ℝ))⁻¹) ^ 2 :=
    Finset.sum_nonneg fun otherIndex _ =>
      mul_nonneg (atomShare_nonneg D otherIndex) (sq_nonneg _)
  have hexpand : ∑ otherIndex, atomShare D otherIndex
        * (directionGram D atomIndex otherIndex ^ 2 - ((k:ℝ))⁻¹) ^ 2
      = (∑ otherIndex, atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 4)
        - 2 * ((k:ℝ))⁻¹ * (∑ otherIndex, atomShare D otherIndex
            * directionGram D atomIndex otherIndex ^ 2)
        + ((k:ℝ))⁻¹ ^ 2 * ∑ otherIndex, atomShare D otherIndex := by
    rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
      show atomShare D otherIndex * (directionGram D atomIndex otherIndex ^ 2 - ((k:ℝ))⁻¹) ^ 2
        = atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 4
            - 2 * ((k:ℝ))⁻¹ * (atomShare D otherIndex
                * directionGram D atomIndex otherIndex ^ 2)
            + ((k:ℝ))⁻¹ ^ 2 * atomShare D otherIndex from by ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexpand, hrow, htotal] at hcertificate
  have hinverse : ((k:ℝ))⁻¹ ^ 2 * (k:ℝ) = ((k:ℝ))⁻¹ := by field_simp
  rw [hinverse] at hcertificate
  linarith

/-- **THE SHARP PER-ROW FLOOR**: `s_a + (1 - s_a)^2/(k - s_a) <= sum_d s_d
gamma_ad^4`.  Same certificate run off the diagonal, where the shipped split row
law gives `sum_{d /= a} s_d gamma_ad^2 = 1 - s_a` and the shares off `a` total
`k - s_a`.  Strictly sharper than the `1/k` floor whenever `s_a /= 1/k`: at
`(7,3)` uniform share it reads `3/7 + (4/7)^2/(18/7) = 5/9` against `1/3`.  The
hypothesis `s_a < k` is what keeps the quotient defined. -/
theorem sharpRowFourthMoment_ge (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex))
    (hstrict : atomShare D atomIndex < (k:ℝ)) :
    atomShare D atomIndex
        + (1 - atomShare D atomIndex) ^ 2 / ((k:ℝ) - atomShare D atomIndex)
      ≤ ∑ otherIndex, atomShare D otherIndex
          * directionGram D atomIndex otherIndex ^ 4 := by
  have hgap : (0:ℝ) < (k:ℝ) - atomShare D atomIndex := sub_pos.mpr hstrict
  have hoffRow := atomShare_add_sum_erase_atomShare_mul_sq_directionGram D hpositive
  have hoffTotal : ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
      = (k:ℝ) - atomShare D atomIndex := by
    have hsplit := Finset.add_sum_erase Finset.univ (atomShare D) (Finset.mem_univ atomIndex)
    rw [sum_atomShare_eq_rank D] at hsplit
    linarith
  have hdiagonalSplit : ∑ otherIndex, atomShare D otherIndex
        * directionGram D atomIndex otherIndex ^ 4
      = atomShare D atomIndex
        + ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
            * directionGram D atomIndex otherIndex ^ 4 := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun otherIndex => atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 4)
      (Finset.mem_univ atomIndex), directionGram_self D hpositive, one_pow, mul_one]
  have hcertificate : 0 ≤ ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
      * (directionGram D atomIndex otherIndex ^ 2
          - (1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2 :=
    Finset.sum_nonneg fun otherIndex _ =>
      mul_nonneg (atomShare_nonneg D otherIndex) (sq_nonneg _)
  have hexpand : ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
        * (directionGram D atomIndex otherIndex ^ 2
            - (1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2
      = (∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
            * directionGram D atomIndex otherIndex ^ 4)
        - 2 * ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex))
            * (∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
                * directionGram D atomIndex otherIndex ^ 2)
        + ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2
            * ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex := by
    rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ.erase atomIndex) =>
      show atomShare D otherIndex
            * (directionGram D atomIndex otherIndex ^ 2
                - (1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2
        = atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 4
            - 2 * ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex))
                * (atomShare D otherIndex * directionGram D atomIndex otherIndex ^ 2)
            + ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2
                * atomShare D otherIndex from by ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hoffSum : ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare D otherIndex
      * directionGram D atomIndex otherIndex ^ 2 = 1 - atomShare D atomIndex := by linarith
  rw [hexpand, hoffSum, hoffTotal] at hcertificate
  have hfinal : 2 * ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex))
        * (1 - atomShare D atomIndex)
      - ((1 - atomShare D atomIndex) / ((k:ℝ) - atomShare D atomIndex)) ^ 2
          * ((k:ℝ) - atomShare D atomIndex)
      = (1 - atomShare D atomIndex) ^ 2 / ((k:ℝ) - atomShare D atomIndex) := by
    field_simp
    ring
  rw [hdiagonalSplit]
  linarith

end Gtz
