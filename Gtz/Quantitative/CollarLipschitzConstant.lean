/-
PROVENANCE.  Harvested by the sweep from the comp-reach reconnaissance rung, which
derived and prototyped every statement below and verified the two measured numbers
quoted in the closing section.  The sweep re-compiled it against the live tree,
re-audited its axioms, re-probed its names against the full environment and wired it
into both umbrellas; the mathematics is comp-reach's.

# The collar lane's OTHER quantitative input: `designMargin` is Lipschitz on the
# collared class, with an EXPLICIT constant

`Gtz.designMargin_ge_neg_reach_of_stressLocus`
(`Gtz/Quantitative/CollarReferenceVariety.lean:539`) assembles an a-priori value
floor `margin >= - lipschitzConstant * reach` from exactly two numbers.  This file
supplies the first of them at general `(size, rank)` and at an explicit value.

## What the shipped header says, and the one place it is wrong

That file's section 4a and the docstring of the assembled floor both say the
Lipschitz hypothesis is "genuinely open: the class is compact
(`Gtz.isCompact_collaredSet`) and the margin is continuous on it
(`Gtz.continuous_designMargin`), so a constant exists on general grounds and the
content is its SIZE."

THE GENERAL-GROUNDS ARGUMENT AS STATED DOES NOT HOLD.  Continuity on a compact set
gives UNIFORM continuity, not a Lipschitz bound: `Real.sqrt` on `[0,1]` is
continuous on a compact set and is Lipschitz with no constant whatever.  So the
existence of a constant on the collared class is not free, and the header's
"exists on general grounds" is a gap rather than a shorthand.

What is true, and is what this file proves, is BETTER than the existential:
`Gtz.subsetSumRaw` is a QUADRATIC map of the atoms and the collared class BOUNDS
the atoms -- `Gtz.leverage_le_inv_floor_of_parseval` caps every leverage at
`1/weightFloor` -- so the margin is Lipschitz there with the explicit constant

    2 * rank ^ (3/2) / sqrt weightFloor ,

which at `(6,3)` and floor `1/8` is `12 * sqrt 6 = 29.393877...`, EXACTLY the hand
estimate `6 * sqrt 3 / sqrt weightFloor` that the shipped header quotes "as
arithmetic, not as a theorem".  It is now a theorem, at every `(size, rank)`.

## The chain

`Gtz.lipschitzWith_lambdaMinCLM` (shipped, Weyl) says `lambda_min` is `1`-Lipschitz
in the operator norm.  The work is the transport from the SUP metric that Lean puts
on `(Fin m -> Fin k -> R) x (Fin m -> R)` -- `Prod.dist_eq` over two Pi-sups -- to
that operator norm, and it is the rank-one identity

    g gᵀ - h hᵀ = g (g-h)ᵀ + (g-h) hᵀ ,

which gives `‖g gᵀ - h hᵀ‖ <= (|g| + |h|) |g - h|` with `|.|` the EUCLIDEAN length
`sqrt (leverageOf .)`, not the Pi sup norm.  Summing over the `rank` atoms of a
candidate and bounding `|g - h| <= sqrt rank * dist` finishes it.

## What this does NOT do

It supplies one of the two inputs; the other is the REACH, and the reach is
measured to be far too large for the product to be useful.  At floor `1/8` the
constant here is `29.39...`, so `- lipschitzConstant * reach` beats even the
trivial floor `-1` only for a reach below `0.0340...`, and beats the crux window
`-4/27` only for a reach below `0.0050...`.  The icosahedral configuration
`Gtz.icosaDesign` -- collared at floor `1/8`, uniform weight `1/6`, every leverage
`3` -- is at sup-distance AT LEAST `0.1683956...` from `Gtz.stressLocus (1/8)`,
by Eckart-Young applied to the Veronese matrix, so the reach at that floor exceeds
the useful threshold by a factor of about `4.95`.  That measurement is NOT
mechanized here; it is recorded so that no reader mistakes this file for progress
on the assembled floor.
-/
import Mathlib
import Gtz.Design.CollaredCompact
import Gtz.Quantitative.CollarReferenceVariety
import Gtz.Quantitative.MarginContinuity
import Gtz.Reduction.ChartAttainmentWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {k : ℕ}

/-! ## 1.  Atom vectors as Euclidean points

The Pi norm on `Fin k → ℝ` is the SUP norm, which is the wrong one for a
rank-one estimate; every length below is the Euclidean `sqrt (leverageOf ·)`.
Reading an atom as a point of `EuclideanSpace` makes the triangle inequality,
`norm_smul` and Cauchy-Schwarz available without reproving any of them. -/

/-- An atom vector read as a Euclidean point. -/
noncomputable def euclidAtom (g : Fin k → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 g

/-- Reading an atom as a Euclidean point and back is the identity. -/
@[simp] theorem ofLp_euclidAtom (g : Fin k → ℝ) : (euclidAtom g).ofLp = g := rfl

/-- The other side of the same round trip. -/
@[simp] theorem euclidAtom_ofLp (point : EuclideanSpace ℝ (Fin k)) :
    euclidAtom point.ofLp = point := rfl

/-- The Euclidean length of an atom is the square root of its leverage. -/
theorem norm_euclidAtom (g : Fin k → ℝ) : ‖euclidAtom g‖ = Real.sqrt (leverageOf g) := by
  rw [EuclideanSpace.norm_eq]
  simp only [ofLp_euclidAtom, Real.norm_eq_abs, sq_abs, leverageOf]

/-- The reading is additive, so the triangle inequality transports. -/
theorem euclidAtom_add (a b : Fin k → ℝ) :
    euclidAtom (a + b) = euclidAtom a + euclidAtom b := rfl

/-- The reading is homogeneous, so `norm_smul` transports. -/
theorem euclidAtom_smul (scalar : ℝ) (a : Fin k → ℝ) :
    euclidAtom (scalar • a) = scalar • euclidAtom a := rfl

/-- The Euclidean inner product of two atoms is their dot product. -/
theorem inner_euclidAtom (a b : Fin k → ℝ) :
    inner ℝ (euclidAtom a) (euclidAtom b) = a ⬝ᵥ b := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- **Cauchy-Schwarz in leverage coordinates.**  The tree measures atom length by
`Gtz.leverageOf`, so this is the form every estimate below needs. -/
theorem abs_dotProduct_le_sqrt_leverage_mul (a b : Fin k → ℝ) :
    |a ⬝ᵥ b| ≤ Real.sqrt (leverageOf a) * Real.sqrt (leverageOf b) := by
  have hbound := abs_real_inner_le_norm (euclidAtom a) (euclidAtom b)
  rw [inner_euclidAtom, norm_euclidAtom, norm_euclidAtom] at hbound
  exact hbound

/-- Applying a matrix as a continuous linear map on `EuclideanSpace` is matrix-vector
multiplication read through the same identification. -/
theorem toEuclideanCLM_apply_eq_euclidAtom (matrix : Matrix (Fin k) (Fin k) ℝ)
    (point : EuclideanSpace ℝ (Fin k)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) matrix point = euclidAtom (matrix *ᵥ point.ofLp) := rfl

/-! ## 2.  The rank-one difference bound -/

/-- **`‖g gᵀ - h hᵀ‖ ≤ (|g| + |h|) |g - h|`.**  The identity
`g gᵀ - h hᵀ = g (g-h)ᵀ + (g-h) hᵀ` turns a QUADRATIC difference into a product of
a length sum and a length difference; this is the whole reason the margin is
Lipschitz on a bounded class and on no unbounded one. -/
theorem opNorm_toEuclideanCLM_atomMatrix_sub_le (g h : Fin k → ℝ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (atomMatrix g - atomMatrix h)‖
      ≤ (Real.sqrt (leverageOf g) + Real.sqrt (leverageOf h))
          * Real.sqrt (leverageOf (g - h)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun point => ?_)
  set probe : Fin k → ℝ := point.ofLp with hprobe
  have hsplit : (atomMatrix g - atomMatrix h) *ᵥ probe
      = ((g - h) ⬝ᵥ probe) • g + ((h ⬝ᵥ probe) • (g - h)) := by
    rw [Matrix.sub_mulVec, atomMatrix_mulVec_eq_smul, atomMatrix_mulVec_eq_smul,
      sub_dotProduct]
    funext coordinate
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnormPoint : ‖point‖ = Real.sqrt (leverageOf probe) := by
    rw [hprobe, ← norm_euclidAtom, euclidAtom_ofLp]
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (atomMatrix g - atomMatrix h) point‖
      = ‖((g - h) ⬝ᵥ probe) • euclidAtom g + (h ⬝ᵥ probe) • euclidAtom (g - h)‖ := by
        rw [toEuclideanCLM_apply_eq_euclidAtom, ← hprobe, hsplit, euclidAtom_add,
          euclidAtom_smul, euclidAtom_smul]
    _ ≤ ‖((g - h) ⬝ᵥ probe) • euclidAtom g‖ + ‖(h ⬝ᵥ probe) • euclidAtom (g - h)‖ :=
        norm_add_le _ _
    _ = |(g - h) ⬝ᵥ probe| * Real.sqrt (leverageOf g)
          + |h ⬝ᵥ probe| * Real.sqrt (leverageOf (g - h)) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_euclidAtom,
          norm_euclidAtom]
    _ ≤ (Real.sqrt (leverageOf (g - h)) * Real.sqrt (leverageOf probe))
            * Real.sqrt (leverageOf g)
          + (Real.sqrt (leverageOf h) * Real.sqrt (leverageOf probe))
            * Real.sqrt (leverageOf (g - h)) := by
        gcongr <;> exact abs_dotProduct_le_sqrt_leverage_mul _ _
    _ = (Real.sqrt (leverageOf g) + Real.sqrt (leverageOf h))
          * Real.sqrt (leverageOf (g - h)) * ‖point‖ := by
        rw [hnormPoint]; ring

/-! ## 3.  What the collared class buys: bounded atoms and controlled differences -/

variable {m : ℕ}

/-- On the collared class every atom has Euclidean length at most
`1 / sqrt weightFloor`.  This is `Gtz.leverage_le_inv_floor_of_parseval` in length
rather than leverage coordinates. -/
theorem sqrt_leverage_le_of_mem_collaredSet {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)}
    (hmem : config ∈ collaredSet m k weightFloor) (chosen : Fin m) :
    Real.sqrt (leverageOf (config.1 chosen)) ≤ 1 / Real.sqrt weightFloor := by
  have hcap := leverage_le_inv_floor_of_parseval hmem.1 hfloor hmem.2.2.1 chosen
  calc Real.sqrt (leverageOf (config.1 chosen))
      ≤ Real.sqrt (1 / weightFloor) := Real.sqrt_le_sqrt hcap
    _ = 1 / Real.sqrt weightFloor := by
        rw [one_div, one_div, Real.sqrt_inv]

/-- A sup-metric step of size `dist` moves each atom by at most `sqrt rank * dist`
in Euclidean length: the Pi metric is the sup over coordinates and there are `rank`
of them. -/
theorem sqrt_leverage_sub_le_dist (x y : (Fin m → Fin k → ℝ) × (Fin m → ℝ))
    (chosen : Fin m) :
    Real.sqrt (leverageOf (x.1 chosen - y.1 chosen))
      ≤ Real.sqrt k * dist x y := by
  have hdistNonneg : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hcoordinate : ∀ coordinate : Fin k,
      (x.1 chosen coordinate - y.1 chosen coordinate) ^ 2 ≤ dist x y ^ 2 := by
    intro coordinate
    have hentry : |x.1 chosen coordinate - y.1 chosen coordinate| ≤ dist x y := by
      have hone : dist (x.1 chosen coordinate) (y.1 chosen coordinate)
          ≤ dist (x.1 chosen) (y.1 chosen) := dist_le_pi_dist _ _ coordinate
      have htwo : dist (x.1 chosen) (y.1 chosen) ≤ dist x.1 y.1 :=
        dist_le_pi_dist _ _ chosen
      have hthree : dist x.1 y.1 ≤ dist x y := by
        rw [Prod.dist_eq]; exact le_max_left _ _
      rw [← Real.dist_eq]
      linarith
    have habs : (x.1 chosen coordinate - y.1 chosen coordinate) ^ 2
        = |x.1 chosen coordinate - y.1 chosen coordinate| ^ 2 := (sq_abs _).symm
    rw [habs]
    exact pow_le_pow_left₀ (abs_nonneg _) hentry 2
  have hsum : leverageOf (x.1 chosen - y.1 chosen) ≤ (k : ℝ) * dist x y ^ 2 := by
    have hcard : ∑ _coordinate : Fin k, dist x y ^ 2 = (k : ℝ) * dist x y ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc leverageOf (x.1 chosen - y.1 chosen)
        = ∑ coordinate, (x.1 chosen coordinate - y.1 chosen coordinate) ^ 2 := by
          simp [leverageOf]
      _ ≤ ∑ _coordinate : Fin k, dist x y ^ 2 :=
          Finset.sum_le_sum fun coordinate _ => hcoordinate coordinate
      _ = (k : ℝ) * dist x y ^ 2 := hcard
  calc Real.sqrt (leverageOf (x.1 chosen - y.1 chosen))
      ≤ Real.sqrt ((k : ℝ) * dist x y ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt k * dist x y := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hdistNonneg]

/-- The per-atom bound on the collared class: each rank-one difference has operator
norm at most `(2 / sqrt weightFloor) * sqrt rank * dist`. -/
theorem opNorm_atomMatrix_sub_le_of_mem_collaredSet {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) {x y : (Fin m → Fin k → ℝ) × (Fin m → ℝ)}
    (hx : x ∈ collaredSet m k weightFloor) (hy : y ∈ collaredSet m k weightFloor)
    (chosen : Fin m) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen))‖
      ≤ 2 * Real.sqrt k / Real.sqrt weightFloor * dist x y := by
  have hfirst := sqrt_leverage_le_of_mem_collaredSet hfloor hx chosen
  have hsecond := sqrt_leverage_le_of_mem_collaredSet hfloor hy chosen
  have hdifference := sqrt_leverage_sub_le_dist x y chosen
  have hrootPos : 0 < Real.sqrt weightFloor := Real.sqrt_pos.mpr hfloor
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen))‖
      ≤ (Real.sqrt (leverageOf (x.1 chosen)) + Real.sqrt (leverageOf (y.1 chosen)))
          * Real.sqrt (leverageOf (x.1 chosen - y.1 chosen)) :=
        opNorm_toEuclideanCLM_atomMatrix_sub_le _ _
    _ ≤ (1 / Real.sqrt weightFloor + 1 / Real.sqrt weightFloor)
          * (Real.sqrt k * dist x y) := by
        gcongr
    _ = 2 * Real.sqrt k / Real.sqrt weightFloor * dist x y := by
        field_simp
        ring

/-! ## 4.  Summing over a candidate, and the `sup'` -/

/-- `Gtz.subsetSumRaw` differences: one rank-one difference per selected atom. -/
theorem opNorm_subsetSumRaw_sub_le_of_mem_collaredSet {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) {x y : (Fin m → Fin k → ℝ) × (Fin m → ℝ)}
    (hx : x ∈ collaredSet m k weightFloor) (hy : y ∈ collaredSet m k weightFloor)
    (selected : Finset (Fin m)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (subsetSumRaw x selected - subsetSumRaw y selected)‖
      ≤ selected.card * (2 * Real.sqrt k / Real.sqrt weightFloor) * dist x y := by
  have hdecompose : subsetSumRaw x selected - subsetSumRaw y selected
      = ∑ chosen ∈ selected, (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen)) := by
    rw [subsetSumRaw, subsetSumRaw, ← Finset.sum_sub_distrib]
  have hmap : Matrix.toEuclideanCLM (𝕜 := ℝ)
        (∑ chosen ∈ selected, (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen)))
      = ∑ chosen ∈ selected, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen)) :=
    map_sum (toEuclideanLM k) _ _
  rw [hdecompose, hmap]
  calc ‖∑ chosen ∈ selected, Matrix.toEuclideanCLM (𝕜 := ℝ)
          (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen))‖
      ≤ ∑ chosen ∈ selected, ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (atomMatrix (x.1 chosen) - atomMatrix (y.1 chosen))‖ := norm_sum_le _ _
    _ ≤ ∑ _chosen ∈ selected, 2 * Real.sqrt k / Real.sqrt weightFloor * dist x y :=
        Finset.sum_le_sum fun chosen _ =>
          opNorm_atomMatrix_sub_le_of_mem_collaredSet hfloor hx hy chosen
    _ = selected.card * (2 * Real.sqrt k / Real.sqrt weightFloor) * dist x y := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

variable [Nonempty (Fin k)]

/-- `λ_min` of a matrix is `1`-Lipschitz in the Euclidean operator norm: the shipped
`Gtz.lipschitzWith_lambdaMinCLM` transported through `Matrix.toEuclideanCLM`. -/
theorem abs_lambdaMinMat_sub_le (first second : Matrix (Fin k) (Fin k) ℝ) :
    |lambdaMinMat first - lambdaMinMat second|
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (first - second)‖ := by
  have hbound := abs_lambdaMinCLM_sub_le (Matrix.toEuclideanCLM (𝕜 := ℝ) first)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) second)
  have hsub : Matrix.toEuclideanCLM (𝕜 := ℝ) first - Matrix.toEuclideanCLM (𝕜 := ℝ) second
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (first - second) := (map_sub (toEuclideanLM k) _ _).symm
  rw [hsub] at hbound
  exact hbound

/-! ## 5.  The theorem -/

/-- **`Gtz.designMargin` IS LIPSCHITZ ON THE COLLARED CLASS, WITH AN EXPLICIT
CONSTANT.**  The constant is `2 * rank ^ (3/2) / sqrt weightFloor`, written here as
`rank * (2 * sqrt rank / sqrt weightFloor)`; at `(6,3)` with floor `1/8` it is
`12 * sqrt 6 = 29.393877...`.

This is the input `Gtz.designMargin_ge_neg_reach_of_stressLocus` asks for, and it is
strictly stronger than the existential that file's header contemplates.  The header
argues the constant exists "on general grounds" because the class is compact and the
margin is continuous on it; that argument is not valid -- continuity on a compact set
gives uniform continuity, and `Real.sqrt` on `[0,1]` is a continuous function on a
compact set with no Lipschitz constant at all.  What makes the constant exist here is
that the class BOUNDS THE ATOMS (`Gtz.leverage_le_inv_floor_of_parseval`) and the
margin is a `sup` of quadratic forms in them. -/
theorem lipschitzOnWith_designMargin_collaredSet (hrank : k ≤ m) {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) :
    LipschitzOnWith
      (Real.toNNReal ((k : ℝ) * (2 * Real.sqrt k / Real.sqrt weightFloor)))
      (designMargin (m := m) (k := k) hrank) (collaredSet m k weightFloor) := by
  have hrootPos : 0 < Real.sqrt weightFloor := Real.sqrt_pos.mpr hfloor
  have hconstNonneg : (0 : ℝ) ≤ (k : ℝ) * (2 * Real.sqrt k / Real.sqrt weightFloor) := by
    positivity
  refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
  rw [Real.coe_toNNReal _ hconstNonneg, Real.dist_eq]
  set constant : ℝ := (k : ℝ) * (2 * Real.sqrt k / Real.sqrt weightFloor) with hconstant
  have hstep : ∀ selected ∈ chartCandidates m k,
      |lambdaMinMat (subsetSumRaw x selected) - lambdaMinMat (subsetSumRaw y selected)|
        ≤ constant * dist x y := by
    intro selected hselected
    have hcard : selected.card = k := (mem_chartCandidates_iff m k selected).mp hselected
    have hbound := opNorm_subsetSumRaw_sub_le_of_mem_collaredSet hfloor hx hy selected
    rw [hcard] at hbound
    exact (abs_lambdaMinMat_sub_le _ _).trans hbound
  have hforward : ∀ (first second : (Fin m → Fin k → ℝ) × (Fin m → ℝ)),
      (∀ selected ∈ chartCandidates m k,
        |lambdaMinMat (subsetSumRaw first selected)
          - lambdaMinMat (subsetSumRaw second selected)| ≤ constant * dist x y) →
      ((chartCandidates m k).sup' (chartCandidates_nonempty hrank)
          fun candidate => lambdaMinMat (subsetSumRaw first candidate))
        ≤ ((chartCandidates m k).sup' (chartCandidates_nonempty hrank)
            fun candidate => lambdaMinMat (subsetSumRaw second candidate))
          + constant * dist x y := by
    intro first second hgap
    refine Finset.sup'_le _ _ (fun candidate hcandidate => ?_)
    have habs := abs_le.mp (hgap candidate hcandidate)
    have hle : lambdaMinMat (subsetSumRaw second candidate)
        ≤ (chartCandidates m k).sup' (chartCandidates_nonempty hrank)
            fun other => lambdaMinMat (subsetSumRaw second other) :=
      Finset.le_sup' (f := fun other => lambdaMinMat (subsetSumRaw second other))
        hcandidate
    linarith [habs.2]
  have hxy := hforward x y hstep
  have hyx := hforward y x (fun selected hselected => by
    rw [abs_sub_comm]; exact hstep selected hselected)
  rw [designMargin, designMargin]
  rw [abs_le]
  constructor <;> linarith

/-- The existential form, which is what a consumer of
`Gtz.designMargin_ge_neg_reach_of_stressLocus` needs to discharge. -/
theorem exists_lipschitzOnWith_designMargin_collaredSet (hrank : k ≤ m) {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) :
    ∃ lipschitzConstant : NNReal,
      LipschitzOnWith lipschitzConstant (designMargin (m := m) (k := k) hrank)
        (collaredSet m k weightFloor) :=
  ⟨_, lipschitzOnWith_designMargin_collaredSet hrank hfloor⟩

/-- **The frontier instance.**  At `(6,3)` and weight floor `1/8` the constant is
`12 * sqrt 6 = 29.393877...`, the number the shipped header quotes as arithmetic. -/
theorem lipschitzOnWith_designMargin_collaredSet_sixThree :
    LipschitzOnWith (Real.toNNReal (12 * Real.sqrt 6))
      (designMargin (m := 6) (k := 3) (show (3 : ℕ) ≤ 6 by norm_num))
      (collaredSet 6 3 (1 / 8)) := by
  have hconvert : ((3 : ℕ) : ℝ) * (2 * Real.sqrt 3 / Real.sqrt (1 / 8))
      = 12 * Real.sqrt 6 := by
    have height : Real.sqrt (1 / 8) = 1 / (2 * Real.sqrt 2) := by
      rw [show (1 : ℝ) / 8 = 1 / 2 ^ 3 by norm_num, one_div, one_div, Real.sqrt_inv]
      congr 1
      rw [show (2 : ℝ) ^ 3 = 2 ^ 2 * 2 by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have hproduct : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [height]
    push_cast
    field_simp
    linarith [hproduct]
  rw [← hconvert]
  exact lipschitzOnWith_designMargin_collaredSet (by norm_num) (by norm_num)

/-- **The assembled a-priori value floor with the constant supplied.**  The only
remaining hypothesis of `Gtz.designMargin_ge_neg_reach_of_stressLocus` at `(6,3)` and
floor `1/8` is the REACH.  Recorded so the residual is a single number: with the
constant now a theorem, the collar assembly delivers `margin ≥ -12*sqrt 6 * reach`,
which is above `-1` only for `reach < 1/(12*sqrt 6) = 0.0340...` and above `-4/27`
only for `reach < 0.0050...`.  The measured reach at floor `1/8` is at least
`0.1683956...`, at `Gtz.icosaDesign`. -/
theorem designMargin_ge_neg_reach_sixThree {reach : ℝ}
    (hReach : ∀ config ∈ collaredSet 6 3 (1 / 8),
      Metric.infDist config (stressLocus (1 / 8)) ≤ reach)
    {config : (Fin 6 → Fin 3 → ℝ) × (Fin 6 → ℝ)}
    (hmem : config ∈ collaredSet 6 3 (1 / 8)) :
    -((12 * Real.sqrt 6) * reach)
      ≤ designMargin (show (3 : ℕ) ≤ 6 by norm_num) config := by
  have hconstNonneg : (0 : ℝ) ≤ 12 * Real.sqrt 6 := by positivity
  have hbase := designMargin_ge_neg_reach_of_stressLocus (by norm_num : (0 : ℝ) < 1 / 8)
    lipschitzOnWith_designMargin_collaredSet_sixThree stressLocus_nonempty hReach hmem
  rwa [Real.coe_toNNReal _ hconstNonneg] at hbase

end Gtz
