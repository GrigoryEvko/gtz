import Gtz.Wave.DiamondNeighborhoodMirror
import Gtz.Wave.DominatorWedgeFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The two-probe lock

The mirror rigidity consumes a SHARED null line; a perturbed tie offers two
null probes an unknown distance apart.  This module closes that gap with
exact identities — no ε anywhere.

* **The bilinear lock** (`Gtz.swap_null_bilinear_lock`).  Evaluating
  `w′ᵀM′w` two ways — through the swap identity and through the second null
  condition — locks the four readings of the exchanged pair:

  `(g_p·w)·(g_p·w′) = (g_q·w)·(g_q·w′)` .

  Exact at every size, with no positivity and no unit norms.
* **The gap lock** (`Gtz.swap_null_gap_lock`): squaring, the two reading
  gaps are proportional with the squared readings as weights.
* **The misalignment floor and ceiling**
  (`Gtz.nullShift_form_floor`, `Gtz.nullShift_form_ceiling`): a symmetric
  form with null probe `w′` and transverse coercivity `μ` reads any probe
  `w` at least `μ·(|w|² − (w·w′)²)` — and, when PSD, at most the trace
  times the same misalignment.  The reading gap of a swap is therefore
  SANDWICHED by the probe misalignment.
* **The Case-A closure** (`Gtz.hasParallelPair_of_swapNulls_reading_eq`).
  Two swap-related null probes with transverse coercivity and EQUAL
  readings force the probes onto one line, hence the mirror rigidity, hence
  the parallel pair.  The shared-null hypothesis of the mirror theorem is
  discharged: reading equality plus corank one IS null sharing.
* **The strict dichotomy** (`Gtz.strict_gap_of_not_hasParallelPair`): at a
  primitive design the two probes are genuinely apart and both reading
  gaps carry the misalignment floor strictly.  This is the exact form of
  "a primitive perturbation must open the reading gap", the quantity the
  finite neighborhood argument prices.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The null-shift calculus, abstract -/

/-- **THE MISALIGNMENT FLOOR.**  A symmetric form with null probe `w′` and
transverse coercivity `μ` reads every probe at least `μ` times the
misalignment `|w|² − (w·w′)²`. -/
theorem nullShift_form_floor {N : Matrix (Fin k) (Fin k) ℝ} (hsymm : Nᵀ = N)
    {w' : Fin k → ℝ} (hunit : w' ⬝ᵥ w' = 1) (hnull : N *ᵥ w' = 0)
    {mu : ℝ}
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w' = 0 → mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ (N *ᵥ v))
    (w : Fin k → ℝ) :
    mu * (w ⬝ᵥ w - (w ⬝ᵥ w') ^ 2) ≤ w ⬝ᵥ (N *ᵥ w) := by
  have hmove : ∀ x y : Fin k → ℝ, x ⬝ᵥ (N *ᵥ y) = y ⬝ᵥ (N *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  set c : ℝ := w ⬝ᵥ w' with hc
  set v : Fin k → ℝ := w - c • w' with hv
  have hvw' : v ⬝ᵥ w' = 0 := by
    rw [hv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one, hc]
    ring
  have hNv : N *ᵥ v = N *ᵥ w := by
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, hnull, smul_zero, sub_zero]
  have hform : w ⬝ᵥ (N *ᵥ w) = v ⬝ᵥ (N *ᵥ v) := by
    have hwv : w = v + c • w' := by rw [hv]; abel
    calc w ⬝ᵥ (N *ᵥ w) = w ⬝ᵥ (N *ᵥ v) := by rw [hNv]
      _ = v ⬝ᵥ (N *ᵥ w) := hmove w v
      _ = v ⬝ᵥ (N *ᵥ v) := by rw [hNv]
  have hvv : v ⬝ᵥ v = w ⬝ᵥ w - c ^ 2 := by
    rw [hv]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hunit, dotProduct_comm w' w, ← hc]
    ring
  have hfloor := hcoer v hvw'
  rw [hvv] at hfloor
  rw [hform]
  exact hfloor

/-- **THE MISALIGNMENT CEILING.**  A PSD form with null probe `w′` reads
every probe at most its trace times the misalignment. -/
theorem nullShift_form_ceiling {N : Matrix (Fin 3) (Fin 3) ℝ}
    (hN : N.PosSemidef) {w' : Fin 3 → ℝ} (hunit : w' ⬝ᵥ w' = 1)
    (hnull : N *ᵥ w' = 0) (w : Fin 3 → ℝ) :
    w ⬝ᵥ (N *ᵥ w) ≤ Matrix.trace N * (w ⬝ᵥ w - (w ⬝ᵥ w') ^ 2) := by
  have hsymm : Nᵀ = N := transpose_eq_of_isHermitian hN.1
  have hmove : ∀ x y : Fin 3 → ℝ, x ⬝ᵥ (N *ᵥ y) = y ⬝ᵥ (N *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  set c : ℝ := w ⬝ᵥ w' with hc
  set v : Fin 3 → ℝ := w - c • w' with hv
  have hNv : N *ᵥ v = N *ᵥ w := by
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, hnull, smul_zero, sub_zero]
  have hform : w ⬝ᵥ (N *ᵥ w) = v ⬝ᵥ (N *ᵥ v) := by
    calc w ⬝ᵥ (N *ᵥ w) = w ⬝ᵥ (N *ᵥ v) := by rw [hNv]
      _ = v ⬝ᵥ (N *ᵥ w) := hmove w v
      _ = v ⬝ᵥ (N *ᵥ v) := by rw [hNv]
  have hvv : v ⬝ᵥ v = w ⬝ᵥ w - c ^ 2 := by
    rw [hv]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hunit, dotProduct_comm w' w, ← hc]
    ring
  have htr := form_le_trace_mul_normSq_of_posSemidef hN v
  rw [hform]
  calc v ⬝ᵥ (N *ᵥ v) ≤ Matrix.trace N * (v ⬝ᵥ v) := htr
    _ = Matrix.trace N * (w ⬝ᵥ w - c ^ 2) := by rw [hvv]

/-- **NULL SHARING FROM A VANISHED FORM.**  With positive transverse
coercivity and unit probes, a vanished form value forces the probe ONTO the
null line, and the form kills it. -/
theorem nullShift_eq_smul_of_form_eq_zero {N : Matrix (Fin k) (Fin k) ℝ}
    (hsymm : Nᵀ = N) {w' : Fin k → ℝ} (hunit : w' ⬝ᵥ w' = 1)
    (hnull : N *ᵥ w' = 0) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w' = 0 → mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ (N *ᵥ v))
    {w : Fin k → ℝ} (hwunit : w ⬝ᵥ w = 1) (hzero : w ⬝ᵥ (N *ᵥ w) = 0) :
    w = (w ⬝ᵥ w') • w' ∧ N *ᵥ w = 0 := by
  have hfloor := nullShift_form_floor hsymm hunit hnull hcoer w
  rw [hzero, hwunit] at hfloor
  -- the misalignment is nonpositive, and it is a squared norm
  have hvv : (w - (w ⬝ᵥ w') • w') ⬝ᵥ (w - (w ⬝ᵥ w') • w')
      = 1 - (w ⬝ᵥ w') ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hunit, hwunit, dotProduct_comm w' w]
    ring
  have hle : 1 - (w ⬝ᵥ w') ^ 2 ≤ 0 := by nlinarith
  have hnn : 0 ≤ (w - (w ⬝ᵥ w') • w') ⬝ᵥ (w - (w ⬝ᵥ w') • w') :=
    dotProduct_self_nonneg _
  have hveq : w - (w ⬝ᵥ w') • w' = 0 := by
    apply dotProduct_self_eq_zero.mp
    rw [hvv]
    linarith
  have hw : w = (w ⬝ᵥ w') • w' := by
    have := sub_eq_zero.mp hveq
    exact this
  refine ⟨hw, ?_⟩
  rw [hw, Matrix.mulVec_smul, hnull, smul_zero]

/-! ## 2. The bilinear lock of a swap -/

/-- **THE BILINEAR LOCK.**  Two swap-related null probes lock the four
readings of the exchanged pair:

  `(g_p·w)·(g_p·w′) = (g_q·w)·(g_q·w′)` .

Evaluate `w′ᵀM′w` through the swap identity and through the second null
condition.  Exact: no positivity, no unit norms, every size. -/
theorem swap_null_bilinear_lock (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w w' : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0) :
    (D.atom p ⬝ᵥ w) * (D.atom p ⬝ᵥ w') = (D.atom q ⬝ᵥ w) * (D.atom q ⬝ᵥ w') := by
  have hsymm : (subsetSum D (insert q (C.erase p)) - 1)ᵀ
      = subsetSum D (insert q (C.erase p)) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D _)
  have hswap := swap_gap_mulVec_of_null D hp hq hnullC
  -- `w′ᵀ M′ w` through symmetry and the second null condition
  have hzero : w' ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hnullSwap,
      zero_dotProduct]
  -- `w′ᵀ M′ w` through the swap identity
  rw [hswap, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm w' (D.atom q), dotProduct_comm w' (D.atom p),
    sub_eq_zero] at hzero
  linarith [hzero]

/-- **THE GAP LOCK.**  Squaring the bilinear lock: the two reading gaps are
proportional, weighted by the squared readings:

  `((g_q·w)² − (g_p·w)²)·(g_p·w′)² = ((g_p·w′)² − (g_q·w′)²)·(g_q·w)²` . -/
theorem swap_null_gap_lock (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w w' : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0) :
    ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) * (D.atom p ⬝ᵥ w') ^ 2
      = ((D.atom p ⬝ᵥ w') ^ 2 - (D.atom q ⬝ᵥ w') ^ 2) * (D.atom q ⬝ᵥ w) ^ 2 := by
  have hlock := swap_null_bilinear_lock D hp hq hnullC hnullSwap
  linear_combination (-(D.atom p ⬝ᵥ w * (D.atom p ⬝ᵥ w'))
    - D.atom q ⬝ᵥ w * (D.atom q ⬝ᵥ w')) * hlock

/-! ## 3. The Case-A closure: reading equality forces the parallel pair -/

/-- **THE READING-GAP FLOOR.**  The reading gap of a swap carries the probe
misalignment at the coercivity rate:

  `μ′·(1 − (w·w′)²) ≤ (g_q·w)² − (g_p·w)²` . -/
theorem reading_gap_floor_of_swapNulls (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w w' : Fin k → ℝ} (hwunit : w ⬝ᵥ w = 1) (hw'unit : w' ⬝ᵥ w' = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0)
    {mu' : ℝ}
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w' = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v)) :
    mu' * (1 - (w ⬝ᵥ w') ^ 2)
      ≤ (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2 := by
  have hsymm : (subsetSum D (insert q (C.erase p)) - 1)ᵀ
      = subsetSum D (insert q (C.erase p)) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D _)
  have hfloor := nullShift_form_floor hsymm hw'unit hnullSwap hcoer w
  rw [swap_nullForm_of_null D hp hq hnullC, hwunit] at hfloor
  exact hfloor

/-- **THE CASE-A CLOSURE.**  Two swap-related null probes with positive
transverse coercivity and EQUAL squared readings force the parallel pair.
The shared-null hypothesis of the mirror rigidity is DISCHARGED: under
corank one, reading equality IS null sharing.  No ε anywhere. -/
theorem hasParallelPair_of_swapNulls_reading_eq (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C)
    {w w' : Fin k → ℝ} (hwunit : w ⬝ᵥ w = 1) (hw'unit : w' ⬝ᵥ w' = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0)
    {mu' : ℝ} (hmu' : 0 < mu')
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w' = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    (hreadeq : (D.atom p ⬝ᵥ w) ^ 2 = (D.atom q ⬝ᵥ w) ^ 2)
    (hread : D.atom p ⬝ᵥ w ≠ 0) :
    HasParallelPair D := by
  have hsymm : (subsetSum D (insert q (C.erase p)) - 1)ᵀ
      = subsetSum D (insert q (C.erase p)) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D _)
  -- reading equality vanishes the swap null form
  have hzero : w ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) = 0 := by
    rw [swap_nullForm_of_null D hp hq hnullC, hreadeq, sub_self]
  -- the null-shift calculus shares the null line
  obtain ⟨-, hshared⟩ := nullShift_eq_smul_of_form_eq_zero hsymm hw'unit
    hnullSwap hmu' hcoer hwunit hzero
  -- and the mirror rigidity fires at the shared probe
  exact hasParallelPair_of_mirror_nullDominators D hpq hp hq hnullC hshared hread

/-! ## 4. The strict dichotomy at a primitive design -/

/-- **THE STRICT GAP.**  At a design with NO parallel pair, two swap-related
null probes with positive transverse coercivity and a live reading keep a
STRICTLY positive misalignment, and the reading gap carries it:

  `(w·w′)² < 1`  and  `0 < μ′·(1 − (w·w′)²) ≤ (g_q·w)² − (g_p·w)²` .

The exact form of "a primitive perturbation must open the reading gap" —
the quantity the finite neighborhood argument prices, and the strict floor
the global aggregation consumes. -/
theorem strict_gap_of_not_hasParallelPair (D : WeightedDesign m k)
    (hprim : ¬ HasParallelPair D) {C : Finset (Fin m)} {p q : Fin m}
    (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C) {w w' : Fin k → ℝ}
    (hwunit : w ⬝ᵥ w = 1) (hw'unit : w' ⬝ᵥ w' = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0)
    {mu' : ℝ}
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w' = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    (hread : D.atom p ⬝ᵥ w ≠ 0) :
    (w ⬝ᵥ w') ^ 2 < 1
      ∧ mu' * (1 - (w ⬝ᵥ w') ^ 2)
          ≤ (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2 := by
  have hfloor := reading_gap_floor_of_swapNulls D hp hq hwunit hw'unit
    hnullC hnullSwap hcoer
  refine ⟨?_, hfloor⟩
  -- misalignment zero would share the null line and force the pair
  by_contra hcon
  push Not at hcon
  have hcs := dotProduct_sq_le_mul w w'
  rw [hwunit, hw'unit, one_mul] at hcs
  have hceq : (w ⬝ᵥ w') ^ 2 = 1 := le_antisymm hcs hcon
  have hveq : w - (w ⬝ᵥ w') • w' = 0 := by
    apply dotProduct_self_eq_zero.mp
    have : (w - (w ⬝ᵥ w') • w') ⬝ᵥ (w - (w ⬝ᵥ w') • w')
        = 1 - (w ⬝ᵥ w') ^ 2 := by
      simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hw'unit, hwunit, dotProduct_comm w' w]
      ring
    rw [this, hceq, sub_self]
  have hshared : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0 := by
    have hw : w = (w ⬝ᵥ w') • w' := sub_eq_zero.mp hveq
    rw [hw, Matrix.mulVec_smul, hnullSwap, smul_zero]
  exact hprim
    (hasParallelPair_of_mirror_nullDominators D hpq hp hq hnullC hshared hread)

/-! ## 5. The neighborhood theorem, with an intrinsic radius

The ball around the fixture is not the right object: the mirror mechanism
is weight-blind, and what actually controls the pair is how far the two
null lines sit apart.  The misalignment `δ = 1 − (w·w′)²` is that radius —
intrinsic, rational, and computable from the contact data alone. -/

/-- The trace of a positive semidefinite matrix is nonnegative. -/
theorem nullShift_trace_nonneg {N : Matrix (Fin 3) (Fin 3) ℝ}
    (hN : N.PosSemidef) : 0 ≤ Matrix.trace N := by
  have hquad : ∀ x : Fin 3 → ℝ, 0 ≤ x ⬝ᵥ (N *ᵥ x) := by
    intro x
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hN).2 x
    rwa [star_trivial] at h
  have hdiag : ∀ i, 0 ≤ N i i := by
    intro i
    have h := hquad (Pi.single i 1)
    rw [single_one_dotProduct, Matrix.mulVec_single_one] at h
    simpa using h
  rw [Matrix.trace_fin_three]
  linarith [hdiag 0, hdiag 1, hdiag 2]

/-- **THE NEIGHBORHOOD THEOREM.**  The pair wedge is capped by the
MISALIGNMENT of the two null probes:

  `w_{pq}·(g_q·w)² ≤ |g_p|²·(tr M′)²·(1 − (w·w′)²)` .

Exact, at every design, with no ball and no ε: the radius is the intrinsic
quantity `δ = 1 − (w·w′)²`, which vanishes EXACTLY when the two mirror
members share their null line — and there the wedge vanishes, i.e. the pair
is parallel.  This is the C1-8 consumable shape: a margin against the pair
wedge, tight at the fixture, with no additive constant. -/
theorem wedge_le_misalignment_of_mirror_dominators (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w w' : Fin 3 → ℝ} (hwunit : w ⬝ᵥ w = 1) (hw'unit : w' ⬝ᵥ w' = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0)
    (hdom : Dominates D (insert q (C.erase p))) :
    (leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2)
        * (D.atom q ⬝ᵥ w) ^ 2
      ≤ leverageOf (D.atom p)
        * (Matrix.trace (subsetSum D (insert q (C.erase p)) - 1) ^ 2
          * (1 - (w ⬝ᵥ w') ^ 2)) := by
  have hgap := wedge_le_reading_gap_of_mirror_dominators D hp hq hnullC hdom
  have hceil := nullShift_form_ceiling hdom hw'unit hnullSwap w
  rw [swap_nullForm_of_null D hp hq hnullC, hwunit] at hceil
  have htr : 0 ≤ Matrix.trace (subsetSum D (insert q (C.erase p)) - 1) :=
    nullShift_trace_nonneg hdom
  have hlevnn : 0 ≤ leverageOf (D.atom p) := by
    rw [leverageOf_eq_dotProduct]
    exact dotProduct_self_nonneg _
  have hinner : Matrix.trace (subsetSum D (insert q (C.erase p)) - 1)
        * ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2)
      ≤ Matrix.trace (subsetSum D (insert q (C.erase p)) - 1) ^ 2
        * (1 - (w ⬝ᵥ w') ^ 2) := by nlinarith [hceil, htr]
  calc (leverageOf (D.atom p) * leverageOf (D.atom q)
          - (D.atom p ⬝ᵥ D.atom q) ^ 2) * (D.atom q ⬝ᵥ w) ^ 2
      ≤ leverageOf (D.atom p)
          * (Matrix.trace (subsetSum D (insert q (C.erase p)) - 1)
            * ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2)) := hgap
    _ ≤ leverageOf (D.atom p)
          * (Matrix.trace (subsetSum D (insert q (C.erase p)) - 1) ^ 2
            * (1 - (w ⬝ᵥ w') ^ 2)) := mul_le_mul_of_nonneg_left hinner hlevnn

/-! ## 6. Case B: the refused swap, and the unified coupling bound

A refused swap has an indefinite gap, hence no null probe, so the lock of
section 2 cannot reach it.  The swap pinch can: it needs only that the
swapped triple is not positive definite, which a tie supplies at EVERY
triple, plus a positive transverse coercivity — and the calibration puts
that coercivity above zero at all twelve contacts of the fixture
(`e₂ > 0` with `e₃ = 0` everywhere).

Adding the census lower bound of a DOMINATING swap traps the reading gap in
a two-sided interval, and the swap defect splits by Pythagoras into the
coupling and the gap.  The wedge is then bounded by the coupling ALONE. -/

/-- **THE DEFECT SPLITS.**  At a unit probe the swap defect is the coupling
plus the squared reading gap — the coupling is transverse to the probe. -/
theorem swapDefect_eq_couplingSq_add_nullFormSq (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin k → ℝ} (hwunit : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
        ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
      = swapCoupling D p q w ⬝ᵥ swapCoupling D p q w
        + ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) ^ 2 := by
  have hv := swap_gap_mulVec_of_null D hp hq hnull
  have hvw : ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) ⬝ᵥ w
      = (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2 := by
    rw [hv, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  have hcoup : swapCoupling D p q w
      = ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
        - ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) • w := by
    rw [swapCoupling, hv]
  rw [hcoup]
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, hwunit]
  rw [hvw, dotProduct_comm w ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w),
    hvw]
  ring

/-- **THE TRAPPED READING GAP.**  At a tie whose swapped triple also weakly
dominates, the reading gap is caught between zero and the coupling at the
coercivity rate:

  `0 ≤ (g_q·w)² − (g_p·w)²`   and   `((g_q·w)² − (g_p·w)²)·μ′ ≤ |b′|²` .

The lower half is the census, the upper half is the pinch. -/
theorem reading_gap_trapped_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w : Fin 3 → ℝ} (hwunit : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) {mu' : ℝ} (hmu' : 0 < mu')
    (hcoer : ∀ v : Fin 3 → ℝ, v ⬝ᵥ w = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    (hdom : Dominates D (insert q (C.erase p))) :
    0 ≤ (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2
      ∧ ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) * mu'
          ≤ swapCoupling D p q w ⬝ᵥ swapCoupling D p q w := by
  refine ⟨?_, swap_pinch_of_isTie D htie hcard hp hq hwunit hnull hmu' hcoer⟩
  have hcensus := swap_reading_sq_le_of_dominates D hp hq hnull hdom
  linarith

/-- **THE WEDGE IS BOUNDED BY THE COUPLING ALONE.**  At a tie with a
dominating swap, with `K = |b′|²` the swap coupling energy:

  `w_{pq}·(g_q·w)²·μ′² ≤ |g_p|²·(K² + μ′²·K)` .

The trapped gap eliminates the reading data entirely: the pair wedge is
controlled by the transverse coupling of the swapped gap, at the calibrated
coercivity.  `K = 0` forces the wedge to vanish, i.e. the parallel pair. -/
theorem wedge_le_coupling_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w : Fin 3 → ℝ} (hwunit : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) {mu' : ℝ} (hmu' : 0 < mu')
    (hcoer : ∀ v : Fin 3 → ℝ, v ⬝ᵥ w = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    (hdom : Dominates D (insert q (C.erase p))) :
    (leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2)
        * (D.atom q ⬝ᵥ w) ^ 2 * mu' ^ 2
      ≤ leverageOf (D.atom p)
        * ((swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) ^ 2
          + mu' ^ 2 * (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w)) := by
  obtain ⟨hlow, hhigh⟩ := reading_gap_trapped_of_isTie D htie hcard hp hq hwunit
    hnull hmu' hcoer hdom
  have hdefect := wedge_mul_reading_sq_le_swap_defect D hp hq hnull
  have hsplit := swapDefect_eq_couplingSq_add_nullFormSq D hp hq hwunit hnull
  have hlevnn : 0 ≤ leverageOf (D.atom p) := by
    rw [leverageOf_eq_dotProduct]
    exact dotProduct_self_nonneg _
  have hKnn : 0 ≤ swapCoupling D p q w ⬝ᵥ swapCoupling D p q w :=
    dotProduct_self_nonneg _
  -- the squared gap is below `K²/μ′²`, so `μ′²·defect ≤ K² + μ′²K`
  have hgapsq : ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) ^ 2 * mu' ^ 2
      ≤ (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) ^ 2 := by
    have hs : 0 ≤ ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) * mu' :=
      mul_nonneg hlow hmu'.le
    nlinarith [mul_self_le_mul_self hs hhigh]
  have hdef : (((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
        ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)) * mu' ^ 2
      ≤ (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) ^ 2
        + mu' ^ 2 * (swapCoupling D p q w ⬝ᵥ swapCoupling D p q w) := by
    rw [hsplit]; nlinarith [hgapsq]
  nlinarith [hdefect, hdef, hlevnn, sq_nonneg mu']

/-! ## 7. The polynomial system at fixed rational probes

The tangent-space LP of the calibration is EVIDENCE, never a proof step:
its functionals are derivatives, its equations are differentiated
constraints, and its variables are perturbations — none of them kernel
objects.  The kernel-native replacement fixes the fixture's twelve rational
null vectors as PROBES and reads the tie through them.  Both facts below
are polynomial in the design and hold PER PROBE.  They are deliberately not
summed: summation collapses a two-point form into a field-blind identity
and destroys the very sensitivity the arm's realness rests on. -/

/-- **THE PROBE FLOOR OF A WEAK DOMINATOR.**  A weakly dominating triple
outreads every probe:

  `v·v ≤ Σ_{c∈C}(g_c·v)²` .

Polynomial in the design at every fixed probe, with no coercivity, no null
hypothesis and no size restriction.  Instantiated at the fixture's twelve
rational null vectors this is the twelve-inequality system. -/
theorem dominates_probe_floor (D : WeightedDesign m k) {C : Finset (Fin m)}
    (hdom : Dominates D C) (v : Fin k → ℝ) :
    v ⬝ᵥ v ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2 := by
  have hq := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 v
  rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub] at hq
  have hsum : v ⬝ᵥ (subsetSum D C *ᵥ v) = ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [atomMatrix_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    ring
  rw [hsum] at hq
  linarith

/-- **A TIE'S WEAK DOMINATOR IS SINGULAR.**  Positive semidefinite and not
positive definite forces a vanishing determinant: an exact POLYNOMIAL
equation at every weak dominator of a tie, with no probe and no coercivity.
Together with the probe floor it makes the twelve-probe system algebraic. -/
theorem isTie_dominates_det_eq_zero (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) (hdom : Dominates D C) :
    (subsetSum D C - 1).det = 0 := by
  by_contra hne
  exact htie.2 C hcard (hdom.posDef_iff_det_ne_zero.mpr hne)

/-- **THE TWELVE-PROBE SYSTEM, PACKAGED.**  At a tie, every weak dominator
satisfies the probe floor at EVERY fixed probe and carries a singular gap.
This is the kernel-native form of the calibration's twelve inequalities:
polynomial, per-probe, and free of any tangent-space object. -/
theorem isTie_dominates_probe_system (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) (hdom : Dominates D C) :
    (∀ v : Fin k → ℝ, v ⬝ᵥ v ≤ ∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2)
      ∧ (subsetSum D C - 1).det = 0 :=
  ⟨dominates_probe_floor D hdom, isTie_dominates_det_eq_zero D htie hcard hdom⟩

/-- **THE MISALIGNMENT IS CAPPED BY THE COUPLING.**  At a tie, with `C` a
weak dominator killing `w` and the swapped triple killing `w'` at
coercivity `mu'`:

  `mu'^2*(1 - (w.w')^2) ≤ K` ,  `K = |b'|^2` the swap coupling energy.

The floor of section 3 pushes the reading gap up by the misalignment, and
the pinch of the previous module caps the reading gap by the coupling; the
two compose into a CEILING on the misalignment itself.  This is the exact
partner of an intrinsic misalignment FLOOR: a floor and this ceiling
together pin the coupling from below. -/
theorem misalignment_le_coupling_of_isTie (D : WeightedDesign m 3) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = 3) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w w' : Fin 3 → ℝ}
    (hwunit : w ⬝ᵥ w = 1) (hw'unit : w' ⬝ᵥ w' = 1)
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w' = 0)
    {mu' : ℝ} (hmu' : 0 < mu')
    (hcoerW : ∀ v : Fin 3 → ℝ, v ⬝ᵥ w = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    (hcoerW' : ∀ v : Fin 3 → ℝ, v ⬝ᵥ w' = 0 →
      mu' * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v)) :
    mu' ^ 2 * (1 - (w ⬝ᵥ w') ^ 2)
      ≤ swapCoupling D p q w ⬝ᵥ swapCoupling D p q w := by
  have hfloor := reading_gap_floor_of_swapNulls D hp hq hwunit hw'unit hnullC
    hnullSwap hcoerW'
  have hpinch := swap_pinch_of_isTie D htie hcard hp hq hwunit hnullC hmu' hcoerW
  nlinarith [hfloor, hpinch, hmu']

/-! ## 8. Where the dominator wedge floor cannot reach

The inside-wedge floor of a weak dominator (`Gtz.dominator_inside_wedge_ge_weight`)
bounds the wedge of a pair that CO-OCCURS in a dominator from below by the
third member's weight.  The pair the hinge hunts never co-occurs: it is
parallel, and no weak dominator carries a parallel inside pair.  So that
floor, strong as it is, is structurally unable to bound the target pair's
wedge — which is why the misalignment floor and the misalignment ceiling of
section 7 do not chain into a contradiction. -/

/-- **THE TARGET PAIR SITS ∈ NO WEAK DOMINATOR.**  A mirror pair of
null-sharing weak dominators with a live reading is parallel, and a weak
dominator has no parallel inside pair.  Hence no weak dominator contains
both exchanged labels.

At the doubled fixture this is exact and visible: the four triples carrying
both spine copies are precisely four of the eight refusals.  The
consequence for the endgame is negative and worth stating: the inside-wedge
floor of a dominator cannot bound the target pair's wedge from below, so it
cannot be chained against an upper bound on that wedge. -/
theorem no_dominator_contains_mirror_pair (D : WeightedDesign 6 3)
    {C : Finset (Fin 6)} {p q : Fin 6} (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin 3 → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0)
    (hread : D.atom p ⬝ᵥ w ≠ 0)
    {r : Fin 6} (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ Dominates D ({p, q, r} : Finset (Fin 6)) := by
  intro hdom
  have h := mirror_reading_smul_eq D hp hq hnullC hnullSwap
  have hscaled := congrArg (fun z : Fin 3 → ℝ => (D.atom p ⬝ᵥ w)⁻¹ • z) h
  simp only [smul_smul, inv_mul_cancel₀ hread, one_smul] at hscaled
  have hset : ({q, p, r} : Finset (Fin 6)) = ({p, q, r} : Finset (Fin 6)) :=
    Finset.insert_comm q p _
  refine dominator_no_inside_parallel D (Ne.symm hpq) hqr hpr ?_ _ hscaled
  rw [hset]
  exact hdom

/-! ## 9. The first-order content: the pinch at a fixed probe

An order count settles which instruments can decide the last step.  Open the
pair by `eps`.  Then the swap null form moves at FIRST order, `a' = O(eps)`,
while the coupling, the misalignment and the wedge all move at SECOND
order, `K = O(eps^2)`, `delta = O(eps^2)`, `w_pq = O(eps^2)`.  The ceiling
`mu'^2 delta ≤ K` and the wedge bound are therefore tight at second order
and cannot by themselves force `eps = 0`: they are homogeneous of the same
degree as the quantity being determined.

The obstruction the calibration LP finds is FIRST order.  The instrument
that carries first-order content is the pinch read at a FIXED probe: the
contact form `a_i(D)` is first order in the deviation, while the tie caps it
by the coupling, which is second order.  Twelve such caps, one per fixture
probe, are the exact polynomial form of the LP's twelve constraints — a
conjunction, never a sum. -/

/-- **THE PINCH AT A FIXED PROBE.**  At a tie, EVERY triple and EVERY unit
probe with positive transverse coercivity obey

  `(Sigma_{c in C}(g_c . v)^2 - 1) * mu ≤ |b|^2` ,

with `b` the transverse part of the gap at the probe.  The left side is the
contact form at a FIXED probe — first order in any deviation from a contact
— and the right side is second order.  Instantiated at the twelve rational
null vectors of the doubled fixture this is the exact polynomial form of the
calibration's twelve first-order constraints, with no tangent-space object
anywhere. -/
theorem isTie_probe_pinch (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) {v : Fin k → ℝ}
    (hunit : v ⬝ᵥ v = 1) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ u : Fin k → ℝ, u ⬝ᵥ v = 0 →
      mu * (u ⬝ᵥ u) ≤ u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u)) :
    (v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) * mu
      ≤ ((subsetSum D C - 1) *ᵥ v - (v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) • v)
        ⬝ᵥ ((subsetSum D C - 1) *ᵥ v
          - (v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v)) • v) := by
  have hsymm : (subsetSum D C - 1)ᵀ = subsetSum D C - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D C)
  exact probe_coercivity_pinch hsymm hunit hmu hcoer (htie.2 C hcard)

/-- The contact form of a triple at a probe, read in atom coordinates: the
polynomial the twelve-inequality system constrains. -/
theorem probe_contactForm_eq (D : WeightedDesign m k) (C : Finset (Fin m))
    (v : Fin k → ℝ) (hunit : v ⬝ᵥ v = 1) :
    v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v) = (∑ c ∈ C, (D.atom c ⬝ᵥ v) ^ 2) - 1 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hunit, subsetSum,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [atomMatrix_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-! ## 10. The coupling in reading coordinates

Everything the swap does at a null probe is visible in five scalars: the two
readings `A = g_q.w`, `B = g_p.w`, the two leverages and the pairing.  This
section writes the defect, the coupling and the wedge in those coordinates
EXACTLY, which sharpens the inequality of the previous module into an
identity and exposes what the coupling measures.

The last identity is the sharp one: it says the missing term in the wedge
bound is the LONGITUDINAL component `A*P - B*l_p` of the swap image along
the outgoing atom.  Dropping it is what turned the identity into the earlier
inequality. -/

/-- **THE SWAP DEFECT ∈ READING COORDINATES.**  Exact, at every design. -/
theorem swapDefect_eq_reading_formula (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
        ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
      = (D.atom q ⬝ᵥ w) ^ 2 * (D.atom q ⬝ᵥ D.atom q)
        - 2 * (D.atom q ⬝ᵥ w) * (D.atom p ⬝ᵥ w) * (D.atom p ⬝ᵥ D.atom q)
        + (D.atom p ⬝ᵥ w) ^ 2 * (D.atom p ⬝ᵥ D.atom p) := by
  rw [swap_gap_mulVec_of_null D hp hq hnull]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm (D.atom q) (D.atom p)]
  ring

/-- **THE COUPLING ∈ READING COORDINATES.**  The transverse coupling energy
is the defect minus the squared reading gap. -/
theorem coupling_eq_reading_formula (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hwunit : w ⬝ᵥ w = 1) (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    swapCoupling D p q w ⬝ᵥ swapCoupling D p q w
      = (D.atom q ⬝ᵥ w) ^ 2 * (D.atom q ⬝ᵥ D.atom q)
        - 2 * (D.atom q ⬝ᵥ w) * (D.atom p ⬝ᵥ w) * (D.atom p ⬝ᵥ D.atom q)
        + (D.atom p ⬝ᵥ w) ^ 2 * (D.atom p ⬝ᵥ D.atom p)
        - ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) ^ 2 := by
  have hsplit := swapDefect_eq_couplingSq_add_nullFormSq D hp hq hwunit hnull
  have hform := swapDefect_eq_reading_formula D hp hq hnull
  rw [hform] at hsplit
  linarith [hsplit]

/-- **THE WEDGE IDENTITY.**  Lagrange at the swap image against the outgoing
atom, in full:

  `A^2*w_{pq} = |defect|^2*l_p - (A*P - B*l_p)^2` .

The subtracted term is the LONGITUDINAL component of the swap image along
`g_p`; discarding it gives the inequality the previous module landed.  So
the wedge bound is tight exactly when the swap image is transverse to the
outgoing atom. -/
theorem wedge_reading_sq_eq_defect_sub_longitudinal (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin 3 → ℝ} (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    (D.atom q ⬝ᵥ w) ^ 2
        * (leverageOf (D.atom p) * leverageOf (D.atom q)
          - (D.atom p ⬝ᵥ D.atom q) ^ 2)
      = (((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
            ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w))
          * leverageOf (D.atom p)
        - ((D.atom q ⬝ᵥ w) * (D.atom p ⬝ᵥ D.atom q)
          - (D.atom p ⬝ᵥ w) * leverageOf (D.atom p)) ^ 2 := by
  have hv := swap_gap_mulVec_of_null D hp hq hnull
  have hcross : bracketNormal ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) (D.atom p)
      = (D.atom q ⬝ᵥ w) • bracketNormal (D.atom q) (D.atom p) := by
    rw [hv]; exact bracketNormal_swapVec (D.atom p) (D.atom q) w
  have hscale : crossNormSq ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) (D.atom p)
      = (D.atom q ⬝ᵥ w) ^ 2 * crossNormSq (D.atom q) (D.atom p) := by
    rw [crossNormSq, crossNormSq, hcross, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  have hL1 := crossNormSq_eq_leverage_mul_sub_sq
    ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) (D.atom p)
  have hL2 := crossNormSq_eq_leverage_mul_sub_sq (D.atom q) (D.atom p)
  have hlev := leverageOf_eq_dotProduct ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
  have hcomm : D.atom q ⬝ᵥ D.atom p = D.atom p ⬝ᵥ D.atom q := dotProduct_comm _ _
  have hlong : ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) ⬝ᵥ D.atom p
      = (D.atom q ⬝ᵥ w) * (D.atom p ⬝ᵥ D.atom q)
        - (D.atom p ⬝ᵥ w) * leverageOf (D.atom p) := by
    rw [hv, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul, leverageOf_eq_dotProduct, hcomm]
  rw [hlev] at hL1
  rw [hlong] at hL1
  rw [hscale, hL2, hcomm] at hL1
  linarith [hL1]

/-- **THE COUPLING OF A PARALLEL PAIR FACTORS.**  If `g_q = rho*g_p` then

  `K = B^2*(rho^2-1)^2*(l_p - B^2)` ,

the squared ratio excess times the probe-transverse leverage of the shared
direction.  So a parallel pair has vanishing coupling EXACTLY when its ratio
is a sign or the shared direction lies along the probe — and the doubled
fixture, whose two copies are equal, sits at `rho = 1`. -/
theorem coupling_parallel_factorization (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin k → ℝ} (hwunit : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0)
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) :
    swapCoupling D p q w ⬝ᵥ swapCoupling D p q w
      = (D.atom p ⬝ᵥ w) ^ 2 * (ratio ^ 2 - 1) ^ 2
        * (D.atom p ⬝ᵥ D.atom p - (D.atom p ⬝ᵥ w) ^ 2) := by
  rw [coupling_eq_reading_formula D hp hq hwunit hnull, hpar]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-! ## 11. The mirror bracket law

A sibling's tie-graph work supplies, at every weak dominator of a tie, the
BRACKET IDENTITY

  `[xyz]^2 = l_x + l_y + l_z - 2 + (pm_{xy} + pm_{xz} + pm_{yz})` ,

`pm` the pair gap minor.  Read it at BOTH members of a mirror pair and
subtract: the shared pair's minor cancels, and what survives is a law about
the exchanged atoms alone.

That module is in flight, so the identity enters here as a HYPOTHESIS rather
than an import — the vocabulary (`atomBracket`, `leverageOf`,
`pairGapMinor`) is all committed, so the bridge composes with their theorem
in one line the moment it lands, and nothing here depends on an uncommitted
module. -/

/-- **THE MIRROR BRACKET DIFFERENCE.**  Subtracting the bracket identity at
the two members of a mirror pair kills the shared pair's minor and leaves

  `[prs]^2 - [qrs]^2 = (l_p - l_q)(l_r + l_s - 1)
      + ((g_q.g_r)^2 - (g_p.g_r)^2) + ((g_q.g_s)^2 - (g_p.g_s)^2)` .

Exact.  The right side is built from the SAME currency as the reading gap of
section 4 — differences of squared readings of the exchanged pair — but read
against the two SHARED atoms instead of against the null probe.  That is the
second family of reading gaps the endgame was missing. -/
theorem mirror_bracket_difference (D : WeightedDesign m 3) (p q r s : Fin m)
    (hP : atomBracket D p r s ^ 2
      = leverageOf (D.atom p) + leverageOf (D.atom r) + leverageOf (D.atom s) - 2
        + (pairGapMinor (D.atom p) (D.atom r) + pairGapMinor (D.atom p) (D.atom s)
          + pairGapMinor (D.atom r) (D.atom s)))
    (hQ : atomBracket D q r s ^ 2
      = leverageOf (D.atom q) + leverageOf (D.atom r) + leverageOf (D.atom s) - 2
        + (pairGapMinor (D.atom q) (D.atom r) + pairGapMinor (D.atom q) (D.atom s)
          + pairGapMinor (D.atom r) (D.atom s))) :
    atomBracket D p r s ^ 2 - atomBracket D q r s ^ 2
      = (leverageOf (D.atom p) - leverageOf (D.atom q))
          * (leverageOf (D.atom r) + leverageOf (D.atom s) - 1)
        + ((D.atom q ⬝ᵥ D.atom r) ^ 2 - (D.atom p ⬝ᵥ D.atom r) ^ 2)
        + ((D.atom q ⬝ᵥ D.atom s) ^ 2 - (D.atom p ⬝ᵥ D.atom s) ^ 2) := by
  simp only [pairGapMinor] at hP hQ
  linarith [hP, hQ]

/-- A bracket is linear in each atom: replacing one member by a multiple
scales it. -/
theorem atomBracket_smul_left (D : WeightedDesign m 3) (p q r s : Fin m)
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) :
    atomBracket D q r s = ratio * atomBracket D p r s := by
  simp only [atomBracket, tripleBracket_eq, hpar, Pi.smul_apply, smul_eq_mul]
  ring

/-- **THE PARALLEL MIRROR CONSTRAINT.**  If the exchanged pair is parallel
with ratio `rho`, `rho^2 != 1`, and BOTH mirror triples carry the bracket
identity, then the shared data satisfies an EXACT equation:

  `[prs]^2 = l_p*(l_r + l_s - 1) - (g_p.g_r)^2 - (g_p.g_s)^2` .

The ratio drops out entirely.  So a parallel pair whose two mirror triples
both weakly dominate is not free: unless its ratio is a sign, it pins the
bracket of the shared triple against the shared leverages.  The doubled
fixture evades this by sitting exactly at `rho = 1`, which is the only place
the constraint is vacuous — a second, independent reason the fixture is the
rigid configuration. -/
theorem parallel_mirror_bracket_constraint (D : WeightedDesign m 3) (p q r s : Fin m)
    (hP : atomBracket D p r s ^ 2
      = leverageOf (D.atom p) + leverageOf (D.atom r) + leverageOf (D.atom s) - 2
        + (pairGapMinor (D.atom p) (D.atom r) + pairGapMinor (D.atom p) (D.atom s)
          + pairGapMinor (D.atom r) (D.atom s)))
    (hQ : atomBracket D q r s ^ 2
      = leverageOf (D.atom q) + leverageOf (D.atom r) + leverageOf (D.atom s) - 2
        + (pairGapMinor (D.atom q) (D.atom r) + pairGapMinor (D.atom q) (D.atom s)
          + pairGapMinor (D.atom r) (D.atom s)))
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) (hratio : ratio ^ 2 ≠ 1) :
    atomBracket D p r s ^ 2
      = leverageOf (D.atom p) * (leverageOf (D.atom r) + leverageOf (D.atom s) - 1)
        - (D.atom p ⬝ᵥ D.atom r) ^ 2 - (D.atom p ⬝ᵥ D.atom s) ^ 2 := by
  have hdiff := mirror_bracket_difference D p q r s hP hQ
  have hbr := atomBracket_smul_left D p q r s hpar
  have hlev : leverageOf (D.atom q) = ratio ^ 2 * leverageOf (D.atom p) := by
    rw [leverageOf_eq_dotProduct, leverageOf_eq_dotProduct, hpar, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hr : D.atom q ⬝ᵥ D.atom r = ratio * (D.atom p ⬝ᵥ D.atom r) := by
    rw [hpar, smul_dotProduct, smul_eq_mul]
  have hs : D.atom q ⬝ᵥ D.atom s = ratio * (D.atom p ⬝ᵥ D.atom s) := by
    rw [hpar, smul_dotProduct, smul_eq_mul]
  rw [hbr, hlev, hr, hs] at hdiff
  have hfac : (1 - ratio ^ 2) * (atomBracket D p r s ^ 2
      - (leverageOf (D.atom p) * (leverageOf (D.atom r) + leverageOf (D.atom s) - 1)
        - (D.atom p ⬝ᵥ D.atom r) ^ 2 - (D.atom p ⬝ᵥ D.atom s) ^ 2)) = 0 := by
    linear_combination hdiff
  have hne : (1 : ℝ) - ratio ^ 2 ≠ 0 := fun h => hratio (by linarith)
  have := mul_eq_zero.mp hfac
  rcases this with h | h
  · exact absurd h hne
  · linarith [h]

end Gtz
