import Gtz.Wave.DiamondNeighborhoodMirror

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

end Gtz
