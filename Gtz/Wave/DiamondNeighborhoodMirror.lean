import Gtz.Wave.TieStratumClassification
import Gtz.Design.TripleGramSylvester
import Gtz.Wave.InvariantTaxTeeth
import Gtz.Wave.TransverseFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The mirror rigidity of a doubled tie

The corank-one arm is a RIGIDITY fight: corank-one ties exist (the split
diamond), so the theorem must read "tie ⟹ parallel pair".  This module
lands the local half of that fight around the doubled fixture, and the
general quantitative instrument the global half needs.

The mechanism is a swap.  Let `C` be a weak dominator whose gap kills the
probe `w`, let `p ∈ C` and `q ∉ C`, and let `C' = C − p + q` be the swapped
triple.  Then the two gaps differ by ONE rank-one exchange, so at the null
probe of `C`

  `(S_{C'} − 1) w = (g_q·w)·g_q − (g_p·w)·g_p`

EXACTLY (`Gtz.swap_gap_mulVec_of_null`).  Every law below reads that one
identity.

* **The mirror rigidity** (`Gtz.hasParallelPair_of_mirror_nullDominators`).
  If `C` and `C'` are BOTH weak dominators and share the null probe, the
  right side vanishes, so `(g_p·w)·g_p = (g_q·w)·g_q`: the two atoms are
  PROPORTIONAL as soon as either reads the probe.  No perturbation theory,
  no eigenvalues, no size restriction — an exact identity.  This is the
  local rigidity of the doubled diamond: its four mirror pairs of weak
  dominators share their null lines exactly, and their spine readings are
  nonzero, so the parallel pair is forced.
* **The primitive obstruction** (`Gtz.nullReading_eq_zero_of_mirror_of_not_hasParallelPair`).
  Contrapositive: a design with no parallel pair admits no mirror pair of
  null-sharing weak dominators with a live reading.  Twelve simultaneous
  contacts are exactly what the doubled family carries, so this is the
  overdetermination that closes the neighborhood.
* **The probe calculus** (`Gtz.posDef_of_probe_coercivity`,
  `Gtz.probe_coercivity_pinch`).  A strict dominator can be produced, and a
  refusal exploited, from ONE probe direction plus a coercivity constant:
  with `a = wᵀAw`, `b = Aw − a·w` the transverse coupling, and `μ` a floor
  for `A` on `w^⊥`,

  `a·μ > b·b ⟹ A ≻ 0`   and   `¬(A ≻ 0) ⟹ a·μ ≤ b·b` .

  Elementary — a Schur complement written as a quadratic in two scalars, no
  spectral theorem, every size.  The pinch is the quantitative form of "a
  contact cannot open upward".
* **The swap pinch** (`Gtz.swap_pinch_of_isTie`) marries the two: at a tie,
  a weak dominator's null probe caps how much more an outside atom may read
  than the member it replaces, at the rate of the swapped triple's
  transverse coupling.  Its parallel specialization
  (`Gtz.parallel_swap_coercivity_bound`) prices a parallel pair of ratio
  `ρ² > 1` against the coercivity directly.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The probe calculus

A symmetric form splits along a unit probe into three scalars: the null
form `a`, the transverse coupling `b`, and the compression.  Positive
definiteness is then a two-variable quadratic. -/

/-- An atom matrix acts on a probe by its own reading. -/
theorem atomMatrix_mulVec (g y : Fin k → ℝ) :
    atomMatrix g *ᵥ y = (g ⬝ᵥ y) • g :=
  vecMulVec_mulVec_eq g g y

/-- **THE PROBE SPLIT.**  Along a unit probe `w`, with `a = wᵀAw` and the
transverse coupling `b = Aw − a·w`, every quadratic value decomposes as

  `uᵀAu = α²·a + 2α·(v·b) + vᵀAv` ,  `α = u·w` ,  `v = u − α·w` .

Symmetry is what makes the two cross terms equal. -/
theorem quadForm_probe_split {A : Matrix (Fin k) (Fin k) ℝ} (hsymm : Aᵀ = A)
    {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1) (u : Fin k → ℝ) :
    u ⬝ᵥ (A *ᵥ u)
      = (u ⬝ᵥ w) ^ 2 * (w ⬝ᵥ (A *ᵥ w))
        + 2 * (u ⬝ᵥ w)
            * ((u - (u ⬝ᵥ w) • w) ⬝ᵥ (A *ᵥ w - (w ⬝ᵥ (A *ᵥ w)) • w))
        + (u - (u ⬝ᵥ w) • w) ⬝ᵥ (A *ᵥ (u - (u ⬝ᵥ w) • w)) := by
  have hmove : ∀ x y : Fin k → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  set alpha : ℝ := u ⬝ᵥ w with halpha
  set a : ℝ := w ⬝ᵥ (A *ᵥ w) with ha
  set v : Fin k → ℝ := u - alpha • w with hv
  have hvw : v ⬝ᵥ w = 0 := by
    rw [hv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hw, mul_one, halpha]
    ring
  have hu : u = alpha • w + v := by rw [hv]; abel
  have hcross : v ⬝ᵥ (A *ᵥ w - a • w) = v ⬝ᵥ (A *ᵥ w) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hvw, mul_zero, sub_zero]
  have hexp : u ⬝ᵥ (A *ᵥ u)
      = alpha ^ 2 * a + alpha * (v ⬝ᵥ (A *ᵥ w)) + alpha * (w ⬝ᵥ (A *ᵥ v))
        + v ⬝ᵥ (A *ᵥ v) := by
    conv_lhs => rw [hu]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← ha]
    ring
  rw [hexp, hcross, hmove w v]
  ring

/-- **THE PROBE PRODUCER.**  A symmetric form is positive definite as soon
as its null form beats its transverse coupling at the coercivity rate:

  `a·μ > b·b ⟹ A ≻ 0` ,

where `μ` floors `A` on the probe's orthogonal complement.  The proof is
one discriminant: `a·(α²a + 2α(v·b) + μ|v|²) = (aα + v·b)² + |v|²(aμ − b·b)`. -/
theorem posDef_of_probe_coercivity {A : Matrix (Fin k) (Fin k) ℝ} (hsymm : Aᵀ = A)
    {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 → mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hgap : ((A *ᵥ w - (w ⬝ᵥ (A *ᵥ w)) • w) ⬝ᵥ (A *ᵥ w - (w ⬝ᵥ (A *ᵥ w)) • w))
      < (w ⬝ᵥ (A *ᵥ w)) * mu) :
    A.PosDef := by
  set a : ℝ := w ⬝ᵥ (A *ᵥ w) with ha
  set b : Fin k → ℝ := A *ᵥ w - a • w with hb
  have hbb : 0 ≤ b ⬝ᵥ b := dotProduct_self_nonneg b
  have hapos : 0 < a := by nlinarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun u hu => ?_⟩
  rw [star_trivial]
  set alpha : ℝ := u ⬝ᵥ w with halpha
  set v : Fin k → ℝ := u - alpha • w with hv
  have hvw : v ⬝ᵥ w = 0 := by
    rw [hv, sub_dotProduct, smul_dotProduct, smul_eq_mul, hw, mul_one, halpha]
    ring
  have hsplit := quadForm_probe_split hsymm hw u
  rw [← ha, ← hv, ← hb, ← halpha] at hsplit
  have hcomp := hcoer v hvw
  have hvv : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg v
  have hcs : (v ⬝ᵥ b) ^ 2 ≤ (v ⬝ᵥ v) * (b ⬝ᵥ b) := dotProduct_sq_le_mul v b
  rcases eq_or_lt_of_le hvv with hv0 | hvpos
  · -- the probe direction alone: the transverse part vanishes
    have hvzero : v = 0 := by
      by_contra hne
      exact absurd hv0.symm (ne_of_gt (dotProduct_self_pos hne))
    have hane : alpha ≠ 0 := by
      intro h0
      refine hu ?_
      rw [hv, h0, zero_smul, sub_zero] at hvzero
      exact hvzero
    have hvb : v ⬝ᵥ b = 0 := by rw [hvzero, zero_dotProduct]
    have hvA : v ⬝ᵥ (A *ᵥ v) = 0 := by rw [hvzero, zero_dotProduct]
    rw [hsplit, hvb, hvA]
    have : 0 < alpha ^ 2 := by positivity
    nlinarith
  · -- a genuine transverse component: the discriminant is negative
    nlinarith [sq_nonneg (a * alpha + v ⬝ᵥ b), mul_pos hvpos (sub_pos.mpr hgap)]

/-- **THE PROBE PINCH.**  A form that is NOT positive definite pays its null
form at the coercivity rate against its transverse coupling:

  `¬(A ≻ 0) ⟹ a·μ ≤ b·b` .

This is the quantitative statement that a contact cannot open upward: the
coupling is the only currency in which it may. -/
theorem probe_coercivity_pinch {A : Matrix (Fin k) (Fin k) ℝ} (hsymm : Aᵀ = A)
    {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 → mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    (hnot : ¬ A.PosDef) :
    (w ⬝ᵥ (A *ᵥ w)) * mu
      ≤ (A *ᵥ w - (w ⬝ᵥ (A *ᵥ w)) • w) ⬝ᵥ (A *ᵥ w - (w ⬝ᵥ (A *ᵥ w)) • w) := by
  by_contra hcon
  exact hnot (posDef_of_probe_coercivity hsymm hw hmu hcoer (not_le.mp hcon))

/-- **THE PROBE STRICT DOMINATOR.**  One probe, one coercivity constant, and
the design has a strictly dominating triple — hence is no tie. -/
theorem not_isTie_of_probe_coercivity (D : WeightedDesign m k) {C : Finset (Fin m)}
    (hcard : C.card = k) {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 →
      mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D C - 1) *ᵥ v))
    (hgap : (((subsetSum D C - 1) *ᵥ w
          - (w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)) • w)
        ⬝ᵥ ((subsetSum D C - 1) *ᵥ w
          - (w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)) • w))
      < (w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w)) * mu) :
    ¬ IsTie D := by
  intro htie
  refine htie.2 C hcard (posDef_of_probe_coercivity ?_ hw hmu hcoer hgap)
  rw [Matrix.transpose_sub, Matrix.transpose_one]
  congr 1
  exact transpose_eq_of_isHermitian (subsetSum_isHermitian D C)

/-! ## 2. The swap calculus

Two triples that differ in one label have gaps differing by one rank-one
exchange.  At the null probe of the first, the whole difference is visible. -/

/-- A subset sum splits off any member. -/
theorem subsetSum_erase_add (D : WeightedDesign m k) {C : Finset (Fin m)} {p : Fin m}
    (hp : p ∈ C) :
    subsetSum D C = atomMatrix (D.atom p) + subsetSum D (C.erase p) :=
  (Finset.add_sum_erase C (fun c => atomMatrix (D.atom c)) hp).symm

/-- **THE SWAP EXCHANGE.**  Replacing `p` by `q` exchanges exactly one atom
matrix. -/
theorem subsetSum_swap_eq (D : WeightedDesign m k) {C : Finset (Fin m)} {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) :
    subsetSum D (insert q (C.erase p))
      = subsetSum D C + atomMatrix (D.atom q) - atomMatrix (D.atom p) := by
  classical
  have hqe : q ∉ C.erase p := fun h => hq (Finset.mem_of_mem_erase h)
  rw [subsetSum, Finset.sum_insert hqe, ← subsetSum, subsetSum_erase_add D hp]
  abel

/-- The swapped triple keeps the cardinality. -/
theorem card_swap_eq {C : Finset (Fin m)} {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) (hcard : C.card = k) :
    (insert q (C.erase p)).card = k := by
  classical
  have hqe : q ∉ C.erase p := fun h => hq (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hqe, Finset.card_erase_of_mem hp, hcard]
  have hk : 1 ≤ k := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨p, hp⟩
  omega

/-- **THE SWAP GAP AT A NULL PROBE.**  If the gap of `C` kills `w`, the gap
of the swapped triple sends `w` to the exchange of the two readings:

  `(S_{C'} − 1) w = (g_q·w)·g_q − (g_p·w)·g_p` .

Exact, at every size, with no positivity hypothesis anywhere. -/
theorem swap_gap_mulVec_of_null (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w
      = (D.atom q ⬝ᵥ w) • D.atom q - (D.atom p ⬝ᵥ w) • D.atom p := by
  have hrw : subsetSum D (insert q (C.erase p)) - 1
      = (subsetSum D C - 1) + atomMatrix (D.atom q) - atomMatrix (D.atom p) := by
    rw [subsetSum_swap_eq D hp hq]; abel
  rw [hrw, Matrix.sub_mulVec, Matrix.add_mulVec, hnull, zero_add,
    atomMatrix_mulVec, atomMatrix_mulVec]

/-- **THE SWAP NULL FORM.**  The swapped triple reads the probe by the
difference of the two squared readings. -/
theorem swap_nullForm_of_null (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    w ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
      = (D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2 := by
  rw [swap_gap_mulVec_of_null D hp hq hnull, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm w (D.atom q),
    dotProduct_comm w (D.atom p)]
  ring

/-- **THE FREE SWAP CENSUS, QUANTITATIVE.**  If the swapped triple weakly
dominates, the incoming atom outreads the outgoing one at the probe. -/
theorem swap_reading_sq_le_of_dominates (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0)
    (hdom : Dominates D (insert q (C.erase p))) :
    (D.atom p ⬝ᵥ w) ^ 2 ≤ (D.atom q ⬝ᵥ w) ^ 2 := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 w
  rw [star_trivial, swap_nullForm_of_null D hp hq hnull] at h
  linarith

/-! ## 3. The mirror rigidity

The doubled fixture carries its weak dominators in MIRROR PAIRS: swapping
the two copies of the split atom carries a dominator to a dominator, and —
because the two copies are equal — the two share their null line.  That
sharing is the whole rigidity. -/

/-- **THE MIRROR IDENTITY.**  If a triple and its swap are BOTH killed at
the same probe, the two exchanged atoms carry the same reading vector:

  `(g_p·w)·g_p = (g_q·w)·g_q` .

One subtraction of two null conditions.  Nothing else is used: no
positivity, no tie, no size. -/
theorem mirror_reading_smul_eq (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0) :
    (D.atom p ⬝ᵥ w) • D.atom p = (D.atom q ⬝ᵥ w) • D.atom q := by
  have h := swap_gap_mulVec_of_null D hp hq hnullC
  rw [hnullSwap] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- **THE MIRROR RIGIDITY.**  A mirror pair of null-sharing weak dominators
with a live reading FORCES the exchanged atoms parallel.  This is the local
rigidity of the doubled diamond in exact form. -/
theorem hasParallelPair_of_mirror_nullDominators (D : WeightedDesign m k)
    {C : Finset (Fin m)} {p q : Fin m} (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0)
    (hread : D.atom p ⬝ᵥ w ≠ 0) :
    HasParallelPair D := by
  refine ⟨q, p, (D.atom q ⬝ᵥ w) / (D.atom p ⬝ᵥ w), (Ne.symm hpq), ?_⟩
  have h := mirror_reading_smul_eq D hp hq hnullC hnullSwap
  have hscaled := congrArg (fun z : Fin k → ℝ => (D.atom p ⬝ᵥ w)⁻¹ • z) h
  simp only [smul_smul, inv_mul_cancel₀ hread, one_smul] at hscaled
  rw [div_eq_inv_mul]
  exact hscaled

/-- **THE PRIMITIVE OBSTRUCTION.**  A design with no parallel pair carries
no mirror pair of null-sharing weak dominators with a live reading: at every
such mirror pair the shared probe is BLIND to the exchanged member.

Twelve simultaneous contacts is exactly what a doubled tie carries, so this
is the overdetermination that closes a neighborhood of the fixture. -/
theorem nullReading_eq_zero_of_mirror_of_not_hasParallelPair (D : WeightedDesign m k)
    (hprim : ¬ HasParallelPair D) {C : Finset (Fin m)} {p q : Fin m}
    (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0) :
    D.atom p ⬝ᵥ w = 0 := by
  by_contra hread
  exact hprim (hasParallelPair_of_mirror_nullDominators D hpq hp hq hnullC hnullSwap hread)

/-- Both members of a mirror pair are blind: the reading identity is
symmetric in the two exchanged labels. -/
theorem mirror_readings_eq_zero_of_not_hasParallelPair (D : WeightedDesign m k)
    (hprim : ¬ HasParallelPair D) {C : Finset (Fin m)} {p q : Fin m}
    (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0) :
    D.atom p ⬝ᵥ w = 0 ∧ D.atom q ⬝ᵥ w = 0 := by
  have hp0 := nullReading_eq_zero_of_mirror_of_not_hasParallelPair D hprim hpq hp hq
    hnullC hnullSwap
  refine ⟨hp0, ?_⟩
  have h := mirror_reading_smul_eq D hp hq hnullC hnullSwap
  rw [hp0, zero_smul] at h
  by_contra hq0
  have hzero : D.atom q = 0 := by
    have := congrArg (fun z : Fin k → ℝ => (D.atom q ⬝ᵥ w)⁻¹ • z) h.symm
    simpa [smul_smul, inv_mul_cancel₀ hq0] using this
  rw [hzero, zero_dotProduct] at hq0
  exact hq0 rfl

/-- **THE TWO-SIDED SQUEEZE.**  When the mirror pair does NOT share a null
line, the two dominators still trap each other: each null probe ranks its
own member below the other.  This is the quantitative residue that the
neighborhood argument closes. -/
theorem mirror_reading_squeeze (D : WeightedDesign m k) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w wswap : Fin k → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ wswap = 0)
    (hdomC : Dominates D C)
    (hdomSwap : Dominates D (insert q (C.erase p))) :
    (D.atom p ⬝ᵥ w) ^ 2 ≤ (D.atom q ⬝ᵥ w) ^ 2
      ∧ (D.atom q ⬝ᵥ wswap) ^ 2 ≤ (D.atom p ⬝ᵥ wswap) ^ 2 := by
  classical
  refine ⟨swap_reading_sq_le_of_dominates D hp hq hnullC hdomSwap, ?_⟩
  -- the reverse swap carries the swapped triple back to `C`
  have hqmem : q ∈ insert q (C.erase p) := Finset.mem_insert_self q _
  have hpnot : p ∉ insert q (C.erase p) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hq (h ▸ hp)
    · exact (Finset.ne_of_mem_erase h) rfl
  have hback : insert p ((insert q (C.erase p)).erase q) = C := by
    rw [Finset.erase_insert (fun h => hq (Finset.mem_of_mem_erase h)),
      Finset.insert_erase hp]
  have h := swap_reading_sq_le_of_dominates D hqmem hpnot hnullSwap (by rw [hback]; exact hdomC)
  exact h

/-! ## 4. The quantitative swap pinch

At a tie the swapped triple is refused, so the probe pinch caps its null
form.  The cap is the transverse coupling of the exchange, and it is
explicit in the two readings and the two atoms. -/

/-- The transverse coupling of a swap at a null probe. -/
noncomputable def swapCoupling (D : WeightedDesign m k) (p q : Fin m)
    (w : Fin k → ℝ) : Fin k → ℝ :=
  (D.atom q ⬝ᵥ w) • D.atom q - (D.atom p ⬝ᵥ w) • D.atom p
    - ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) • w

/-- **THE SWAP PINCH OF A TIE.**  At a tie, a weak dominator's null probe
caps how much more an outside atom may read than the member it replaces:

  `((g_q·w)² − (g_p·w)²)·μ ≤ |swapCoupling|²` ,

with `μ` any coercivity floor of the swapped gap transverse to the probe.
The landed census is the `μ`-free half of this; the content here is that
the excess is paid ENTIRELY by the transverse coupling. -/
theorem swap_pinch_of_isTie (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 →
      mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v)) :
    ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) * mu
      ≤ swapCoupling D p q w ⬝ᵥ swapCoupling D p q w := by
  have hsymm : (subsetSum D (insert q (C.erase p)) - 1)ᵀ
      = subsetSum D (insert q (C.erase p)) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    exact transpose_eq_of_isHermitian (subsetSum_isHermitian D _)
  have hnotPD := htie.2 _ (card_swap_eq hp hq hcard)
  have hpinch := probe_coercivity_pinch hsymm hw hmu hcoer hnotPD
  rw [swap_nullForm_of_null D hp hq hnull] at hpinch
  have hcoup : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w
        - ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2) • w
      = swapCoupling D p q w := by
    rw [swap_gap_mulVec_of_null D hp hq hnull, swapCoupling]
  rw [hcoup] at hpinch
  exact hpinch

/-- **THE PARALLEL PRICE.**  A parallel pair of ratio `ρ` with `ρ² > 1`
caps the coercivity of every swapped triple by the ratio excess times the
probe-transverse leverage of the replaced atom:

  `μ ≤ (ρ² − 1)·(|g_p|² − (g_p·w)²)` .

The coupling of a parallel exchange is a multiple of the transverse part of
the shared direction, so the pinch becomes a bound with no atom data beyond
one leverage. -/
theorem parallel_swap_coercivity_bound (D : WeightedDesign m k) (htie : IsTie D)
    {C : Finset (Fin m)} (hcard : C.card = k) {p q : Fin m}
    (hp : p ∈ C) (hq : q ∉ C) {w : Fin k → ℝ} (hw : w ⬝ᵥ w = 1)
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) {mu : ℝ} (hmu : 0 < mu)
    (hcoer : ∀ v : Fin k → ℝ, v ⬝ᵥ w = 0 →
      mu * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ v))
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p)
    (hratio : 1 < ratio ^ 2) (hread : D.atom p ⬝ᵥ w ≠ 0) :
    mu ≤ (ratio ^ 2 - 1) * (D.atom p ⬝ᵥ D.atom p - (D.atom p ⬝ᵥ w) ^ 2) := by
  have hpinch := swap_pinch_of_isTie D htie hcard hp hq hw hnull hmu hcoer
  have hqr : D.atom q ⬝ᵥ w = ratio * (D.atom p ⬝ᵥ w) := by
    rw [hpar, smul_dotProduct, smul_eq_mul]
  -- the coupling is `(ρ²−1)·r` times the transverse part of `g_p`
  have hcoup : swapCoupling D p q w
      = ((ratio ^ 2 - 1) * (D.atom p ⬝ᵥ w)) • (D.atom p - (D.atom p ⬝ᵥ w) • w) := by
    rw [swapCoupling, hqr, hpar]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcomm : w ⬝ᵥ D.atom p = D.atom p ⬝ᵥ w := dotProduct_comm w (D.atom p)
  have hexpand : swapCoupling D p q w ⬝ᵥ swapCoupling D p q w
      = ((ratio ^ 2 - 1) * (D.atom p ⬝ᵥ w)) ^ 2
        * (D.atom p ⬝ᵥ D.atom p - (D.atom p ⬝ᵥ w) ^ 2) := by
    rw [hcoup]
    simp only [smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub,
      smul_eq_mul]
    rw [hw, hcomm]
    ring
  rw [hexpand, hqr] at hpinch
  have hrsq : 0 < (D.atom p ⬝ᵥ w) ^ 2 := by positivity
  have hpos : 0 < (ratio ^ 2 - 1) * (D.atom p ⬝ᵥ w) ^ 2 := by nlinarith
  refine le_of_mul_le_mul_left ?_ hpos
  nlinarith [hpinch]

/-! ## 5. The wedge defect

The hinge's conclusion is a VANISHING WEDGE: a parallel pair is exactly a
vanishing pair cross, which is what the pair-minor bridge reads as a
singular pivot minor and what the wedge-bracket tax prices.  This section
carries the mirror rigidity into that currency AND quantifies it: the pair
wedge is capped by the SWAP DEFECT — the failure of the swapped gap to kill
the probe — with no smallness hypothesis anywhere. -/

/-- The cross of the swap vector against the outgoing atom is the incoming
reading times the pair cross: the outgoing atom cancels itself. -/
theorem bracketNormal_swapVec (gp gq w : Fin 3 → ℝ) :
    bracketNormal ((gq ⬝ᵥ w) • gq - (gp ⬝ᵥ w) • gp) gp
      = (gq ⬝ᵥ w) • bracketNormal gq gp := by
  ext i
  fin_cases i <;>
    simp [bracketNormal, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- **THE WEDGE DEFECT BOUND.**  At the null probe of a weak dominator, the
wedge of the exchanged pair is capped by the swap defect:

  `w_{pq}·(g_q·w)² ≤ |g_p|²·|(S_{C'} − 1)w|²` .

Exact at every design: no positivity, no tie, no smallness.  The right side
vanishes EXACTLY when the swapped gap also kills the probe — the mirror
hypothesis — so this is the quantitative form of the mirror rigidity, and
it degenerates at precisely the locus the rigidity claims. -/
theorem wedge_mul_reading_sq_le_swap_defect (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin 3 → ℝ} (hnull : (subsetSum D C - 1) *ᵥ w = 0) :
    (leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2)
        * (D.atom q ⬝ᵥ w) ^ 2
      ≤ leverageOf (D.atom p)
        * (((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
            ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)) := by
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
  have hcomm : D.atom q ⬝ᵥ D.atom p = D.atom p ⬝ᵥ D.atom q :=
    dotProduct_comm _ _
  rw [hlev] at hL1
  have hstep : (leverageOf (D.atom p) * leverageOf (D.atom q)
        - (D.atom p ⬝ᵥ D.atom q) ^ 2) * (D.atom q ⬝ᵥ w) ^ 2
      = crossNormSq ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) (D.atom p) := by
    rw [hscale, hL2, hcomm]; ring
  rw [hstep, hL1]
  nlinarith [sq_nonneg (((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) ⬝ᵥ D.atom p)]

/-- The wedge of any pair is nonnegative — it is a squared cross. -/
theorem wedge_nonneg (a b : Fin 3 → ℝ) :
    0 ≤ leverageOf a * leverageOf b - (a ⬝ᵥ b) ^ 2 := by
  rw [← crossNormSq_eq_leverage_mul_sub_sq, crossNormSq]
  exact dotProduct_self_nonneg _

/-- **THE MIRROR WEDGE.**  A mirror pair of null-sharing weak dominators has
VANISHING WEDGE.  This is the mirror rigidity delivered in the hinge's own
currency: the pair-minor bridge reads a zero wedge as a singular pivot
minor, and the wedge-bracket tax reads it as a floorless block. -/
theorem mirror_wedge_eq_zero (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin 3 → ℝ}
    (hnullC : (subsetSum D C - 1) *ᵥ w = 0)
    (hnullSwap : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0)
    (hread : D.atom q ⬝ᵥ w ≠ 0) :
    leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2 = 0 := by
  have hbound := wedge_mul_reading_sq_le_swap_defect D hp hq hnullC
  rw [hnullSwap, zero_dotProduct, mul_zero] at hbound
  have hpos : 0 < (D.atom q ⬝ᵥ w) ^ 2 := by positivity
  have hnn := wedge_nonneg (D.atom p) (D.atom q)
  nlinarith [hbound, hpos, hnn]

/-- **THE WEDGE FLOOR ON THE SWAP DEFECT.**  The defect bound, divided: the
swapped gap of every mirror candidate must miss the probe by at least the
pair's own wedge, scaled by the incoming reading and the outgoing leverage.

This is the shape a global rigidity law consumes — margins against the
minimum pair wedge — with the constant supplied by the fixture. -/
theorem swap_defect_ge_wedge_ratio (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) (hlevpos : 0 < leverageOf (D.atom p)) :
    (leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2)
        * (D.atom q ⬝ᵥ w) ^ 2 / leverageOf (D.atom p)
      ≤ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
          ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) := by
  have hbound := wedge_mul_reading_sq_le_swap_defect D hp hq hnull
  rw [div_le_iff₀ hlevpos]
  nlinarith [hbound]

/-- **THE PRIMITIVE DEFECT IS STRICT.**  At a design with NO parallel pair,
every mirror-candidate swap misses the probe STRICTLY, as soon as the
incoming atom reads it at all:

  `0 < |(S_{C'} − 1)w|²` .

Contrapositive of the mirror rigidity, and the exact statement a
neighborhood argument needs: the doubled fixture sits at defect zero on all
four of its mirror pairs, so every primitive design near it is pushed away
from every one of them at once.  Twelve contacts, four of them mirrored —
the overdetermination has nowhere to go. -/
theorem swap_defect_pos_of_not_hasParallelPair (D : WeightedDesign m 3)
    (hprim : ¬ HasParallelPair D) {C : Finset (Fin m)} {p q : Fin m}
    (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D C - 1) *ᵥ w = 0) (hread : D.atom q ⬝ᵥ w ≠ 0) :
    0 < ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
        ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w) := by
  rcases (dotProduct_self_nonneg
    ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hzero : (subsetSum D (insert q (C.erase p)) - 1) *ᵥ w = 0 := by
      by_contra hne
      exact absurd heq.symm (ne_of_gt (dotProduct_self_pos hne))
    exact hread
      (mirror_readings_eq_zero_of_not_hasParallelPair D hprim hpq hp hq hnull hzero).2

/-! ## 6. Discharging the shared null line

Section 3 buys the parallel pair from a SHARED null line, and section 5
prices the wedge by the swap defect.  Both hypotheses can now be removed at
once.  A positive semidefinite gap cannot send a probe far while reading it
little: Cauchy–Schwarz in the gap's own form, against the landed trace law,
gives

  `|M w|² ≤ tr M · (wᵀ M w)` ,

so the swap defect is at most the trace times the swap's null form — and
the swap's null form at the probe of a weak dominator is exactly the
READING GAP of the exchanged pair.  The wedge is therefore capped by how
much more the incoming atom reads than the outgoing one.  At the doubled
fixture the two copies read EQUALLY, so the cap is zero. -/

/-- **A SEMIDEFINITE GAP CANNOT THROW A PROBE IT BARELY READS.**  For a
positive semidefinite matrix, `|Mw|² ≤ tr M · (wᵀMw)`.  Proved from the
form's own Cauchy–Schwarz against the landed trace law — no spectral
theorem, no square root. -/
theorem psd_mulVec_normSq_le_trace_mul_quadForm
    {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) (w : Fin 3 → ℝ) :
    (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ Matrix.trace M * (w ⬝ᵥ (M *ᵥ w)) := by
  have hsymm : Mᵀ = M := transpose_eq_of_isHermitian hM.1
  have hmove : ∀ x y : Fin 3 → ℝ, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm]
  have hquad : ∀ x : Fin 3 → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
    intro x
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 x
    rwa [star_trivial] at h
  -- `|Mw|²` is the `M`-pairing of `w` against `Mw`
  have hX : w ⬝ᵥ (M *ᵥ (M *ᵥ w)) = (M *ᵥ w) ⬝ᵥ (M *ᵥ w) := by
    rw [hmove w (M *ᵥ w)]
  have hcs := posSemidef_bilinear_sq_le hM w (M *ᵥ w)
  rw [hX] at hcs
  have htrace := form_le_trace_mul_normSq_of_posSemidef hM (M *ᵥ w)
  set X : ℝ := (M *ᵥ w) ⬝ᵥ (M *ᵥ w) with hXdef
  have hXnn : 0 ≤ X := dotProduct_self_nonneg _
  rcases hXnn.lt_or_eq with hpos | hzero
  · nlinarith [hcs, htrace, hquad w, hpos]
  · rw [← hzero]
    have hdiag : ∀ i, 0 ≤ M i i := by
      intro i
      have h := hquad (Pi.single i 1)
      rw [single_one_dotProduct, Matrix.mulVec_single_one] at h
      simpa using h
    have htr : 0 ≤ Matrix.trace M := by
      rw [Matrix.trace_fin_three]
      linarith [hdiag 0, hdiag 1, hdiag 2]
    exact mul_nonneg htr (hquad w)

/-- **THE READING-GAP RIGIDITY.**  When BOTH members of a mirror candidate
weakly dominate and the first kills the probe, the pair wedge is capped by
the READING GAP alone:

  `w_{pq}·(g_q·w)² ≤ |g_p|²·tr(S_{C'} − 1)·((g_q·w)² − (g_p·w)²)` .

No coercivity constant, no shared null line, no smallness hypothesis.  The
mirror hypothesis of section 3 has been traded for two weak dominations,
and the entire obstruction is the excess reading of the incoming atom.  At
the doubled fixture the two copies read EQUALLY, the right side is zero,
and the wedge vanishes: the local rigidity with its analytic hypothesis
discharged. -/
theorem wedge_le_reading_gap_of_mirror_dominators (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin 3 → ℝ} (hnull : (subsetSum D C - 1) *ᵥ w = 0)
    (hdom : Dominates D (insert q (C.erase p))) :
    (leverageOf (D.atom p) * leverageOf (D.atom q) - (D.atom p ⬝ᵥ D.atom q) ^ 2)
        * (D.atom q ⬝ᵥ w) ^ 2
      ≤ leverageOf (D.atom p)
        * (Matrix.trace (subsetSum D (insert q (C.erase p)) - 1)
          * ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2)) := by
  have hdefect := wedge_mul_reading_sq_le_swap_defect D hp hq hnull
  have hthrow := psd_mulVec_normSq_le_trace_mul_quadForm hdom w
  rw [swap_nullForm_of_null D hp hq hnull] at hthrow
  have hlevnn : 0 ≤ leverageOf (D.atom p) := by
    rw [leverageOf_eq_dotProduct]
    exact dotProduct_self_nonneg _
  calc (leverageOf (D.atom p) * leverageOf (D.atom q)
          - (D.atom p ⬝ᵥ D.atom q) ^ 2) * (D.atom q ⬝ᵥ w) ^ 2
      ≤ leverageOf (D.atom p)
          * (((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)
            ⬝ᵥ ((subsetSum D (insert q (C.erase p)) - 1) *ᵥ w)) := hdefect
    _ ≤ leverageOf (D.atom p)
          * (Matrix.trace (subsetSum D (insert q (C.erase p)) - 1)
            * ((D.atom q ⬝ᵥ w) ^ 2 - (D.atom p ⬝ᵥ w) ^ 2)) :=
        mul_le_mul_of_nonneg_left hthrow hlevnn

/-- **THE MIRROR RIGIDITY WITHOUT THE SHARED NULL.**  Two weakly dominating
mirror members whose exchanged atoms read the probe EQUALLY force the pair
parallel.  This is the local rigidity in its final hypothesis: equal
readings, not a shared null line. -/
theorem hasParallelPair_of_mirror_dominators_of_readings_eq (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {p q : Fin m} (hpq : p ≠ q) (hp : p ∈ C) (hq : q ∉ C)
    {w : Fin 3 → ℝ} (hnull : (subsetSum D C - 1) *ᵥ w = 0)
    (hdom : Dominates D (insert q (C.erase p)))
    (hreadeq : (D.atom p ⬝ᵥ w) ^ 2 = (D.atom q ⬝ᵥ w) ^ 2)
    (hread : D.atom q ⬝ᵥ w ≠ 0) :
    HasParallelPair D := by
  have hbound := wedge_le_reading_gap_of_mirror_dominators D hp hq hnull hdom
  rw [← hreadeq, sub_self, mul_zero, mul_zero] at hbound
  have hwedge : leverageOf (D.atom p) * leverageOf (D.atom q)
      - (D.atom p ⬝ᵥ D.atom q) ^ 2 = 0 := by
    have hpos : 0 < (D.atom q ⬝ᵥ w) ^ 2 := by positivity
    have hnn := wedge_nonneg (D.atom p) (D.atom q)
    nlinarith [hbound, hpos, hnn]
  -- a vanishing wedge is a vanishing cross, hence a parallel pair
  have hcross : crossNormSq (D.atom p) (D.atom q) = 0 := by
    rw [crossNormSq_eq_leverage_mul_sub_sq]; exact hwedge
  have hbn : bracketNormal (D.atom p) (D.atom q) = 0 := by
    rw [crossNormSq] at hcross
    exact dotProduct_self_eq_zero.mp hcross
  have hpne : D.atom p ≠ 0 := by
    intro h0
    refine hread ?_
    have hsq : (D.atom q ⬝ᵥ w) ^ 2 = 0 := by
      rw [← hreadeq, h0, zero_dotProduct]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  exact ⟨p, q, (D.atom p ⬝ᵥ D.atom q) / (D.atom p ⬝ᵥ D.atom p), hpq,
    eq_smul_of_bracketNormal_eq_zero (D.atom p) (D.atom q) hpne hbn⟩

end Gtz
