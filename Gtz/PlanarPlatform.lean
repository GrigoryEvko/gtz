/-
# The planar GAP-S platform: Theorem R′, Corollary R″, the dust expansion, the pinch

Mechanizes the AUDITED planar layer of the weighted-(6,3) campaign (diary §53
repaired, §68 audited): the corrected E-restricted master identity for an
ARBITRARY finite family of vectors — no design hypothesis, no closure. The
closure/trace/weight residuals enter the master matrix in closed form, and the
shifted-leverage parameters are FREE (the strengthening the audit verified:
the identity is polynomial in them).

Contents:
* `pairEntry` — the pair obstruction entry `⟨S_c,S_d⟩ − z_c z_d + 2a²` (in the
  g-space dictionary this equals `2[p_cd² − (ℓ_c−a)(ℓ_d−a)]`);
* `planarMaster` — the corrected master matrix `R_E` of Theorem R′;
* `planarMaster_quadraticForm` — Theorem R′: the quadratic form of `R_E` is the
  half pair-sum `(1/2)Σ_{c,d} M_cd t_c t_d ⟨S_c−S_d, ξ⟩²` (diagonal terms
  vanish, so the all-pairs sum equals the artifact's `c ≠ d` sum);
* `planarMaster_trace` — the trace form `B_E = tr R_E`;
* `posSemidef_planarMaster_of_pairEntry_nonneg` — the abstract Corollary R″:
  nonnegative off-diagonal pair entries force `R_E ⪰ 0` (the concrete step
  "silence at level a on heavy atoms ⟹ M_cd ≥ 0" is the g-space dictionary,
  consumed at closure time);
* `sum_sub_normSq_expansion` — the dust expansion identity behind the repaired
  Proposition D.3: `Σ_{c,d} f_c f_d |S_c−S_d|² = 2(Σf)(Σf|S|²) − 2|Σ f S|²`;
* `sum_sub_normSq_levWeighted` — its leverage-weighted sibling, the general
  form of the family-calculus moment identity;
* `pinch_quadratic` — on full planar designs (`Σt = 1`, `Σ t S = 0`,
  `Σ t ℓ = 2`, `|S_c| = ℓ_c`) the trace of `R` at level `1 + σ` is the exact
  quadratic `tr R(0) + 2 T₃ σ − 2 T₂ σ²`.
-/
import Mathlib
import Gtz.Basic
import Gtz.SchurRankOne
import Gtz.PsdKit

namespace Gtz

open Matrix

variable {m n : ℕ}

/-- The pair entry of the planar obstruction: `⟨S_c,S_d⟩ − z_c z_d + 2a²`. -/
def pairEntry (squares : Fin m → Fin n → ℝ) (shiftedLev : Fin m → ℝ)
    (level : ℝ) (c d : Fin m) : ℝ :=
  squares c ⬝ᵥ squares d - shiftedLev c * shiftedLev d + 2 * level ^ 2

/-- The corrected E-restricted master matrix `R_E` of Theorem R′:
`2a²τ_E Φ − s Φ_z + Ψ(r) − Φ² + Λ_z Λ_zᵀ − 2a² r rᵀ`, with every E-moment
written out (`r` closure residual, `τ_E` weight, `s` shifted-leverage mass,
`Λ_z` shifted moment, `Φ`/`Φ_z` frame operators, `Ψ(r)` third moment). -/
def planarMaster (E : Finset (Fin m)) (squares : Fin m → Fin n → ℝ)
    (weight shiftedLev : Fin m → ℝ) (level : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (2 * level ^ 2 * ∑ c ∈ E, weight c) •
      (∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c))
    - (∑ c ∈ E, weight c * shiftedLev c) •
      (∑ c ∈ E, (weight c * shiftedLev c) •
        Matrix.vecMulVec (squares c) (squares c))
    + (∑ c ∈ E, (weight c * (squares c ⬝ᵥ ∑ e ∈ E, weight e • squares e)) •
        Matrix.vecMulVec (squares c) (squares c))
    - (∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c)) *
      (∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c))
    + Matrix.vecMulVec (∑ c ∈ E, (weight c * shiftedLev c) • squares c)
        (∑ c ∈ E, (weight c * shiftedLev c) • squares c)
    - (2 * level ^ 2) •
      Matrix.vecMulVec (∑ c ∈ E, weight c • squares c)
        (∑ c ∈ E, weight c • squares c)

/-- Rank-one action on a vector, real scalars: `(vwᵀ)x = (w·x)v`. -/
private theorem vecMulVec_mulVec_real (v w x : Fin n → ℝ) :
    Matrix.vecMulVec v w *ᵥ x = (w ⬝ᵥ x) • v := by
  ext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Quadratic form of a weighted Gram-type sum: pointwise squares. -/
private theorem quadForm_weightedGram (E : Finset (Fin m))
    (coeff : Fin m → ℝ) (squares : Fin m → Fin n → ℝ) (probe : Fin n → ℝ) :
    probe ⬝ᵥ ((∑ c ∈ E, coeff c • Matrix.vecMulVec (squares c) (squares c))
        *ᵥ probe)
      = ∑ c ∈ E, coeff c * (squares c ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, vecMulVec_mulVec_real, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul,
    dotProduct_comm probe (squares c)]
  ring

/-- Quadratic form of a rank-one matrix: the square of the pairing. -/
private theorem quadForm_rankOne (direction probe : Fin n → ℝ) :
    probe ⬝ᵥ (Matrix.vecMulVec direction direction *ᵥ probe)
      = (direction ⬝ᵥ probe) ^ 2 := by
  rw [vecMulVec_mulVec_real, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe direction]
  ring

/-- The weighted Gram operator is symmetric. -/
private theorem gramOp_transpose (E : Finset (Fin m)) (coeff : Fin m → ℝ)
    (squares : Fin m → Fin n → ℝ) :
    (∑ c ∈ E, coeff c • Matrix.vecMulVec (squares c) (squares c))ᵀ
      = ∑ c ∈ E, coeff c • Matrix.vecMulVec (squares c) (squares c) := by
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec]

/-- The weighted Gram operator applied to the probe, as a vector sum. -/
private theorem gramOp_mulVec (E : Finset (Fin m)) (coeff : Fin m → ℝ)
    (squares : Fin m → Fin n → ℝ) (probe : Fin n → ℝ) :
    (∑ c ∈ E, coeff c • Matrix.vecMulVec (squares c) (squares c)) *ᵥ probe
      = ∑ c ∈ E, (coeff c * (squares c ⬝ᵥ probe)) • squares c := by
  rw [Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, vecMulVec_mulVec_real, smul_smul]

/-- Pairing of two weighted vector sums: the double sum of dot products. -/
private theorem sum_smul_dotProduct_sum (E : Finset (Fin m))
    (leftCoeff rightCoeff : Fin m → ℝ) (squares : Fin m → Fin n → ℝ) :
    ((∑ c ∈ E, leftCoeff c • squares c) ⬝ᵥ ∑ c ∈ E, rightCoeff c • squares c)
      = ∑ c ∈ E, ∑ d ∈ E,
          leftCoeff c * rightCoeff d * (squares c ⬝ᵥ squares d) := by
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_dotProduct, dotProduct_sum, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [dotProduct_smul, smul_eq_mul]
  ring

/-- Quadratic form of the squared Gram operator: the full double sum. -/
private theorem quadForm_gramSq (E : Finset (Fin m)) (weight : Fin m → ℝ)
    (squares : Fin m → Fin n → ℝ) (probe : Fin n → ℝ) :
    probe ⬝ᵥ (((∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c)) *
        (∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c)))
        *ᵥ probe)
      = ∑ c ∈ E, ∑ d ∈ E,
          weight c * (squares c ⬝ᵥ probe) * (weight d * (squares d ⬝ᵥ probe))
            * (squares c ⬝ᵥ squares d) := by
  rw [← Matrix.mulVec_mulVec, ← dotProduct_mulVec_transpose
      (∑ c ∈ E, weight c • Matrix.vecMulVec (squares c) (squares c)) probe,
    gramOp_transpose, gramOp_mulVec, sum_smul_dotProduct_sum]

/-- The scalar core of Theorem R′: for an abstract symmetric pairing and
free shifted leverages, the half pair-sum of `(pairDot − z z + 2a²)`-weighted
squared differences equals the six-moment expansion. Pure `Finset` algebra. -/
private theorem master_scalar (E : Finset (Fin m))
    (pairDot : Fin m → Fin m → ℝ)
    (hpairSymm : ∀ c d, pairDot c d = pairDot d c)
    (weight shiftedLev probeVal : Fin m → ℝ) (level : ℝ) :
    (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
        (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
          * weight c * weight d * (probeVal c - probeVal d) ^ 2
      = 2 * level ^ 2 * (∑ c ∈ E, weight c)
            * (∑ c ∈ E, weight c * probeVal c ^ 2)
        - (∑ c ∈ E, weight c * shiftedLev c)
            * (∑ c ∈ E, weight c * shiftedLev c * probeVal c ^ 2)
        + (∑ c ∈ E, ∑ d ∈ E,
            weight c * weight d * pairDot c d * probeVal c ^ 2)
        - (∑ c ∈ E, ∑ d ∈ E,
            weight c * weight d * pairDot c d * probeVal c * probeVal d)
        + (∑ c ∈ E, weight c * shiftedLev c * probeVal c) ^ 2
        - 2 * level ^ 2 * (∑ c ∈ E, weight c * probeVal c) ^ 2 := by
  -- Fold the symmetric pair-sum: (1/2) ΣΣ K (p_c − p_d)² = ΣΣ K p_c² − ΣΣ K p_c p_d.
  have hfold :
      (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
          (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
            * weight c * weight d * (probeVal c - probeVal d) ^ 2
        = (∑ c ∈ E, ∑ d ∈ E,
            (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
              * weight c * weight d * probeVal c ^ 2)
          - ∑ c ∈ E, ∑ d ∈ E,
              (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal c * probeVal d := by
    have hsplit :
        (∑ c ∈ E, ∑ d ∈ E,
            (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
              * weight c * weight d * (probeVal c - probeVal d) ^ 2)
          = (∑ c ∈ E, ∑ d ∈ E,
              ((pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                  * weight c * weight d * probeVal c ^ 2
                - (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                  * weight c * weight d * probeVal c * probeVal d))
            + ∑ c ∈ E, ∑ d ∈ E,
                ((pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                    * weight c * weight d * probeVal d ^ 2
                  - (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                    * weight c * weight d * probeVal c * probeVal d) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hswap :
        (∑ c ∈ E, ∑ d ∈ E,
            ((pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal d ^ 2
              - (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal c * probeVal d))
          = ∑ c ∈ E, ∑ d ∈ E,
              ((pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                  * weight c * weight d * probeVal c ^ 2
                - (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                  * weight c * weight d * probeVal c * probeVal d) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [hpairSymm d c]
      ring
    have hsub :
        (∑ c ∈ E, ∑ d ∈ E,
            ((pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal c ^ 2
              - (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal c * probeVal d))
          = (∑ c ∈ E, ∑ d ∈ E,
              (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                * weight c * weight d * probeVal c ^ 2)
            - ∑ c ∈ E, ∑ d ∈ E,
                (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
                  * weight c * weight d * probeVal c * probeVal d := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_sub_distrib]
    rw [hsplit, hswap, hsub]
    ring
  rw [hfold]
  -- Expand the squared-value double sum into the three moment pieces.
  have hsq :
      (∑ c ∈ E, ∑ d ∈ E,
          (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
            * weight c * weight d * probeVal c ^ 2)
        = (∑ c ∈ E, ∑ d ∈ E,
            weight c * weight d * pairDot c d * probeVal c ^ 2)
          - (∑ c ∈ E, weight c * shiftedLev c * probeVal c ^ 2)
              * (∑ c ∈ E, weight c * shiftedLev c)
          + 2 * level ^ 2 * ((∑ c ∈ E, weight c * probeVal c ^ 2)
              * (∑ c ∈ E, weight c)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  -- Expand the cross-value double sum into the three moment pieces.
  have hcross :
      (∑ c ∈ E, ∑ d ∈ E,
          (pairDot c d - shiftedLev c * shiftedLev d + 2 * level ^ 2)
            * weight c * weight d * probeVal c * probeVal d)
        = (∑ c ∈ E, ∑ d ∈ E,
            weight c * weight d * pairDot c d * probeVal c * probeVal d)
          - (∑ c ∈ E, weight c * shiftedLev c * probeVal c)
              * (∑ c ∈ E, weight c * shiftedLev c * probeVal c)
          + 2 * level ^ 2 * ((∑ c ∈ E, weight c * probeVal c)
              * (∑ c ∈ E, weight c * probeVal c)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hsq, hcross]
  ring

/-- **Theorem R′, quadratic-form statement** (the corrected E-restricted
master identity, free shifted leverages): for every probe vector `ξ`,
`ξᵀ R_E ξ = (1/2) Σ_{c,d∈E} M_cd t_c t_d ⟨S_c−S_d, ξ⟩²`. Diagonal terms
vanish, so the all-pairs sum is the artifact's `c ≠ d` sum. -/
theorem planarMaster_quadraticForm (E : Finset (Fin m))
    (squares : Fin m → Fin n → ℝ) (weight shiftedLev : Fin m → ℝ)
    (level : ℝ) (probe : Fin n → ℝ) :
    probe ⬝ᵥ (planarMaster E squares weight shiftedLev level *ᵥ probe)
      = (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
          pairEntry squares shiftedLev level c d * weight c * weight d
            * ((squares c - squares d) ⬝ᵥ probe) ^ 2 := by
  have hscalar := master_scalar E (fun c d => squares c ⬝ᵥ squares d)
    (fun c d => dotProduct_comm _ _) weight shiftedLev
    (fun c => squares c ⬝ᵥ probe) level
  have hlhs :
      probe ⬝ᵥ (planarMaster E squares weight shiftedLev level *ᵥ probe)
        = 2 * level ^ 2 * (∑ c ∈ E, weight c)
              * (∑ c ∈ E, weight c * (squares c ⬝ᵥ probe) ^ 2)
          - (∑ c ∈ E, weight c * shiftedLev c)
              * (∑ c ∈ E, weight c * shiftedLev c * (squares c ⬝ᵥ probe) ^ 2)
          + (∑ c ∈ E, ∑ d ∈ E, weight c * weight d * (squares c ⬝ᵥ squares d)
              * (squares c ⬝ᵥ probe) ^ 2)
          - (∑ c ∈ E, ∑ d ∈ E, weight c * weight d * (squares c ⬝ᵥ squares d)
              * (squares c ⬝ᵥ probe) * (squares d ⬝ᵥ probe))
          + (∑ c ∈ E, weight c * shiftedLev c * (squares c ⬝ᵥ probe)) ^ 2
          - 2 * level ^ 2 * (∑ c ∈ E, weight c * (squares c ⬝ᵥ probe)) ^ 2 := by
    simp only [planarMaster, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    rw [quadForm_weightedGram, quadForm_weightedGram, quadForm_weightedGram,
      quadForm_gramSq, quadForm_rankOne, quadForm_rankOne]
    -- Convert the third-moment coefficients and the moment-vector pairings
    -- into the scalar atoms of `master_scalar`.
    have hpsi :
        (∑ c ∈ E, weight c * (squares c ⬝ᵥ ∑ e ∈ E, weight e • squares e)
            * (squares c ⬝ᵥ probe) ^ 2)
          = ∑ c ∈ E, ∑ d ∈ E, weight c * weight d * (squares c ⬝ᵥ squares d)
              * (squares c ⬝ᵥ probe) ^ 2 := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dotProduct_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [dotProduct_smul, smul_eq_mul]
      ring
    have hlam :
        (∑ c ∈ E, (weight c * shiftedLev c) • squares c) ⬝ᵥ probe
          = ∑ c ∈ E, weight c * shiftedLev c * (squares c ⬝ᵥ probe) := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun c _ => by
        rw [smul_dotProduct, smul_eq_mul]
    have hres :
        (∑ c ∈ E, weight c • squares c) ⬝ᵥ probe
          = ∑ c ∈ E, weight c * (squares c ⬝ᵥ probe) := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun c _ => by
        rw [smul_dotProduct, smul_eq_mul]
    have hgramsq :
        (∑ c ∈ E, ∑ d ∈ E,
            weight c * (squares c ⬝ᵥ probe) * (weight d * (squares d ⬝ᵥ probe))
              * (squares c ⬝ᵥ squares d))
          = ∑ c ∈ E, ∑ d ∈ E, weight c * weight d * (squares c ⬝ᵥ squares d)
              * (squares c ⬝ᵥ probe) * (squares d ⬝ᵥ probe) := by
      exact Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => by ring
    rw [hpsi, hlam, hres, hgramsq]
  rw [hlhs, ← hscalar]
  refine congrArg (1 / 2 * ·) ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [sub_dotProduct, pairEntry]

/-- **Theorem R′, trace form**: `B_E = tr R_E` — the half pair-sum of
`M_cd t_c t_d |S_c − S_d|²` is exactly the trace of the master matrix. -/
theorem planarMaster_trace (E : Finset (Fin m))
    (squares : Fin m → Fin n → ℝ) (weight shiftedLev : Fin m → ℝ)
    (level : ℝ) :
    Matrix.trace (planarMaster E squares weight shiftedLev level)
      = (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
          pairEntry squares shiftedLev level c d * weight c * weight d
            * ((squares c - squares d) ⬝ᵥ (squares c - squares d)) := by
  have hdiag : ∀ i : Fin n,
      planarMaster E squares weight shiftedLev level i i
        = (Pi.single i 1 : Fin n → ℝ) ⬝ᵥ
            (planarMaster E squares weight shiftedLev level *ᵥ
              (Pi.single i 1 : Fin n → ℝ)) := by
    intro i
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    rfl
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc (∑ i, planarMaster E squares weight shiftedLev level i i)
      = ∑ i, (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
          pairEntry squares shiftedLev level c d * weight c * weight d
            * ((squares c - squares d) ⬝ᵥ (Pi.single i 1 : Fin n → ℝ)) ^ 2 := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [hdiag i, planarMaster_quadraticForm]
    _ = (1 / 2) * ∑ c ∈ E, ∑ d ∈ E,
          pairEntry squares shiftedLev level c d * weight c * weight d
            * ((squares c - squares d) ⬝ᵥ (squares c - squares d)) := by
        rw [← Finset.mul_sum]
        refine congrArg (1 / 2 * ·) ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.mul_sum]
        refine congrArg _ ?_
        calc (∑ i, ((squares c - squares d) ⬝ᵥ (Pi.single i 1 : Fin n → ℝ)) ^ 2)
            = ∑ i, (squares c - squares d) i * (squares c - squares d) i :=
              Finset.sum_congr rfl fun i _ => by
                rw [dotProduct_single, mul_one]; ring
          _ = (squares c - squares d) ⬝ᵥ (squares c - squares d) := rfl

/-- The master matrix is symmetric. -/
theorem planarMaster_transpose (E : Finset (Fin m))
    (squares : Fin m → Fin n → ℝ) (weight shiftedLev : Fin m → ℝ)
    (level : ℝ) :
    (planarMaster E squares weight shiftedLev level)ᵀ
      = planarMaster E squares weight shiftedLev level := by
  simp only [planarMaster, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_vecMulVec,
    gramOp_transpose]

/-- **Corollary R″, abstract form**: nonnegative weights and nonnegative
off-diagonal pair entries force the master matrix PSD. (The concrete planar
step — silence at level `a` on heavy atoms makes every `M_cd ≥ 0` — is the
g-space dictionary, applied when this is consumed with concrete data.) -/
theorem posSemidef_planarMaster_of_pairEntry_nonneg (E : Finset (Fin m))
    (squares : Fin m → Fin n → ℝ) (weight shiftedLev : Fin m → ℝ)
    (level : ℝ) (hweight : ∀ c ∈ E, 0 ≤ weight c)
    (hentry : ∀ c ∈ E, ∀ d ∈ E, c ≠ d →
      0 ≤ pairEntry squares shiftedLev level c d) :
    (planarMaster E squares weight shiftedLev level).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (planarMaster_transpose E squares weight
      shiftedLev level), fun probe => ?_⟩
  rw [star_trivial, planarMaster_quadraticForm]
  have hterms : 0 ≤ ∑ c ∈ E, ∑ d ∈ E,
      pairEntry squares shiftedLev level c d * weight c * weight d
        * ((squares c - squares d) ⬝ᵥ probe) ^ 2 := by
    refine Finset.sum_nonneg fun c hc => Finset.sum_nonneg fun d hd => ?_
    rcases eq_or_ne c d with rfl | hne
    · simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hentry c hc d hd hne)
        (hweight c hc)) (hweight d hd)) (sq_nonneg _)
  linarith

/-- **The dust expansion identity** (the exact repair of Proposition D.3, and
`(P2)` of the pinch): `Σ_{c,d} f_c f_d |S_c−S_d|² = 2(Σf)(Σ f|S|²) − 2|Σ f S|²`.
All-pairs sum; diagonal terms vanish. -/
theorem sum_sub_normSq_expansion (E : Finset (Fin m))
    (coefficient : Fin m → ℝ) (squares : Fin m → Fin n → ℝ) :
    (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
        ((squares c - squares d) ⬝ᵥ (squares c - squares d)))
      = 2 * (∑ c ∈ E, coefficient c)
          * (∑ c ∈ E, coefficient c * (squares c ⬝ᵥ squares c))
        - 2 * ((∑ c ∈ E, coefficient c • squares c) ⬝ᵥ
            (∑ c ∈ E, coefficient c • squares c)) := by
  rw [sum_smul_dotProduct_sum]
  have hexpand :
      (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
          ((squares c - squares d) ⬝ᵥ (squares c - squares d)))
        = (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
            (squares c ⬝ᵥ squares c))
          + (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
              (squares d ⬝ᵥ squares d))
          - 2 * ∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
              (squares c ⬝ᵥ squares d) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (squares d) (squares c)]
    ring
  have hfirst :
      (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
          (squares c ⬝ᵥ squares c))
        = (∑ c ∈ E, coefficient c * (squares c ⬝ᵥ squares c))
            * ∑ c ∈ E, coefficient c := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have hsecond :
      (∑ c ∈ E, ∑ d ∈ E, coefficient c * coefficient d *
          (squares d ⬝ᵥ squares d))
        = (∑ c ∈ E, coefficient c)
            * ∑ c ∈ E, coefficient c * (squares c ⬝ᵥ squares c) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  rw [hexpand, hfirst, hsecond]
  ring

/-- **The leverage-weighted expansion** (`(P1)` of the pinch, hypothesis-free
general form): weighting each squared difference by `ℓ_c + ℓ_d − 2` expands
into five moment pieces, the mixed ones through the leverage moment vector. -/
theorem sum_sub_normSq_levWeighted (E : Finset (Fin m))
    (weight lev : Fin m → ℝ) (squares : Fin m → Fin n → ℝ) :
    (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
        ((squares c - squares d) ⬝ᵥ (squares c - squares d))
          * (lev c + lev d - 2))
      = 2 * (∑ c ∈ E, weight c)
          * (∑ c ∈ E, weight c * lev c * (squares c ⬝ᵥ squares c))
        + 2 * (∑ c ∈ E, weight c * lev c)
            * (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
        - 4 * (∑ c ∈ E, weight c)
            * (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
        - 4 * ((∑ c ∈ E, (weight c * lev c) • squares c) ⬝ᵥ
            (∑ c ∈ E, weight c • squares c))
        + 4 * ((∑ c ∈ E, weight c • squares c) ⬝ᵥ
            (∑ c ∈ E, weight c • squares c)) := by
  rw [sum_smul_dotProduct_sum, sum_smul_dotProduct_sum]
  have hexpand :
      (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
          ((squares c - squares d) ⬝ᵥ (squares c - squares d))
            * (lev c + lev d - 2))
        = (∑ c ∈ E, ∑ d ∈ E, weight c * lev c *
              (squares c ⬝ᵥ squares c) * weight d)
          + (∑ c ∈ E, ∑ d ∈ E, weight c * (squares c ⬝ᵥ squares c) *
              (weight d * lev d))
          - 2 * (∑ c ∈ E, ∑ d ∈ E, weight c * (squares c ⬝ᵥ squares c) *
              weight d)
          + ((∑ c ∈ E, ∑ d ∈ E, weight c * (weight d * lev d) *
              (squares d ⬝ᵥ squares d))
            + (∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
                (squares d ⬝ᵥ squares d))
            - 2 * ∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
                (squares d ⬝ᵥ squares d))
          - 2 * ((∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
              (squares c ⬝ᵥ squares d))
            + (∑ c ∈ E, ∑ d ∈ E, weight c * (weight d * lev d) *
                (squares c ⬝ᵥ squares d))
            - 2 * ∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
                (squares c ⬝ᵥ squares d)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (squares d) (squares c)]
    ring
  have hCW : ∀ leftFactor : Fin m → ℝ,
      (∑ c ∈ E, ∑ d ∈ E, leftFactor c * weight d) =
        (∑ c ∈ E, leftFactor c) * ∑ c ∈ E, weight c := by
    intro leftFactor
    rw [Finset.sum_mul_sum]
  have hWC : ∀ rightFactor : Fin m → ℝ,
      (∑ c ∈ E, ∑ d ∈ E, weight c * rightFactor d) =
        (∑ c ∈ E, weight c) * ∑ c ∈ E, rightFactor c := by
    intro rightFactor
    rw [Finset.sum_mul_sum]
  have h1 : (∑ c ∈ E, ∑ d ∈ E, weight c * lev c *
      (squares c ⬝ᵥ squares c) * weight d)
        = (∑ c ∈ E, weight c * lev c * (squares c ⬝ᵥ squares c))
            * ∑ c ∈ E, weight c := hCW _
  have h2 : (∑ c ∈ E, ∑ d ∈ E, weight c * (squares c ⬝ᵥ squares c) *
      (weight d * lev d))
        = (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
            * ∑ c ∈ E, weight c * lev c := by
    rw [Finset.sum_mul_sum]
  have h3 : (∑ c ∈ E, ∑ d ∈ E, weight c * (squares c ⬝ᵥ squares c) * weight d)
        = (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
            * ∑ c ∈ E, weight c := hCW _
  have h4 : (∑ c ∈ E, ∑ d ∈ E, weight c * (weight d * lev d) *
      (squares d ⬝ᵥ squares d))
        = (∑ c ∈ E, weight c)
            * ∑ c ∈ E, weight c * lev c * (squares c ⬝ᵥ squares c) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h5 : (∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
      (squares d ⬝ᵥ squares d))
        = (∑ c ∈ E, weight c * lev c)
            * ∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h6 : (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
      (squares d ⬝ᵥ squares d))
        = (∑ c ∈ E, weight c)
            * ∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by ring
  have h7 : (∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
      (squares c ⬝ᵥ squares d))
        = ∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
            (squares c ⬝ᵥ squares d) := rfl
  have h8 : (∑ c ∈ E, ∑ d ∈ E, weight c * (weight d * lev d) *
      (squares c ⬝ᵥ squares d))
        = ∑ c ∈ E, ∑ d ∈ E, weight c * lev c * weight d *
            (squares c ⬝ᵥ squares d) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [dotProduct_comm (squares d) (squares c)]
    ring
  rw [hexpand, h1, h2, h3, h4, h5, h6, h8]
  ring

/-- **The pinch quadratic** (Theorem R′ specialized to full planar designs,
`z_c = ℓ_c − 2a`, `a = 1 + σ`): under `Σt = 1`, `Σ t S = 0`, `Σ t ℓ = 2`, and
`|S_c|² = ℓ_c²`, the trace of the master matrix is the exact quadratic
`tr R(0) + 2 T₃ σ − 2 T₂ σ²` in the level shift. -/
theorem pinch_quadratic (E : Finset (Fin m))
    (squares : Fin m → Fin n → ℝ) (weight lev : Fin m → ℝ)
    (hweightSum : ∑ c ∈ E, weight c = 1)
    (hclosure : (∑ c ∈ E, weight c • squares c) = 0)
    (htraceTwo : ∑ c ∈ E, weight c * lev c = 2)
    (hnormSq : ∀ c ∈ E, squares c ⬝ᵥ squares c = lev c ^ 2)
    (shift : ℝ) :
    Matrix.trace (planarMaster E squares weight
        (fun c => lev c - 2 * (1 + shift)) (1 + shift))
      = Matrix.trace (planarMaster E squares weight
          (fun c => lev c - 2) 1)
        + 2 * (∑ c ∈ E, weight c * lev c ^ 3) * shift
        - 2 * (∑ c ∈ E, weight c * lev c ^ 2) * shift ^ 2 := by
  rw [planarMaster_trace, planarMaster_trace]
  -- (P2): the plain pair-sum collapses to 2 T₂ on full designs.
  have hP2 : (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
      ((squares c - squares d) ⬝ᵥ (squares c - squares d)))
        = 2 * ∑ c ∈ E, weight c * lev c ^ 2 := by
    rw [sum_sub_normSq_expansion, hclosure, hweightSum]
    have hT2 : (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
        = ∑ c ∈ E, weight c * lev c ^ 2 :=
      Finset.sum_congr rfl fun c hc => by rw [hnormSq c hc]
    rw [hT2]
    simp only [zero_dotProduct, mul_zero, sub_zero]
    ring
  -- (P1): the leverage-weighted pair-sum collapses to 2 T₃ on full designs.
  have hP1 : (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
      ((squares c - squares d) ⬝ᵥ (squares c - squares d))
        * (lev c + lev d - 2))
        = 2 * ∑ c ∈ E, weight c * lev c ^ 3 := by
    rw [sum_sub_normSq_levWeighted, hclosure, hweightSum, htraceTwo]
    have hT2 : (∑ c ∈ E, weight c * (squares c ⬝ᵥ squares c))
        = ∑ c ∈ E, weight c * lev c ^ 2 :=
      Finset.sum_congr rfl fun c hc => by rw [hnormSq c hc]
    have hT3 : (∑ c ∈ E, weight c * lev c * (squares c ⬝ᵥ squares c))
        = ∑ c ∈ E, weight c * lev c ^ 3 :=
      Finset.sum_congr rfl fun c hc => by rw [hnormSq c hc]; ring
    rw [hT2, hT3]
    simp only [dotProduct_zero, mul_zero, sub_zero, add_zero]
    ring
  -- Per-pair, the entry at shift σ is the entry at 0 plus the linear-quadratic
  -- correction; split the pair-sum accordingly and consume (P1), (P2).
  have hsplit : (∑ c ∈ E, ∑ d ∈ E,
      pairEntry squares (fun c => lev c - 2 * (1 + shift)) (1 + shift) c d
        * weight c * weight d
        * ((squares c - squares d) ⬝ᵥ (squares c - squares d)))
        = (∑ c ∈ E, ∑ d ∈ E,
            pairEntry squares (fun c => lev c - 2) 1 c d
              * weight c * weight d
              * ((squares c - squares d) ⬝ᵥ (squares c - squares d)))
          + 2 * shift * (∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
              ((squares c - squares d) ⬝ᵥ (squares c - squares d))
                * (lev c + lev d - 2))
          - 2 * shift ^ 2 * ∑ c ∈ E, ∑ d ∈ E, weight c * weight d *
              ((squares c - squares d) ⬝ᵥ (squares c - squares d)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [pairEntry]
    ring
  rw [hsplit, hP1, hP2]
  ring

end Gtz
