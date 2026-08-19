import Gtz.Wave.FourSetCoweightCap
import Gtz.Wave.FiveSetPairFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The coweight reading ledger, the excluded-atom law, and the deficiency floor

Parseval splits the coweighted atom sum of ANY subset into its gap and the
weighted mass of the excluded atoms
(`Gtz.subsetSum_coweight_split`).  Tracing that split against the inverse gap
turns it into an exact scalar ledger (`Gtz.subset_reading_ledger`):

  `Σ_{a ∈ F} (1 − t_a) · r_a  =  3 + Σ_{b ∉ F} t_b · r_b`,

where `r_c = g_cᵀ (S_F − 1)⁻¹ g_c` reads any atom of the design — member or
not — at the subset's inverse gap.  The ledger is an identity of every design
with a strictly dominating subset, of any cardinality and at any size.

## The excluded-atom law

At a tie, a strictly dominating four-set floors its members' readings at one
(`Gtz.fourSet_leverage_ge_one`), so the ledger forces the EXCLUDED atoms to
read at least one on weighted average (`Gtz.tie_fourSet_excluded_floor`), and
some excluded atom reads at least one outright
(`Gtz.tie_fourSet_excluded_witness`).  This is the first law of the campaign
that reads a tie's refusals on the atoms a dominating set leaves OUT.

## The weighted ceiling

The same Parseval split proves a domination criterion with no tie: if the
weighted mass of the excluded atoms fits below `μ • 1` and every member weight
is at most `tbar` with `μ + tbar < 1`, the subset dominates strictly
(`Gtz.subset_dominates_of_weighted_ceiling`).  At a tie no triple dominates
strictly, so every triple obeys the floor `1 ≤ μ + tbar`
(`Gtz.tie_weighted_ceiling_floor`).

## The deficiency floor at an erased atom

At the five-set anchor of an atom of leverage at most one — the anchor is
positive definite by `Gtz.complement_erase_posDef_of_leverage_le_one` — the
ledger meets the trace identity `Σ_F r_a = 3 + tr (S_F − 1)⁻¹` and the
diagonal-below-trace bound for the erased atom, and yields the exact identity

  `Σ_{a ≠ x} (1 − t_a − t_x)(1 − r_a) = (m − 5)(1 − t_x) + t_x·(tr B⁻¹ − r_x)`

whose inequality form is `Gtz.erase_deficiency_floor`.  The floor constant
`m − 5` is the size marker: at `(6,3)` the coweighted deficiencies of the five
anchored atoms total at least `1 − t_x`, and when every anchored atom is light
the raw deficiencies total at least one
(`Gtz.sixThree_erase_deficiency_total`); at `(5,3)` the same floor is zero and
the law says nothing.  The `Z1` stratum of the corank-two corner instantiates
the floor with no extra hypothesis: its zero-reading inside atom is unit
(`Gtz.corner_oneAxisZero_deficiency_floor`).

## Calibration

The excluded-atom law and the ceiling floor are tie-necessary and field-blind:
both are VIOLATED at the three non-tie foils on record (`signCoherentFoil` at
the four-set `{0,2,4,5}` and the triple `{0,3,5}`; `ledgerFoil` at `{1,2,3,4}`
and `{2,3,4}`; `residualFoil` at `{1,3,4,5}` and `{3,4,5}`) and both HOLD at
the complex corner-tie witness at every applicable instance.  The deficiency
floor is structural — no tie — and holds at every fixture whose erased atom
has leverage at most one.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The Parseval coweight split of a subset -/

/-- **The coweight split.**  The coweighted atom sum of any subset is its gap
plus the weighted mass of the excluded atoms.  Pure Parseval. -/
theorem subsetSum_coweight_split (D : WeightedDesign m 3) (F : Finset (Fin m)) :
    ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = (subsetSum D F - 1) + ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b) := by
  classical
  have hsplit := Finset.sum_add_sum_compl F
    (fun a => D.weight a • atomMatrix (D.atom a))
  rw [D.isParseval] at hsplit
  have hexpand : ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
      = subsetSum D F - ∑ a ∈ F, D.weight a • atomMatrix (D.atom a) := by
    rw [subsetSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sub_smul, one_smul]
  have hmass : ∑ a ∈ F, D.weight a • atomMatrix (D.atom a)
      = 1 - ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b) := by
    rw [← hsplit]
    abel
  rw [hexpand, hmass]
  abel

/-! ## 2. The reading ledger -/

/-- **THE COWEIGHT READING LEDGER.**  At any strictly dominating subset, the
coweighted readings of the members total three plus the weighted readings of
the excluded atoms — an exact identity, at every subset cardinality and every
design size. -/
theorem subset_reading_ledger (D : WeightedDesign m 3) (F : Finset (Fin m))
    (hPD : (subsetSum D F - 1).PosDef) :
    ∑ a ∈ F, (1 - D.weight a)
        * (D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a))
      = 3 + ∑ b ∈ Fᶜ, D.weight b
        * (D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b)) := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have htr : ∀ (s : Finset (Fin m)) (w : Fin m → ℝ),
      Matrix.trace (A⁻¹ * ∑ a ∈ s, w a • atomMatrix (D.atom a))
        = ∑ a ∈ s, w a * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)) := by
    intro s w
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  have hsplit := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ
    => Matrix.trace (A⁻¹ * M)) (subsetSum_coweight_split D F)
  simp only [Matrix.mul_add, Matrix.trace_add] at hsplit
  rw [htr F (fun a => 1 - D.weight a), htr Fᶜ D.weight, ← hA,
    Matrix.nonsing_inv_mul A hdet, Matrix.trace_one] at hsplit
  rw [hsplit]
  norm_num

/-! ## 3. The excluded-atom law at a strictly dominating four-set -/

/-- **THE EXCLUDED-ATOM FLOOR.**  At a tie, a strictly dominating four-set
forces the atoms it excludes to read the inverse gap at least at one on
weighted average: the member floors saturate the ledger's left side. -/
theorem tie_fourSet_excluded_floor (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) :
    ∑ b ∈ Fᶜ, D.weight b
      ≤ ∑ b ∈ Fᶜ, D.weight b
          * (D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b)) := by
  classical
  have hm : 2 ≤ m := by
    have hle := Finset.card_le_card (Finset.subset_univ F)
    rw [hF, Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hledger := subset_reading_ledger D F hPD
  have hmembers : ∑ a ∈ F, (1 - D.weight a)
      ≤ ∑ a ∈ F, (1 - D.weight a)
          * (D.atom a ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hfloor := fourSet_leverage_ge_one D htie F hF hPD ha
    have hco : (0 : ℝ) ≤ 1 - D.weight a := by
      linarith [weight_lt_one D hm a]
    nlinarith [hfloor, hco]
  have hcoweight : ∑ a ∈ F, (1 - D.weight a) = 3 + ∑ b ∈ Fᶜ, D.weight b := by
    have hsplitw := Finset.sum_add_sum_compl F D.weight
    rw [D.weight_sum_one] at hsplitw
    have hones : ∑ _a ∈ F, (1 : ℝ) = 4 := by
      rw [Finset.sum_const, hF]
      norm_num
    rw [Finset.sum_sub_distrib, hones]
    linarith
  linarith [hledger, hmembers, hcoweight]

/-- **THE EXCLUDED-TRACE FLOOR.**  At a tie, a strictly dominating four-set
floors its excluded weighted readings not merely at their weight total but at
the inverse-gap trace, through every admissible odds level `o`: the coweights
`(1 − t_a) − o·t_a` stay nonnegative up to the smallest member odds, and the
member floors then charge the excluded atoms `o·(tr (S_F−1)⁻¹ − 1)` beyond
the zero-odds floor.  At `o = 0` this is `Gtz.tie_fourSet_excluded_floor`. -/
theorem tie_fourSet_excluded_trace_floor (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) {o : ℝ} (ho : 0 ≤ o)
    (hodds : ∀ a ∈ F, o * D.weight a ≤ 1 - D.weight a) :
    o * (Matrix.trace (subsetSum D F - 1)⁻¹ - 1)
      ≤ (1 + o) * (∑ b ∈ Fᶜ, D.weight b
          * (D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b))
        - ∑ b ∈ Fᶜ, D.weight b) := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  -- the coweighted member mass, exactly
  have hmassmat : ∑ a ∈ F, ((1 - D.weight a) - o * D.weight a)
      • atomMatrix (D.atom a)
      = (A - o • 1)
        + (1 + o) • ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b) := by
    have hsplit0 := subsetSum_coweight_split D F
    have hparse := Finset.sum_add_sum_compl F
      (fun a => D.weight a • atomMatrix (D.atom a))
    rw [D.isParseval] at hparse
    have hexp : ∑ a ∈ F, ((1 - D.weight a) - o * D.weight a)
        • atomMatrix (D.atom a)
        = ∑ a ∈ F, (1 - D.weight a) • atomMatrix (D.atom a)
          - o • ∑ a ∈ F, D.weight a • atomMatrix (D.atom a) := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [sub_smul, smul_smul]
    have hFin : ∑ a ∈ F, D.weight a • atomMatrix (D.atom a)
        = 1 - ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b) := by
      rw [← hparse]; abel
    rw [hexp, hsplit0, hFin, ← hA, smul_sub]
    have hone : (1 : ℝ) • ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b)
        = ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b) := one_smul _ _
    rw [add_smul, hone]
    abel
  -- the trace pairing
  have htr : ∀ (s : Finset (Fin m)) (w : Fin m → ℝ),
      Matrix.trace (A⁻¹ * ∑ a ∈ s, w a • atomMatrix (D.atom a))
        = ∑ a ∈ s, w a * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)) := by
    intro s w
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  have htrace := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ
    => Matrix.trace (A⁻¹ * M)) hmassmat
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_sub,
    Matrix.trace_sub] at htrace
  rw [htr F (fun a => (1 - D.weight a) - o * D.weight a),
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_smul, Matrix.trace_smul,
    htr Fᶜ D.weight, Matrix.nonsing_inv_mul A hdet, Matrix.trace_one,
    Matrix.mul_one] at htrace
  -- the member floors
  have hfloors : ∑ a ∈ F, ((1 - D.weight a) - o * D.weight a)
      ≤ ∑ a ∈ F, ((1 - D.weight a) - o * D.weight a)
          * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hfloor := fourSet_leverage_ge_one D htie F hF hPD ha
    rw [← hA] at hfloor
    have hw : (0 : ℝ) ≤ (1 - D.weight a) - o * D.weight a := by
      linarith [hodds a ha]
    nlinarith [hfloor, hw]
  -- the coweight totals
  have hcoweight : ∑ a ∈ F, (1 - D.weight a) = 3 + ∑ b ∈ Fᶜ, D.weight b := by
    have hsplitw := Finset.sum_add_sum_compl F D.weight
    rw [D.weight_sum_one] at hsplitw
    have hones : ∑ _a ∈ F, (1 : ℝ) = 4 := by
      rw [Finset.sum_const, hF]
      norm_num
    rw [Finset.sum_sub_distrib, hones]
    linarith
  have hwsum : ∑ a ∈ F, ((1 - D.weight a) - o * D.weight a)
      = (3 + ∑ b ∈ Fᶜ, D.weight b) - o * (1 - ∑ b ∈ Fᶜ, D.weight b) := by
    have hsplitw := Finset.sum_add_sum_compl F D.weight
    rw [D.weight_sum_one] at hsplitw
    rw [Finset.sum_sub_distrib, hcoweight, ← Finset.mul_sum]
    have : ∑ a ∈ F, D.weight a = 1 - ∑ b ∈ Fᶜ, D.weight b := by linarith
    rw [this]
  rw [hwsum] at hfloors
  rw [htrace] at hfloors
  have hcast : ((Fintype.card (Fin 3) : ℝ)) = 3 := by
    rw [Fintype.card_fin]; norm_num
  rw [hcast] at hfloors
  simp only [smul_eq_mul] at hfloors
  linarith [hfloors]

/-- **THE EXCLUDED-ATOM WITNESS.**  At a tie, a strictly dominating four-set
hands some excluded atom a reading of at least one. -/
theorem tie_fourSet_excluded_witness (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 4)
    (hPD : (subsetSum D F - 1).PosDef) (hne : (Fᶜ : Finset (Fin m)).Nonempty) :
    ∃ b ∈ Fᶜ, 1 ≤ D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hstrict : ∑ b ∈ Fᶜ, D.weight b
      * (D.atom b ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom b))
      < ∑ b ∈ Fᶜ, D.weight b := by
    refine Finset.sum_lt_sum_of_nonempty hne fun b hb => ?_
    have hlt := hcon b hb
    nlinarith [D.weight_pos b]
  linarith [tie_fourSet_excluded_floor D htie F hF hPD]

/-! ## 4. The weighted ceiling: a tie-free domination criterion -/

/-- **THE WEIGHTED CEILING CRITERION.**  If the weighted mass of the atoms a
subset excludes fits below `μ • 1`, and every member weight is at most `tbar`
with `μ + tbar < 1`, the subset dominates strictly.  Parseval pays each member
reading through its own weight, and the ceiling caps the leak. -/
theorem subset_dominates_of_weighted_ceiling (D : WeightedDesign m 3)
    (F : Finset (Fin m)) {mu tbar : ℝ}
    (htbar : ∀ a ∈ F, D.weight a ≤ tbar) (htpos : 0 < tbar)
    (hceil : (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b)).PosSemidef)
    (hlt : mu + tbar < 1) : (subsetSum D F - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D _), fun v hv => ?_⟩
  rw [star_trivial, quadForm_subsetSum_sub_one]
  have hvpos : 0 < v ⬝ᵥ v := dotProduct_self_pos hv
  have hread := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hceil).2 v
  rw [star_trivial] at hread
  have hceilv : ∑ b ∈ Fᶜ, D.weight b * (D.atom b ⬝ᵥ v) ^ 2 ≤ mu * (v ⬝ᵥ v) := by
    have hexp : v ⬝ᵥ ((mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b)) *ᵥ v)
        = mu * (v ⬝ᵥ v) - ∑ b ∈ Fᶜ, D.weight b * (D.atom b ⬝ᵥ v) ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul, Matrix.sum_mulVec, dotProduct_sum]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        show atomMatrix (D.atom b) = Matrix.vecMulVec (D.atom b) (D.atom b) from rfl,
        quadForm_atomMatrix]
    rw [hexp] at hread
    linarith
  have hpar := sum_weight_read_sq D v
  have hsplit := Finset.sum_add_sum_compl F
    (fun a => D.weight a * (D.atom a ⬝ᵥ v) ^ 2)
  rw [hpar] at hsplit
  have hcap : ∑ a ∈ F, D.weight a * (D.atom a ⬝ᵥ v) ^ 2
      ≤ tbar * ∑ a ∈ F, (D.atom a ⬝ᵥ v) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_right (htbar a ha) (sq_nonneg _)
  have hchain : (1 - mu - tbar) * (v ⬝ᵥ v)
      ≤ tbar * (∑ a ∈ F, (D.atom a ⬝ᵥ v) ^ 2 - v ⬝ᵥ v) := by
    have hmem : v ⬝ᵥ v - mu * (v ⬝ᵥ v)
        ≤ ∑ a ∈ F, D.weight a * (D.atom a ⬝ᵥ v) ^ 2 := by
      linarith [hceilv, hsplit]
    nlinarith [hcap, hmem]
  have hprod : 0 < tbar * (∑ a ∈ F, (D.atom a ⬝ᵥ v) ^ 2 - v ⬝ᵥ v) := by
    have : 0 < (1 - mu - tbar) * (v ⬝ᵥ v) :=
      mul_pos (by linarith) hvpos
    linarith
  by_contra hnon
  push_neg at hnon
  have : tbar * (∑ a ∈ F, (D.atom a ⬝ᵥ v) ^ 2 - v ⬝ᵥ v) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htpos.le (by linarith)
  linarith

/-- **THE CEILING FLOOR OF A TIE.**  A tie refuses every triple, so every
triple's excluded weighted mass ceiling plus its heaviest member weight
reaches one. -/
theorem tie_weighted_ceiling_floor (D : WeightedDesign m 3) (htie : IsTie D)
    (F : Finset (Fin m)) (hF : F.card = 3) {mu tbar : ℝ}
    (htbar : ∀ a ∈ F, D.weight a ≤ tbar) (htpos : 0 < tbar)
    (hceil : (mu • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - ∑ b ∈ Fᶜ, D.weight b • atomMatrix (D.atom b)).PosSemidef) :
    1 ≤ mu + tbar := by
  by_contra hcon
  push_neg at hcon
  exact htie.2 F hF
    (subset_dominates_of_weighted_ceiling D F htbar htpos hceil hcon)

/-! ## 5. The deficiency floor at an erased atom -/

/-- A rank-one atom of leverage at most one sits below the identity. -/
theorem one_sub_atomMatrix_posSemidef {g : Fin 3 → ℝ} (hlev : g ⬝ᵥ g ≤ 1) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix g).PosSemidef := by
  have hsym : ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix g)ᵀ
      = 1 - atomMatrix g := by
    rw [Matrix.transpose_sub, Matrix.transpose_one,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix g).1]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsym, fun v => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    show atomMatrix g = Matrix.vecMulVec g g from rfl, quadForm_atomMatrix]
  have hcs := dotProduct_sq_le_mul g v
  nlinarith [hcs, dotProduct_self_nonneg v]

/-- **THE DEFICIENCY FLOOR.**  At the positive-definite anchor of an atom of
leverage at most one, the coweighted deficiencies of the anchored atoms total
at least `(m − 5)(1 − t_x)`.  The exact remainder is `t_x (tr B⁻¹ − r_x) ≥ 0`:
the ledger, the trace identity and the diagonal-below-trace bound of the
erased atom.  The floor constant is the size marker — positive from six atoms
on, zero at five. -/
theorem erase_deficiency_floor (D : WeightedDesign m 3) {x : Fin m}
    (hlev : D.atom x ⬝ᵥ D.atom x ≤ 1)
    (hPD : (subsetSum D ((univ : Finset (Fin m)).erase x) - 1).PosDef) :
    ((m : ℝ) - 5) * (1 - D.weight x)
      ≤ ∑ a ∈ (univ : Finset (Fin m)).erase x,
          (1 - D.weight a - D.weight x)
            * (1 - D.atom a ⬝ᵥ
                ((subsetSum D ((univ : Finset (Fin m)).erase x) - 1)⁻¹
                  *ᵥ D.atom a)) := by
  classical
  set F : Finset (Fin m) := (univ : Finset (Fin m)).erase x with hFdef
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hPD.det_pos)
  have hcompl : (Fᶜ : Finset (Fin m)) = {x} := by
    rw [hFdef, Finset.compl_erase, Finset.compl_univ]
    rfl
  -- the ledger at the erased-atom anchor
  have hledger := subset_reading_ledger D F hPD
  rw [hcompl, Finset.sum_singleton, ← hA] at hledger
  -- the trace identity: the member readings total three plus the trace
  have htrace : ∑ a ∈ F, D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)
      = 3 + Matrix.trace A⁻¹ := by
    have hSF : subsetSum D F = A + 1 := by rw [hA]; abel
    have hexp : Matrix.trace (A⁻¹ * subsetSum D F)
        = ∑ a ∈ F, D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a) := by
      rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun a _ => trace_mul_atomMatrix A⁻¹ (D.atom a)
    rw [hSF, Matrix.mul_add, Matrix.trace_add, Matrix.nonsing_inv_mul A hdet,
      Matrix.trace_one, Matrix.mul_one] at hexp
    rw [← hexp, Fintype.card_fin]
    norm_num
  -- the erased reading sits below the trace
  have hrx : D.atom x ⬝ᵥ (A⁻¹ *ᵥ D.atom x) ≤ Matrix.trace A⁻¹ := by
    have hpsd := one_sub_atomMatrix_posSemidef hlev
    have hnn := trace_mul_nonneg_of_posSemidef hPD.inv.posSemidef hpsd
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one,
      trace_mul_atomMatrix] at hnn
    linarith
  -- the primitive sums
  have hxmem : x ∈ (univ : Finset (Fin m)) := Finset.mem_univ x
  have hones : ∑ _a ∈ F, (1 : ℝ) = (m : ℝ) - 1 := by
    rw [Finset.sum_const, hFdef, Finset.card_erase_of_mem hxmem,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hpos : 0 < m := Fin.pos x
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hweights : ∑ a ∈ F, D.weight a = 1 - D.weight x := by
    have := Finset.add_sum_erase (univ : Finset (Fin m)) D.weight hxmem
    rw [D.weight_sum_one] at this
    rw [hFdef]
    linarith
  -- expand the target into the primitive sums
  have hpoint : ∀ a ∈ F, (1 - D.weight a - D.weight x)
      * (1 - D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))
      = ((1 : ℝ) - D.weight a - D.weight x * 1)
        - ((1 - D.weight a) * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))
            - D.weight x * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))) := by
    intro a _
    ring
  have hsplit : ∑ a ∈ F, (1 - D.weight a - D.weight x)
      * (1 - D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))
      = ((∑ _a ∈ F, (1 : ℝ)) - (∑ a ∈ F, D.weight a)
          - D.weight x * (∑ _a ∈ F, (1 : ℝ)))
        - ((∑ a ∈ F, (1 - D.weight a) * (D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a)))
            - D.weight x * (∑ a ∈ F, D.atom a ⬝ᵥ (A⁻¹ *ᵥ D.atom a))) := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsplit, hones, hweights, hledger, htrace]
  nlinarith [mul_le_mul_of_nonneg_left hrx (D.weight_pos x).le]

/-- **THE `(6,3)` DEFICIENCY TOTAL.**  At six atoms, when every anchored atom
of a light-leverage anchor is itself light — every reading at most one — the
raw deficiencies total at least one. -/
theorem sixThree_erase_deficiency_total (D : WeightedDesign 6 3) {x : Fin 6}
    (hlev : D.atom x ⬝ᵥ D.atom x ≤ 1)
    (hPD : (subsetSum D ((univ : Finset (Fin 6)).erase x) - 1).PosDef)
    (hlight : ∀ a ∈ (univ : Finset (Fin 6)).erase x,
      D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom a) ≤ 1) :
    1 ≤ ∑ a ∈ (univ : Finset (Fin 6)).erase x,
        (1 - D.atom a ⬝ᵥ
          ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a)) := by
  have hfloor := erase_deficiency_floor D hlev hPD
  have hsix : ((6 : ℕ) : ℝ) - 5 = 1 := by norm_num
  rw [hsix, one_mul] at hfloor
  have hterm : ∀ a ∈ (univ : Finset (Fin 6)).erase x,
      (1 - D.weight a - D.weight x)
        * (1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a))
      ≤ (1 - D.weight x)
        * (1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a)) := by
    intro a ha
    exact mul_le_mul_of_nonneg_right (by linarith [D.weight_pos a])
      (by linarith [hlight a ha])
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hwx : 0 < 1 - D.weight x := by
    linarith [weight_lt_one D (by norm_num) x]
  have hchain : (1 - D.weight x) * 1
      ≤ (1 - D.weight x) * ∑ a ∈ (univ : Finset (Fin 6)).erase x,
          (1 - D.atom a ⬝ᵥ
            ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom a)) := by
    rw [mul_one]
    linarith [hfloor, hsum]
  exact le_of_mul_le_mul_left hchain hwx

/-! ## 6. The floor at the residual degenerate stratum -/

/-- **THE `Z1` DEFICIENCY FLOOR.**  At a corank-two corner whose gap axis one
inside atom reads at zero, that atom is unit, its anchor is positive definite
outright, and the floor binds with constant one — with no tie hypothesis. -/
theorem corner_oneAxisZero_deficiency_floor (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    1 - D.weight x
      ≤ ∑ a ∈ (univ : Finset (Fin 6)).erase x,
          (1 - D.weight a - D.weight x)
            * (1 - D.atom a ⬝ᵥ
                ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
                  *ᵥ D.atom a)) := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hcard : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hx : x ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  have hexX := corner_heavyExcess_axis D _ hcard hlam hunit hgap hx
  simp only [heavyExcess] at hexX
  rw [hax, show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
    (dotProduct_self_eq_sum_sq (D.atom x)).symm] at hexX
  have hlev : D.atom x ⬝ᵥ D.atom x = 1 := by
    have hcancel := mul_left_cancel₀ (ne_of_gt hone)
      (show (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = (1 + lam) * 0 by
        rw [mul_zero]
        nlinarith [hexX])
    linarith
  have hPD := corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  have hfloor := erase_deficiency_floor D hlev.le hPD
  have hsix : ((6 : ℕ) : ℝ) - 5 = 1 := by norm_num
  rw [hsix, one_mul] at hfloor
  exact hfloor

end Gtz
