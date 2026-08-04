import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-
# The K4 diagonal bricks

K4 -- six edges on four vertices -- is the unique non-series-parallel graph a
parallel-free graphic (6,3) design can realize, so it is the entire graphic
residue of the hinge once Nesterenko's fixed-graph theorem (arXiv:2511.02387v2,
Theorem 4.1) settles the series-parallel family.  This file turns the exact
findings of the K4 measurement lane (gtz-staging-p6/graphic/findings.txt,
sections 3-6) into kernel facts, in the gauge coordinates of that lane:
vertex 0 grounded, potentials `y : Fin 3 -> R` at vertices 1,2,3, edges
`e0=(0,1) e1=(0,2) e2=(0,3) e3=(1,2) e4=(1,3) e5=(2,3)`, and on the diagonal
slice `c = w` the gap form of a spanning tree `T` is
`sum_{e in T} drop_e^2 - sum_e w_e drop_e^2`.

Three bricks, every constant re-derived in exact rationals first
(`verify_k4_diagonal.py`, ALL EXACT CHECKS PASS):

1. **Stratum A.**  On `w = (a,a,a,b,b,b)` the apex-star gap matrix is
   `(1-a-2b)` on the diagonal and `b` off it; its characteristic polynomial
   factors as `(X - (1-a-3b))^2 (X - (1-a))`, hence on the simplex
   `3a+3b = 1` the gauge spectrum is `{2a, 2a, 1-a}`.  The findings' printed
   spectrum `{2a, 2a, 4-4a}` is the SAME quadratic form read in the ambient
   `1`-orthogonal picture of `R^4` -- congruent, not similar, to the gauge
   matrix; both spectra are verified in the sympy script.  The sharp law of
   findings section 4 is here in exact pencil form: on the simplex,
   `Gap - 2a*B = (b + a/2) * (y0+y1+y2)^2` where `B` is the gauge matrix of
   the ambient restricted norm, so `Gap >= 2a*B` always, with equality on
   the whole sum-zero plane.
2. **The exchange lemma.**  No positive conductances, positive weights and
   nonzero probe make all sixteen spanning-tree gap forms vanish
   simultaneously: tree exchanges force the six quantities
   `(c_e/w_e) drop_e^2` equal, and the two evaluations of the common tie
   level -- three tree edges versus the weighted total on the simplex --
   force `3d = d`.
3. **Averaged positivity.**  Each edge lies in exactly eight of the sixteen
   trees, so the SUM of the sixteen gap forms is
   `8 * sum_e c_e (1/w_e - 2) drop_e^2`, nonnegative whenever every
   `w_e <= 1/2`; some tree gap form is then nonnegative at every probe.
-/

namespace Gtz

open Matrix

/-! ## The gauge drops and the sixteen spanning trees -/

/-- Gauge-fixed potential drop of each K4 edge: vertex 0 is grounded and
`y i` is the potential at vertex `i + 1`. -/
def k4Drop (y : Fin 3 → ℝ) : Fin 6 → ℝ
  | 0 => y 0
  | 1 => y 1
  | 2 => y 2
  | 3 => y 0 - y 1
  | 4 => y 0 - y 2
  | 5 => y 1 - y 2

theorem k4Drop_zero (y : Fin 3 → ℝ) : k4Drop y 0 = y 0 := rfl
theorem k4Drop_one (y : Fin 3 → ℝ) : k4Drop y 1 = y 1 := rfl
theorem k4Drop_two (y : Fin 3 → ℝ) : k4Drop y 2 = y 2 := rfl
theorem k4Drop_three (y : Fin 3 → ℝ) : k4Drop y 3 = y 0 - y 1 := rfl
theorem k4Drop_four (y : Fin 3 → ℝ) : k4Drop y 4 = y 0 - y 2 := rfl
theorem k4Drop_five (y : Fin 3 → ℝ) : k4Drop y 5 = y 1 - y 2 := rfl

/-- The sixteen spanning trees of K4 as edge triples: all twenty
three-subsets except the four triangles `{0,1,3}, {0,2,4}, {1,2,5},
{3,4,5}`.  Verified against the gauge drop covectors in the sympy script:
a triple is a spanning tree exactly when its three drop covectors are
linearly independent. -/
def k4TreeTriples : List (Fin 6 × Fin 6 × Fin 6) :=
  [(0, 1, 2), (0, 1, 4), (0, 1, 5), (0, 2, 3), (0, 2, 5), (0, 3, 4),
   (0, 3, 5), (0, 4, 5), (1, 2, 3), (1, 2, 4), (1, 3, 4), (1, 3, 5),
   (1, 4, 5), (2, 3, 4), (2, 3, 5), (2, 4, 5)]

theorem k4TreeTriples_length : k4TreeTriples.length = 16 := rfl

/-- Every edge of K4 lies in exactly eight of the sixteen spanning trees. -/
theorem k4TreeTriples_count_eq_eight :
    ∀ e : Fin 6, (k4TreeTriples.countP fun T =>
      decide (T.1 = e ∨ T.2.1 = e ∨ T.2.2 = e)) = 8 := by decide

/-- The diagonal-slice gap form of one spanning tree of the graphic family
with conductances `c` and design weights `w`: the tree's own
conductance-to-weight rescaled energy against the total weighted energy.
The design dominates on the tree exactly when this form is nonnegative at
every probe (findings section 0, the sign dictionary). -/
noncomputable def k4TreeGapForm (c w : Fin 6 → ℝ) (y : Fin 3 → ℝ)
    (T : Fin 6 × Fin 6 × Fin 6) : ℝ :=
  c T.1 / w T.1 * k4Drop y T.1 ^ 2 + c T.2.1 / w T.2.1 * k4Drop y T.2.1 ^ 2
    + c T.2.2 / w T.2.2 * k4Drop y T.2.2 ^ 2
    - ∑ e, c e * k4Drop y e ^ 2

/-! ## Brick 2: the exchange lemma at K4 -/

/-- **The exchange lemma, concretely at K4.**  If every one of the sixteen
spanning-tree gap forms vanishes at the probe `y`, then `y = 0`: tree
exchanges force all six rescaled energies `(c_e/w_e) drop_e^2` to one common
value `d`; the common tie level is `3d` counted along a tree and `d`
counted against the weight simplex, so `d = 0`, and vanishing star drops
ground the probe. -/
theorem k4_all_trees_tight_forces_zero (c w : Fin 6 → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 < w e) (hsum : ∑ e, w e = 1)
    (y : Fin 3 → ℝ)
    (htight : ∀ T ∈ k4TreeTriples, k4TreeGapForm c w y T = 0) : y = 0 := by
  have h012 := htight (0, 1, 2) (by decide)
  have h014 := htight (0, 1, 4) (by decide)
  have h015 := htight (0, 1, 5) (by decide)
  have h023 := htight (0, 2, 3) (by decide)
  have h025 := htight (0, 2, 5) (by decide)
  have h123 := htight (1, 2, 3) (by decide)
  simp only [k4TreeGapForm, Fin.sum_univ_six] at h012 h014 h015 h023 h025 h123
  have hb0 : w 0 * (c 0 / w 0 * k4Drop y 0 ^ 2) = c 0 * k4Drop y 0 ^ 2 := by
    have hne := (hw 0).ne'; field_simp
  have hb1 : w 1 * (c 1 / w 1 * k4Drop y 1 ^ 2) = c 1 * k4Drop y 1 ^ 2 := by
    have hne := (hw 1).ne'; field_simp
  have hb2 : w 2 * (c 2 / w 2 * k4Drop y 2 ^ 2) = c 2 * k4Drop y 2 ^ 2 := by
    have hne := (hw 2).ne'; field_simp
  have hb3 : w 3 * (c 3 / w 3 * k4Drop y 3 ^ 2) = c 3 * k4Drop y 3 ^ 2 := by
    have hne := (hw 3).ne'; field_simp
  have hb4 : w 4 * (c 4 / w 4 * k4Drop y 4 ^ 2) = c 4 * k4Drop y 4 ^ 2 := by
    have hne := (hw 4).ne'; field_simp
  have hb5 : w 5 * (c 5 / w 5 * k4Drop y 5 ^ 2) = c 5 * k4Drop y 5 ^ 2 := by
    have hne := (hw 5).ne'; field_simp
  have hw6 : w 0 + w 1 + w 2 + w 3 + w 4 + w 5 = 1 := by
    simpa [Fin.sum_univ_six] using hsum
  -- the exchange chain: trees 012/123, 012/023, 015/025, 012/014, 012/015
  have e3 : c 3 / w 3 * k4Drop y 3 ^ 2 = c 0 / w 0 * k4Drop y 0 ^ 2 := by
    linarith
  have e1 : c 1 / w 1 * k4Drop y 1 ^ 2 = c 0 / w 0 * k4Drop y 0 ^ 2 := by
    linarith
  have e2 : c 2 / w 2 * k4Drop y 2 ^ 2 = c 0 / w 0 * k4Drop y 0 ^ 2 := by
    linarith
  have e4 : c 4 / w 4 * k4Drop y 4 ^ 2 = c 0 / w 0 * k4Drop y 0 ^ 2 := by
    linarith
  have e5 : c 5 / w 5 * k4Drop y 5 ^ 2 = c 0 / w 0 * k4Drop y 0 ^ 2 := by
    linarith
  -- the weighted total collapses onto the common value
  have hkap : c 0 * k4Drop y 0 ^ 2 + c 1 * k4Drop y 1 ^ 2 + c 2 * k4Drop y 2 ^ 2
      + c 3 * k4Drop y 3 ^ 2 + c 4 * k4Drop y 4 ^ 2 + c 5 * k4Drop y 5 ^ 2
      = (w 0 + w 1 + w 2 + w 3 + w 4 + w 5) * (c 0 / w 0 * k4Drop y 0 ^ 2) := by
    rw [← hb0, ← hb1, ← hb2, ← hb3, ← hb4, ← hb5, e1, e2, e3, e4, e5]
    ring
  rw [hw6, one_mul] at hkap
  have hq0 : c 0 / w 0 * k4Drop y 0 ^ 2 = 0 := by linarith
  have hdropZero : ∀ e : Fin 6, c e / w e * k4Drop y e ^ 2 = 0 →
      k4Drop y e = 0 := by
    intro e he
    have hpos : 0 < c e / w e := div_pos (hc e) (hw e)
    have hsq : k4Drop y e ^ 2 = 0 := by
      by_contra hne
      have hlt : 0 < k4Drop y e ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have := mul_pos hpos hlt
      linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  have hy0 : y 0 = 0 := by
    rw [← k4Drop_zero y]; exact hdropZero 0 hq0
  have hy1 : y 1 = 0 := by
    rw [← k4Drop_one y]; exact hdropZero 1 (by linarith)
  have hy2 : y 2 = 0 := by
    rw [← k4Drop_two y]; exact hdropZero 2 (by linarith)
  funext i
  fin_cases i
  · exact hy0
  · exact hy1
  · exact hy2

/-- The directive form: a nonzero probe cannot be a common kernel direction
of all sixteen tree gap forms.  With the shipped diamond calibration --
where all eight diamond trees ARE simultaneously tight, on pairwise
DISTINCT kernels -- this is the structural signature separating
simultaneous tightness from a common kernel. -/
theorem k4_no_common_kernel_all_trees_tight (c w : Fin 6 → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 < w e) (hsum : ∑ e, w e = 1)
    (y : Fin 3 → ℝ) (hy : y ≠ 0) :
    ¬ ∀ T ∈ k4TreeTriples, k4TreeGapForm c w y T = 0 := fun htight =>
  hy (k4_all_trees_tight_forces_zero c w hc hw hsum y htight)

/-! ## Brick 3: averaged positivity -/

/-- **The averaging identity.**  Summing the sixteen tree gap forms counts
each edge eight times on the tree side and sixteen times on the total side:
the sum is `8 * sum_e c_e (1/w_e - 2) drop_e^2` exactly. -/
theorem k4_averaged_gapForm_identity (c w : Fin 6 → ℝ) (y : Fin 3 → ℝ) :
    (k4TreeTriples.map (k4TreeGapForm c w y)).sum
      = 8 * ∑ e, c e * (1 / w e - 2) * k4Drop y e ^ 2 := by
  simp only [k4TreeTriples, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, k4TreeGapForm, Fin.sum_univ_six]
  ring

/-- **Averaged positivity.**  When no edge carries more than half the design
weight, the sum of the sixteen tree gap forms is nonnegative at every
probe. -/
theorem k4_averaged_positivity (c w : Fin 6 → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hw : ∀ e, 0 < w e) (hhalf : ∀ e, w e ≤ 1 / 2) (y : Fin 3 → ℝ) :
    0 ≤ (k4TreeTriples.map (k4TreeGapForm c w y)).sum := by
  rw [k4_averaged_gapForm_identity]
  have h8 : (0 : ℝ) ≤ 8 := by norm_num
  refine mul_nonneg h8 (Finset.sum_nonneg fun e _ => ?_)
  have hinv : (2 : ℝ) ≤ 1 / w e := by
    rw [le_div_iff₀ (hw e)]
    linarith [hhalf e]
  exact mul_nonneg (mul_nonneg (hc e) (by linarith)) (sq_nonneg _)

/-- At every probe of a half-bounded weighting, SOME spanning tree of K4 has
nonnegative gap form -- the per-direction escape hatch of findings
section 6, pinning any candidate K4 tie to the `max w_e > 1/2` regime. -/
theorem k4_exists_tree_gapForm_nonneg (c w : Fin 6 → ℝ) (hc : ∀ e, 0 ≤ c e)
    (hw : ∀ e, 0 < w e) (hhalf : ∀ e, w e ≤ 1 / 2) (y : Fin 3 → ℝ) :
    ∃ T ∈ k4TreeTriples, 0 ≤ k4TreeGapForm c w y T := by
  by_contra hcon
  push Not at hcon
  have n01 := hcon (0, 1, 2) (by decide)
  have n02 := hcon (0, 1, 4) (by decide)
  have n03 := hcon (0, 1, 5) (by decide)
  have n04 := hcon (0, 2, 3) (by decide)
  have n05 := hcon (0, 2, 5) (by decide)
  have n06 := hcon (0, 3, 4) (by decide)
  have n07 := hcon (0, 3, 5) (by decide)
  have n08 := hcon (0, 4, 5) (by decide)
  have n09 := hcon (1, 2, 3) (by decide)
  have n10 := hcon (1, 2, 4) (by decide)
  have n11 := hcon (1, 3, 4) (by decide)
  have n12 := hcon (1, 3, 5) (by decide)
  have n13 := hcon (1, 4, 5) (by decide)
  have n14 := hcon (2, 3, 4) (by decide)
  have n15 := hcon (2, 3, 5) (by decide)
  have n16 := hcon (2, 4, 5) (by decide)
  have hpos := k4_averaged_positivity c w hc hw hhalf y
  simp only [k4TreeTriples, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hpos
  linarith

/-! ## Brick 1: the stratum-A apex-star gap -/

/-- The apex-star gap matrix on the stratum `w = (a,a,a,b,b,b)` in the gauge
coordinates: unit-conductance star energy at the grounded apex minus the
weighted total energy. -/
def k4StratumGapEntry (a b : ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1 - a - 2 * b
  | 0, 1 => b
  | 0, 2 => b
  | 1, 0 => b
  | 1, 1 => 1 - a - 2 * b
  | 1, 2 => b
  | 2, 0 => b
  | 2, 1 => b
  | 2, 2 => 1 - a - 2 * b

def k4StratumGapMatrix (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (k4StratumGapEntry a b)

theorem k4StratumGap_zero_zero (a b : ℝ) :
    k4StratumGapMatrix a b 0 0 = 1 - a - 2 * b := rfl
theorem k4StratumGap_zero_one (a b : ℝ) : k4StratumGapMatrix a b 0 1 = b := rfl
theorem k4StratumGap_zero_two (a b : ℝ) : k4StratumGapMatrix a b 0 2 = b := rfl
theorem k4StratumGap_one_zero (a b : ℝ) : k4StratumGapMatrix a b 1 0 = b := rfl
theorem k4StratumGap_one_one (a b : ℝ) :
    k4StratumGapMatrix a b 1 1 = 1 - a - 2 * b := rfl
theorem k4StratumGap_one_two (a b : ℝ) : k4StratumGapMatrix a b 1 2 = b := rfl
theorem k4StratumGap_two_zero (a b : ℝ) : k4StratumGapMatrix a b 2 0 = b := rfl
theorem k4StratumGap_two_one (a b : ℝ) : k4StratumGapMatrix a b 2 1 = b := rfl
theorem k4StratumGap_two_two (a b : ℝ) :
    k4StratumGapMatrix a b 2 2 = 1 - a - 2 * b := rfl

/-- The stratum weights as a K4 edge vector: `a` on the three apex-star
edges, `b` on the opposite triangle. -/
def k4StratumWeights (a b : ℝ) : Fin 6 → ℝ
  | 0 => a
  | 1 => a
  | 2 => a
  | 3 => b
  | 4 => b
  | 5 => b

theorem k4StratumWeights_zero (a b : ℝ) : k4StratumWeights a b 0 = a := rfl
theorem k4StratumWeights_one (a b : ℝ) : k4StratumWeights a b 1 = a := rfl
theorem k4StratumWeights_two (a b : ℝ) : k4StratumWeights a b 2 = a := rfl
theorem k4StratumWeights_three (a b : ℝ) : k4StratumWeights a b 3 = b := rfl
theorem k4StratumWeights_four (a b : ℝ) : k4StratumWeights a b 4 = b := rfl
theorem k4StratumWeights_five (a b : ℝ) : k4StratumWeights a b 5 = b := rfl

/-- The apex-star tree gap form of the diagonal graphic family at the
stratum weights IS the quadratic form of the stratum gap matrix: the
convention of findings section 0 lands exactly on `k4StratumGapMatrix`. -/
theorem k4TreeGapForm_apexStar_stratum (a b : ℝ) (ha : a ≠ 0)
    (y : Fin 3 → ℝ) :
    k4TreeGapForm (k4StratumWeights a b) (k4StratumWeights a b) y (0, 1, 2)
      = y ⬝ᵥ (k4StratumGapMatrix a b).mulVec y := by
  simp only [k4TreeGapForm, Fin.sum_univ_six, Fin.sum_univ_three,
    k4Drop_zero, k4Drop_one, k4Drop_two, k4Drop_three, k4Drop_four,
    k4Drop_five, k4StratumWeights_zero, k4StratumWeights_one,
    k4StratumWeights_two, k4StratumWeights_three, k4StratumWeights_four,
    k4StratumWeights_five, Matrix.mulVec, dotProduct,
    k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
    k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
    k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two]
  field_simp
  ring

/-- The characteristic determinant of the stratum gap matrix factors,
constraint-free: `(1-a-3b-lam)^2 (1-a-lam)`. -/
theorem k4StratumGapMatrix_det_sub_smul (a b lam : ℝ) :
    (k4StratumGapMatrix a b - lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = (1 - a - 3 * b - lam) ^ 2 * (1 - a - lam) := by
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide),
    Matrix.one_apply_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide),
    k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
    k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
    k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two]
  ring

/-- On the weight simplex `3a + 3b = 1` the gauge spectrum of the apex-star
gap is `{2a, 2a, 1-a}`: the sharp-law eigenvalue `2a` of findings section 3
carries a double eigenvalue, and the third gauge eigenvalue is `1 - a`.
(The findings' third value `4 - 4a` is the same quadratic form read in the
`1`-orthogonal picture of `R^4`, congruent -- not similar -- to this
matrix; both spectra are verified in the sympy script.) -/
theorem k4StratumGapMatrix_det_sub_smul_stratum (a b lam : ℝ)
    (hsum : 3 * a + 3 * b = 1) :
    (k4StratumGapMatrix a b - lam • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = (2 * a - lam) ^ 2 * (1 - a - lam) := by
  rw [k4StratumGapMatrix_det_sub_smul]
  have h : (1 : ℝ) - a - 3 * b = 2 * a := by linarith
  rw [h]

/-- The characteristic polynomial itself factors the same way. -/
theorem k4StratumGapMatrix_charpoly (a b : ℝ) :
    (k4StratumGapMatrix a b).charpoly
      = (Polynomial.X - Polynomial.C (1 - a - 3 * b)) ^ 2
        * (Polynomial.X - Polynomial.C (1 - a)) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply_eq,
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (0 : Fin 3) ≠ 1),
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (0 : Fin 3) ≠ 2),
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0),
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (1 : Fin 3) ≠ 2),
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0),
    Matrix.charmatrix_apply_ne _ _ _ (by decide : (2 : Fin 3) ≠ 1),
    k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
    k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
    k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two,
    map_sub, map_mul, map_one, map_ofNat]
  ring

/-- **Stratum-A charpoly, the findings' mechanizable identity.**  On the
simplex the characteristic polynomial is `(X - 2a)^2 (X - (1-a))`. -/
theorem k4StratumGapMatrix_charpoly_stratum (a b : ℝ)
    (hsum : 3 * a + 3 * b = 1) :
    (k4StratumGapMatrix a b).charpoly
      = (Polynomial.X - Polynomial.C (2 * a)) ^ 2
        * (Polynomial.X - Polynomial.C (1 - a)) := by
  rw [k4StratumGapMatrix_charpoly]
  have h : (1 : ℝ) - a - 3 * b = 2 * a := by linarith
  rw [h]

/-- The sum-zero plane is the double eigenspace, constraint-free at
eigenvalue `1 - a - 3b` (which reads `2a` on the simplex). -/
theorem k4StratumGapMatrix_mulVec_of_sum_eq_zero (a b : ℝ) (y : Fin 3 → ℝ)
    (hy : y 0 + y 1 + y 2 = 0) :
    (k4StratumGapMatrix a b).mulVec y = (1 - a - 3 * b) • y := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
      k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
      k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two] <;>
    linear_combination b * hy

/-- The constant vector is the third eigenvector, at eigenvalue `1 - a`,
constraint-free. -/
theorem k4StratumGapMatrix_mulVec_const (a b t : ℝ) :
    (k4StratumGapMatrix a b).mulVec (fun _ => t) = fun _ => (1 - a) * t := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
      k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
      k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two] <;>
    ring

/-- The gauge matrix of the ambient restricted norm: `|x|^2` of the
`1`-orthogonal projection of the grounded potential, i.e.
`y0^2+y1^2+y2^2 - (y0+y1+y2)^2/4` as a quadratic form. -/
noncomputable def k4RestrictedNormForm (y : Fin 3 → ℝ) : ℝ :=
  y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - (y 0 + y 1 + y 2) ^ 2 / 4

/-- **The exact pencil law behind `phi(w) >= 2 min_e w_e` on stratum A.**
On the simplex the apex-star gap form exceeds `2a` times the restricted
norm by the rank-one square `(b + a/2)(y0+y1+y2)^2` -- exactly. -/
theorem k4StratumGapForm_pencil (a b : ℝ) (hsum : 3 * a + 3 * b = 1)
    (y : Fin 3 → ℝ) :
    y ⬝ᵥ (k4StratumGapMatrix a b).mulVec y - 2 * a * k4RestrictedNormForm y
      = (b + a / 2) * (y 0 + y 1 + y 2) ^ 2 := by
  simp only [k4RestrictedNormForm, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three,
    k4StratumGap_zero_zero, k4StratumGap_zero_one, k4StratumGap_zero_two,
    k4StratumGap_one_zero, k4StratumGap_one_one, k4StratumGap_one_two,
    k4StratumGap_two_zero, k4StratumGap_two_one, k4StratumGap_two_two]
  linear_combination (-(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)) * hsum

/-- The apex star always clears the level `2a` on stratum A: the sharp-law
lower bound of findings section 3, in exact form and with no condition
beyond nonnegative weights. -/
theorem k4StratumGapForm_ge_twoMin (a b : ℝ) (hb : 0 ≤ b)
    (hsum : 3 * a + 3 * b = 1) (y : Fin 3 → ℝ) :
    2 * a * k4RestrictedNormForm y ≤ y ⬝ᵥ (k4StratumGapMatrix a b).mulVec y := by
  have hp := k4StratumGapForm_pencil a b hsum y
  have hnn : 0 ≤ (b + a / 2) * (y 0 + y 1 + y 2) ^ 2 :=
    mul_nonneg (by linarith [hb, hsum]) (sq_nonneg _)
  linarith

/-- Equality holds on the whole sum-zero plane: the level `2a` is EXACT
there, so on the stratum with `a = min_e w_e` the sharp law
`phi >= 2 min_e w_e` is attained by the apex star.  The plane is
two-dimensional, so sharpness is not a single accidental direction. -/
theorem k4StratumGapForm_eq_twoMin_of_sum_eq_zero (a b : ℝ)
    (hsum : 3 * a + 3 * b = 1) (y : Fin 3 → ℝ) (hy : y 0 + y 1 + y 2 = 0) :
    y ⬝ᵥ (k4StratumGapMatrix a b).mulVec y = 2 * a * k4RestrictedNormForm y := by
  have hp := k4StratumGapForm_pencil a b hsum y
  rw [hy] at hp
  norm_num at hp
  linarith

end Gtz
