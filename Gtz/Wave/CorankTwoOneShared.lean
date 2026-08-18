/-
# The one-shared triples of a rank-one gap: the split criterion and the engines

At a corank-two `(6,3)` tie the dominator's gap is `lam • gapDir gapDirᵀ` with
`lam > 0`.  The twenty triples split `1 + 9 + 1 + 9`: the dominator, the nine
swaps (informationless there, `Gtz.not_posDef_swap_of_rankOneGap`), the
complement (priced by `Gtz.rankOneGap_threshold_of_isTie`), and the nine
triples that share ONE atom with the dominator.  All remaining information
about a corank-two tie lives in those nine, and this module builds the
instrument that reads them.

## The split criterion

For ANY subset `T`, any design, any rank, and any unit direction `u`, the gap
`S_T − 1` splits along `u` and its orthogonal hyperplane.  Positive
definiteness is exactly

  `1 < B_T`  and  `∀ w ⊥ u, w ≠ 0:  cross_T(w)² < (B_T − 1)·(G_T(w))`

with `B_T = Σ_{c∈T} (g_c·u)²` the `u`-mass, `cross_T(w) = Σ (g_c·u)(g_c·w)`
the mixed reading, and `G_T(w) = Σ (g_c·w)² − |w|²` the in-plane gap form.
This is the block Schur complement of the `u`-corner, stated basis-free as a
quadratic condition — no coordinates on the plane are ever chosen.

## The engines

* the free-refusal engine: a plane witness `w` with
  `(B_T − 1)·G_T(w) ≤ cross_T(w)²` refuses the triple with no further data —
  in particular any `w` with `G_T(w) ≤ 0` when `B_T > 1`, and any triple with
  `B_T ≤ 1` outright;
* the strict engine: `u`-mass above one plus the full plane cover make the
  triple strictly dominating, so no design carrying such a triple is a tie.

## The five-set reading

A one-shared triple is the five-set `C ∪ {d₁, d₂}` with two inside atoms
removed, so when the five-set gap is PD its refusal is priced by the
depth-two downdate (`Gtz.not_posDef_sub_two_vecMulVec_iff`): the removed
pair's Gram in the five-set anchor metric must reach the unit box.  The same
instrument prices the triples beyond the four-set at corank one — the global
refusals the adjacency lane's conic theorem needs.

## Scope

The one-shared reading needs TWO atoms outside the dominator and the
complement threshold needs the complement to be a triple, so none of this can
even be stated at `(5,3)`.  There is no diamond hazard, by construction.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.RayleighCertificate
import Gtz.Quantitative.DesignQuadraticFloors
import Gtz.Reduction.RealVolumeFloor
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.DepthTwoDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The affine sum expansion -/

/-- Squares of affine readings expand into the three layer sums. -/
theorem sum_sq_affine (T : Finset (Fin m)) (a b : Fin m → ℝ) (α : ℝ) :
    ∑ c ∈ T, (α * a c + b c) ^ 2
      = α ^ 2 * ∑ c ∈ T, (a c) ^ 2 + 2 * α * ∑ c ∈ T, a c * b c
        + ∑ c ∈ T, (b c) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The gap form along the `u`-split.**  For `y = α·u + w` with `w ⊥ u` the
gap form of any subset is a quadratic in `α` whose three coefficients are the
`u`-mass gap, the mixed reading, and the in-plane gap form. -/
theorem gapForm_uSplit (D : WeightedDesign m k) (T : Finset (Fin m))
    {u w : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ u = 0) (α : ℝ) :
    (α • u + w) ⬝ᵥ ((subsetSum D T - 1) *ᵥ (α • u + w))
      = α ^ 2 * ((∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2) - 1)
        + 2 * α * (∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w))
        + ((∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w) := by
  have huw : u ⬝ᵥ w = 0 := by rwa [dotProduct_comm] at hw
  rw [dominationGap_form]
  have hdot : ∀ c : Fin m, D.atom c ⬝ᵥ (α • u + w)
      = α * (D.atom c ⬝ᵥ u) + D.atom c ⬝ᵥ w := by
    intro c
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hyy : (α • u + w) ⬝ᵥ (α • u + w) = α ^ 2 + w ⬝ᵥ w := by
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hunit, hw, huw]
    ring
  simp only [hdot]
  rw [sum_sq_affine, hyy]
  ring

/-! ## 2. The split criterion -/

/-- **The split criterion.**  The gap of a subset is positive definite exactly
when the `u`-mass exceeds one and the discriminant condition holds on the
whole orthogonal hyperplane.  Basis-free block Schur at the `u`-corner. -/
theorem posDef_gap_iff_uSplit (D : WeightedDesign m k) (T : Finset (Fin m))
    {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1) :
    (subsetSum D T - 1).PosDef
      ↔ 1 < ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2
        ∧ ∀ w : Fin k → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
            (∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)) ^ 2
              < ((∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2) - 1)
                * ((∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w) := by
  set B : ℝ := ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2 with hB
  constructor
  · intro hpd
    have hune : u ≠ 0 := by
      intro hzero
      rw [hzero] at hunit
      simp at hunit
    have hBpos : 1 < B := by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hune
      rw [star_trivial, dominationGap_form, hunit] at h
      rw [hB]
      linarith
    refine ⟨hBpos, fun w hw hwne => ?_⟩
    set cross : ℝ := ∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w) with hcross
    set G : ℝ := (∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w with hG
    set α : ℝ := -cross / (B - 1) with hα
    have hApos : (0 : ℝ) < B - 1 := by linarith
    have hyne : α • u + w ≠ 0 := by
      intro hzero
      have hα0 : α = 0 := by
        have hd := congrArg (fun v => v ⬝ᵥ u) hzero
        simpa [add_dotProduct, smul_dotProduct, smul_eq_mul, hunit, hw] using hd
      rw [hα0, zero_smul, zero_add] at hzero
      exact hwne hzero
    have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hyne
    rw [star_trivial, gapForm_uSplit D T hunit hw] at hform
    have hval : α ^ 2 * (B - 1) + 2 * α * cross + G
        = G - cross ^ 2 / (B - 1) := by
      rw [hα]
      field_simp
      ring
    rw [← hB, ← hcross, ← hG, hval] at hform
    have hmul := mul_pos hApos hform
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hApos)] at hmul
    linarith
  · rintro ⟨hBpos, hcover⟩
    have hApos : (0 : ℝ) < B - 1 := by linarith
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D T),
        fun y hyne => ?_⟩
    rw [star_trivial]
    set α : ℝ := y ⬝ᵥ u with hα
    set w : Fin k → ℝ := y - α • u with hwdef
    have hw : w ⬝ᵥ u = 0 := by
      rw [hwdef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, mul_one,
        hα, sub_self]
    have hy : y = α • u + w := by
      rw [hwdef]
      abel
    rw [hy, gapForm_uSplit D T hunit hw, ← hB]
    by_cases hwzero : w = 0
    · have hαne : α ≠ 0 := by
        intro hα0
        rw [hα0, zero_smul, zero_add] at hy
        rw [hy] at hyne
        exact hyne hwzero
      rw [hwzero]
      have h1 : ∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ (0 : Fin k → ℝ)) = 0 := by
        simp
      have h2 : ∑ c ∈ T, (D.atom c ⬝ᵥ (0 : Fin k → ℝ)) ^ 2 = 0 := by simp
      have h3 : (0 : Fin k → ℝ) ⬝ᵥ (0 : Fin k → ℝ) = 0 := by simp
      rw [h1, h2, h3]
      have hsq : 0 < α ^ 2 := by positivity
      nlinarith
    · have hcov := hcover w hw hwzero
      set cross : ℝ := ∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w) with hcross
      set G : ℝ := (∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w with hG
      nlinarith [sq_nonneg ((B - 1) * α + cross), hApos]

/-! ## 3. The engines -/

/-- **The `u`-mass refusal.**  A subset whose `u`-mass stays at or below one is
never strictly dominating. -/
theorem not_posDef_gap_of_uMass_le (D : WeightedDesign m k) (T : Finset (Fin m))
    {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hmass : ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2 ≤ 1) :
    ¬ (subsetSum D T - 1).PosDef := by
  intro hpd
  have h := (posDef_gap_iff_uSplit D T hunit).mp hpd
  linarith [h.1]

/-- **The plane-witness refusal.**  One orthogonal witness beating the
discriminant refuses the subset with no further data. -/
theorem not_posDef_gap_of_planeWitness (D : WeightedDesign m k)
    (T : Finset (Fin m)) {u w : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hw : w ⬝ᵥ u = 0) (hwne : w ≠ 0)
    (hbeat : ((∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2) - 1)
        * ((∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w)
      ≤ (∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)) ^ 2) :
    ¬ (subsetSum D T - 1).PosDef := by
  intro hpd
  have h := (posDef_gap_iff_uSplit D T hunit).mp hpd
  exact absurd hbeat (not_le.mpr (h.2 w hw hwne))

/-- **The strict engine.**  `u`-mass above one plus the plane cover force the
subset to dominate strictly, so a design carrying such a card-`k` subset is
not a tie. -/
theorem not_isTie_of_uSplit_cover (D : WeightedDesign m k) (T : Finset (Fin m))
    (hcard : T.card = k) {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hmass : 1 < ∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2)
    (hcover : ∀ w : Fin k → ℝ, w ⬝ᵥ u = 0 → w ≠ 0 →
        (∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)) ^ 2
          < ((∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2) - 1)
            * ((∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w)) :
    ¬ IsTie D := by
  intro htie
  exact htie.2 T hcard ((posDef_gap_iff_uSplit D T hunit).mpr ⟨hmass, hcover⟩)

/-- **The refusal dichotomy at a tie.**  Every card-`k` subset of a tie either
keeps its `u`-mass at one or concedes a plane witness. -/
theorem uMass_le_or_planeWitness_of_isTie (D : WeightedDesign m k)
    (htie : IsTie D) (T : Finset (Fin m)) (hcard : T.card = k)
    {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1) :
    (∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2 ≤ 1)
      ∨ ∃ w : Fin k → ℝ, w ⬝ᵥ u = 0 ∧ w ≠ 0
          ∧ ((∑ c ∈ T, (D.atom c ⬝ᵥ u) ^ 2) - 1)
              * ((∑ c ∈ T, (D.atom c ⬝ᵥ w) ^ 2) - w ⬝ᵥ w)
            ≤ (∑ c ∈ T, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w)) ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hmass, hwitness⟩ := hcon
  exact not_isTie_of_uSplit_cover D T hcard hunit hmass
    (fun w hw hwne => hwitness w hw hwne) htie

/-! ## 4. The rank-one-gap identities -/

/-- **The `u`-mass of the dominator.**  A rank-one gap pins the dominator's
`u`-mass at `1 + lam` exactly. -/
theorem uMass_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ u) ^ 2 = 1 + lam := by
  have hform : u ⬝ᵥ ((subsetSum D C - 1) *ᵥ u) = lam := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, hunit]
    ring
  rw [dominationGap_form, hunit] at hform
  linarith

/-- **The resolve identity at a rank-one gap.**  The dominator's atoms resolve
the gap direction with total mass `1 + lam`. -/
theorem resolve_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m))
    {lam : ℝ} {u : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ u) • D.atom c = (1 + lam) • u := by
  have hmul : (subsetSum D C - 1) *ᵥ u = lam • u := by
    rw [hgap, Matrix.smul_mulVec, atomMatrix, vecMulVec_mulVec_eq, hunit,
      one_smul]
  have hsub : subsetSum D C *ᵥ u = u + lam • u := by
    have h := congrArg (fun v => v + u) hmul
    simpa [Matrix.sub_mulVec, sub_add_cancel, add_comm] using h
  have hsum : subsetSum D C *ᵥ u = ∑ c ∈ C, (D.atom c ⬝ᵥ u) • D.atom c := by
    rw [subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun c _ => by
      rw [atomMatrix, vecMulVec_mulVec_eq]
  rw [hsum] at hsub
  rw [hsub]
  module

/-- **The mixed reading of the dominator vanishes on the plane.**  Against any
`w ⊥ u` the dominator's cross sum is zero: the rank-one gap has no mixed
block. -/
theorem cross_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m))
    {lam : ℝ} {u w : Fin k → ℝ} (hunit : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ u) * (D.atom c ⬝ᵥ w) = 0 := by
  have hresolve := resolve_of_rankOneGap D C hunit hgap
  have hdot := congrArg (fun v => v ⬝ᵥ w) hresolve
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at hdot
  rw [show u ⬝ᵥ w = 0 from by rwa [dotProduct_comm] at hw, mul_zero] at hdot
  exact hdot

/-- **The in-plane Parseval of the dominator.**  On the orthogonal hyperplane
the dominator's atoms read exactly the plane norm: the gap vanishes there. -/
theorem planeMass_of_rankOneGap (D : WeightedDesign m k) (C : Finset (Fin m))
    {lam : ℝ} {u w : Fin k → ℝ} (hw : w ⬝ᵥ u = 0)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ w) ^ 2 = w ⬝ᵥ w := by
  have hform : w ⬝ᵥ ((subsetSum D C - 1) *ᵥ w) = 0 := by
    rw [hgap, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      show u ⬝ᵥ w = 0 from by rwa [dotProduct_comm] at hw]
    ring
  rw [dominationGap_form] at hform
  linarith

/-! ## 5. The five-set reading -/

/-- Erasing two labels peels their atoms off the subset gap. -/
theorem gap_erase_two (D : WeightedDesign m k) (F : Finset (Fin m))
    {x y : Fin m} (hx : x ∈ F) (hy : y ∈ F) (hxy : x ≠ y) :
    subsetSum D ((F.erase x).erase y) - 1
      = (subsetSum D F - 1) - Matrix.vecMulVec (D.atom x) (D.atom x)
        - Matrix.vecMulVec (D.atom y) (D.atom y) := by
  have hyx : y ∈ F.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hstep1 : subsetSum D (F.erase x)
      = subsetSum D F - atomMatrix (D.atom x) := by
    rw [subsetSum, subsetSum, ← Finset.sum_erase_add F _ hx]
    abel
  have hstep2 : subsetSum D ((F.erase x).erase y)
      = subsetSum D (F.erase x) - atomMatrix (D.atom y) := by
    rw [subsetSum, subsetSum, ← Finset.sum_erase_add (F.erase x) _ hyx]
    abel
  rw [hstep2, hstep1, atomMatrix, atomMatrix]
  abel

/-- **The one-shared refusal in the five-set anchor metric.**  When the
five-set gap is PD, the triple obtained by removing two of its atoms is
refused exactly when the removed pair's Gram in the anchor metric reaches the
unit box — the depth-two downdate criterion, with all quantifiers gone. -/
theorem erased_two_not_posDef_iff_gram (D : WeightedDesign m k)
    (F : Finset (Fin m)) {x y : Fin m} (hx : x ∈ F) (hy : y ∈ F) (hxy : x ≠ y)
    (hF : (subsetSum D F - 1).PosDef) :
    ¬ (subsetSum D ((F.erase x).erase y) - 1).PosDef
      ↔ 1 ≤ D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x)
          ∨ (1 - D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom x))
              * (1 - D.atom y ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom y))
            ≤ (D.atom x ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom y)) ^ 2 := by
  rw [gap_erase_two D F hx hy hxy]
  exact not_posDef_sub_two_vecMulVec_iff (subsetSum D F - 1) hF
    (D.atom x) (D.atom y)

/-! ## 6. The planar corner forces a heavy inside atom -/

/-- **Planar outside forces a heavy inside atom.**  When every atom off `C`
reads zero against the unit direction `u`, the directional Parseval
`Σ_c t_c (g_c·u)² = 1` is carried entirely by `C`, whose total weight is
strictly below one.  Some atom of `C` must read above one.  This is the
structural driver of the planar-outside corner: the heavy atom's one-shared
triples are the ones the refusals must fight. -/
theorem exists_heavy_inside_of_planarOutside (D : WeightedDesign m k)
    (C : Finset (Fin m)) (hne : Cᶜ.Nonempty) {u : Fin k → ℝ}
    (hunit : u ⬝ᵥ u = 1) (houtside : ∀ d ∈ Cᶜ, D.atom d ⬝ᵥ u = 0) :
    ∃ e ∈ C, 1 < (D.atom e ⬝ᵥ u) ^ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  have htotal := dotProduct_self_eq_sum_weight_mul_sq D u
  rw [hunit] at htotal
  have hsplit : ∑ c, D.weight c * (D.atom c ⬝ᵥ u) ^ 2
      = ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ u) ^ 2
        + ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ u) ^ 2 :=
    (Finset.sum_add_sum_compl C _).symm
  have houtzero : ∑ c ∈ Cᶜ, D.weight c * (D.atom c ⬝ᵥ u) ^ 2 = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [houtside d hd]; ring
  have hinside_le : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ u) ^ 2
      ≤ ∑ c ∈ C, D.weight c := by
    refine Finset.sum_le_sum fun e he => ?_
    nlinarith [hcon e he, le_of_lt (D.weight_pos e), sq_nonneg (D.atom e ⬝ᵥ u)]
  have hweightC : ∑ c ∈ C, D.weight c < 1 := by
    have hall : ∑ c ∈ C, D.weight c + ∑ c ∈ Cᶜ, D.weight c = 1 := by
      rw [Finset.sum_add_sum_compl]
      exact D.weight_sum_one
    have hpos : 0 < ∑ c ∈ Cᶜ, D.weight c :=
      Finset.sum_pos (fun c _ => D.weight_pos c) hne
    linarith
  linarith [htotal, hsplit, houtzero, hinside_le, hweightC]

end Gtz
