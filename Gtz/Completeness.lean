/-
# Theorem C: the equality manifold is exactly the family splits

The completeness half of the chord layer, assembled from four kernel pieces.
At a pairwise-tight cluster triangle: every atom silent against the three
clusters either IS a cluster square or has strictly positive defect. Light
atoms (`ℓ ≤ 1`, dust included) are positive because the conic curve stays
positive inside the moment disk; heavy atoms off the cluster directions are
positive because Theorem S hands them a strictly violated chord; heavy atoms
ON a cluster direction are squeezed to the cluster's own level by silence
against another cluster. The pairing `Σ t·d = 0` then annihilates the
non-cluster population: **there are no mid-leverage extras, no gray atoms, and
no dust**. The equality manifold is family splits, full stop — the statement
whose informal version refuted Theorem E's dust clause.
-/
import Mathlib
import Gtz.Pushoff
import Gtz.ChordTheorem
import Gtz.BallPerturbation

namespace Gtz

variable {m : ℕ}

/-! ### The defect through the conic -/

/-- The defect of a scaled direction: `d = 1 − ℓ·(1/2 − ⟨ξ,û⟩)`. -/
theorem planarDefect_scaled (moment unitDir : Fin 2 → ℝ) {lev : ℝ}
    (hlevPos : 0 < lev) (hunit : unitDir ⬝ᵥ unitDir = 1) :
    planarDefect moment (lev • unitDir)
      = 1 - lev * (1 / 2 - moment ⬝ᵥ unitDir) := by
  rw [planarDefect, dotProduct_smul, smul_eq_mul]
  have hnorm : planarNorm (lev • unitDir) = lev := by
    rw [planarNorm]
    have hdot : (lev • unitDir) ⬝ᵥ (lev • unitDir) = lev ^ 2 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hunit]
      ring
    rw [hdot, Real.sqrt_sq hlevPos.le]
  rw [hnorm]
  ring

/-- Inside the moment disk the conic curve is positive at every unit
direction: `1/2 + ⟨ξ,û⟩ ≥ 1/2 − |ξ| > 0`. -/
theorem conic_curve_pos {moment unitDir : Fin 2 → ℝ}
    (hshort : moment ⬝ᵥ moment < 1 / 4) (hunit : unitDir ⬝ᵥ unitDir = 1) :
    0 < 1 / 2 + moment ⬝ᵥ unitDir := by
  have hcs := abs_dotProduct_le moment unitDir
  rw [hunit, Real.sqrt_one, mul_one] at hcs
  have hsqrtLt : Real.sqrt (moment ⬝ᵥ moment) < 1 / 2 := by
    have hquarter : Real.sqrt (moment ⬝ᵥ moment) < Real.sqrt (1 / 4) := by
      refine Real.sqrt_lt_sqrt ?_ hshort
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rwa [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] at hquarter
  have habs := abs_lt.mp (lt_of_le_of_lt hcs hsqrtLt)
  linarith [habs.1]

/-! ### Theorem C -/

/-- **Theorem C, the completeness of the equality manifold**: in a design
carrying a pairwise-tight nondegenerate cluster triangle, with every atom
silent against the three clusters in conic form, every atom's square IS one
of the three cluster squares. No mid-leverage extras, no gray atoms, no dust. -/
theorem equality_manifold_complete
    (weight lev : Fin m → ℝ) (unitDir : Fin m → Fin 2 → ℝ)
    (moment vertexA vertexB vertexC : Fin 2 → ℝ)
    {conicA conicB conicC levA levB levC : ℝ}
    -- the design
    (hweightPos : ∀ c, 0 < weight c) (hlevPos : ∀ c, 0 < lev c)
    (hunit : ∀ c, unitDir c ⬝ᵥ unitDir c = 1)
    (hweightSum : ∑ c, weight c = 1)
    (hclosure : ∑ c, weight c • (lev c • unitDir c) = 0)
    (htrace : ∑ c, weight c * planarNorm (lev c • unitDir c) = 2)
    -- the cluster triangle
    (hunitA : vertexA ⬝ᵥ vertexA = 1) (hunitB : vertexB ⬝ᵥ vertexB = 1)
    (hunitC : vertexC ⬝ᵥ vertexC = 1)
    (hgapAB : vertexA ⬝ᵥ vertexB < 1) (hgapAC : vertexA ⬝ᵥ vertexC < 1)
    (hgapBC : vertexB ⬝ᵥ vertexC < 1)
    (hindep : planarDet (vertexA - vertexC) (vertexB - vertexC) ≠ 0)
    (hconicAtA : conicA = 1 / 2 + moment ⬝ᵥ vertexA)
    (hconicAtB : conicB = 1 / 2 + moment ⬝ᵥ vertexB)
    (hconicAtC : conicC = 1 / 2 + moment ⬝ᵥ vertexC)
    (hopenA : conicA ^ 2 < 1) (hopenB : conicB ^ 2 < 1)
    (hopenC : conicC ^ 2 < 1)
    (hposA : 0 < conicA) (hposB : 0 < conicB) (hposC : 0 < conicC)
    (hlevClusterA : levA * (1 - conicA) = 1)
    (hlevClusterB : levB * (1 - conicB) = 1)
    (hlevClusterC : levC * (1 - conicC) = 1)
    (htightAB : (1 + vertexA ⬝ᵥ vertexB) / 2 = conicA * conicB)
    (htightAC : (1 + vertexA ⬝ᵥ vertexC) / 2 = conicA * conicC)
    (htightBC : (1 + vertexB ⬝ᵥ vertexC) / 2 = conicB * conicC)
    -- the moment bound and the silence of every atom against the clusters
    (hshort : moment ⬝ᵥ moment < 1 / 4)
    (hsilentA : ∀ c, (1 - 1 / lev c) * conicA
      ≤ (1 + unitDir c ⬝ᵥ vertexA) / 2)
    (hsilentB : ∀ c, (1 - 1 / lev c) * conicB
      ≤ (1 + unitDir c ⬝ᵥ vertexB) / 2)
    (hsilentC : ∀ c, (1 - 1 / lev c) * conicC
      ≤ (1 + unitDir c ⬝ᵥ vertexC) / 2) :
    ∀ c, lev c • unitDir c = levA • vertexA
      ∨ lev c • unitDir c = levB • vertexB
      ∨ lev c • unitDir c = levC • vertexC := by
  -- every atom's defect is nonnegative, positive unless a cluster square
  have hdefect : ∀ c, 0 ≤ planarDefect moment (lev c • unitDir c)
      ∧ (planarDefect moment (lev c • unitDir c) = 0
        → lev c • unitDir c = levA • vertexA
          ∨ lev c • unitDir c = levB • vertexB
          ∨ lev c • unitDir c = levC • vertexC) := by
    intro c
    have hcurvePos : 0 < 1 / 2 + moment ⬝ᵥ unitDir c :=
      conic_curve_pos hshort (hunit c)
    rw [planarDefect_scaled moment (unitDir c) (hlevPos c) (hunit c)]
    rcases le_or_gt (lev c) 1 with hlight | hheavy
    · -- light atoms: `d = 1 − ℓ(1 − ν_curve) > 0` outright
      constructor
      · linarith [mul_pos (hlevPos c) hcurvePos, hlight]
      · intro hzero
        exfalso
        linarith [mul_pos (hlevPos c) hcurvePos, hlight, hzero]
    · -- heavy atoms: the chord envelope decides
      rcases eq_or_ne (unitDir c) vertexA with hdirA | hne
      · -- on vertex A: silence against B squeezes the level to the cluster's
        have hsqueeze : 1 - 1 / lev c ≤ conicA := by
          have hs := hsilentB c
          rw [hdirA, htightAB] at hs
          have hscaled : conicB * (1 - 1 / lev c) ≤ conicB * conicA := by
            linarith
          exact le_of_mul_le_mul_left hscaled hposB
        have hcompl : 1 / 2 - moment ⬝ᵥ vertexA = 1 - conicA := by
          rw [hconicAtA]; ring
        have hinv : 1 / lev c * lev c = 1 :=
          one_div_mul_cancel (hlevPos c).ne'
        constructor
        · rw [hdirA, hcompl]
          linarith [mul_le_mul_of_nonneg_right hsqueeze (hlevPos c).le, hinv]
        · intro hzero
          refine Or.inl ?_
          rw [hdirA] at hzero ⊢
          rw [hcompl] at hzero
          have hgap : (0 : ℝ) < 1 - conicA := by
            linarith [hopenA, sq_nonneg (conicA - 1)]
          have hexpand : lev c * (1 - conicA) = 1 := by linarith
          have hlevEq : lev c = levA :=
            mul_right_cancel₀ hgap.ne' (by rw [hexpand, hlevClusterA])
          rw [hlevEq]
      rcases eq_or_ne (unitDir c) vertexB with hdirB | hneB
      · have hsqueeze : 1 - 1 / lev c ≤ conicB := by
          have hs := hsilentA c
          rw [hdirB, dotProduct_comm, htightAB] at hs
          have hscaled : conicA * (1 - 1 / lev c) ≤ conicA * conicB := by
            linarith
          exact le_of_mul_le_mul_left hscaled hposA
        have hcompl : 1 / 2 - moment ⬝ᵥ vertexB = 1 - conicB := by
          rw [hconicAtB]; ring
        have hinv : 1 / lev c * lev c = 1 :=
          one_div_mul_cancel (hlevPos c).ne'
        constructor
        · rw [hdirB, hcompl]
          linarith [mul_le_mul_of_nonneg_right hsqueeze (hlevPos c).le, hinv]
        · intro hzero
          refine Or.inr (Or.inl ?_)
          rw [hdirB] at hzero ⊢
          rw [hcompl] at hzero
          have hgap : (0 : ℝ) < 1 - conicB := by
            linarith [hopenB, sq_nonneg (conicB - 1)]
          have hexpand : lev c * (1 - conicB) = 1 := by linarith
          have hlevEq : lev c = levB :=
            mul_right_cancel₀ hgap.ne' (by rw [hexpand, hlevClusterB])
          rw [hlevEq]
      rcases eq_or_ne (unitDir c) vertexC with hdirC | hneC
      · have hsqueeze : 1 - 1 / lev c ≤ conicC := by
          have hs := hsilentA c
          rw [hdirC, dotProduct_comm, htightAC] at hs
          have hscaled : conicA * (1 - 1 / lev c) ≤ conicA * conicC := by
            linarith
          exact le_of_mul_le_mul_left hscaled hposA
        have hcompl : 1 / 2 - moment ⬝ᵥ vertexC = 1 - conicC := by
          rw [hconicAtC]; ring
        have hinv : 1 / lev c * lev c = 1 :=
          one_div_mul_cancel (hlevPos c).ne'
        constructor
        · rw [hdirC, hcompl]
          linarith [mul_le_mul_of_nonneg_right hsqueeze (hlevPos c).le, hinv]
        · intro hzero
          refine Or.inr (Or.inr ?_)
          rw [hdirC] at hzero ⊢
          rw [hcompl] at hzero
          have hgap : (0 : ℝ) < 1 - conicC := by
            linarith [hopenC, sq_nonneg (conicC - 1)]
          have hexpand : lev c * (1 - conicC) = 1 := by linarith
          have hlevEq : lev c = levC :=
            mul_right_cancel₀ hgap.ne' (by rw [hexpand, hlevClusterC])
          rw [hlevEq]
      · -- off every vertex: Theorem S hands a strictly violated chord
        have henvelope := chord_silence_envelope hunitA hunitB hunitC
          (hunit c) hgapAB hgapAC hgapBC hindep hconicAtA hconicAtB
          hconicAtC hopenA hopenB hopenC htightAB htightAC htightBC
          (probe := unitDir c)
        have hviolated : ¬ (0 ≤ chordFn vertexA moment conicA (unitDir c)
            ∧ 0 ≤ chordFn vertexB moment conicB (unitDir c)
            ∧ 0 ≤ chordFn vertexC moment conicC (unitDir c)) := by
          intro ⟨hA, hB, hC⟩
          rcases henvelope hA hB hC with h | h | h
          · exact hne h
          · exact hneB h
          · exact hneC h
        -- some chord is strictly negative: the curve strictly exceeds ν_c
        have hcurveGt : 1 - 1 / lev c < 1 / 2 + moment ⬝ᵥ unitDir c := by
          by_contra hcontra
          push_neg at hcontra
          refine hviolated ⟨?_, ?_, ?_⟩
          · rw [chordFn, dotProduct_comm vertexA (unitDir c)]
            linarith [mul_le_mul_of_nonneg_left hcontra hposA.le, hsilentA c]
          · rw [chordFn, dotProduct_comm vertexB (unitDir c)]
            linarith [mul_le_mul_of_nonneg_left hcontra hposB.le, hsilentB c]
          · rw [chordFn, dotProduct_comm vertexC (unitDir c)]
            linarith [mul_le_mul_of_nonneg_left hcontra hposC.le, hsilentC c]
        have hinv : 1 / lev c * lev c = 1 :=
          one_div_mul_cancel (hlevPos c).ne'
        have hmul := mul_lt_mul_of_pos_right hcurveGt (hlevPos c)
        constructor
        · linarith [hmul, hinv]
        · intro hzero
          exfalso
          linarith [hmul, hinv, hzero]
  -- the pairing annihilates positive defects
  have hpairing := sum_weighted_defect_eq_zero Finset.univ weight
    (fun c => lev c • unitDir c) moment hweightSum hclosure htrace
  have hallZero : ∀ c, planarDefect moment (lev c • unitDir c) = 0 := by
    have hnonneg : ∀ c ∈ Finset.univ,
        0 ≤ weight c * planarDefect moment (lev c • unitDir c) := fun c _ =>
      mul_nonneg (hweightPos c).le (hdefect c).1
    intro c
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hpairing c
      (Finset.mem_univ c)
    rcases mul_eq_zero.mp hterm with hw | hd
    · exact absurd hw (ne_of_gt (hweightPos c))
    · exact hd
  exact fun c => (hdefect c).2 (hallZero c)

end Gtz
