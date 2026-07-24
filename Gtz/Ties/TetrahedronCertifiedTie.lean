/-
# The regular tetrahedron is a certified tie

The `(4,3)` regular-tetrahedron design is an exact tie (`tetraDesign_isTie`): subset
`{0,1,2}` dominates weakly — its gap is the sum of squares
`(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²` — and every 3-subset misses one vertex `d`, where the
gap form vanishes (`(v_c ⬝ᵥ v_d)² = 1` for `c ≠ d`, so `v_dᵀ S_C v_d = 3 = |v_d|²`):
no subset dominates strictly.

Unlike the asymmetric split-tetrahedron ties (`SplitTetrahedronTie`), this tie CARRIES
its stress certificate: the constant coefficients `1/48` on the four vertex directions
reproduce every weight, `∑_l (1/48)(v_c ⬝ᵥ v_l)² = (9 + 3·1)/48 = 1/4 = t_c`
(`tetraDesign_stressCertificate`, the multiplier `Λ = I/12`). Together with
`exists_isTie_and_noStressCertificate`, both sides of the alternative are inhabited at
genuine ties: certificates exist exactly when the weights are duplicate-consistent —
the certificate is an invariant of the merged design.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Reduction.RayleighCertificate
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StressCertificate
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

@[simp] theorem tetraDesign_atom : tetraDesign.atom = tetraAtom := rfl

@[simp] theorem tetraDesign_weight : tetraDesign.weight = fun _ => (1 : ℝ) / 4 := rfl

/-- Distinct tetrahedron vertices pair to `±1` — squared, to `1`. -/
theorem tetraAtom_dot_sq_of_ne {c d : Fin 4} (hne : c ≠ d) :
    (tetraAtom c ⬝ᵥ tetraAtom d) ^ 2 = 1 := by
  fin_cases c <;> fin_cases d <;>
    simp_all [tetraAtom, dotProduct, Fin.sum_univ_three]

/-- Three vertices never exhaust the four. -/
theorem exists_unusedVertex (vertOne vertTwo vertThree : Fin 4) :
    ∃ d : Fin 4, vertOne ≠ d ∧ vertTwo ≠ d ∧ vertThree ≠ d := by
  decide +revert

/-- The gap of any 3-subset vanishes at the vertex it misses: each of the three atoms
pairs to `(±1)² = 1` with the unused `v_d`, so `v_dᵀ S_C v_d = 3 = |v_d|²`. -/
theorem tetraDesign_gapForm_zero_of_unusedVertex {C : Finset (Fin 4)}
    (hcard : C.card = 3) {d : Fin 4} (hunused : ∀ c ∈ C, c ≠ d) :
    tetraAtom d ⬝ᵥ ((subsetSum tetraDesign C - 1) *ᵥ tetraAtom d) = 0 := by
  rw [dominationGap_form]
  have hone : ∀ c ∈ C, (tetraDesign.atom c ⬝ᵥ tetraAtom d) ^ 2 = 1 :=
    fun c hc => tetraAtom_dot_sq_of_ne (hunused c hc)
  rw [Finset.sum_congr rfl hone, Finset.sum_const, hcard, tetraAtom_dot_self,
    nsmul_eq_mul]
  norm_num

/-- **The subset `{0,1,2}` dominates weakly** — its gap is the sum of squares
`(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²`. -/
theorem tetraDesign_dominates : Dominates tetraDesign {0, 1, 2} := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 1, 2} : Finset (Fin 4)) fun c _ =>
      posSemidef_atomMatrix (tetraDesign.atom c)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, dominationGap_form,
      show ({0, 1, 2} : Finset (Fin 4)) = insert 0 (insert 1 {2}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [tetraDesign_atom, tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, dotProduct,
      Fin.sum_univ_three]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 2), sq_nonneg (x 1 + x 2)]

/-- **No 3-subset dominates strictly**: it misses some vertex, and the gap form
vanishes there. -/
theorem tetraDesign_no_strictDominator :
    ∀ C : Finset (Fin 4), C.card = 3 → ¬(subsetSum tetraDesign C - 1).PosDef := by
  intro C hcard hpd
  obtain ⟨vertOne, vertTwo, vertThree, hOneTwo, hOneThree, hTwoThree, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  obtain ⟨d, hdOne, hdTwo, hdThree⟩ := exists_unusedVertex vertOne vertTwo vertThree
  have hunused : ∀ c ∈ ({vertOne, vertTwo, vertThree} : Finset (Fin 4)), c ≠ d := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hdOne
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hdTwo
    · exact (Finset.mem_singleton.mp hc) ▸ hdThree
  have hzero := tetraDesign_gapForm_zero_of_unusedVertex hcard hunused
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 (tetraAtom_ne_zero d)
  rw [star_trivial, hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **The regular tetrahedron is an exact tie.** -/
theorem tetraDesign_isTie : IsTie tetraDesign :=
  ⟨⟨{0, 1, 2}, by decide, tetraDesign_dominates⟩, tetraDesign_no_strictDominator⟩

/-- **The tetrahedron's stress certificate**: the constant coefficients `1/48` on the
four vertex directions reproduce every weight —
`∑_l (1/48)(v_c ⬝ᵥ v_l)² = (9 + 3·1)/48 = 1/4 = t_c`; the multiplier is `Λ = I/12`. -/
theorem tetraDesign_stressCertificate (c : Fin 4) :
    ∑ l : Fin 4, (1/48 : ℝ) * (tetraDesign.atom c ⬝ᵥ tetraDesign.atom l) ^ 2
      = tetraDesign.weight c := by
  fin_cases c <;>
    simp [tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_four, Fin.sum_univ_three] <;>
    norm_num

/-- **Certified ties exist**: the regular tetrahedron is a genuine `(4,3)` tie carrying
a stress certificate. Together with `exists_isTie_and_noStressCertificate`, both sides
of the alternative are inhabited at genuine ties; the discriminator is
duplicate-weight consistency. -/
theorem exists_isTie_and_stressCertificate :
    ∃ D : WeightedDesign 4 3, IsTie D ∧
      ∃ (family : Finset (Fin 4)) (dir : Fin 4 → Fin 3 → ℝ) (coeff : Fin 4 → ℝ),
        (∀ i ∈ family, 0 ≤ coeff i) ∧
        ∀ c : Fin 4, ∑ i ∈ family, coeff i * (D.atom c ⬝ᵥ dir i) ^ 2 = D.weight c :=
  ⟨tetraDesign, tetraDesign_isTie, Finset.univ, tetraDesign.atom, fun _ => 1/48,
    fun _ _ => by norm_num, tetraDesign_stressCertificate⟩

end Gtz
