import Mathlib
import Gtz.Reduction.StressWalk
import Gtz.Reduction.StressSignSplit
import Gtz.Reduction.StressConditionalWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
# The stress-existence brick: every generic `(7,3)` design carries a canonical triple

The landed split law (`Gtz.sevenThree_design_stress_split`,
`Gtz/Reduction/StressSignSplit.lean`) reads the sign pattern of a stress it is
HANDED: a full-support stress of a `(7,3)` design splits `(3,4)` up to sign.  The
tree also manufactures stresses (`Gtz.exists_parsevalNullDirection`,
`Gtz/Reduction/StressWalk.lean`: `k(k+1)/2 < m` forces one), but nothing between
the two: no bridge from EXISTENCE to FULL SUPPORT.  This file is that bridge.

The hinge is a genericity notion, `Gtz.HasIndependentDropOneFamilies`: every
subfamily omitting one atom has linearly independent atom matrices.  Under it a
stress vanishing anywhere dies outright
(`Gtz.stress_eq_zero_of_coordinate_eq_zero`), so every nonzero stress has full
support, any two stresses are proportional -- the stress space is exactly a line
(`Gtz.sevenThree_stressLine_of_dropOneIndependent`, producing verbatim the
unique-stress premise of `Gtz.gtzWeighted_seven_three_iff_uniqueStress`, which
had NO producer in the tree) -- and the capstone composes with the landed law:
`Gtz.sevenThree_canonicalStress_of_dropOneIndependent`, every drop-one-generic
`(7,3)` design carries a stress, unique up to scale, everywhere nonzero, whose
sign split is exactly `(3,4)` or `(4,3)`.  The smaller sign side is the
canonical triple of the syzygy lane.

Off the generic stratum nothing is lost: the support dichotomy
(`Gtz.stress_support_dichotomy`) restricts a partially supported stress to a
genuine stress of the proper subfamily its support carries, witnessing the
linear dependence of that subfamily
(`Gtz.not_linearIndependent_on_support_of_stress`).

The walk `Gtz.exists_rescaledReducedDesign_of_stress`
(`Gtz/Reduction/StressConditionalWalk.lean`) consumes exactly the hypothesis
shape produced here -- a nonzero `z` with `∑ c, z c • atomMatrix (atom c) = 0` --
so the canonical stress feeds both consumers from one supply;
`Gtz.sevenThree_exists_rescaledReducedDesign` is the `(7,3)` landing stated
standalone, where existence is free of any genericity.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Drop-one genericity -/

/-- **Drop-one genericity.**  Every subfamily omitting one atom has linearly
independent atom matrices.  At `(7,3)` this says every six of the seven Veronese
images are independent in `Sym_3(R)` -- the atoms are in general position on the
Veronese surface. -/
def HasIndependentDropOneFamilies (v : Fin m → Fin k → ℝ) : Prop :=
  ∀ dropped : Fin m,
    LinearIndependent ℝ (fun c : {c : Fin m // c ≠ dropped} => atomMatrix (v c.1))

/-- **The forcing lemma.**  Under drop-one genericity a stress vanishing at one
coordinate vanishes everywhere: erase the vanished coordinate and the remaining
combination is a dependency of an independent family. -/
theorem stress_eq_zero_of_coordinate_eq_zero {v : Fin m → Fin k → ℝ}
    (hdropOne : HasIndependentDropOneFamilies v) {z : Fin m → ℝ}
    (hstress : (∑ c, z c • atomMatrix (v c)) = 0) {vanished : Fin m}
    (hvanished : z vanished = 0) : z = 0 := by
  have herase :
      (∑ c ∈ Finset.univ.erase vanished, z c • atomMatrix (v c))
        = ∑ c : {c : Fin m // c ≠ vanished}, z c.1 • atomMatrix (v c.1) :=
    Finset.sum_subtype (Finset.univ.erase vanished)
      (fun c => by simp [Finset.mem_erase]) (fun c => z c • atomMatrix (v c))
  have hdrop : (∑ c ∈ Finset.univ.erase vanished, z c • atomMatrix (v c))
      = ∑ c, z c • atomMatrix (v c) :=
    Finset.sum_erase (f := fun c => z c • atomMatrix (v c)) Finset.univ
      (show z vanished • atomMatrix (v vanished) = 0 by rw [hvanished, zero_smul])
  have hsubtypeSum :
      (∑ c : {c : Fin m // c ≠ vanished}, z c.1 • atomMatrix (v c.1)) = 0 := by
    rw [← herase, hdrop]
    exact hstress
  have hcoefficients :=
    Fintype.linearIndependent_iff.mp (hdropOne vanished) (fun c => z c.1) hsubtypeSum
  funext c
  show z c = 0
  by_cases hc : c = vanished
  · rw [hc, hvanished]
  · exact hcoefficients ⟨c, hc⟩

/-- Under drop-one genericity a nonzero stress has FULL support. -/
theorem stress_coordinates_ne_zero {v : Fin m → Fin k → ℝ}
    (hdropOne : HasIndependentDropOneFamilies v) {z : Fin m → ℝ}
    (hstress : (∑ c, z c • atomMatrix (v c)) = 0) (hne : z ≠ 0) :
    ∀ c, z c ≠ 0 := by
  intro c hzero
  exact hne (stress_eq_zero_of_coordinate_eq_zero hdropOne hstress hzero)

/-- **Uniqueness up to scale.**  Under drop-one genericity every stress is a
scalar multiple of any fixed nonzero one: the difference
`w - (w anchor / direction anchor) • direction` is a stress vanishing at the
anchor, so the forcing lemma kills it.  This is verbatim the unique-stress
premise of `Gtz.gtzWeighted_seven_three_iff_uniqueStress`, stated at general
size and rank. -/
theorem exists_ratio_of_second_stress {v : Fin m → Fin k → ℝ}
    (hdropOne : HasIndependentDropOneFamilies v) {direction : Fin m → ℝ}
    (hdirectionStress : (∑ c, direction c • atomMatrix (v c)) = 0)
    (hdirectionNe : direction ≠ 0) (w : Fin m → ℝ)
    (hwStress : (∑ c, w c • atomMatrix (v c)) = 0) :
    ∃ ratio : ℝ, w = ratio • direction := by
  obtain ⟨anchor, hanchor⟩ := Function.ne_iff.mp hdirectionNe
  have hanchorNe : direction anchor ≠ 0 := by simpa using hanchor
  refine ⟨w anchor / direction anchor, ?_⟩
  set ratio : ℝ := w anchor / direction anchor with hratio
  have hpointwise : ∀ c, ((w - ratio • direction) c) • atomMatrix (v c)
      = w c • atomMatrix (v c) - ratio • (direction c • atomMatrix (v c)) := by
    intro c
    show (w c - ratio * direction c) • atomMatrix (v c) = _
    rw [sub_smul, smul_smul]
  have hcomboStress : (∑ c, ((w - ratio • direction) c) • atomMatrix (v c)) = 0 := by
    rw [Finset.sum_congr rfl fun c _ => hpointwise c, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hwStress, hdirectionStress, smul_zero, sub_zero]
  have hcomboAnchor : (w - ratio • direction) anchor = 0 := by
    show w anchor - ratio * direction anchor = 0
    rw [hratio, div_mul_cancel₀ _ hanchorNe, sub_self]
  have hcomboZero :=
    stress_eq_zero_of_coordinate_eq_zero hdropOne hcomboStress hcomboAnchor
  exact sub_eq_zero.mp hcomboZero

/-! ## The support dichotomy, off the generic stratum -/

/-- A stress restricts to its support: the vanished coordinates contribute
nothing, so the support subfamily carries a genuine stress of its own. -/
theorem stress_restricts_to_support {v : Fin m → Fin k → ℝ} {z : Fin m → ℝ}
    (hstress : (∑ c, z c • atomMatrix (v c)) = 0) :
    (∑ c ∈ Finset.univ.filter fun c => z c ≠ 0, z c • atomMatrix (v c)) = 0 := by
  have hkeeps : ∀ c ∈ Finset.univ, z c • atomMatrix (v c) ≠ 0 → z c ≠ 0 := by
    intro c _ hterm hzero
    exact hterm (by rw [hzero, zero_smul])
  calc (∑ c ∈ Finset.univ.filter fun c => z c ≠ 0, z c • atomMatrix (v c))
      = ∑ c, z c • atomMatrix (v c) := Finset.sum_filter_of_ne hkeeps
    _ = 0 := hstress

/-- **The support dichotomy.**  A nonzero stress either has full support, or its
support is a proper nonempty subfamily carrying the restricted stress -- a linear
dependency of that subfamily. -/
theorem stress_support_dichotomy {v : Fin m → Fin k → ℝ} {z : Fin m → ℝ}
    (hstress : (∑ c, z c • atomMatrix (v c)) = 0) (hne : z ≠ 0) :
    (∀ c, z c ≠ 0) ∨
      ((Finset.univ.filter fun c => z c ≠ 0).Nonempty ∧
        (Finset.univ.filter fun c => z c ≠ 0) ≠ Finset.univ ∧
        (∑ c ∈ Finset.univ.filter fun c => z c ≠ 0, z c • atomMatrix (v c)) = 0) := by
  by_cases hfull : ∀ c, z c ≠ 0
  · exact Or.inl hfull
  · push Not at hfull
    obtain ⟨dead, hdead⟩ := hfull
    obtain ⟨live, hlive⟩ := Function.ne_iff.mp hne
    have hliveNe : z live ≠ 0 := by simpa using hlive
    refine Or.inr ⟨⟨live, Finset.mem_filter.mpr ⟨Finset.mem_univ live, hliveNe⟩⟩,
      ?_, stress_restricts_to_support hstress⟩
    intro huniv
    have hmem : dead ∈ Finset.univ.filter fun c => z c ≠ 0 := by
      rw [huniv]
      exact Finset.mem_univ dead
    exact (Finset.mem_filter.mp hmem).2 hdead

/-- The support of a nonzero stress witnesses the linear DEPENDENCE of the atom
matrices it carries. -/
theorem not_linearIndependent_on_support_of_stress {v : Fin m → Fin k → ℝ}
    {z : Fin m → ℝ} (hstress : (∑ c, z c • atomMatrix (v c)) = 0) (hne : z ≠ 0) :
    ¬ LinearIndependent ℝ
      (fun c : ↥(Finset.univ.filter fun c => z c ≠ 0) => atomMatrix (v c.1)) := by
  rw [Fintype.not_linearIndependent_iff]
  obtain ⟨live, hlive⟩ := Function.ne_iff.mp hne
  have hliveNe : z live ≠ 0 := by simpa using hlive
  refine ⟨fun c => z c.1, ?_,
    ⟨live, Finset.mem_filter.mpr ⟨Finset.mem_univ live, hliveNe⟩⟩, hliveNe⟩
  rw [Finset.univ_eq_attach, Finset.sum_attach _ fun c => z c • atomMatrix (v c)]
  exact stress_restricts_to_support hstress

/-! ## The `(7,3)` capstones -/

/-- **The stress line.**  A drop-one-generic `(7,3)` design carries a nonzero
stress, and its whole stress space is the line through it.  The inner clause is
verbatim the unique-stress premise of
`Gtz.gtzWeighted_seven_three_iff_uniqueStress`, which had no producer in the
tree. -/
theorem sevenThree_stressLine_of_dropOneIndependent (design : WeightedDesign 7 3)
    (hdropOne : HasIndependentDropOneFamilies design.atom) :
    ∃ direction : Fin 7 → ℝ, direction ≠ 0 ∧
      (∑ c, direction c • atomMatrix (design.atom c)) = 0 ∧
      ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
        ∃ ratio : ℝ, stress = ratio • direction := by
  obtain ⟨direction, hne, hstress⟩ :=
    exists_parsevalNullDirection design.atom (by norm_num)
  exact ⟨direction, hne, hstress,
    fun stress hstressEq =>
      exists_ratio_of_second_stress hdropOne hstress hne stress hstressEq⟩

/-- **THE CANONICAL STRESS.**  Every drop-one-generic `(7,3)` design carries a
stress that is everywhere nonzero, is unique up to scale, and -- by the landed
split law `Gtz.sevenThree_design_stress_split` -- splits exactly `(3,4)` or
`(4,3)` by sign.  The smaller sign side is the canonical triple the syzygy lane
hands to the domination question. -/
theorem sevenThree_canonicalStress_of_dropOneIndependent (design : WeightedDesign 7 3)
    (hdropOne : HasIndependentDropOneFamilies design.atom) :
    ∃ z : Fin 7 → ℝ,
      (∑ c, z c • atomMatrix (design.atom c)) = 0 ∧ (∀ c, z c ≠ 0) ∧
      (((Finset.univ.filter fun c => 0 < z c).card = 3
          ∧ (Finset.univ.filter fun c => z c < 0).card = 4)
        ∨ ((Finset.univ.filter fun c => 0 < z c).card = 4
          ∧ (Finset.univ.filter fun c => z c < 0).card = 3)) ∧
      ∀ stress : Fin 7 → ℝ, (∑ c, stress c • atomMatrix (design.atom c)) = 0 →
        ∃ ratio : ℝ, stress = ratio • z := by
  obtain ⟨z, hne, hstress⟩ := exists_parsevalNullDirection design.atom (by norm_num)
  have hfull : ∀ c, z c ≠ 0 := stress_coordinates_ne_zero hdropOne hstress hne
  exact ⟨z, hstress, hfull, sevenThree_design_stress_split design hstress hfull,
    fun stress hstressEq =>
      exists_ratio_of_second_stress hdropOne hstress hne stress hstressEq⟩

/-- **The walk landing at `(7,3)`, standalone.**  Existence of the stress is
free -- `3 * 4 / 2 = 6 < 7` -- so EVERY `(7,3)` design walks to a strictly
smaller design on a rescaled subfamily of its own atoms, no genericity needed.
Under drop-one genericity the stress this consumes is (up to scale) THE
canonical stress of `Gtz.sevenThree_canonicalStress_of_dropOneIndependent`:
the split law and the walk share one supply. -/
theorem sevenThree_exists_rescaledReducedDesign (design : WeightedDesign 7 3) :
    ∃ scale : ℝ, 0 < scale ∧ scale ≤ 1 ∧
      ∃ smallSize : ℕ, smallSize < 7 ∧ ∃ smallDesign : WeightedDesign smallSize 3,
        ∃ inject : Fin smallSize → Fin 7, Function.Injective inject ∧
          ∀ i, smallDesign.atom i = Real.sqrt scale • design.atom (inject i) := by
  obtain ⟨z, hne, hstress⟩ := exists_parsevalNullDirection design.atom (by norm_num)
  exact exists_rescaledReducedDesign_of_stress design (by norm_num) hne hstress

end Gtz
