import Gtz.Design.StarSignRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The star amplified exchange

A weak-not-strict vertex star hands a sign-mixed kernel probe.  This module
turns the mixed signs into quantitative exchange data.

* `exists_amplified_pair_of_signMixed` — mixed readings contain a pair whose
  difference-square strictly exceeds both endpoint squares.
* The four bundle-translation lemmas — the opposite triangle of every star
  reads the pairwise differences of that star's gauge bundle, and each bundle
  reading squares to its chart reading.
* The four star theorems — a weak-not-strict star has a kernel probe, an
  amplifying opposite-triangle label, and two distinct star labels that the
  amplifying label strictly beats in squared reading.
* `dotProduct_exchangeGap_at_kernel` — at a kernel probe of a selection, one
  exchange reads exactly the incoming boost minus the outgoing boost.
* `exchangeGap_pos_at_kernel_of_le` — the amplified exchange reads strictly
  positively at the kernel when the incoming boost quotient is at least the
  outgoing one.
* `exists_kernel_pointer_of_posSemidef_not_posDef` — the kernel probe and its
  outside pointer arrive together from a weak-not-strict selection.
* `kFourStarGauge_exists_conditional_exchange` — the assembled gauge-star
  package: kernel probe, amplifying label, out label, and the conditional
  strict reading of the exchanged selection.

The sweep behind this module (star_sweep.jl, star_law.jl, 50000 exact tangent
points with free masses and free weights) shows that no single-statistic
selection closes the star branch: the minority star fires at 84 percent, some
vertex star at 98 percent, and the pointer host can fail exactly at tangency.
The amplified exchange is the per-probe repair step that every global
argument can consume.
-/

namespace Gtz

open Matrix

/-! ## 1. The amplification core -/

/-- A positive and a negative number amplify: the difference-square strictly
exceeds both squares. -/
theorem sq_lt_sq_sub_of_pos_of_neg {posRead negRead : ℝ}
    (hpos : 0 < posRead) (hneg : negRead < 0) :
    posRead ^ 2 < (posRead - negRead) ^ 2
      ∧ negRead ^ 2 < (posRead - negRead) ^ 2 := by
  constructor <;> nlinarith

/-- Sign-mixed readings contain an amplified pair. -/
theorem exists_amplified_pair_of_signMixed {readings : Fin 3 → ℝ}
    (hpos : ∃ index, 0 < readings index)
    (hneg : ∃ index, readings index < 0) :
    ∃ posIdx negIdx : Fin 3, posIdx ≠ negIdx
      ∧ readings posIdx ^ 2 < (readings posIdx - readings negIdx) ^ 2
      ∧ readings negIdx ^ 2 < (readings posIdx - readings negIdx) ^ 2 := by
  obtain ⟨posIdx, hp⟩ := hpos
  obtain ⟨negIdx, hn⟩ := hneg
  have hne : posIdx ≠ negIdx := by
    intro h
    rw [h] at hp
    linarith
  exact ⟨posIdx, negIdx, hne, sq_lt_sq_sub_of_pos_of_neg hp hn⟩

/-! ## 2. The bundle translations

Each star's gauge bundle has the property that every pairwise bundle
difference is, up to sign, one opposite-triangle chart direction, and every
bundle entry is, up to sign, one star chart direction.  Squared readings do
not see the signs. -/

section BundleTranslate

variable (x : Fin 3 → ℝ)

/-- The gauge star `{3, 4, 5}` with bundle `(v3, v4, v5)` and opposite
triangle `{0, 1, 2}`. -/
theorem kFourStarGauge_bundle_translate :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({3, 4, 5} : Finset (Fin 6))
      ∧ outOne ∈ ({3, 4, 5} : Finset (Fin 6))
      ∧ outTwo ∈ ({3, 4, 5} : Finset (Fin 6))
      ∧ outOne ≠ outTwo
      ∧ (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          = ((![kFourDirection 3, kFourDirection 4, kFourDirection 5] posIdx ⬝ᵥ x)
            - (![kFourDirection 3, kFourDirection 4, kFourDirection 5] negIdx ⬝ᵥ x)) ^ 2
      ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2
          = (![kFourDirection 3, kFourDirection 4, kFourDirection 5] posIdx ⬝ᵥ x) ^ 2
      ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
          = (![kFourDirection 3, kFourDirection 4, kFourDirection 5] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨0, 3, 4, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 3, 5, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨0, 4, 3, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨2, 4, 5, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 5, 3, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨2, 5, 4, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- The star `{0, 1, 3}` at vertex `a` with bundle `(v0, v1, v3)` and
opposite triangle `{2, 4, 5}`. -/
theorem kFourStarA_bundle_translate :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({0, 1, 3} : Finset (Fin 6))
      ∧ outOne ∈ ({0, 1, 3} : Finset (Fin 6))
      ∧ outTwo ∈ ({0, 1, 3} : Finset (Fin 6))
      ∧ outOne ≠ outTwo
      ∧ (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          = ((![kFourDirection 0, kFourDirection 1, kFourDirection 3] posIdx ⬝ᵥ x)
            - (![kFourDirection 0, kFourDirection 1, kFourDirection 3] negIdx ⬝ᵥ x)) ^ 2
      ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2
          = (![kFourDirection 0, kFourDirection 1, kFourDirection 3] posIdx ⬝ᵥ x) ^ 2
      ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
          = (![kFourDirection 0, kFourDirection 1, kFourDirection 3] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨2, 0, 1, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 0, 3, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨2, 1, 0, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨5, 1, 3, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 3, 0, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨5, 3, 1, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- The star `{0, 2, 4}` at vertex `b` with the flipped bundle
`(v0, -v2, -v4)` and opposite triangle `{1, 3, 5}`. -/
theorem kFourStarB_bundle_translate :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({0, 2, 4} : Finset (Fin 6))
      ∧ outOne ∈ ({0, 2, 4} : Finset (Fin 6))
      ∧ outTwo ∈ ({0, 2, 4} : Finset (Fin 6))
      ∧ outOne ≠ outTwo
      ∧ (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          = ((![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] posIdx ⬝ᵥ x)
            - (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] negIdx ⬝ᵥ x)) ^ 2
      ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2
          = (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] posIdx ⬝ᵥ x) ^ 2
      ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
          = (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨1, 0, 2, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 0, 4, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 2, 0, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨5, 2, 4, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 4, 0, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨5, 4, 2, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- The star `{1, 2, 5}` at vertex `c` with the flipped bundle
`(v1, v2, -v5)` and opposite triangle `{0, 3, 4}`. -/
theorem kFourStarC_bundle_translate :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({1, 2, 5} : Finset (Fin 6))
      ∧ outOne ∈ ({1, 2, 5} : Finset (Fin 6))
      ∧ outTwo ∈ ({1, 2, 5} : Finset (Fin 6))
      ∧ outOne ≠ outTwo
      ∧ (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          = ((![kFourDirection 1, kFourDirection 2, -kFourDirection 5] posIdx ⬝ᵥ x)
            - (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] negIdx ⬝ᵥ x)) ^ 2
      ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2
          = (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] posIdx ⬝ᵥ x) ^ 2
      ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
          = (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨0, 1, 2, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 1, 5, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨0, 2, 1, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨4, 2, 5, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 5, 1, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 5, 2, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

end BundleTranslate

/-! ## 3. The four star amplified-triangle theorems -/

section StarAmplified

variable (point : DirectionChartPoint 6)

/-- The gauge star `{3, 4, 5}`: a weak-not-strict star has a kernel probe and
an amplifying opposite-triangle label that strictly beats two distinct star
labels in squared reading. -/
theorem kFourStarGauge_exists_amplified_triangle
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {3, 4, 5} *ᵥ x = 0
      ∧ ∃ ampLabel outOne outTwo : Fin 6,
          ampLabel ∉ ({3, 4, 5} : Finset (Fin 6))
          ∧ outOne ∈ ({3, 4, 5} : Finset (Fin 6))
          ∧ outTwo ∈ ({3, 4, 5} : Finset (Fin 6))
          ∧ outOne ≠ outTwo
          ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2 < (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
              < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
  obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
    kFourStarGauge_kernel_readings_signMixed point hpsd hnot
  obtain ⟨posIdx, negIdx, hne, hampPos, hampNeg⟩ :=
    exists_amplified_pair_of_signMixed
      (readings := fun index =>
        ![kFourDirection 3, kFourDirection 4, kFourDirection 5] index ⬝ᵥ x)
      hpos hneg
  obtain ⟨ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo, houtNe, hampEq,
    houtOneEq, houtTwoEq⟩ := kFourStarGauge_bundle_translate x posIdx negIdx hne
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo,
    houtNe, ?_, ?_⟩
  · rw [houtOneEq, hampEq]
    exact hampPos
  · rw [houtTwoEq, hampEq]
    exact hampNeg

/-- The star `{0, 1, 3}` at vertex `a`, amplified by its opposite triangle. -/
theorem kFourStarA_exists_amplified_triangle
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {0, 1, 3} *ᵥ x = 0
      ∧ ∃ ampLabel outOne outTwo : Fin 6,
          ampLabel ∉ ({0, 1, 3} : Finset (Fin 6))
          ∧ outOne ∈ ({0, 1, 3} : Finset (Fin 6))
          ∧ outTwo ∈ ({0, 1, 3} : Finset (Fin 6))
          ∧ outOne ≠ outTwo
          ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2 < (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
              < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
  obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
    kFourStarA_kernel_readings_signMixed point hpsd hnot
  obtain ⟨posIdx, negIdx, hne, hampPos, hampNeg⟩ :=
    exists_amplified_pair_of_signMixed
      (readings := fun index =>
        ![kFourDirection 0, kFourDirection 1, kFourDirection 3] index ⬝ᵥ x)
      hpos hneg
  obtain ⟨ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo, houtNe, hampEq,
    houtOneEq, houtTwoEq⟩ := kFourStarA_bundle_translate x posIdx negIdx hne
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo,
    houtNe, ?_, ?_⟩
  · rw [houtOneEq, hampEq]
    exact hampPos
  · rw [houtTwoEq, hampEq]
    exact hampNeg

/-- The star `{0, 2, 4}` at vertex `b`, amplified by its opposite triangle.
The flipped bundle does not change squared chart readings. -/
theorem kFourStarB_exists_amplified_triangle
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {0, 2, 4} *ᵥ x = 0
      ∧ ∃ ampLabel outOne outTwo : Fin 6,
          ampLabel ∉ ({0, 2, 4} : Finset (Fin 6))
          ∧ outOne ∈ ({0, 2, 4} : Finset (Fin 6))
          ∧ outTwo ∈ ({0, 2, 4} : Finset (Fin 6))
          ∧ outOne ≠ outTwo
          ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2 < (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
              < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
  obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
    kFourStarB_kernel_readings_signMixed point hpsd hnot
  obtain ⟨posIdx, negIdx, hne, hampPos, hampNeg⟩ :=
    exists_amplified_pair_of_signMixed
      (readings := fun index =>
        ![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] index ⬝ᵥ x)
      hpos hneg
  obtain ⟨ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo, houtNe, hampEq,
    houtOneEq, houtTwoEq⟩ := kFourStarB_bundle_translate x posIdx negIdx hne
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo,
    houtNe, ?_, ?_⟩
  · rw [houtOneEq, hampEq]
    exact hampPos
  · rw [houtTwoEq, hampEq]
    exact hampNeg

/-- The star `{1, 2, 5}` at vertex `c`, amplified by its opposite triangle. -/
theorem kFourStarC_exists_amplified_triangle
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {1, 2, 5} *ᵥ x = 0
      ∧ ∃ ampLabel outOne outTwo : Fin 6,
          ampLabel ∉ ({1, 2, 5} : Finset (Fin 6))
          ∧ outOne ∈ ({1, 2, 5} : Finset (Fin 6))
          ∧ outTwo ∈ ({1, 2, 5} : Finset (Fin 6))
          ∧ outOne ≠ outTwo
          ∧ (kFourDirection outOne ⬝ᵥ x) ^ 2 < (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          ∧ (kFourDirection outTwo ⬝ᵥ x) ^ 2
              < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
  obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
    kFourStarC_kernel_readings_signMixed point hpsd hnot
  obtain ⟨posIdx, negIdx, hne, hampPos, hampNeg⟩ :=
    exists_amplified_pair_of_signMixed
      (readings := fun index =>
        ![kFourDirection 1, kFourDirection 2, -kFourDirection 5] index ⬝ᵥ x)
      hpos hneg
  obtain ⟨ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo, houtNe, hampEq,
    houtOneEq, houtTwoEq⟩ := kFourStarC_bundle_translate x posIdx negIdx hne
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampMem, houtOne, houtTwo,
    houtNe, ?_, ?_⟩
  · rw [houtOneEq, hampEq]
    exact hampPos
  · rw [houtTwoEq, hampEq]
    exact hampNeg

end StarAmplified

/-! ## 4. The exchange at a kernel probe -/

/-- At a kernel probe of a selection, one exchange reads exactly the incoming
boost minus the outgoing boost. -/
theorem dotProduct_exchangeGap_at_kernel {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {outLabel incLabel : Fin size}
    (hout : outLabel ∈ selected) (hinc : incLabel ∉ selected)
    {x : Fin 3 → ℝ}
    (hker : directionChartGap direction mass weight selected *ᵥ x = 0) :
    x ⬝ᵥ (directionChartGap direction mass weight
        (insert incLabel (selected.erase outLabel)) *ᵥ x)
      = mass incLabel / weight incLabel * (direction incLabel ⬝ᵥ x) ^ 2
        - mass outLabel / weight outLabel * (direction outLabel ⬝ᵥ x) ^ 2 := by
  rw [directionChartGap_exchange direction mass weight hout hinc,
    Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add, hker,
    dotProduct_zero, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_smul,
    dotProduct_smul, dotProduct_atomMatrix_mulVec_pair,
    dotProduct_atomMatrix_mulVec_pair, smul_eq_mul, smul_eq_mul]
  ring

/-- The amplified exchange reads strictly positively at the kernel probe when
the incoming boost quotient is at least the outgoing one. -/
theorem exchangeGap_pos_at_kernel_of_le {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {outLabel incLabel : Fin size}
    (hout : outLabel ∈ selected) (hinc : incLabel ∉ selected)
    (hmassOut : 0 < mass outLabel) (hweightOut : 0 < weight outLabel)
    {x : Fin 3 → ℝ}
    (hker : directionChartGap direction mass weight selected *ᵥ x = 0)
    (hamp : (direction outLabel ⬝ᵥ x) ^ 2 < (direction incLabel ⬝ᵥ x) ^ 2)
    (hquot : mass outLabel / weight outLabel
      ≤ mass incLabel / weight incLabel) :
    0 < x ⬝ᵥ (directionChartGap direction mass weight
      (insert incLabel (selected.erase outLabel)) *ᵥ x) := by
  rw [dotProduct_exchangeGap_at_kernel direction mass weight hout hinc hker]
  have hquotOut : 0 < mass outLabel / weight outLabel :=
    div_pos hmassOut hweightOut
  nlinarith [mul_nonneg (sub_nonneg.mpr hquot)
      (sq_nonneg (direction incLabel ⬝ᵥ x)),
    mul_pos hquotOut (sub_pos.mpr hamp)]

/-! ## 5. The kernel probe and its pointer arrive together -/

/-- A weak-not-strict selection on the K4 chart hands its kernel probe and
the outside pointer in one package. -/
theorem exists_kernel_pointer_of_posSemidef_not_posDef
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcard : 2 ≤ selected.card)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight selected *ᵥ x = 0
      ∧ ∃ pointer, pointer ∉ selected ∧
          ∀ swap : Finset (Fin 6), pointer ∈ swap →
            0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
              swap *ᵥ x) := by
  obtain ⟨x, hxne, hker⟩ := exists_kernelVec_of_posSemidef_not_posDef
    (directionChartGap_transpose kFourDirection point.mass point.weight selected)
    hpsd hnot
  obtain ⟨pointer, hout, hswap⟩ := kFour_pointer_of_kernel point hcard hxne hker
  exact ⟨x, hxne, hker, pointer, hout, hswap⟩

/-! ## 6. The assembled gauge-star package -/

/-- **The conditional exchange.**  A weak-not-strict gauge star hands a kernel
probe, an amplifying triangle label, and an out label of the star, with the
exchange reading strictly positive at the probe whenever the amplifying boost
quotient is at least the outgoing one. -/
theorem kFourStarGauge_exists_conditional_exchange
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosDef) :
    ∃ x : Fin 3 → ℝ, x ≠ 0
      ∧ directionChartGap kFourDirection point.mass point.weight {3, 4, 5} *ᵥ x = 0
      ∧ ∃ ampLabel outLabel : Fin 6,
          ampLabel ∉ ({3, 4, 5} : Finset (Fin 6))
          ∧ outLabel ∈ ({3, 4, 5} : Finset (Fin 6))
          ∧ (kFourDirection outLabel ⬝ᵥ x) ^ 2
              < (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          ∧ (point.mass outLabel / point.weight outLabel
                ≤ point.mass ampLabel / point.weight ampLabel →
              0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
                (insert ampLabel (({3, 4, 5} : Finset (Fin 6)).erase outLabel))
                  *ᵥ x)) := by
  obtain ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampMem, houtOne, houtTwoMem,
    houtNe, hampOneLt, hampTwoLt⟩ :=
    kFourStarGauge_exists_amplified_triangle point hpsd hnot
  refine ⟨x, hxne, hker, ampLabel, outOne, hampMem, houtOne, hampOneLt,
    fun hquot => ?_⟩
  exact exchangeGap_pos_at_kernel_of_le kFourDirection point.mass point.weight
    houtOne hampMem (point.mass_pos outOne) (point.weight_pos outOne) hker
    hampOneLt hquot

end Gtz
