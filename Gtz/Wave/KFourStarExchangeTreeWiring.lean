import Gtz.Wave.KFourStarAmplifiedWallWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Preserve the spanning-tree content of the K4 star amplification

The four bundle translations used by `StarAmplifiedExchange` choose more than
an outside label and two distinct star labels.  The outside label is the edge
joining the two leaves indexed by the outgoing labels.  Consequently, replacing
either outgoing star edge by the amplifying edge is again a K4 spanning tree.

That combinatorial fact was lost by the first common amplified interface.  It
matters: an arbitrary outside edge and an arbitrary deleted star edge can leave
the fourth vertex isolated.  This module therefore replays the finite bundle
translation, records both spanning-tree witnesses, and carries them through the
exact exchange readings and into the registered A3 wall.
-/

namespace Gtz

open Matrix

/-! ## Bundle translations that retain both spanning trees -/

/-- Gauge-star bundle translation with the two exchanged spanning trees kept. -/
theorem kFourStarGauge_bundle_translate_spanning (x : Fin 3 → ℝ) :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({3, 4, 5} : Finset (Fin 6)) ∧
      outOne ∈ ({3, 4, 5} : Finset (Fin 6)) ∧
      outTwo ∈ ({3, 4, 5} : Finset (Fin 6)) ∧ outOne ≠ outTwo ∧
      insert ampLabel (({3, 4, 5} : Finset (Fin 6)).erase outOne)
        ∈ kFourSpanningTreeList ∧
      insert ampLabel (({3, 4, 5} : Finset (Fin 6)).erase outTwo)
        ∈ kFourSpanningTreeList ∧
      (kFourDirection ampLabel ⬝ᵥ x) ^ 2 =
        ((![kFourDirection 3, kFourDirection 4, kFourDirection 5] posIdx ⬝ᵥ x) -
          (![kFourDirection 3, kFourDirection 4, kFourDirection 5] negIdx ⬝ᵥ x)) ^ 2 ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2 =
        (![kFourDirection 3, kFourDirection 4, kFourDirection 5] posIdx ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2 =
        (![kFourDirection 3, kFourDirection 4, kFourDirection 5] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨0, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 3, 5, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨0, 4, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨2, 4, 5, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 5, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨2, 5, 4, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- Vertex-`a` star bundle translation with both exchanged spanning trees. -/
theorem kFourStarA_bundle_translate_spanning (x : Fin 3 → ℝ) :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({0, 1, 3} : Finset (Fin 6)) ∧
      outOne ∈ ({0, 1, 3} : Finset (Fin 6)) ∧
      outTwo ∈ ({0, 1, 3} : Finset (Fin 6)) ∧ outOne ≠ outTwo ∧
      insert ampLabel (({0, 1, 3} : Finset (Fin 6)).erase outOne)
        ∈ kFourSpanningTreeList ∧
      insert ampLabel (({0, 1, 3} : Finset (Fin 6)).erase outTwo)
        ∈ kFourSpanningTreeList ∧
      (kFourDirection ampLabel ⬝ᵥ x) ^ 2 =
        ((![kFourDirection 0, kFourDirection 1, kFourDirection 3] posIdx ⬝ᵥ x) -
          (![kFourDirection 0, kFourDirection 1, kFourDirection 3] negIdx ⬝ᵥ x)) ^ 2 ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2 =
        (![kFourDirection 0, kFourDirection 1, kFourDirection 3] posIdx ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2 =
        (![kFourDirection 0, kFourDirection 1, kFourDirection 3] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨2, 0, 1, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 0, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨2, 1, 0, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨5, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 3, 0, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨5, 3, 1, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- Vertex-`b` star bundle translation with both exchanged spanning trees. -/
theorem kFourStarB_bundle_translate_spanning (x : Fin 3 → ℝ) :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({0, 2, 4} : Finset (Fin 6)) ∧
      outOne ∈ ({0, 2, 4} : Finset (Fin 6)) ∧
      outTwo ∈ ({0, 2, 4} : Finset (Fin 6)) ∧ outOne ≠ outTwo ∧
      insert ampLabel (({0, 2, 4} : Finset (Fin 6)).erase outOne)
        ∈ kFourSpanningTreeList ∧
      insert ampLabel (({0, 2, 4} : Finset (Fin 6)).erase outTwo)
        ∈ kFourSpanningTreeList ∧
      (kFourDirection ampLabel ⬝ᵥ x) ^ 2 =
        ((![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] posIdx ⬝ᵥ x) -
          (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] negIdx ⬝ᵥ x)) ^ 2 ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2 =
        (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] posIdx ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2 =
        (![kFourDirection 0, -kFourDirection 2, -kFourDirection 4] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨1, 0, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 0, 4, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨1, 2, 0, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨5, 2, 4, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 4, 0, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨5, 4, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-- Vertex-`c` star bundle translation with both exchanged spanning trees. -/
theorem kFourStarC_bundle_translate_spanning (x : Fin 3 → ℝ) :
    ∀ posIdx negIdx : Fin 3, posIdx ≠ negIdx →
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ ({1, 2, 5} : Finset (Fin 6)) ∧
      outOne ∈ ({1, 2, 5} : Finset (Fin 6)) ∧
      outTwo ∈ ({1, 2, 5} : Finset (Fin 6)) ∧ outOne ≠ outTwo ∧
      insert ampLabel (({1, 2, 5} : Finset (Fin 6)).erase outOne)
        ∈ kFourSpanningTreeList ∧
      insert ampLabel (({1, 2, 5} : Finset (Fin 6)).erase outTwo)
        ∈ kFourSpanningTreeList ∧
      (kFourDirection ampLabel ⬝ᵥ x) ^ 2 =
        ((![kFourDirection 1, kFourDirection 2, -kFourDirection 5] posIdx ⬝ᵥ x) -
          (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] negIdx ⬝ᵥ x)) ^ 2 ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2 =
        (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] posIdx ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2 =
        (![kFourDirection 1, kFourDirection 2, -kFourDirection 5] negIdx ⬝ᵥ x) ^ 2 := by
  intro posIdx negIdx hne
  fin_cases posIdx <;> fin_cases negIdx
  · exact absurd rfl hne
  · exact ⟨0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 1, 5, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨0, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne
  · exact ⟨4, 2, 5, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨3, 5, 1, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact ⟨4, 5, 2, by decide, by decide, by decide, by decide, by decide, by decide,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring,
      by simp [kFourDirection, dotProduct, Fin.sum_univ_three]; try ring⟩
  · exact absurd rfl hne

/-! ## The common spanning-exchange package -/

/-- Amplification data with both repaired selections certified as K4 trees. -/
def KFourTreeAmplifiedSpanningExchangeData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree *ᵥ x = 0 ∧
    ∃ ampLabel outOne outTwo : Fin 6,
      ampLabel ∉ tree ∧ outOne ∈ tree ∧ outTwo ∈ tree ∧ outOne ≠ outTwo ∧
      insert ampLabel (tree.erase outOne) ∈ kFourSpanningTreeList ∧
      insert ampLabel (tree.erase outTwo) ∈ kFourSpanningTreeList ∧
      (kFourDirection outOne ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 ∧
      (kFourDirection outTwo ⬝ᵥ x) ^ 2
        < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 ∧
      x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outOne)) *ᵥ x)
        = point.mass ampLabel / point.weight ampLabel
            * (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          - point.mass outOne / point.weight outOne
            * (kFourDirection outOne ⬝ᵥ x) ^ 2 ∧
      x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outTwo)) *ᵥ x)
        = point.mass ampLabel / point.weight ampLabel
            * (kFourDirection ampLabel ⬝ᵥ x) ^ 2
          - point.mass outTwo / point.weight outTwo
            * (kFourDirection outTwo ⬝ᵥ x) ^ 2 ∧
      (0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outOne)) *ᵥ x) ∨
        0 < x ⬝ᵥ (directionChartGap kFourDirection point.mass point.weight
          (insert ampLabel (tree.erase outTwo)) *ᵥ x) ∨
        (point.mass ampLabel / point.weight ampLabel
            < point.mass outOne / point.weight outOne ∧
          point.mass ampLabel / point.weight ampLabel
            < point.mass outTwo / point.weight outTwo))

private theorem amplifiedSpanningExchange_of_bundle
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (bundle : Fin 3 → (Fin 3 → ℝ))
    (hmixed : ∀ (x : Fin 3 → ℝ),
      (∃ index, 0 < bundle index ⬝ᵥ x) →
      (∃ index, bundle index ⬝ᵥ x < 0) →
      ∃ posIdx negIdx : Fin 3, posIdx ≠ negIdx ∧
        (bundle posIdx ⬝ᵥ x) ^ 2
          < ((bundle posIdx ⬝ᵥ x) - (bundle negIdx ⬝ᵥ x)) ^ 2 ∧
        (bundle negIdx ⬝ᵥ x) ^ 2
          < ((bundle posIdx ⬝ᵥ x) - (bundle negIdx ⬝ᵥ x)) ^ 2)
    (htranslate : ∀ (x : Fin 3 → ℝ) (posIdx negIdx : Fin 3), posIdx ≠ negIdx →
      ∃ ampLabel outOne outTwo : Fin 6,
        ampLabel ∉ tree ∧ outOne ∈ tree ∧ outTwo ∈ tree ∧ outOne ≠ outTwo ∧
        insert ampLabel (tree.erase outOne) ∈ kFourSpanningTreeList ∧
        insert ampLabel (tree.erase outTwo) ∈ kFourSpanningTreeList ∧
        (kFourDirection ampLabel ⬝ᵥ x) ^ 2 =
          ((bundle posIdx ⬝ᵥ x) - (bundle negIdx ⬝ᵥ x)) ^ 2 ∧
        (kFourDirection outOne ⬝ᵥ x) ^ 2 = (bundle posIdx ⬝ᵥ x) ^ 2 ∧
        (kFourDirection outTwo ⬝ᵥ x) ^ 2 = (bundle negIdx ⬝ᵥ x) ^ 2)
    {x : Fin 3 → ℝ} (hxne : x ≠ 0)
    (hker : directionChartGap kFourDirection point.mass point.weight tree *ᵥ x = 0)
    (hpos : ∃ index, 0 < bundle index ⬝ᵥ x)
    (hneg : ∃ index, bundle index ⬝ᵥ x < 0) :
    KFourTreeAmplifiedSpanningExchangeData point tree := by
  obtain ⟨posIdx, negIdx, hne, hampPos, hampNeg⟩ := hmixed x hpos hneg
  obtain ⟨ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo, houtNe,
    htreeOne, htreeTwo, hampEq, houtOneEq, houtTwoEq⟩ :=
    htranslate x posIdx negIdx hne
  have hsquareOne : (kFourDirection outOne ⬝ᵥ x) ^ 2
      < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
    rw [houtOneEq, hampEq]
    exact hampPos
  have hsquareTwo : (kFourDirection outTwo ⬝ᵥ x) ^ 2
      < (kFourDirection ampLabel ⬝ᵥ x) ^ 2 := by
    rw [houtTwoEq, hampEq]
    exact hampNeg
  have hreadOne := dotProduct_exchangeGap_at_kernel
    kFourDirection point.mass point.weight houtOne hampOut hker
  have hreadTwo := dotProduct_exchangeGap_at_kernel
    kFourDirection point.mass point.weight houtTwo hampOut hker
  refine ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, htreeOne, htreeTwo, hsquareOne, hsquareTwo, hreadOne, hreadTwo, ?_⟩
  by_cases hquotOne : point.mass outOne / point.weight outOne
      ≤ point.mass ampLabel / point.weight ampLabel
  · exact Or.inl (exchangeGap_pos_at_kernel_of_le
      kFourDirection point.mass point.weight houtOne hampOut
      (point.mass_pos outOne) (point.weight_pos outOne) hker hsquareOne hquotOne)
  · have hreverseOne : point.mass ampLabel / point.weight ampLabel
        < point.mass outOne / point.weight outOne := lt_of_not_ge hquotOne
    by_cases hquotTwo : point.mass outTwo / point.weight outTwo
        ≤ point.mass ampLabel / point.weight ampLabel
    · exact Or.inr (Or.inl (exchangeGap_pos_at_kernel_of_le
        kFourDirection point.mass point.weight houtTwo hampOut
        (point.mass_pos outTwo) (point.weight_pos outTwo) hker hsquareTwo hquotTwo))
    · exact Or.inr (Or.inr ⟨hreverseOne, lt_of_not_ge hquotTwo⟩)

/-- Every weak-not-strict K4 vertex star has two genuine spanning-tree
exchanges carrying the exact amplified readings. -/
theorem kFourTreeAmplifiedSpanningExchangeData_of_star
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hstar : tree ∈ kFourStarList)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hnot : ¬ (directionChartGap kFourDirection point.mass point.weight
      tree).PosDef) :
    KFourTreeAmplifiedSpanningExchangeData point tree := by
  simp only [kFourStarList, List.mem_cons, List.not_mem_nil, or_false] at hstar
  rcases hstar with rfl | rfl | rfl | rfl
  · obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
      kFourStarA_kernel_readings_signMixed point hpsd hnot
    exact amplifiedSpanningExchange_of_bundle point {0, 1, 3}
      ![kFourDirection 0, kFourDirection 1, kFourDirection 3]
      (fun probe hp hn => exists_amplified_pair_of_signMixed hp hn)
      kFourStarA_bundle_translate_spanning hxne hker hpos hneg
  · obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
      kFourStarB_kernel_readings_signMixed point hpsd hnot
    exact amplifiedSpanningExchange_of_bundle point {0, 2, 4}
      ![kFourDirection 0, -kFourDirection 2, -kFourDirection 4]
      (fun probe hp hn => exists_amplified_pair_of_signMixed hp hn)
      kFourStarB_bundle_translate_spanning hxne hker hpos hneg
  · obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
      kFourStarC_kernel_readings_signMixed point hpsd hnot
    exact amplifiedSpanningExchange_of_bundle point {1, 2, 5}
      ![kFourDirection 1, kFourDirection 2, -kFourDirection 5]
      (fun probe hp hn => exists_amplified_pair_of_signMixed hp hn)
      kFourStarC_bundle_translate_spanning hxne hker hpos hneg
  · obtain ⟨x, hxne, hker, hpos, hneg⟩ :=
      kFourStarGauge_kernel_readings_signMixed point hpsd hnot
    exact amplifiedSpanningExchange_of_bundle point {3, 4, 5}
      ![kFourDirection 3, kFourDirection 4, kFourDirection 5]
      (fun probe hp hn => exists_amplified_pair_of_signMixed hp hn)
      kFourStarGauge_bundle_translate_spanning hxne hker hpos hneg

/-- Forget only the two tree-membership fields. -/
theorem kFourTreeAmplifiedExchangeData_of_spanning
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hdata : KFourTreeAmplifiedSpanningExchangeData point tree) :
    KFourTreeAmplifiedExchangeData point tree := by
  obtain ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, _, _, hsquareOne, hsquareTwo, hreadOne, hreadTwo, hsplit⟩ := hdata
  exact ⟨x, hxne, hker, ampLabel, outOne, outTwo, hampOut, houtOne, houtTwo,
    houtNe, hsquareOne, hsquareTwo, hreadOne, hreadTwo, hsplit⟩

/-! ## The exact spanning-exchange wall and registry joint -/

def KFourTreeStarSpanningExchangeWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarCorankWallData point tree ∧
  KFourTreeAmplifiedSpanningExchangeData point tree

def KFourWeakTreeStarSpanningExchangeWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarSpanningExchangeWallData point tree)

theorem kFourWeakTreeStarSpanningExchangeWallResidual_of_starWallResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarWallResidual point) :
    KFourWeakTreeStarSpanningExchangeWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar,
      kFourTreeAmplifiedSpanningExchangeData_of_star point hstar.1 hgap
        (not_posDef_of_kFourTreeWindowData point hwindow)⟩⟩

theorem kFourWeakTreeStarWallResidual_of_spanningExchangeWallResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarSpanningExchangeWallResidual point) :
    KFourWeakTreeStarWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr hstar.1⟩

theorem kFourWeakTreeStarSpanningExchangeWallResidual_iff_starWallResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeStarSpanningExchangeWallResidual point ↔
      KFourWeakTreeStarWallResidual point :=
  ⟨kFourWeakTreeStarWallResidual_of_spanningExchangeWallResidual point,
    kFourWeakTreeStarSpanningExchangeWallResidual_of_starWallResidual point⟩

/-- **THE SPANNING-EXCHANGE A3 JOINT.**  Both amplified exchanges now belong
to the registry's sixteen-tree family, rather than merely being card-three
selections with a positive reading on one probe. -/
noncomputable def KFourKnifeBandRefinedTreeStarSpanningExchangeWallWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarSpanningExchangeWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarSpanningExchangeWall_iff_starWall :
    KFourKnifeBandRefinedTreeStarSpanningExchangeWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarWallWeakToStrict := by
  constructor
  · intro hspan point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hspan point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarSpanningExchangeWallResidual_of_starWallResidual point hwitness)
  · intro hwall point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hwall point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarWallResidual_of_spanningExchangeWallResidual point hwitness)

theorem kFourKnifeBandRefinedTreeStarSpanningExchangeWall_iff :
    KFourKnifeBandRefinedTreeStarSpanningExchangeWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarSpanningExchangeWall_iff_starWall.trans
    kFourKnifeBandRefinedTreeStarWall_iff

theorem kFourFamilySelection_iff_treeStarSpanningExchangeWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarSpanningExchangeWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarWall.trans
    kFourKnifeBandRefinedTreeStarSpanningExchangeWall_iff_starWall.symm

end Gtz
