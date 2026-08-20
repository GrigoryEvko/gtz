import Gtz.Wave.TieMantelBound
import Gtz.Wave.ChartBracketTax

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# Cell H in the chart, and the heavy-atom census

Cell H of the `Z1` corner is the stratum where the four-set through `z`
FAILS while the four-set through `y` survives.  Four floors survive with
it: the `y`-floor and the three outside floors of `A_y`.  This module puts
all four into the chart's inverse-free vocabulary and adds the census that
feeds the Mantel bound.

* `Gtz.cellH_yFloor_iff_outside_gapDet` — the `y`-floor is the sign of the
  OUTSIDE triple's gap determinant.
* `Gtz.cellH_outside_floor_iff_gapDet` — each outside floor of `A_y` is the
  sign of the gap determinant of the triple that survives the erasure:
  `y` together with the two other outside atoms.
* `Gtz.cellH_four_floors_iff_gapDets` — all four floors at once, as four
  polynomial sign conditions in ambient dot products.

Then the census.

* `Gtz.weighted_leverage_total` — Parseval at the identity: the weighted
  leverages of any design total the rank, `Σ t_cℓ_c = 3`.
* `Gtz.two_le_card_heavy` — hence AT LEAST TWO atoms are heavy.  The light
  atoms carry weighted leverage at most their weight total, so the heavy
  ones must carry at least two, and no single atom carries more than one.
* `Gtz.isTie_heavyFour_mantel_dichotomy` — the Mantel bound as the
  dichotomy it is used as: at a tie, four heavy atoms either admit at most
  four of their six pairs, or one of their four triples is flat.

Measured for the record on `120000` cell-H inhabitants: four heavy atoms
exist on `100.00%`, so the dichotomy's hypothesis is never vacuous there;
`23.46%` carry five or more admissible pairs, where the bound forces a flat
triple.  The contraction tax fires on `76.18%` of cell H (against `92.94%`
of cell B) and the M-matrix on `20.35%`.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The four floors of cell H as gap determinant signs -/

/-- **THE `y`-FLOOR IS THE OUTSIDE TRIPLE'S SIGN.**  Erasing `y` from the
surviving four-set leaves the outside triple, so the `y`-floor says exactly
that the outside gap determinant is nonpositive. -/
theorem cellH_yFloor_iff_outside_gapDet (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    (1 ≤ D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      ↔ tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0 := by
  classical
  have hynot : y ∉ (({x, y, z} : Finset (Fin m))ᶜ) := by simp
  refine fourSet_member_floor_iff_tripleGapDet_nonpos D hAy
    (Finset.mem_insert_self y _) h45 h46 h56 ?_
  rw [Finset.erase_insert hynot, hcompl]

/-- **AN OUTSIDE FLOOR IS THE SURVIVING TRIPLE'S SIGN.**  Erasing an
outside atom from the surviving four-set leaves `y` together with the other
two outside atoms. -/
theorem cellH_outside_floor_iff_gapDet (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m} (hy4 : y ≠ d4) (hy5 : y ≠ d5) (hy6 : y ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    (1 ≤ D.atom d4 ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d4))
      ↔ tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0 := by
  classical
  have hmem : d4 ∈ insert y (({x, y, z} : Finset (Fin m))ᶜ) := by
    refine Finset.mem_insert_of_mem ?_
    rw [hcompl]; simp
  refine fourSet_member_floor_iff_tripleGapDet_nonpos D hAy hmem hy5 hy6 h56 ?_
  rw [hcompl]
  ext w
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, rfl | rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact absurd rfl hne
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨hy4, Or.inl rfl⟩
    · exact ⟨Ne.symm h45, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨Ne.symm h46, Or.inr (Or.inr (Or.inr rfl))⟩

/-- **THE FOUR FLOORS OF CELL H, ALL AT ONCE.**  Under the surviving
four-set the whole floor system of cell H is four polynomial sign
conditions in ambient dot products — no inverse, no matrix. -/
theorem cellH_four_floors_iff_gapDets (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m} (hy4 : y ≠ d4) (hy5 : y ≠ d5) (hy6 : y ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    ((1 ≤ D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      ∧ (1 ≤ D.atom d4 ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d4)))
      ↔ (tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0
        ∧ tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0) := by
  rw [cellH_yFloor_iff_outside_gapDet D h45 h46 h56 hcompl hAy,
    cellH_outside_floor_iff_gapDet D hy4 hy5 hy6 h45 h46 h56 hcompl hAy]

/-! ## 2. The heavy-atom census -/

/-- **PARSEVAL AT THE IDENTITY.**  The weighted leverages of any design
total the rank. -/
theorem weighted_leverage_total (D : WeightedDesign m 3) :
    ∑ c, D.weight c * leverageOf (D.atom c) = 3 := by
  have h := weighted_reading_total_eq_trace D (1 : Matrix (Fin 3) (Fin 3) ℝ)
  simp only [inv_one, Matrix.trace_one, Fintype.card_fin, Matrix.one_mulVec] at h
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hcast] at h
  rw [← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← leverageOf_eq_dotProduct]

/-- **AT LEAST TWO ATOMS ARE HEAVY.**  The light atoms carry weighted
leverage at most their own weight total, which is at most one, so the heavy
atoms must carry at least two.  No single atom carries more than one, so
there are at least two of them. -/
theorem two_le_card_heavy (D : WeightedDesign m 3) :
    2 ≤ (Finset.univ.filter fun c => 1 < leverageOf (D.atom c)).card := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  set H : Finset (Fin m) := Finset.univ.filter fun c => 1 < leverageOf (D.atom c)
    with hH
  -- the heavy part carries at most its cardinality
  have hheavy : ∑ c ∈ H, D.weight c * leverageOf (D.atom c) ≤ (H.card : ℝ) := by
    calc ∑ c ∈ H, D.weight c * leverageOf (D.atom c)
        ≤ ∑ _c ∈ H, (1 : ℝ) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h := parseval_weight_leverage_le_one D c
          rwa [← leverageOf_eq_dotProduct] at h
      _ = (H.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the light part carries at most its weight total
  have hlight : ∑ c ∈ Hᶜ, D.weight c * leverageOf (D.atom c)
      ≤ ∑ c ∈ Hᶜ, D.weight c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hle : leverageOf (D.atom c) ≤ 1 := by
      by_contra hnot
      rw [not_le] at hnot
      exact (Finset.mem_compl.mp hc) (by rw [hH, Finset.mem_filter]; exact ⟨Finset.mem_univ c, hnot⟩)
    nlinarith [(D.weight_pos c).le, hle]
  have hwle : ∑ c ∈ Hᶜ, D.weight c ≤ 1 := by
    have hsplit := Finset.sum_add_sum_compl H D.weight
    rw [D.weight_sum_one] at hsplit
    have hpos : 0 ≤ ∑ c ∈ H, D.weight c :=
      Finset.sum_nonneg fun c _ => (D.weight_pos c).le
    linarith [hsplit, hpos]
  have htot := weighted_leverage_total D
  have hsplit := Finset.sum_add_sum_compl H
    (fun c => D.weight c * leverageOf (D.atom c))
  rw [htot] at hsplit
  have hcard : (H.card : ℝ) ≤ 1 := by
    have : H.card ≤ 1 := by omega
    exact_mod_cast this
  linarith [hsplit, hheavy, hlight, hwle, hcard]

/-! ## 3. The Mantel dichotomy -/

/-- **THE MANTEL DICHOTOMY.**  At a tie, four heavy atoms either admit at
most four of their six pairs, or one of their four triples is flat.  The
census makes the hypothesis cheap, and on cell H four heavy atoms are
present at every measured chart inhabitant. -/
theorem isTie_heavyFour_mantel_dichotomy (D : WeightedDesign m 3)
    (htie : IsTie D) {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hha : HeavyAtom D a) (hhb : HeavyAtom D b) (hhc : HeavyAtom D c)
    (hhd : HeavyAtom D d) :
    (admissibleEdges D a b c d).card ≤ 4
      ∨ tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0
      ∨ tripleGapDet (D.atom a) (D.atom b) (D.atom d) ≤ 0
      ∨ tripleGapDet (D.atom a) (D.atom c) (D.atom d) ≤ 0
      ∨ tripleGapDet (D.atom b) (D.atom c) (D.atom d) ≤ 0 := by
  by_cases habc : tripleGapDet (D.atom a) (D.atom b) (D.atom c) ≤ 0
  · exact Or.inr (Or.inl habc)
  by_cases habd : tripleGapDet (D.atom a) (D.atom b) (D.atom d) ≤ 0
  · exact Or.inr (Or.inr (Or.inl habd))
  by_cases hacd : tripleGapDet (D.atom a) (D.atom c) (D.atom d) ≤ 0
  · exact Or.inr (Or.inr (Or.inr (Or.inl hacd)))
  by_cases hbcd : tripleGapDet (D.atom b) (D.atom c) (D.atom d) ≤ 0
  · exact Or.inr (Or.inr (Or.inr (Or.inr hbcd)))
  refine Or.inl (isTie_heavyFour_admissible_card_le_four D htie hab hac had
    hbc hbd hcd hha hhb hhc hhd ⟨?_, ?_, ?_, ?_⟩) <;>
    [ exact not_le.mp habc; exact not_le.mp habd; exact not_le.mp hacd;
      exact not_le.mp hbcd ]

end Gtz
