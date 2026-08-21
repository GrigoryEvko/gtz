/-
# Every one-inside triple at a corner is a depth-two downdate of a corner superset

The ten refusals that a tie owes at a corank-two corner are the complement triple
and the nine triples built from one inside atom and two outside atoms.  This
module shows that the nine are not nine independent objects: they are THREE
forms, each downdated by TWO inside atoms.

For an outside label `d`, erase it from the universe.  The result contains the
whole corner, so its gap `F_d := S_{univ \ d} − 1` is positive semidefinite
(`Gtz.corner_erase_gap_posSemidef`) — a corner gap is `lam·u uᵀ`, and adding
atoms to a positive semidefinite form keeps it so.  And for every inside atom
`e`,

  `S_{{e} ∪ Cᶜ \ d} − 1  =  F_d − ∑_{c ∈ C, c ≠ e} g_c g_cᵀ`

(`Gtz.corner_oneInside_gap_eq_erase_downdate`), because the two index sets
partition `univ \ d`.  At `C.card = 3` the correction is exactly two atoms, so
each of the nine triples is a DEPTH-TWO DOWNDATE of one of the three erased
gaps, and the landed depth-two criterion turns each refusal into one reading and
one two-by-two determinant in the metric of `F_d`.

## Why this is the right frame for the corner

* `F_d` is a corner superset, so it is positive semidefinite for free and its
  determinant is nonnegative for free.  The four-set gaps `A_y`, `A_z` that the
  cell system uses have NEITHER property: `A_z` is exactly the one that fails.
* The three `F_d` do not depend on which inside atom anchors the triple, so the
  three refusals of a star and the three refusals of a five-set are the SAME
  nine numbers read two different ways.  The cell dichotomy `A_y ≻ 0`,
  `A_z ⊁ 0` disappears from the statement.
* At a `Z1` corner the downdated pair for the `y`-anchored triple is `(g_x, g_z)`
  and `g_x` is a UNIT vector orthogonal to `g_z`
  (`Gtz.zeroAxis_leverage_eq_one`, `Gtz.zeroAxis_orthogonal`), so the pair the
  criterion reads is half pinned before any chart.

[MEASURED in quad precision over 156421 exact `Z1` corners of the closed-form
chart of `scratchpad/NOTES-cellh.txt`, three erased gaps each:
the downdate identity holds to a relative `3.5e-33`; the erased gap determinant
equals `lam` times the squared bracket of the axis with the two surviving
outside atoms, to a relative `1.6e-20`; and all 469263 erased gaps are positive
definite, the smallest eigenvalue never dropping below `1.2e-15` of the matrix
scale.]
-/
import Gtz.Wave.OutsideFrameMomentLadder
import Gtz.LinAlg.DepthTwoDowndate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The partition of the erased universe -/

/-- The one-inside triple through `e` and the other two inside atoms partition
the universe with `d` erased. -/
theorem corner_erase_partition {C : Finset (Fin m)} {e d : Fin m} (he : e ∈ C)
    (hd : d ∉ C) :
    insert e ((Cᶜ : Finset (Fin m)).erase d) ∪ C.erase e
      = (univ : Finset (Fin m)).erase d := by
  ext a
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
    Finset.mem_compl, Finset.mem_univ, and_true]
  constructor
  · rintro ((rfl | ⟨hane, haC⟩) | ⟨hane, haC⟩)
    · exact fun hcon => hd (hcon ▸ he)
    · exact hane
    · exact fun hcon => hd (hcon ▸ haC)
  · intro hane
    by_cases haC : a ∈ C
    · by_cases hae : a = e
      · exact Or.inl (Or.inl hae)
      · exact Or.inr ⟨hae, haC⟩
    · exact Or.inl (Or.inr ⟨hane, haC⟩)

/-- The two parts of the partition are disjoint. -/
theorem corner_erase_disjoint {C : Finset (Fin m)} {e d : Fin m} :
    Disjoint (insert e ((Cᶜ : Finset (Fin m)).erase d)) (C.erase e) := by
  refine Finset.disjoint_left.mpr fun a ha hb => ?_
  rcases Finset.mem_insert.mp ha with rfl | hac
  · exact (Finset.notMem_erase a C) hb
  · exact (Finset.mem_compl.mp (Finset.mem_of_mem_erase hac))
      (Finset.mem_of_mem_erase hb)

/-- **THE ONE-INSIDE TRIPLE IS AN ERASED-UNIVERSE DOWNDATE.**  The gap of
`{e} ∪ Cᶜ \ {d}` is the gap of `univ \ {d}` less the atoms of the other members
of `C`.  No corner hypothesis: this is the partition, nothing more. -/
theorem corner_oneInside_gap_eq_erase_downdate (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) :
    subsetSum D (insert e ((Cᶜ : Finset (Fin m)).erase d)) - 1
      = (subsetSum D ((univ : Finset (Fin m)).erase d) - 1)
        - ∑ c ∈ C.erase e, atomMatrix (D.atom c) := by
  have hsplit : subsetSum D ((univ : Finset (Fin m)).erase d)
      = subsetSum D (insert e ((Cᶜ : Finset (Fin m)).erase d))
        + ∑ c ∈ C.erase e, atomMatrix (D.atom c) := by
    rw [← corner_erase_partition he hd, subsetSum,
      Finset.sum_union corner_erase_disjoint, ← subsetSum]
  rw [hsplit]
  abel

/-! ## 2. The erased gap is a corner superset -/

/-- **THE ERASED GAP IS POSITIVE SEMIDEFINITE.**  Erasing an OUTSIDE label from
the universe leaves a superset of the corner. -/
theorem corner_erase_gap_posSemidef (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {d : Fin m} (hd : d ∉ C) :
    (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).PosSemidef := by
  refine corner_superset_gap_posSemidef D ?_ hlam hgap
  intro a haC
  exact Finset.mem_erase.mpr ⟨fun hcon => hd (hcon ▸ haC), Finset.mem_univ a⟩

/-- **THE ERASED GAP IS POSITIVE DEFINITE EXACTLY WHEN IT IS NONSINGULAR.** -/
theorem corner_erase_gap_posDef_of_det_ne_zero (D : WeightedDesign m 3)
    {C : Finset (Fin m)} {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {d : Fin m} (hd : d ∉ C)
    (hne : (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).det ≠ 0) :
    (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).PosDef :=
  (corner_erase_gap_posSemidef D hlam hgap hd).posDef_iff_det_ne_zero.mpr hne

/-- **THE ERASED GAP HAS NONNEGATIVE DETERMINANT.** -/
theorem corner_erase_gapDet_nonneg (D : WeightedDesign m 3) {C : Finset (Fin m)}
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) {d : Fin m} (hd : d ∉ C) :
    0 ≤ (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).det :=
  (corner_erase_gap_posSemidef D hlam hgap hd).det_nonneg

/-! ## 3. Depth two at a corner triple -/

/-- The corner triple less one of its members is the pair of the other two. -/
theorem cornerTriple_erase_eq_pair {x y z : Fin m} (hxy : x ≠ y) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Fin m)).erase y = {x, z} := by
  ext a
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hane, rfl | rfl | rfl⟩
    · exact Or.inl rfl
    · exact absurd rfl hane
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hxy, Or.inl rfl⟩
    · exact ⟨fun h => hyz h.symm, Or.inr (Or.inr rfl)⟩

/-- **THE `y`-ANCHORED TRIPLE IS A DEPTH-TWO DOWNDATE.**  The gap of
`{y} ∪ Cᶜ \ {d}` is the erased gap less the atoms of `x` and `z`. -/
theorem corner_yTriple_gap_eq_depthTwo (D : WeightedDesign m 3) {x y z d : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : d ∉ ({x, y, z} : Finset (Fin m))) :
    subsetSum D (insert y ((({x, y, z} : Finset (Fin m))ᶜ).erase d)) - 1
      = (subsetSum D ((univ : Finset (Fin m)).erase d) - 1)
        - Matrix.vecMulVec (D.atom x) (D.atom x)
        - Matrix.vecMulVec (D.atom z) (D.atom z) := by
  have hy : y ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have h := corner_oneInside_gap_eq_erase_downdate D hy hd
  rw [cornerTriple_erase_eq_pair hxy hyz] at h
  rw [h, Finset.sum_insert (by simp [hxz]), Finset.sum_singleton]
  simp only [atomMatrix]
  abel

/-- **THE `y`-ANCHORED REFUSAL, READ IN THE ERASED GAP.**  When the erased gap is
positive definite, the triple `{y} ∪ Cᶜ \ {d}` fails exactly when the pair
`(g_x, g_z)` saturates the depth-two criterion in that metric. -/
theorem corner_yTriple_not_posDef_iff_readings (D : WeightedDesign m 3)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : d ∉ ({x, y, z} : Finset (Fin m)))
    (hF : (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).PosDef) :
    ¬ (subsetSum D (insert y ((({x, y, z} : Finset (Fin m))ᶜ).erase d)) - 1).PosDef
      ↔ 1 ≤ D.atom x ⬝ᵥ
            ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom x)
        ∨ (1 - D.atom x ⬝ᵥ
              ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom x))
            * (1 - D.atom z ⬝ᵥ
              ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom z))
          ≤ (D.atom x ⬝ᵥ
              ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹
                *ᵥ D.atom z)) ^ 2 := by
  rw [corner_yTriple_gap_eq_depthTwo D hxy hxz hyz hd]
  exact not_posDef_sub_two_vecMulVec_iff _ hF (D.atom x) (D.atom z)

/-- **THE `y`-ANCHORED PRODUCER.**  Two strict readings at the erased gap give a
strictly dominating triple. -/
theorem corner_yTriple_posDef_of_readings (D : WeightedDesign m 3)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : d ∉ ({x, y, z} : Finset (Fin m)))
    (hF : (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).PosDef)
    (hfirst : D.atom x ⬝ᵥ
        ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom x) < 1)
    (hdet : (D.atom x ⬝ᵥ
          ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        < (1 - D.atom x ⬝ᵥ
            ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom x))
          * (1 - D.atom z ⬝ᵥ
            ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom z))) :
    (subsetSum D (insert y ((({x, y, z} : Finset (Fin m))ᶜ).erase d)) - 1).PosDef := by
  rw [corner_yTriple_gap_eq_depthTwo D hxy hxz hyz hd]
  exact (posDef_sub_two_vecMulVec_iff _ hF (D.atom x) (D.atom z)).mpr ⟨hfirst, hdet⟩

/-- **THE SECOND READING IS FREE.**  If the `y`-anchored triple dominates then
the third inside atom also reads the erased gap below one. -/
theorem corner_yTriple_second_reading_lt_one (D : WeightedDesign m 3)
    {x y z d : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : d ∉ ({x, y, z} : Finset (Fin m)))
    (hF : (subsetSum D ((univ : Finset (Fin m)).erase d) - 1).PosDef)
    (hPD : (subsetSum D
      (insert y ((({x, y, z} : Finset (Fin m))ᶜ).erase d)) - 1).PosDef) :
    D.atom z ⬝ᵥ
      ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)⁻¹ *ᵥ D.atom z) < 1 := by
  rw [corner_yTriple_gap_eq_depthTwo D hxy hxz hyz hd] at hPD
  exact second_reading_lt_one_of_posDef_sub_two _ hF (D.atom x) (D.atom z) hPD

/-! ## 4. The `Z1` reading of the pair -/

/-- **AT A `Z1` CORNER THE DOWNDATED PAIR IS HALF PINNED.**  The pair the
`y`-anchored criterion reads is `(g_x, g_z)`, and `g_x` is a unit vector
orthogonal to `g_z`.  The criterion therefore reads a pair whose EUCLIDEAN Gram
is `diag(1, |g_z|²)` — only the metric of the erased gap is free. -/
theorem zeroAxis_downdated_pair_gram (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x z : Fin m} (hx : x ∈ C) (hz : z ∈ C) (hxz : x ≠ z)
    (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ D.atom x = 1 ∧ D.atom x ⬝ᵥ D.atom z = 0 :=
  ⟨zeroAxis_leverage_eq_one D C hcard hlam hunit hgap hx hax,
    zeroAxis_orthogonal D C hcard hlam hunit hgap hx hz hxz hax⟩

/-- **THE TIE REFUSES EVERY ERASED-GAP DOWNDATE.**  At a corner, a tie turns the
nine one-inside refusals into nine depth-two refusals of the three erased
gaps. -/
theorem isTie_erase_downdate_not_posDef (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hC : C.card = 3)
    (hcompl : (Cᶜ : Finset (Fin m)).card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (htie : IsTie D) {e d : Fin m} (he : e ∈ C) (hd : d ∈ (Cᶜ : Finset (Fin m))) :
    ¬ ((subsetSum D ((univ : Finset (Fin m)).erase d) - 1)
        - ∑ c ∈ C.erase e, atomMatrix (D.atom c)).PosDef := by
  have hdC : d ∉ C := Finset.mem_compl.mp hd
  rw [← corner_oneInside_gap_eq_erase_downdate D he hdC]
  exact isTie_oneInside_not_posDef D hC hcompl hlam hgap htie he hd

end Gtz
