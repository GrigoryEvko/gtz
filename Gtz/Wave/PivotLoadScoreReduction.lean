import Gtz.Design.LoadBearingTriple
import Gtz.Design.SharedAtomPivotExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The aggregate pivot-load reduction

`Gtz.posDef_subsetSum_of_card_pivot_univ_ge_one` closes a rank-sized
selection when each selected label has full-selection pivot at least one.  The
proof actually spends only the SUM of those pointwise inequalities.

For a label `c`, define its pivot load by

  `(1 - weight c) * pivot c + weight c`.

The loads sum to `rank + 1`.  A rank-sized selection is positive definite as
soon as its selected load reaches `rank`.  This strictly extends the
pointwise-high theorem: labels below unit pivot may be admitted when another
selected label pays the deficit.

At `(6,3)` this gives a compact universal residue.  If no strict triple exists,
then every triple has load strictly below three, at most two labels have pivot
at least one, and at least four labels have pivot strictly below one.  Every
future stratum argument may start from those three scalar facts.
-/

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The load and its conservation law -/

/-- The full-selection load carried by one label. -/
noncomputable def pivotLoadScore (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  (1 - D.weight c) * pivot D Finset.univ c + D.weight c

/-- **THE LOAD CONSERVATION LAW.**  Pivot load sums to rank plus total weight,
hence to `rank + 1` for a weighted design. -/
theorem sum_pivotLoadScore (D : WeightedDesign m k) (hm : 2 ≤ m) :
    ∑ c, pivotLoadScore D c = (k : ℝ) + 1 := by
  rw [show (∑ c, pivotLoadScore D c) =
      (∑ c, (1 - D.weight c) * pivot D Finset.univ c) + ∑ c, D.weight c by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ => rfl,
    sum_deficiency_mul_pivot_univ D hm, D.weight_sum_one]

/-- The co-weight-scaled residual diagonal.  In the normalized projection
picture this is the diagonal of `I - T - P`. -/
noncomputable def scaledResidualDiag (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  (1 - D.weight c) * (1 - pivot D Finset.univ c)

/-- Load and scaled residual are pointwise complementary. -/
theorem pivotLoadScore_add_scaledResidualDiag (D : WeightedDesign m k) (c : Fin m) :
    pivotLoadScore D c + scaledResidualDiag D c = 1 := by
  simp only [pivotLoadScore, scaledResidualDiag]
  ring

/-- At `(6,3)` the scaled residual diagonal is exactly the residual pairing
diagonal in co-weight units. -/
theorem scaledResidualDiag_eq_coweight_mul_residualPairing_diag
    (D : WeightedDesign 6 3) (c : Fin 6) :
    scaledResidualDiag D c = (1 - D.weight c) * residualPairing D c c := by
  rw [scaledResidualDiag, residualPairing_diag]

/-- **THE SCALED RESIDUAL TRACE.**  At `(6,3)` the normalized residual matrix
has trace two. -/
theorem sum_scaledResidualDiag_eq_two (D : WeightedDesign 6 3) :
    ∑ c, scaledResidualDiag D c = 2 := by
  have hload := sum_pivotLoadScore D (by norm_num)
  have hpoint : ∀ c : Fin 6, scaledResidualDiag D c = 1 - pivotLoadScore D c := by
    intro c
    linarith [pivotLoadScore_add_scaledResidualDiag D c]
  rw [Finset.sum_congr rfl fun c _ => hpoint c, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul] at *
  norm_num at hload ⊢
  linarith

/-- If a selection carries load at least the rank, its complement's
deficiency-weighted pivot budget is paid by the selected weight. -/
theorem sum_deficiency_mul_pivot_compl_le_of_loadScore
    (D : WeightedDesign m k) (hm : 2 ≤ m) (B : Finset (Fin m))
    (hload : (k : ℝ) ≤ ∑ c ∈ B, pivotLoadScore D c) :
    ∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c
      ≤ ∑ c ∈ B, D.weight c := by
  have htotal := sum_deficiency_mul_pivot_univ D hm
  have hsplit :
      (∑ c ∈ B, (1 - D.weight c) * pivot D Finset.univ c)
          + ∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c = (k : ℝ) := by
    rw [Finset.sum_add_sum_compl B
      (fun c => (1 - D.weight c) * pivot D Finset.univ c)]
    exact htotal
  have hselected : ∑ c ∈ B, pivotLoadScore D c =
      (∑ c ∈ B, (1 - D.weight c) * pivot D Finset.univ c)
        + ∑ c ∈ B, D.weight c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hselected] at hload
  linarith

/-! ## 2. Aggregate load produces a positive-definite selection -/

/-- **THE AGGREGATE LOAD-BEARING SELECTION.**  A rank-sized selection is
positive definite when its total pivot load reaches the rank.  This is the
sum-level form of `posDef_subsetSum_of_card_pivot_univ_ge_one`; it allows some
selected pivots below one when other selected labels compensate.

The two-label clearance hypothesis `k + 2 ≤ m` is sharp for this proof: after
fixing one omitted label, another positive-weight omitted label makes the
selected weight strictly smaller than that label's deficiency. -/
theorem posDef_subsetSum_of_pivotLoadScore_sum_ge_rank
    (D : WeightedDesign m k) (hm : k + 2 ≤ m) (B : Finset (Fin m))
    (hcard : B.card = k)
    (hload : (k : ℝ) ≤ ∑ c ∈ B, pivotLoadScore D c) :
    (subsetSum D B - 1).PosDef := by
  have hm2 : 2 ≤ m := by omega
  have hK := posDef_fullExcess D hm2
  have hbudget : ∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c
      ≤ ∑ c ∈ B, D.weight c :=
    sum_deficiency_mul_pivot_compl_le_of_loadScore D hm2 B hload
  have hstrict : ∀ c ∈ Bᶜ, ∑ j ∈ B, D.weight j < 1 - D.weight c := by
    intro c hc
    have hcB : c ∉ B := Finset.mem_compl.mp hc
    have hins : ∑ j ∈ insert c B, D.weight j =
        D.weight c + ∑ j ∈ B, D.weight j := Finset.sum_insert hcB
    have hcard' : (insert c B).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hcB, hcard]
    obtain ⟨e, he⟩ : ∃ e, e ∉ insert c B := by
      by_contra hcon
      push Not at hcon
      have huniv : insert c B = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard'
      omega
    have hlt : ∑ j ∈ insert c B, D.weight j < ∑ j ∈ Finset.univ, D.weight j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ e) he
        (D.weight_pos e) (fun j _ _ => (D.weight_pos j).le)
    rw [D.weight_sum_one, hins] at hlt
    linarith
  have hmain : ∀ y : Fin m → ℝ, (∃ c ∈ Bᶜ, y c ≠ 0) →
      0 < designComplementForm D Bᶜ y := by
    intro y hy
    have hQnn : 0 ≤ ∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c) :=
      Finset.sum_nonneg fun c _ =>
        div_nonneg (sq_nonneg _) (deficiency_pos D hm2 c).le
    have hsnn : 0 ≤ ∑ j ∈ B, D.weight j :=
      Finset.sum_nonneg fun j _ => (D.weight_pos j).le
    have hfa : ∀ q : Fin k → ℝ,
        (complementCombination D Bᶜ y ⬝ᵥ q) ^ 2
          ≤ ((∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * ∑ j ∈ B, D.weight j)
            * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by
      intro q
      have henergy : 0 ≤ q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q) := by
        rcases eq_or_ne q 0 with rfl | hq
        · simp
        · have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hK).2 hq
          simpa only [star_trivial] using hpos.le
      rw [dotProduct_complementCombination]
      calc
        (∑ c ∈ Bᶜ, y c * (D.atom c ⬝ᵥ q)) ^ 2
            ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
                * ∑ c ∈ Bᶜ, (1 - D.weight c) * (D.atom c ⬝ᵥ q) ^ 2 :=
              sq_sum_mul_le_weighted Bᶜ y (fun c => D.atom c ⬝ᵥ q)
                (fun c => 1 - D.weight c) (fun c _ => deficiency_pos D hm2 c)
        _ ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
                * ((∑ c ∈ Bᶜ, (1 - D.weight c) * pivot D Finset.univ c)
                  * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q))) :=
              mul_le_mul_of_nonneg_left
                (sum_deficiency_mul_sq_reading_le D hm2 Bᶜ q) hQnn
        _ ≤ (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c))
                * ((∑ j ∈ B, D.weight j)
                  * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q))) := by
              refine mul_le_mul_of_nonneg_left ?_ hQnn
              exact mul_le_mul_of_nonneg_right hbudget henergy
        _ = ((∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * ∑ j ∈ B, D.weight j)
                * (q ⬝ᵥ ((subsetSum D Finset.univ - 1) *ᵥ q)) := by ring
    have hbound := inverseForm_le_of_forall_sq_le hK (complementCombination D Bᶜ y)
      (mul_nonneg hQnn hsnn) hfa
    have hgap : (∑ c ∈ Bᶜ, y c ^ 2 / (1 - D.weight c)) * (∑ j ∈ B, D.weight j)
        < ∑ c ∈ Bᶜ, y c ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_lt_sum (fun c hc => ?_) ?_
      · have hd := deficiency_pos D hm2 c
        have hs := (hstrict c hc).le
        rw [div_mul_eq_mul_div, div_le_iff₀ hd]
        nlinarith [sq_nonneg (y c)]
      · obtain ⟨c, hc, hyc⟩ := hy
        refine ⟨c, hc, ?_⟩
        have hd := deficiency_pos D hm2 c
        have hlt := hstrict c hc
        have hy2 : 0 < y c ^ 2 := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
        nlinarith
    rw [designComplementForm]
    linarith
  have hres := (posDef_complementGap_iff_designComplementForm_pos D Bᶜ hK).mpr hmain
  rwa [compl_compl] at hres

/-- The pointwise high-pivot theorem is an immediate special case of the
aggregate theorem. -/
theorem posDef_subsetSum_of_pivot_ge_one_via_loadScore
    (D : WeightedDesign m k) (hm : k + 2 ≤ m) (B : Finset (Fin m))
    (hcard : B.card = k) (hhigh : ∀ c ∈ B, 1 ≤ pivot D Finset.univ c) :
    (subsetSum D B - 1).PosDef := by
  apply posDef_subsetSum_of_pivotLoadScore_sum_ge_rank D hm B hcard
  calc
    (k : ℝ) = ∑ _c ∈ B, (1 : ℝ) := by
      simp [hcard]
    _ ≤ ∑ c ∈ B, pivotLoadScore D c := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hd := deficiency_pos D (by omega) c
      dsimp only [pivotLoadScore]
      nlinarith [hhigh c hc]

/-! ## 3. The exact `(6,3)` no-strict residue -/

/-- In a no-strict `(6,3)` design every triple carries load strictly below
three.  Equality is already enough to produce a strict winner. -/
theorem sum_pivotLoadScore_lt_three_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∑ c ∈ selected, pivotLoadScore D c < 3 := by
  by_contra hge
  push Not at hge
  exact hnoStrict selected hcard
    (posDef_subsetSum_of_pivotLoadScore_sum_ge_rank D (by norm_num) selected hcard hge)

/-- The complementary half of the load window.  Applying the strict upper
bound to the complementary triple and spending total load four forces every
triple's own load above one. -/
theorem one_lt_sum_pivotLoadScore_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    1 < ∑ c ∈ selected, pivotLoadScore D c := by
  have hcomplCard : selectedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hcompl := sum_pivotLoadScore_lt_three_of_noStrict D hnoStrict selectedᶜ hcomplCard
  have hsplit := Finset.sum_add_sum_compl selected (pivotLoadScore D)
  have htotal := sum_pivotLoadScore D (by norm_num)
  rw [htotal] at hsplit
  norm_num at hsplit
  linarith

/-- **THE NO-STRICT LOAD WINDOW.**  Every triple in an unresolved `(6,3)`
design carries total load strictly between one and three. -/
theorem triple_pivotLoadScore_mem_Ioo_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∑ c ∈ selected, pivotLoadScore D c ∈ Set.Ioo (1 : ℝ) 3 :=
  ⟨one_lt_sum_pivotLoadScore_of_noStrict D hnoStrict selected hcard,
    sum_pivotLoadScore_lt_three_of_noStrict D hnoStrict selected hcard⟩

/-- On a card-three set, scaled residual trace is three minus pivot load. -/
theorem sum_scaledResidualDiag_eq_three_sub_load
    (D : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    ∑ c ∈ selected, scaledResidualDiag D c
      = 3 - ∑ c ∈ selected, pivotLoadScore D c := by
  have hpoint : ∀ c : Fin 6, scaledResidualDiag D c = 1 - pivotLoadScore D c := by
    intro c
    linarith [pivotLoadScore_add_scaledResidualDiag D c]
  rw [Finset.sum_congr rfl fun c _ => hpoint c, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, hcard]
  norm_num

/-- **THE NO-STRICT RESIDUAL TRACE WINDOW.**  Every principal three-label
diagonal trace of the normalized residual matrix lies strictly between zero
and two.  This is stronger than the global trace and survives every stratum. -/
theorem triple_scaledResidualDiag_mem_Ioo_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∑ c ∈ selected, scaledResidualDiag D c ∈ Set.Ioo (0 : ℝ) 2 := by
  rw [sum_scaledResidualDiag_eq_three_sub_load D selected hcard]
  have hwindow := triple_pivotLoadScore_mem_Ioo_of_noStrict D hnoStrict selected hcard
  constructor <;> linarith [hwindow.1, hwindow.2]

/-- The labels with full-selection pivot at least one. -/
noncomputable def highPivotLabels (D : WeightedDesign 6 3) : Finset (Fin 6) :=
  Finset.univ.filter fun c => 1 ≤ pivot D Finset.univ c

/-- The labels with full-selection pivot strictly below one. -/
noncomputable def lowPivotLabels (D : WeightedDesign 6 3) : Finset (Fin 6) :=
  Finset.univ.filter fun c => pivot D Finset.univ c < 1

/-- The high and low pivot sets are exact complements. -/
theorem lowPivotLabels_eq_compl_highPivotLabels (D : WeightedDesign 6 3) :
    lowPivotLabels D = (highPivotLabels D)ᶜ := by
  ext c
  simp only [lowPivotLabels, highPivotLabels, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_compl, not_le]

/-- **NO-STRICT LEAVES AT MOST TWO HIGH PIVOTS.**  Three high-pivot labels
would be the load-bearing triple and would already be positive definite. -/
theorem card_highPivotLabels_le_two_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    (highPivotLabels D).card ≤ 2 := by
  by_contra hnot
  have hbig : 3 ≤ (highPivotLabels D).card := by omega
  obtain ⟨selected, hsubset, hcard⟩ := Finset.exists_subset_card_eq hbig
  have hhigh : ∀ c ∈ selected, 1 ≤ pivot D Finset.univ c := by
    intro c hc
    exact (Finset.mem_filter.mp (hsubset hc)).2
  exact hnoStrict selected hcard
    (posDef_subsetSum_of_cardThree_pivot_univ_ge_one D selected hhigh hcard)

/-- **NO-STRICT LEAVES AT LEAST FOUR LOW PIVOTS.**  This strengthens the free
three-positive-diagonal count on precisely the unresolved branch. -/
theorem four_le_card_lowPivotLabels_of_noStrict
    (D : WeightedDesign 6 3)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    4 ≤ (lowPivotLabels D).card := by
  rw [lowPivotLabels_eq_compl_highPivotLabels, Finset.card_compl, Fintype.card_fin]
  have hhigh := card_highPivotLabels_le_two_of_noStrict D hnoStrict
  omega

/-- Every strict triple contains every high-pivot label.  Equivalently, the
three labels it omits all lie in the low-pivot set. -/
theorem highPivotLabels_subset_of_posDef
    (D : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hpos : (subsetSum D selected - 1).PosDef) :
    highPivotLabels D ⊆ selected := by
  intro c hc
  by_contra hcSelected
  have hcCompl : c ∈ selectedᶜ := Finset.mem_compl.mpr hcSelected
  have hlow := pivot_univ_lt_one_of_posDef_of_mem_compl D (by norm_num)
    selected c hcCompl hpos
  have hhigh := (Finset.mem_filter.mp hc).2
  linarith

/-- Complement form: a strict triple may omit only low-pivot labels. -/
theorem compl_subset_lowPivotLabels_of_posDef
    (D : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hpos : (subsetSum D selected - 1).PosDef) :
    selectedᶜ ⊆ lowPivotLabels D := by
  intro c hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ c,
    pivot_univ_lt_one_of_posDef_of_mem_compl D (by norm_num) selected c hc hpos⟩

end Gtz
