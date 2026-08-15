import Gtz.Design.ChartReadingLaw

/-!
# The general covering cell

`Gtz/Design/ThreeLinesVertexCover.lean` pays each outside label against exactly
two selected labels, at the fixed factor four, and instantiates that at the two
direction families the tree owns.  This module removes both restrictions.

An outside label is paid against the WHOLE selected set, at coefficients the
caller supplies, and the cost is one scalar per label:

  `coverCost kappa selected coeff f = kappa f * (∑ |coeff f i|) * (∑ |coeff f i| / kappa i)`

`readingCover_of_generalCoverCellFires` proves that `coverCost ≤ 1` at every
label forces the reading cover, hence a positive definite chart gap.  The
statement is generic in the chart size, in the direction family, and in the
number of terms, so it applies at a direction family nobody has built yet.

The two-term factor four is the special case: with two unit coefficients the
cost is `2 * kappa f * (1 / kappa a + 1 / kappa b)`, which is at most one
exactly when `4 * kappa f ≤ kappa a` and `4 * kappa f ≤ kappa b`.
-/

namespace Gtz

open Finset

variable {size : ℕ}

/-! ## The combination data -/

/-- The selected labels read every label.  At a spanning selection in rank
three this is automatic, and the coefficients are the unique ones. -/
def ReadsThrough (direction : Fin size → (Fin 3 → ℝ)) (selected : Finset (Fin size))
    (coeff : Fin size → Fin size → ℝ) : Prop :=
  ∀ label : Fin size, ∀ probe : Fin 3 → ℝ,
    direction label ⬝ᵥ probe = ∑ i ∈ selected, coeff label i * (direction i ⬝ᵥ probe)

/-- The total combination weight of a label. -/
noncomputable def combinationMass (selected : Finset (Fin size))
    (coeff : Fin size → Fin size → ℝ) (label : Fin size) : ℝ :=
  ∑ i ∈ selected, |coeff label i|

/-- The priced combination weight: each term divided by the ratio that pays it. -/
noncomputable def combinationPrice (kappa : Fin size → ℝ) (selected : Finset (Fin size))
    (coeff : Fin size → Fin size → ℝ) (label : Fin size) : ℝ :=
  ∑ i ∈ selected, |coeff label i| / kappa i

/-- **The cover cost of a label.** -/
noncomputable def coverCost (kappa : Fin size → ℝ) (selected : Finset (Fin size))
    (coeff : Fin size → Fin size → ℝ) (label : Fin size) : ℝ :=
  kappa label * combinationMass selected coeff label
    * combinationPrice kappa selected coeff label

/-- **The general covering cell.**  One inequality per label. -/
def GeneralCoverCellFires (kappa : Fin size → ℝ) (selected : Finset (Fin size))
    (coeff : Fin size → Fin size → ℝ) : Prop :=
  ∀ label : Fin size, coverCost kappa selected coeff label ≤ 1

/-! ## The weighted Cauchy-Schwarz step -/

/-- A sum against nonnegative weights is squared-dominated by the weight total
times the weighted sum of squares.  No term count and no coefficient sign. -/
theorem sq_sum_le_mass_mul_weighted (s : Finset (Fin size)) (c r : Fin size → ℝ) :
    (∑ i ∈ s, c i * r i) ^ 2 ≤ (∑ i ∈ s, |c i|) * ∑ i ∈ s, |c i| * r i ^ 2 := by
  have habs : |∑ i ∈ s, c i * r i| ≤ ∑ i ∈ s, Real.sqrt |c i| * (Real.sqrt |c i| * |r i|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro i _
    have hsq : Real.sqrt |c i| * Real.sqrt |c i| = |c i| :=
      Real.mul_self_sqrt (abs_nonneg _)
    rw [abs_mul, ← mul_assoc, hsq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt |c i|) (fun i => Real.sqrt |c i| * |r i|)
  have hleft : (∑ i ∈ s, Real.sqrt |c i| ^ 2) = ∑ i ∈ s, |c i| := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Real.sq_sqrt (abs_nonneg _)
  have hright : (∑ i ∈ s, (Real.sqrt |c i| * |r i|) ^ 2) = ∑ i ∈ s, |c i| * r i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsq : Real.sqrt |c i| ^ 2 = |c i| := Real.sq_sqrt (abs_nonneg _)
    rw [mul_pow, hsq, sq_abs]
  rw [hleft, hright] at hcs
  have hsqabs : (∑ i ∈ s, c i * r i) ^ 2 = |∑ i ∈ s, c i * r i| ^ 2 := (sq_abs _).symm
  have hnonneg : 0 ≤ ∑ i ∈ s, Real.sqrt |c i| * (Real.sqrt |c i| * |r i|) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : 0 ≤ Real.sqrt |c i| := Real.sqrt_nonneg _
    have h2 : 0 ≤ |r i| := abs_nonneg _
    positivity
  calc (∑ i ∈ s, c i * r i) ^ 2
      = |∑ i ∈ s, c i * r i| ^ 2 := hsqabs
    _ ≤ (∑ i ∈ s, Real.sqrt |c i| * (Real.sqrt |c i| * |r i|)) ^ 2 := by
        nlinarith [habs, abs_nonneg (∑ i ∈ s, c i * r i)]
    _ ≤ (∑ i ∈ s, |c i|) * ∑ i ∈ s, |c i| * r i ^ 2 := hcs

/-! ## The maximum step -/

/-- A weighted sum of readings is dominated by the priced weight times the
largest priced reading. -/
theorem weighted_le_price_mul_max (s : Finset (Fin size)) (kappa : Fin size → ℝ)
    (hkappa : ∀ i, 0 < kappa i) (c r : Fin size → ℝ) (best : Fin size)
    (hbest : ∀ i ∈ s, kappa i * r i ^ 2 ≤ kappa best * r best ^ 2) :
    (∑ i ∈ s, |c i| * r i ^ 2)
      ≤ (∑ i ∈ s, |c i| / kappa i) * (kappa best * r best ^ 2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hpos := hkappa i
  have hterm : |c i| * r i ^ 2 = (|c i| / kappa i) * (kappa i * r i ^ 2) := by
    field_simp
  rw [hterm]
  exact mul_le_mul_of_nonneg_left (hbest i hi) (by positivity)

/-! ## The cell forces the cover -/

/-- **The general covering theorem.**  If every label's cover cost is at most
one, the selected set carries a maximal priced reading at every probe. -/
theorem readingCover_of_generalCoverCellFires (direction : Fin size → (Fin 3 → ℝ))
    (kappa : Fin size → ℝ) (hkappa : ∀ i, 0 < kappa i)
    {selected : Finset (Fin size)} (hne : selected.Nonempty)
    (coeff : Fin size → Fin size → ℝ)
    (hreads : ReadsThrough direction selected coeff)
    (hcell : GeneralCoverCellFires kappa selected coeff) :
    ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
      kappa label * (direction label ⬝ᵥ probe) ^ 2
        ≤ kappa good * (direction good ⬝ᵥ probe) ^ 2 := by
  intro probe
  set r : Fin size → ℝ := fun i => direction i ⬝ᵥ probe with hr
  obtain ⟨best, hbestMem, hbest⟩ :=
    selected.exists_max_image (fun i => kappa i * r i ^ 2) hne
  refine ⟨best, hbestMem, fun label => ?_⟩
  have hstep1 : (r label) ^ 2 ≤ combinationMass selected coeff label
      * ∑ i ∈ selected, |coeff label i| * r i ^ 2 := by
    have := sq_sum_le_mass_mul_weighted selected (coeff label) r
    rw [← hreads label probe] at this
    exact this
  have hstep2 : (∑ i ∈ selected, |coeff label i| * r i ^ 2)
      ≤ combinationPrice kappa selected coeff label * (kappa best * r best ^ 2) :=
    weighted_le_price_mul_max selected kappa hkappa (coeff label) r best hbest
  have hmassNonneg : 0 ≤ combinationMass selected coeff label :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hchain : (r label) ^ 2
      ≤ combinationMass selected coeff label * combinationPrice kappa selected coeff label
        * (kappa best * r best ^ 2) := by
    calc (r label) ^ 2
        ≤ combinationMass selected coeff label
            * ∑ i ∈ selected, |coeff label i| * r i ^ 2 := hstep1
      _ ≤ combinationMass selected coeff label
            * (combinationPrice kappa selected coeff label * (kappa best * r best ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep2 hmassNonneg
      _ = combinationMass selected coeff label * combinationPrice kappa selected coeff label
            * (kappa best * r best ^ 2) := by ring
  have hcost := hcell label
  have hkl := hkappa label
  have hbestNonneg : 0 ≤ kappa best * r best ^ 2 := by
    have := hkappa best
    positivity
  have hscaled : kappa label * (r label) ^ 2
      ≤ coverCost kappa selected coeff label * (kappa best * r best ^ 2) := by
    have := mul_le_mul_of_nonneg_left hchain (le_of_lt hkl)
    unfold coverCost
    calc kappa label * (r label) ^ 2
        ≤ kappa label * (combinationMass selected coeff label
            * combinationPrice kappa selected coeff label * (kappa best * r best ^ 2)) := this
      _ = kappa label * combinationMass selected coeff label
            * combinationPrice kappa selected coeff label * (kappa best * r best ^ 2) := by ring
  refine hscaled.trans ?_
  calc coverCost kappa selected coeff label * (kappa best * r best ^ 2)
      ≤ 1 * (kappa best * r best ^ 2) :=
        mul_le_mul_of_nonneg_right hcost hbestNonneg
    _ = kappa best * r best ^ 2 := one_mul _

/-! ## The consumer -/

/-- **The general cover cell gives a positive definite chart gap.** -/
theorem posDef_directionChartGap_of_generalCoverCell (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0)
    {selected : Finset (Fin size)} (hcard : 2 ≤ selected.card)
    (coeff : Fin size → Fin size → ℝ)
    (hreads : ReadsThrough direction selected coeff)
    (hcell : GeneralCoverCellFires (fun label => mass label / weight label) selected coeff) :
    (directionChartGap direction mass weight selected).PosDef := by
  have hne : selected.Nonempty := Finset.card_pos.mp (by omega)
  have hkappa : ∀ i, 0 < mass i / weight i := fun i => div_pos (hmass i) (hweight i)
  exact posDef_directionChartGap_of_readingCover direction mass weight hmass hweight hsum
    hspan hcard (readingCover_of_generalCoverCellFires direction _ hkappa hne coeff hreads hcell)

/-! ## Which selections can be paid against at all

The engine needs the selected labels to read every label.  In rank three that
is exactly a determinant condition on the selected triple, and it is the true
transport condition — not a bound on the number of terms.  A spanning triple
reads every label through all three of its members, and no rank-three chart
ever needs more. -/

/-- The determinant of a direction triple, in coordinates. -/
def tripleDet (a b c : Fin 3 → ℝ) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0)
    + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- **The Cramer reading identity, division-free.**  A polynomial identity in
all fifteen variables: no hypothesis, no inverse, no determinant in a
denominator. -/
theorem tripleDet_smul_reading (a b c target probe : Fin 3 → ℝ) :
    tripleDet a b c * (target ⬝ᵥ probe)
      = tripleDet target b c * (a ⬝ᵥ probe)
        + tripleDet a target c * (b ⬝ᵥ probe)
        + tripleDet a b target * (c ⬝ᵥ probe) := by
  simp only [dotProduct, Fin.sum_univ_three, tripleDet]
  ring

/-- **A spanning triple reads every direction, with Cramer coefficients.**  The
combination weights are ratios of triple determinants, so the engine's
coefficients are explicit and computable from the chart alone.  This is the
true transport condition — a determinant, not a term count. -/
theorem reading_eq_cramer (a b c target : Fin 3 → ℝ)
    (hdet : tripleDet a b c ≠ 0) (probe : Fin 3 → ℝ) :
    target ⬝ᵥ probe
      = (tripleDet target b c / tripleDet a b c) * (a ⬝ᵥ probe)
        + (tripleDet a target c / tripleDet a b c) * (b ⬝ᵥ probe)
        + (tripleDet a b target / tripleDet a b c) * (c ⬝ᵥ probe) := by
  have hkey := tripleDet_smul_reading a b c target probe
  field_simp
  linarith [hkey]

/-- The common orthogonal of two directions, in coordinates. -/
def commonOrthogonal (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- **A coplanar triple is blind at its common orthogonal.**  Three directions
on one plane — the third a combination of the first two — all read zero at the
plane normal.  This is the one-line and two-meeting-lines geometry: a selection
drawn from a single three-point line can never carry the cover. -/
theorem coplanar_triple_blind (a b : Fin 3 → ℝ) (s t : ℝ) :
    a ⬝ᵥ commonOrthogonal a b = 0
      ∧ b ⬝ᵥ commonOrthogonal a b = 0
      ∧ (fun i => s * a i + t * b i) ⬝ᵥ commonOrthogonal a b = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [commonOrthogonal, dotProduct, Fin.sum_univ_three] <;> ring

/-- **The blindness is fatal to any cover at that selection.**  At the blind
probe every selected reading is zero, so a label reading nonzero there cannot
be dominated. -/
theorem not_readingCover_of_blind_probe (direction : Fin size → (Fin 3 → ℝ))
    (kappa : Fin size → ℝ) (hkappa : ∀ i, 0 < kappa i)
    {selected : Finset (Fin size)} (probe : Fin 3 → ℝ)
    (hblind : ∀ i ∈ selected, direction i ⬝ᵥ probe = 0)
    (bad : Fin size) (hbad : direction bad ⬝ᵥ probe ≠ 0) :
    ¬ (∃ good ∈ selected, ∀ label,
        kappa label * (direction label ⬝ᵥ probe) ^ 2
          ≤ kappa good * (direction good ⬝ᵥ probe) ^ 2) := by
  rintro ⟨good, hgood, hcover⟩
  have hgz : direction good ⬝ᵥ probe = 0 := hblind good hgood
  have hle := hcover bad
  rw [hgz] at hle
  have hpos : 0 < kappa bad * (direction bad ⬝ᵥ probe) ^ 2 := by
    have := hkappa bad
    have hsq : 0 < (direction bad ⬝ᵥ probe) ^ 2 := by positivity
    positivity
  simp at hle
  linarith

/-! ## The two-term factor four is the special case -/

/-- With two unit coefficients the general cost reduces to the factor-four
pair condition of `ThreeLinesVertexCover`. -/
theorem coverCost_pair (kappa : Fin size → ℝ)
    (a b label : Fin size) (hab : a ≠ b)
    (coeff : Fin size → Fin size → ℝ)
    (ha : |coeff label a| = 1) (hb : |coeff label b| = 1) :
    coverCost kappa ({a, b} : Finset (Fin size)) coeff label
      = 2 * kappa label * (1 / kappa a + 1 / kappa b) := by
  unfold coverCost combinationMass combinationPrice
  rw [Finset.sum_pair hab, Finset.sum_pair hab, ha, hb]
  ring

/-- The factor-four pair cell implies the general cell at that pair. -/
theorem generalCost_le_one_of_quarter (kappa : Fin size → ℝ) (hkappa : ∀ i, 0 < kappa i)
    (a b label : Fin size) (hab : a ≠ b)
    (coeff : Fin size → Fin size → ℝ)
    (ha : |coeff label a| = 1) (hb : |coeff label b| = 1)
    (hqa : 4 * kappa label ≤ kappa a) (hqb : 4 * kappa label ≤ kappa b) :
    coverCost kappa ({a, b} : Finset (Fin size)) coeff label ≤ 1 := by
  rw [coverCost_pair kappa a b label hab coeff ha hb]
  have hka := hkappa a
  have hkb := hkappa b
  have hkl := hkappa label
  have hkey : 2 * kappa label * (kappa b + kappa a) ≤ kappa a * kappa b := by nlinarith
  have hrewrite : 2 * kappa label * (1 / kappa a + 1 / kappa b)
      = 2 * kappa label * (kappa b + kappa a) / (kappa a * kappa b) := by
    field_simp
  rw [hrewrite, div_le_one (by positivity)]
  exact hkey

/-! ## The three-term factor nine

A rank-three chart whose selected triple spans reads every outside label
through all three members, so the pair factor four is replaced by the triple
factor nine.  Nothing beyond three terms is ever needed. -/

/-- With three unit coefficients the cost is three times the priced sum. -/
theorem coverCost_triple (kappa : Fin size → ℝ)
    (a b c label : Fin size) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (coeff : Fin size → Fin size → ℝ)
    (ha : |coeff label a| = 1) (hb : |coeff label b| = 1) (hc : |coeff label c| = 1) :
    coverCost kappa ({a, b, c} : Finset (Fin size)) coeff label
      = 3 * kappa label * (1 / kappa a + 1 / kappa b + 1 / kappa c) := by
  classical
  have hset : ∀ f : Fin size → ℝ,
      ∑ i ∈ ({a, b, c} : Finset (Fin size)), f i = f a + f b + f c := by
    intro f
    rw [show ({a, b, c} : Finset (Fin size)) = insert a {b, c} from rfl,
      Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
    ring
  unfold coverCost combinationMass combinationPrice
  rw [hset, hset, ha, hb, hc]
  ring

/-- **The factor-nine triple cell.**  Three selected labels each nine times the
outside ratio pay for it, whatever the probe. -/
theorem generalCost_le_one_of_ninth (kappa : Fin size → ℝ) (hkappa : ∀ i, 0 < kappa i)
    (a b c label : Fin size) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (coeff : Fin size → Fin size → ℝ)
    (ha : |coeff label a| = 1) (hb : |coeff label b| = 1) (hc : |coeff label c| = 1)
    (hna : 9 * kappa label ≤ kappa a) (hnb : 9 * kappa label ≤ kappa b)
    (hnc : 9 * kappa label ≤ kappa c) :
    coverCost kappa ({a, b, c} : Finset (Fin size)) coeff label ≤ 1 := by
  rw [coverCost_triple kappa a b c label hab hac hbc coeff ha hb hc]
  have hka := hkappa a
  have hkb := hkappa b
  have hkc := hkappa c
  have hkl := hkappa label
  have hkey : 3 * kappa label * (kappa b * kappa c + kappa a * kappa c + kappa a * kappa b)
      ≤ kappa a * kappa b * kappa c := by
    have h1 := mul_le_mul_of_nonneg_right hna (le_of_lt (mul_pos hkb hkc))
    have h2 := mul_le_mul_of_nonneg_right hnb (le_of_lt (mul_pos hka hkc))
    have h3 := mul_le_mul_of_nonneg_right hnc (le_of_lt (mul_pos hka hkb))
    nlinarith [h1, h2, h3]
  have hrewrite : 3 * kappa label * (1 / kappa a + 1 / kappa b + 1 / kappa c)
      = 3 * kappa label * (kappa b * kappa c + kappa a * kappa c + kappa a * kappa b)
        / (kappa a * kappa b * kappa c) := by
    field_simp
  rw [hrewrite, div_le_one (by positivity)]
  exact hkey

end Gtz
