/-
# The normal budget of a flat set

`Gtz.flatSplit_posDef_iff` decides a selection against a flat set by two
conditions: an EXCESS condition, which reads only the squared normal readings of
the labels the selection holds OUTSIDE the flat set, and a plane inequality.
This module prices the excess condition exactly, and shows it is free.

At a unit normal that every flat atom kills, Parseval carries the whole probe
energy to the labels outside the flat set:

  `∑_{c ∉ flat} w_c (a_c ⬝ n)² = 1`     (the normal budget)

Every weight is strictly below one, so the UNWEIGHTED sum of the same readings
is strictly above one.  The complement of the flat set therefore always clears
the excess condition, with no hypothesis beyond the pattern.

When the complement carries exactly three labels the sharper statement holds.
Fix ANY one of the three.  One of the two pairs that contains it already clears
the excess.  The reason is a weight count: the dropped label's reading is priced
by `2 - w_y - w_z`, which exceeds one because the third weight is positive.

At the one-line stratum the complement of the line is the free triple, so the
statement covers nine of the ten plane-branch candidates.  At two meeting lines
the same statement runs at BOTH normals with the open label designated, and the
two conclusions select one transversal that clears the excess at each normal.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.UniversalNeedle
import Gtz.Design.LineClassObstructions
import Gtz.Design.ComplementLeverageLaw
import Gtz.Design.WholeLineMarginCriterion

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## The budget -/

/-- **The normal budget.**  At a unit normal killed by every flat atom, Parseval
carries the entire probe energy to the labels outside the flat set. -/
theorem flat_normalBudget (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ flatᶜ,
        design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2) = 1 := by
  have hall := sum_weight_mul_sq_dotProduct design normalVec
  have hflatZero : (∑ label ∈ flat,
      design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2) = 0 :=
    Finset.sum_eq_zero fun label hlabel => by rw [hflat label hlabel]; ring
  have hsplit := Finset.sum_add_sum_compl flat
    (fun label => design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2)
  rw [hall, hunit] at hsplit
  linarith [hsplit, hflatZero]

/-- The unweighted excess of the complement over the budget, as a single sum of
nonnegative terms. -/
theorem sum_sq_normalReading_compl_sub_one (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ normalVec) ^ 2) - 1
      = ∑ label ∈ flatᶜ,
          (1 - design.weight label) * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  have hbudget := flat_normalBudget design flat normalVec hunit hflat
  have hterm : ∀ label : Fin size,
      (1 - design.weight label) * (design.atom label ⬝ᵥ normalVec) ^ 2
        = (design.atom label ⬝ᵥ normalVec) ^ 2
          - design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2 :=
    fun label => by ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib, hbudget]

/-- **The complement always clears the excess.**  Every weight is strictly below
one, so the unweighted sum of the squared normal readings outside the flat set
exceeds the budget.  No hypothesis beyond the flat pattern is used. -/
theorem one_lt_sum_sq_normalReading_compl (design : WeightedDesign size rank)
    (hsize : 2 ≤ size)
    (flat : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    1 < ∑ label ∈ flatᶜ, (design.atom label ⬝ᵥ normalVec) ^ 2 := by
  have hbudget := flat_normalBudget design flat normalVec hunit hflat
  have hgap := sum_sq_normalReading_compl_sub_one design flat normalVec hunit hflat
  have hne : (∑ label ∈ flatᶜ,
      design.weight label * (design.atom label ⬝ᵥ normalVec) ^ 2) ≠ 0 := by
    rw [hbudget]; norm_num
  obtain ⟨witness, hwitnessMem, hwitnessNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hne
  have hpos : 0 < ∑ label ∈ flatᶜ,
      (1 - design.weight label) * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    refine Finset.sum_pos' (fun label _ => ?_) ⟨witness, hwitnessMem, ?_⟩
    · exact mul_nonneg (by linarith [design_weight_lt_one design hsize label])
        (sq_nonneg _)
    · have hwLt := design_weight_lt_one design hsize witness
      have hsqNe : (design.atom witness ⬝ᵥ normalVec) ^ 2 ≠ 0 := by
        intro hzero; exact hwitnessNe (by rw [hzero]; ring)
      have hsqPos : 0 < (design.atom witness ⬝ᵥ normalVec) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hsqNe)
      exact mul_pos (by linarith) hsqPos
  linarith

/-! ## The designated pair -/

/-- The three labels of a complement carry total weight at most one. -/
theorem sum_three_weight_le_one (design : WeightedDesign size rank)
    (x y z : Fin size) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    design.weight x + design.weight y + design.weight z ≤ 1 := by
  have hsub : ({x, y, z} : Finset (Fin size)) ⊆ Finset.univ := Finset.subset_univ _
  have hle : (∑ label ∈ ({x, y, z} : Finset (Fin size)), design.weight label)
      ≤ ∑ label, design.weight label :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun label _ _ => (design.weight_pos label).le
  rw [design.weight_sum_one] at hle
  rwa [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, ← add_assoc] at hle

/-- **The designated-pair excess.**  When the complement of the flat set carries
exactly three labels, fix any ONE of them.  One of the two pairs containing it
already clears the excess condition.

The dropped label is the smaller of the other two, and its reading is priced by
`2 - w_y - w_z`, which exceeds one because the designated label's own weight is
positive.  This is the first condition of `Gtz.flatSplit_pair_posDef_iff` at a
selection holding one flat atom, and it costs nothing. -/
theorem exists_partner_excess_gt_one (design : WeightedDesign size rank)
    (hsize : 2 ≤ size)
    (flat : Finset (Fin size)) (x y z : Fin size)
    (hcompl : flatᶜ = ({x, y, z} : Finset (Fin size)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    1 < (design.atom x ⬝ᵥ normalVec) ^ 2 + (design.atom y ⬝ᵥ normalVec) ^ 2
      ∨ 1 < (design.atom x ⬝ᵥ normalVec) ^ 2
          + (design.atom z ⬝ᵥ normalVec) ^ 2 := by
  set readX := (design.atom x ⬝ᵥ normalVec) ^ 2 with hreadX
  set readY := (design.atom y ⬝ᵥ normalVec) ^ 2 with hreadY
  set readZ := (design.atom z ⬝ᵥ normalVec) ^ 2 with hreadZ
  have hbudget := flat_normalBudget design flat normalVec hunit hflat
  rw [hcompl, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hbudget
  have hweights := sum_three_weight_le_one design x y z hxy hxz hyz
  have hxPos := design.weight_pos x
  have hyPos := design.weight_pos y
  have hzPos := design.weight_pos z
  have hxNonneg : 0 ≤ readX := by rw [hreadX]; exact sq_nonneg _
  have hyNonneg : 0 ≤ readY := by rw [hreadY]; exact sq_nonneg _
  have hzNonneg : 0 ≤ readZ := by rw [hreadZ]; exact sq_nonneg _
  have hxLt := design_weight_lt_one design hsize x
  -- the pair keeping the LARGER of `y` and `z` clears the excess
  rcases le_total readY readZ with hle | hle
  · right
    -- `1 = w_x readX + w_y readY + w_z readZ ≤ w_x readX + (w_y + w_z) readZ`
    have hstep : (1 : ℝ)
        ≤ design.weight x * readX + (design.weight y + design.weight z) * readZ := by
      nlinarith [mul_le_mul_of_nonneg_left hle hyPos.le]
    have hsumPos : 0 < readX + readZ := by nlinarith
    rcases lt_or_ge 0 readX with hxpos | hxzero
    · nlinarith
    · have hxeq : readX = 0 := le_antisymm hxzero hxNonneg
      have hzPosStrict : 0 < readZ := by rw [hxeq] at hsumPos; linarith
      nlinarith
  · left
    have hstep : (1 : ℝ)
        ≤ design.weight x * readX + (design.weight y + design.weight z) * readY := by
      nlinarith [mul_le_mul_of_nonneg_left hle hzPos.le]
    have hsumPos : 0 < readX + readY := by nlinarith
    rcases lt_or_ge 0 readX with hxpos | hxzero
    · nlinarith
    · have hxeq : readX = 0 := le_antisymm hxzero hxNonneg
      have hyPosStrict : 0 < readY := by rw [hxeq] at hsumPos; linarith
      nlinarith

/-! ## The sharp excess already in kernel

`Gtz.exists_complementAtom_overcovers_normal` supplies a SINGLE free atom whose
squared normal reading exceeds the probe energy.  That is strictly stronger than
the counting argument above: every pair holding that atom clears the excess, and
the designated label is free to be anything.  Prefer this route.  The counting
argument is retained because it is generic in the size, the rank and the flat
set, while the pointwise seed is stated at `(6,3)` for a line triple. -/

/-- **The sharp pair excess.**  One free atom alone beats the probe energy, so
every pair holding it clears the excess whatever the partner is. -/
theorem exists_complementAtom_pair_excess (design : WeightedDesign 6 3)
    (lineTriple : Finset (Fin 6)) (normalVec : Fin 3 → ℝ)
    (hlineNonempty : lineTriple.Nonempty)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (horthogonal : ∀ lineLabel ∈ lineTriple,
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (partner : Fin 6) :
    ∃ freeLabel ∈ lineTripleᶜ,
      1 < (design.atom freeLabel ⬝ᵥ normalVec) ^ 2
        + (design.atom partner ⬝ᵥ normalVec) ^ 2 := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  obtain ⟨freeLabel, hmem, hover⟩ :=
    exists_complementAtom_overcovers_normal design lineTriple normalVec
      hlineNonempty hnormalNe horthogonal
  refine ⟨freeLabel, hmem, ?_⟩
  rw [hunit] at hover
  nlinarith [sq_nonneg (design.atom partner ⬝ᵥ normalVec)]

/-! ## The reduction to the plane inequality -/

/-- **The excess condition discharged.**  Once the labels a selection holds
outside the flat set clear the excess, the criterion collapses to its plane
inequality alone.  Every selection whose excess this module supplies is decided
by one probe-quantified polynomial statement, with no scalar side condition. -/
theorem flatSplit_posDef_iff_planeInequality (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size))
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0)
    (hexcess : 1 < ∑ label ∈ selected \ flat,
      (design.atom label ⬝ᵥ normalVec) ^ 2) :
    (subsetSum design selected - 1).PosDef ↔
      ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ label ∈ selected \ flat,
            (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)) ^ 2
          < ((∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ normalVec) ^ 2) - 1)
            * ((∑ label ∈ selected, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                - planeProbe ⬝ᵥ planeProbe) := by
  rw [flatSplit_posDef_iff design selected flat normalVec hunit hflat]
  exact and_iff_right hexcess

/-! ## The one-line stratum -/

/-- **The free triple always clears the excess at the one-line stratum.**  The
complement of the line `{0,1,2}` is the free triple `{3,4,5}`, and the budget
lives entirely on it. -/
theorem oneLine_freeTriple_excess (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0) :
    1 < (design.atom 3 ⬝ᵥ normalVec) ^ 2 + (design.atom 4 ⬝ᵥ normalVec) ^ 2
      + (design.atom 5 ⬝ᵥ normalVec) ^ 2 := by
  have hcompl : (({0, 1, 2} : Finset (Fin 6)))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by
    decide
  have hmain := one_lt_sum_sq_normalReading_compl design (by norm_num)
    ({0, 1, 2} : Finset (Fin 6)) normalVec hunit hflat
  rw [hcompl, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hmain
  linarith

/-- **The free triple is decided by its plane inequality alone.**  At the
one-line stratum the excess of `{3,4,5}` is free, so the entire content of its
strict domination is the plane inequality.  `{3,4,5}` is the tenth member of
`Gtz.PlaneBranchTenCandidate`, the only one holding no line atom. -/
theorem oneLine_freeTriple_posDef_iff_planeInequality (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0) :
    (subsetSum design ({3, 4, 5} : Finset (Fin 6)) - 1).PosDef ↔
      ∀ planeProbe : Fin 3 → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
        (∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
            (design.atom label ⬝ᵥ planeProbe)
              * (design.atom label ⬝ᵥ normalVec)) ^ 2
          < ((∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
                (design.atom label ⬝ᵥ normalVec) ^ 2) - 1)
            * ((∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
                  (design.atom label ⬝ᵥ planeProbe) ^ 2)
                - planeProbe ⬝ᵥ planeProbe) := by
  have hsdiff : ({3, 4, 5} : Finset (Fin 6)) \ ({0, 1, 2} : Finset (Fin 6))
      = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hexcess : 1 < ∑ label ∈ (({3, 4, 5} : Finset (Fin 6))
      \ ({0, 1, 2} : Finset (Fin 6))), (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [hsdiff, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    linarith [oneLine_freeTriple_excess design normalVec hunit hflat]
  have hmain := flatSplit_posDef_iff_planeInequality design
    ({3, 4, 5} : Finset (Fin 6)) ({0, 1, 2} : Finset (Fin 6))
    normalVec hunit hflat hexcess
  rwa [hsdiff] at hmain

/-- **A free pair clears the excess at the one-line stratum.**  Designating the
free label `5`, one of the two pairs `{3,5}` and `{4,5}` already satisfies the
first condition of `Gtz.flatSplit_pair_posDef_iff`.  Both pairs occur inside
`Gtz.PlaneBranchTenCandidate`, paired with each of the three line atoms. -/
theorem oneLine_freePair_excess (design : WeightedDesign 6 3)
    (normalVec : Fin 3 → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalVec = 0) :
    1 < (design.atom 5 ⬝ᵥ normalVec) ^ 2 + (design.atom 3 ⬝ᵥ normalVec) ^ 2
      ∨ 1 < (design.atom 5 ⬝ᵥ normalVec) ^ 2
          + (design.atom 4 ⬝ᵥ normalVec) ^ 2 :=
  exists_partner_excess_gt_one design (by norm_num)
    ({0, 1, 2} : Finset (Fin 6)) 5 3 4 (by decide) (by decide) (by decide)
    (by decide) normalVec hunit hflat

/-! ## The two-meeting-lines stratum -/

/-- **A transversal clears the excess at BOTH normals.**  The two lines are
`{0,1,2}` and `{0,3,4}`, sharing the atom `0` and leaving `5` open.  Designating
`5` at each normal, the first line's normal selects a partner in `{3,4}` and the
second line's normal selects a partner in `{1,2}`.  The transversal built from
the two partners is one of the four members of
`Gtz.TwoMeetingLinesTransversalStrict`, and it clears the excess condition of
`Gtz.flatSplit_pair_posDef_iff` at each of the two normals.

#ZERO-CONSUMER, and it is UNCONDITIONAL apart from the two normals, which the
registry axiom `Skeleton.obligationSeededTransversalTwoMeetingLines` hands over.
It is the closest landed statement to the first of the three invariant
inequalities of `Gtz.twoMeetingLinesTransversalStrict_iff_invariants`
(Gtz/Design/TwoMeetingLinesNeedle.lean:226).  The two disjunctions DO name one
transversal `{i, j, 5}` with `i` in `{1,2}` and `j` in `{3,4}`.  What the
statement does NOT give is a condition on that transversal as a whole: the first
excess reads the PAIR `{5, j}` at the first normal, the second reads the PAIR
`{5, i}` at the second normal, and neither reads all three members. -/
theorem twoMeetingLines_transversal_excess (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (hflatFirst : ∀ label ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalFirst = 0)
    (hflatSecond : ∀ label ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom label ⬝ᵥ normalSecond = 0) :
    (1 < (design.atom 5 ⬝ᵥ normalFirst) ^ 2 + (design.atom 3 ⬝ᵥ normalFirst) ^ 2
        ∨ 1 < (design.atom 5 ⬝ᵥ normalFirst) ^ 2
            + (design.atom 4 ⬝ᵥ normalFirst) ^ 2)
      ∧ (1 < (design.atom 5 ⬝ᵥ normalSecond) ^ 2
            + (design.atom 1 ⬝ᵥ normalSecond) ^ 2
        ∨ 1 < (design.atom 5 ⬝ᵥ normalSecond) ^ 2
            + (design.atom 2 ⬝ᵥ normalSecond) ^ 2) := by
  constructor
  · exact exists_partner_excess_gt_one design (by norm_num)
      ({0, 1, 2} : Finset (Fin 6)) 5 3 4 (by decide) (by decide) (by decide)
      (by decide) normalFirst hunitFirst hflatFirst
  · exact exists_partner_excess_gt_one design (by norm_num)
      ({0, 3, 4} : Finset (Fin 6)) 5 1 2 (by decide) (by decide) (by decide)
      (by decide) normalSecond hunitSecond hflatSecond

end Gtz
