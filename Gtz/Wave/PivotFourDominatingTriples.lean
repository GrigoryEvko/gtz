/-
# The three-class law for rank-two ties, and four dominating triples at `(5,3)`

A rank-two tie is rigid.  Its atoms fall into exactly THREE parallel classes, and
a pair of atoms dominates exactly when the two atoms lie in DIFFERENT classes.
Nothing is left to choose: the dominating pairs are read off the partition.

## The engine

Write `q_cd = pairGapForm D c d = det (S_{c,d} - 1)` and `t_c` for the weights.
Three landed identities carry everything.

* Heaviness.  A strictly light atom hands a rank-two design a STRICT dominator
  (`Gtz.posDef_of_strictly_light_atom` fed by `Gtz.gtz_rank_two`), so every atom
  of a tie has `1 <= l_c`.
* The sign law.  A positive `q_cd` at a heavy atom is a strict dominator
  (`Gtz.posDef_pairGap_of_pairGapForm_pos`), so `q_cd <= 0` off the diagonal.
* The master identity `sum_d t_d q_cd = -1` (`Gtz.sum_weight_mul_pairGapForm_rankTwo`).

Sum the master identity over a parallel class `X` against the weights.  Split the
total by classes and put `T_X = sum_{c in X} t_c`, `M_X = sum_{c in X} t_c l_c`,
`Q_XY = sum_{c in X} sum_{d in Y} t_c t_d q_cd`:

    sum_Y Q_XY = -T_X ,        Q_XX = -T_X (2 M_X - T_X) ,

the second because a parallel pair has `q_cd = 1 - l_c - l_d` (Lagrange, with a
vanishing bracket).  Subtracting,

    sum_{Y /= X} Q_XY = -T_X * (1 + T_X - 2 M_X) = -T_X * CLASSDEFECT(X).

Each cross term is at most zero by the sign law, and `T_X > 0`, so every class
defect is at least zero.  But the defects add to `p - 3`, where `p` is the number
of classes: Parseval gives `sum_X T_X = 1` and `sum_X M_X = 2`.  The rank-two
four-direction hinge (`Gtz.not_isTie_of_fourNonParallel`) caps `p` at three.  So

    p = 3   and   CLASSDEFECT(X) = 0 for every class,

hence `Q_XY = 0` for `X /= Y`, hence `q_cd = 0` at every cross-class pair, and a
vanishing gap determinant at two heavy atoms is weak domination.

## The count at five

Three classes cannot cover five atoms with every class of size two or more, so
some class is a SINGLETON.  Its atom is cross-class to the other four, so it lies
in four dominating pairs.  Naimark duality in its two-sided Loewner form
(`Gtz.exists_naimarkDual_loewnerEquiv`) carries a `(5,3)` tie to a `(5,2)` tie and
the dominating pairs back to the complementary dominating triples.  That answers
Question 7.1: **every `(5,3)` tie carries at least four dominating triples.**

[MEASURED before proving.  The class algebra was checked on 159 constructed
rank-two ties: the master identity to 3.2e-14, `sum_Y Q_XY + T_X` to 4.4e-16,
`Q_XX + T_X(2M_X - T_X)` to 2.2e-16, the defect identity to 4.9e-16, every class
defect to 8.9e-16, every off-diagonal `q` at most 4.6e-13, the smallest leverage
1.0147.  Dominating pairs equalled cross-class pairs on every one of them, with
counts 7 (87 systems) and 8 (72 systems) -- never fewer.  The `(5,3)` diamond has
Parseval error 1.7e-15, tie margin 1.2e-15 and EIGHT dominating triples, and its
sharp `(5,2)` partner has leverages `(3, 7/4, 7/4, 7/4, 7/4)`, class defects
`(0, 1/2, 1/2, 1/2, 1/2)` summing to two, and the same eight selections read
through complementation.]
-/
import Gtz.Design.RankTwoTieCriterion
import Gtz.Ties.RankTwoHingeBridge
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.Deflation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-! ## 1. A `2 x 2` positivity test with a slack trace -/

/-- **Trace and determinant decide, with no strictness anywhere.**  A symmetric
`2 x 2` matrix with nonnegative trace and nonnegative determinant is positive
semidefinite.  The diagonal clause of `Gtz.posSemidef_two_iff` comes for free:
the two diagonal entries have a nonnegative product, so they share a sign, and a
common negative sign contradicts the trace. -/
theorem posSemidef_two_of_trace_nonneg_of_det_nonneg {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hsymmetric : Xᵀ = X) (htrace : 0 ≤ X 0 0 + X 1 1) (hdet : 0 ≤ X.det) :
    X.PosSemidef := by
  have hoff : X 1 0 = X 0 1 := by
    have hentry := congrFun (congrFun hsymmetric 0) 1
    rwa [Matrix.transpose_apply] at hentry
  have hminor : 0 ≤ X 0 0 * X 1 1 - X 0 1 ^ 2 := by
    have hsquare : X 0 1 ^ 2 = X 0 1 * X 0 1 := by ring
    rw [Matrix.det_fin_two, hoff] at hdet
    linarith [hdet, hsquare]
  have hcorner : 0 ≤ X 0 0 := by nlinarith [hminor, htrace, sq_nonneg (X 0 1)]
  have hsecond : 0 ≤ X 1 1 := by nlinarith [hminor, htrace, sq_nonneg (X 0 1)]
  exact (posSemidef_two_iff hsymmetric).mpr ⟨hcorner, hsecond, hminor⟩

/-! ## 2. Heaviness and the sign law at a rank-two tie -/

/-- **Every atom of a rank-two tie is heavy.**  A leverage strictly below one
deflates to a STRICT dominator one size down, and rank-two GTZ supplies the weak
dominator that the deflation needs. -/
theorem one_le_leverage_of_isTie_rankTwo {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) (label : Fin atoms) :
    1 ≤ leverageOf (D.atom label) := by
  rcases le_or_gt 1 (leverageOf (D.atom label)) with hheavy | hlight
  · exact hheavy
  · exfalso
    obtain ⟨predecessor, rfl⟩ : ∃ predecessor, atoms = predecessor + 1 :=
      ⟨atoms - 1, by omega⟩
    obtain ⟨selected, hcard, hposDef⟩ :=
      posDef_of_strictly_light_atom D (by omega) (gtz_rank_two predecessor) label hlight
    exact htie.2 selected hcard hposDef

/-- An atom of leverage at least one has a nonzero coordinate. -/
theorem atom_coordinate_ne_zero_of_one_le_leverage {atoms : ℕ} (D : WeightedDesign atoms 2)
    {label : Fin atoms} (hheavy : 1 ≤ leverageOf (D.atom label)) :
    D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 := by
  by_contra hboth
  push Not at hboth
  obtain ⟨hzero, hone⟩ := hboth
  rw [leverageOf, Fin.sum_univ_two, hzero, hone] at hheavy
  norm_num at hheavy

/-- **The sign law.**  Off the diagonal of a rank-two tie the pair gap form is
never positive: a positive one at a heavy pivot is a strict dominator, and the
tie's own heaviness supplies the pivot. -/
theorem pairGapForm_nonpos_of_isTie_rankTwo {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) {pivotLabel partnerLabel : Fin atoms}
    (hdistinct : pivotLabel ≠ partnerLabel) :
    pairGapForm D pivotLabel partnerLabel ≤ 0 := by
  rcases le_or_gt (pairGapForm D pivotLabel partnerLabel) 0 with hnonpos | hpos
  · exact hnonpos
  · exfalso
    have hpivotHeavy := one_le_leverage_of_isTie_rankTwo D hatoms htie pivotLabel
    have hpartnerHeavy := one_le_leverage_of_isTie_rankTwo D hatoms htie partnerLabel
    have hstrict : 1 < leverageOf (D.atom pivotLabel) := by
      rw [pairGapForm] at hpos
      nlinarith [hpos, sq_nonneg (D.atom pivotLabel ⬝ᵥ D.atom partnerLabel),
        hpivotHeavy, hpartnerHeavy]
    exact htie.2 {pivotLabel, partnerLabel} (Finset.card_pair hdistinct)
      (posDef_pairGap_of_pairGapForm_pos D hdistinct hstrict hpos)

/-- **A tight pair of a tie dominates.**  The gap determinant is the pair gap
form, so a vanishing gap form is a vanishing determinant, and heaviness supplies
the nonnegative trace. -/
theorem dominates_pair_of_pairGapForm_eq_zero {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) {pivotLabel partnerLabel : Fin atoms}
    (hdistinct : pivotLabel ≠ partnerLabel)
    (htight : pairGapForm D pivotLabel partnerLabel = 0) :
    Dominates D {pivotLabel, partnerLabel} := by
  have hpivotHeavy := one_le_leverage_of_isTie_rankTwo D hatoms htie pivotLabel
  have hpartnerHeavy := one_le_leverage_of_isTie_rankTwo D hatoms htie partnerLabel
  refine posSemidef_two_of_trace_nonneg_of_det_nonneg
    (transpose_pairGap D pivotLabel partnerLabel) ?_ ?_
  · rw [entryDiagonal_pairGap D hdistinct]
    linarith
  · rw [det_pairGap_eq_pairGapForm D hdistinct, htight]

/-! ## 3. Parallel classes -/

/-- Parallelism is transitive through an atom with a nonzero coordinate: the two
brackets multiply the target bracket against each coordinate of the middle atom,
and one of those coordinates is alive. -/
theorem pairBracket_trans {atoms : ℕ} (D : WeightedDesign atoms 2)
    {leftLabel middleLabel rightLabel : Fin atoms}
    (hmiddle : D.atom middleLabel 0 ≠ 0 ∨ D.atom middleLabel 1 ≠ 0)
    (hleft : pairBracket D leftLabel middleLabel = 0)
    (hright : pairBracket D middleLabel rightLabel = 0) :
    pairBracket D leftLabel rightLabel = 0 := by
  simp only [pairBracket] at hleft hright ⊢
  have hfirst : (D.atom leftLabel 0 * D.atom rightLabel 1
      - D.atom leftLabel 1 * D.atom rightLabel 0) * D.atom middleLabel 0 = 0 := by
    linear_combination D.atom leftLabel 0 * hright + D.atom rightLabel 0 * hleft
  have hsecond : (D.atom leftLabel 0 * D.atom rightLabel 1
      - D.atom leftLabel 1 * D.atom rightLabel 0) * D.atom middleLabel 1 = 0 := by
    linear_combination D.atom leftLabel 1 * hright + D.atom rightLabel 1 * hleft
  rcases hmiddle with halive | halive
  · exact (mul_eq_zero.mp hfirst).resolve_right halive
  · exact (mul_eq_zero.mp hsecond).resolve_right halive

theorem pairBracket_self {atoms : ℕ} (D : WeightedDesign atoms 2) (label : Fin atoms) :
    pairBracket D label label = 0 := by
  simp only [pairBracket]
  ring

theorem pairBracket_eq_zero_comm {atoms : ℕ} (D : WeightedDesign atoms 2)
    {leftLabel rightLabel : Fin atoms} (hzero : pairBracket D leftLabel rightLabel = 0) :
    pairBracket D rightLabel leftLabel = 0 := by
  simp only [pairBracket] at hzero ⊢
  linarith

open scoped Classical in
/-- The **parallel class** of an atom: the atoms whose bracket against it
vanishes. -/
noncomputable def rankTwoParallelClass (D : WeightedDesign size 2) (pivot : Fin size) :
    Finset (Fin size) :=
  Finset.univ.filter fun other => pairBracket D pivot other = 0

open scoped Classical in
/-- The family of parallel classes of a rank-two design. -/
noncomputable def parallelClasses (D : WeightedDesign size 2) : Finset (Finset (Fin size)) :=
  Finset.image (rankTwoParallelClass D) Finset.univ

open scoped Classical in
theorem mem_parallelClass_iff (D : WeightedDesign size 2) (pivot other : Fin size) :
    other ∈ rankTwoParallelClass D pivot ↔ pairBracket D pivot other = 0 := by
  rw [rankTwoParallelClass, Finset.mem_filter]
  exact ⟨fun hmember => hmember.2, fun hzero => ⟨Finset.mem_univ other, hzero⟩⟩

theorem self_mem_parallelClass (D : WeightedDesign size 2) (pivot : Fin size) :
    pivot ∈ rankTwoParallelClass D pivot :=
  (mem_parallelClass_iff D pivot pivot).mpr (pairBracket_self D pivot)

theorem parallelClass_mem_parallelClasses (D : WeightedDesign size 2) (pivot : Fin size) :
    rankTwoParallelClass D pivot ∈ parallelClasses D :=
  Finset.mem_image_of_mem _ (Finset.mem_univ pivot)

/-- **Classes are classes.**  Membership and equality of parallel classes agree,
once every atom has a live coordinate. -/
theorem parallelClass_eq_of_mem (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {pivot other : Fin size} (hmember : other ∈ rankTwoParallelClass D pivot) :
    rankTwoParallelClass D other = rankTwoParallelClass D pivot := by
  have hbracket : pairBracket D pivot other = 0 := (mem_parallelClass_iff D pivot other).mp hmember
  ext probe
  rw [mem_parallelClass_iff, mem_parallelClass_iff]
  constructor
  · intro hprobe
    exact pairBracket_trans D (hlive other) hbracket hprobe
  · intro hprobe
    exact pairBracket_trans D (hlive pivot) (pairBracket_eq_zero_comm D hbracket) hprobe

/-- Two atoms of one class are parallel. -/
theorem pairBracket_eq_zero_of_mem_of_mem (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {pivot leftLabel rightLabel : Fin size}
    (hleft : leftLabel ∈ rankTwoParallelClass D pivot) (hright : rightLabel ∈ rankTwoParallelClass D pivot) :
    pairBracket D leftLabel rightLabel = 0 :=
  pairBracket_trans D (hlive pivot)
    (pairBracket_eq_zero_comm D ((mem_parallelClass_iff D pivot leftLabel).mp hleft))
    ((mem_parallelClass_iff D pivot rightLabel).mp hright)

open scoped Classical in
/-- The fibre of the class map over a class is that class. -/
theorem filter_parallelClass_eq (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {block : Finset (Fin size)} (hblock : block ∈ parallelClasses D) :
    (Finset.univ.filter fun label => rankTwoParallelClass D label = block) = block := by
  obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hblock
  subst hpivot
  ext probe
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, hequal⟩
    rw [← hequal]
    exact self_mem_parallelClass D probe
  · intro hmember
    exact ⟨Finset.mem_univ probe, parallelClass_eq_of_mem D hlive hmember⟩

open scoped Classical in
/-- **The classes partition.**  Any sum over the atoms breaks into a sum over the
parallel classes. -/
theorem sum_over_parallelClasses {M : Type*} [AddCommMonoid M] (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    (readout : Fin size → M) :
    ∑ block ∈ parallelClasses D, ∑ label ∈ block, readout label = ∑ label, readout label := by
  have hmaps : ∀ label ∈ (Finset.univ : Finset (Fin size)),
      rankTwoParallelClass D label ∈ parallelClasses D :=
    fun label _ => parallelClass_mem_parallelClasses D label
  have hfibre := Finset.sum_fiberwise_of_maps_to hmaps readout
  rw [← hfibre]
  refine Finset.sum_congr rfl fun block hblock => ?_
  rw [filter_parallelClass_eq D hlive hblock]


open scoped Classical in
/-- A member of a parallel class has that class. -/
theorem parallelClass_eq_of_mem_class (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {block : Finset (Fin size)} (hblock : block ∈ parallelClasses D)
    {label : Fin size} (hmember : label ∈ block) :
    rankTwoParallelClass D label = block := by
  obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hblock
  subst hpivot
  exact parallelClass_eq_of_mem D hlive hmember

open scoped Classical in
/-- Atoms drawn from two different classes are different atoms. -/
theorem ne_of_mem_parallelClass_of_class_ne (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {leftPivot rightPivot leftLabel rightLabel : Fin size}
    (hleft : leftLabel ∈ rankTwoParallelClass D leftPivot)
    (hright : rightLabel ∈ rankTwoParallelClass D rightPivot)
    (hclass : rankTwoParallelClass D leftPivot ≠ rankTwoParallelClass D rightPivot) :
    leftLabel ≠ rightLabel := by
  intro hequal
  subst hequal
  exact hclass ((parallelClass_eq_of_mem D hlive hleft).symm.trans
    (parallelClass_eq_of_mem D hlive hright))

/-- A nonpositive family with vanishing total vanishes termwise. -/
theorem eq_zero_of_sum_eq_zero_of_nonpos {index : Type*} (support : Finset index)
    (readout : index → ℝ) (hnonpos : ∀ item ∈ support, readout item ≤ 0)
    (hsum : ∑ item ∈ support, readout item = 0) {chosen : index} (hchosen : chosen ∈ support) :
    readout chosen = 0 := by
  have hnonneg : ∀ item ∈ support, 0 ≤ - readout item :=
    fun item hitem => neg_nonneg.mpr (hnonpos item hitem)
  have hnegSum : ∑ item ∈ support, - readout item = 0 := by
    rw [Finset.sum_neg_distrib, hsum, neg_zero]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hnegSum chosen hchosen
  linarith

/-! ## 4. The class algebra -/

/-- The weight of a parallel class. -/
noncomputable def classWeight (D : WeightedDesign size 2) (block : Finset (Fin size)) : ℝ :=
  ∑ label ∈ block, D.weight label

/-- The mass of a parallel class: its weighted leverage total. -/
noncomputable def classMass (D : WeightedDesign size 2) (block : Finset (Fin size)) : ℝ :=
  ∑ label ∈ block, D.weight label * leverageOf (D.atom label)

/-- The **class defect**: the Nesterenko slack of a whole class. -/
noncomputable def classDefect (D : WeightedDesign size 2) (block : Finset (Fin size)) : ℝ :=
  1 + classWeight D block - 2 * classMass D block

/-- The doubly weighted pair gap total between two classes. -/
noncomputable def classGapForm (D : WeightedDesign size 2)
    (leftBlock rightBlock : Finset (Fin size)) : ℝ :=
  ∑ leftLabel ∈ leftBlock, ∑ rightLabel ∈ rightBlock,
    D.weight leftLabel * D.weight rightLabel * pairGapForm D leftLabel rightLabel

theorem rankTwoClassWeight_pos (D : WeightedDesign size 2) {block : Finset (Fin size)}
    (hnonempty : block.Nonempty) : 0 < classWeight D block :=
  Finset.sum_pos (fun label _ => D.weight_pos label) hnonempty

open scoped Classical in
/-- **The class master identity.**  Summing `sum_d t_d q_cd = -1` against the
weights of a class and splitting the inner total by classes. -/
theorem sum_classGapForm_eq_neg_classWeight (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    (block : Finset (Fin size)) :
    ∑ other ∈ parallelClasses D, classGapForm D block other = - classWeight D block := by
  have hswap : ∑ other ∈ parallelClasses D, classGapForm D block other
      = ∑ leftLabel ∈ block, ∑ other ∈ parallelClasses D, ∑ rightLabel ∈ other,
          D.weight leftLabel * D.weight rightLabel * pairGapForm D leftLabel rightLabel := by
    simp only [classGapForm]
    rw [Finset.sum_comm]
  rw [hswap]
  have hinner : ∀ leftLabel ∈ block,
      (∑ other ∈ parallelClasses D, ∑ rightLabel ∈ other,
        D.weight leftLabel * D.weight rightLabel * pairGapForm D leftLabel rightLabel)
        = - D.weight leftLabel := by
    intro leftLabel _
    rw [sum_over_parallelClasses D hlive
      (fun rightLabel => D.weight leftLabel * D.weight rightLabel
        * pairGapForm D leftLabel rightLabel)]
    have hfactor : ∀ rightLabel : Fin size,
        D.weight leftLabel * D.weight rightLabel * pairGapForm D leftLabel rightLabel
          = D.weight leftLabel * (D.weight rightLabel * pairGapForm D leftLabel rightLabel) :=
      fun rightLabel => by ring
    rw [Finset.sum_congr rfl fun rightLabel _ => hfactor rightLabel, ← Finset.mul_sum,
      sum_weight_mul_pairGapForm_rankTwo D leftLabel]
    ring
  rw [Finset.sum_congr rfl hinner, classWeight, ← Finset.sum_neg_distrib]

/-- **The diagonal class block.**  Inside a class every bracket vanishes, so
Lagrange's identity reads the pair gap form as `1 - l_c - l_d` and the double sum
collapses onto the class weight and the class mass. -/
theorem classGapForm_self (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {block : Finset (Fin size)} (hblock : block ∈ parallelClasses D) :
    classGapForm D block block
      = - classWeight D block * (2 * classMass D block - classWeight D block) := by
  obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hblock
  have hentry : ∀ leftLabel ∈ block, ∀ rightLabel ∈ block,
      D.weight leftLabel * D.weight rightLabel * pairGapForm D leftLabel rightLabel
        = D.weight leftLabel * D.weight rightLabel
          - D.weight leftLabel * (D.weight rightLabel * leverageOf (D.atom rightLabel))
          - D.weight rightLabel * (D.weight leftLabel * leverageOf (D.atom leftLabel)) := by
    intro leftLabel hleft rightLabel hright
    have hbracket : pairBracket D leftLabel rightLabel = 0 := by
      refine pairBracket_eq_zero_of_mem_of_mem D hlive (pivot := pivot) ?_ ?_
      · rw [hpivot]; exact hleft
      · rw [hpivot]; exact hright
    rw [pairGapForm_eq_pairBracket_sq_sub, hbracket]
    ring
  rw [classGapForm]
  rw [Finset.sum_congr rfl fun leftLabel hleft =>
    Finset.sum_congr rfl fun rightLabel hright => hentry leftLabel hleft rightLabel hright]
  have hsplit : ∀ leftLabel ∈ block,
      (∑ rightLabel ∈ block, (D.weight leftLabel * D.weight rightLabel
          - D.weight leftLabel * (D.weight rightLabel * leverageOf (D.atom rightLabel))
          - D.weight rightLabel * (D.weight leftLabel * leverageOf (D.atom leftLabel))))
        = D.weight leftLabel * classWeight D block
          - D.weight leftLabel * classMass D block
          - classWeight D block * (D.weight leftLabel * leverageOf (D.atom leftLabel)) := by
    intro leftLabel _
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.sum_mul, classWeight, classMass]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← classWeight, ← classMass]
  ring

open scoped Classical in
/-- **The defect identity.**  The off-diagonal class blocks total exactly minus
the class weight times the class defect. -/
theorem sum_erase_classGapForm_eq (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0)
    {block : Finset (Fin size)} (hblock : block ∈ parallelClasses D) :
    ∑ other ∈ (parallelClasses D).erase block, classGapForm D block other
      = - classWeight D block * classDefect D block := by
  have hfull := sum_classGapForm_eq_neg_classWeight D hlive block
  rw [← Finset.add_sum_erase _ _ hblock, classGapForm_self D hlive hblock] at hfull
  rw [classDefect]
  linarith

/-- **The class defect is nonnegative.**  Every off-diagonal class block is at
most zero, because distinct classes are disjoint and the sign law holds at every
cross pair. -/
theorem classDefect_nonneg {atoms : ℕ} (D : WeightedDesign atoms 2) (hatoms : 2 ≤ atoms)
    (htie : IsTie D) {block : Finset (Fin atoms)} (hblock : block ∈ parallelClasses D) :
    0 ≤ classDefect D block := by
  classical
  have hlive : ∀ label : Fin atoms, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D hatoms htie label)
  have hnonempty : block.Nonempty := by
    obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hblock
    exact ⟨pivot, by rw [← hpivot]; exact self_mem_parallelClass D pivot⟩
  have hcross : ∀ other ∈ (parallelClasses D).erase block, classGapForm D block other ≤ 0 := by
    intro other hother
    have hne : other ≠ block := (Finset.mem_erase.mp hother).1
    have hotherMem : other ∈ parallelClasses D := (Finset.mem_erase.mp hother).2
    refine Finset.sum_nonpos fun leftLabel hleft => Finset.sum_nonpos fun rightLabel hright => ?_
    have hdistinct : leftLabel ≠ rightLabel := by
      intro hequal
      subst hequal
      exact hne ((parallelClass_eq_of_mem_class D hlive hotherMem hright).symm.trans
        (parallelClass_eq_of_mem_class D hlive hblock hleft))
    have hsign := pairGapForm_nonpos_of_isTie_rankTwo D hatoms htie hdistinct
    have hweights : 0 < D.weight leftLabel * D.weight rightLabel :=
      mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
    exact mul_nonpos_of_nonneg_of_nonpos hweights.le hsign
  have htotal := sum_erase_classGapForm_eq D hlive hblock
  have hnonpos : ∑ other ∈ (parallelClasses D).erase block, classGapForm D block other ≤ 0 :=
    Finset.sum_nonpos hcross
  rw [htotal] at hnonpos
  have hweightPos := rankTwoClassWeight_pos D hnonempty
  nlinarith [hnonpos, hweightPos]

open scoped Classical in
/-- **The defect budget.**  Parseval fixes the two class totals — the weights add
to one and the masses to the rank — so the class defects add to `p - 3`. -/
theorem sum_classDefect_eq (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0) :
    ∑ block ∈ parallelClasses D, classDefect D block
      = ((parallelClasses D).card : ℝ) - 3 := by
  have hweightTotal : ∑ block ∈ parallelClasses D, classWeight D block = 1 := by
    have hunfold : ∑ block ∈ parallelClasses D, classWeight D block
        = ∑ block ∈ parallelClasses D, ∑ label ∈ block, D.weight label := rfl
    rw [hunfold, sum_over_parallelClasses D hlive D.weight]
    exact D.weight_sum_one
  have hmassTotal : ∑ block ∈ parallelClasses D, classMass D block = 2 := by
    have hunfold : ∑ block ∈ parallelClasses D, classMass D block
        = ∑ block ∈ parallelClasses D, ∑ label ∈ block,
            D.weight label * leverageOf (D.atom label) := rfl
    rw [hunfold, sum_over_parallelClasses D hlive
      (fun label => D.weight label * leverageOf (D.atom label))]
    have hparseval := sum_weighted_leverage D
    rw [hparseval]
    norm_num
  simp only [classDefect]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hweightTotal, hmassTotal,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-! ## 5. Three classes, and every cross pair tight -/

open scoped Classical in
/-- **At most three parallel classes.**  Four classes would supply four pairwise
non-parallel atoms, and the rank-two four-direction hinge refuses them at a
tie. -/
theorem card_parallelClasses_le_three {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) : (parallelClasses D).card ≤ 3 := by
  by_contra hbig
  rw [Nat.not_le] at hbig
  have : Nonempty (Fin atoms) := ⟨⟨0, by omega⟩⟩
  set firstLabel : Fin atoms := ⟨0, by omega⟩ with hfirstLabel
  have hcover : ∀ chosen : List (Fin atoms),
      (∀ probe : Fin atoms, ∃ pivot ∈ chosen, pairBracket D pivot probe = 0) →
      (parallelClasses D).card ≤ chosen.length := by
    intro chosen hchosen
    have hsubset : parallelClasses D ⊆ (chosen.map (rankTwoParallelClass D)).toFinset := by
      intro block hblock
      obtain ⟨probe, -, hprobe⟩ := Finset.mem_image.mp hblock
      obtain ⟨pivot, hpivotMem, hpivotZero⟩ := hchosen probe
      have hequal : rankTwoParallelClass D probe = rankTwoParallelClass D pivot :=
        parallelClass_eq_of_mem D
          (fun label => atom_coordinate_ne_zero_of_one_le_leverage D
            (one_le_leverage_of_isTie_rankTwo D hatoms htie label))
          ((mem_parallelClass_iff D pivot probe).mpr hpivotZero)
      rw [← hprobe, hequal, List.mem_toFinset]
      exact List.mem_map_of_mem hpivotMem
    calc (parallelClasses D).card ≤ (chosen.map (rankTwoParallelClass D)).toFinset.card :=
          Finset.card_le_card hsubset
      _ ≤ (chosen.map (rankTwoParallelClass D)).length := List.toFinset_card_le _
      _ = chosen.length := by rw [List.length_map]
  have hone : ∃ secondLabel, pairBracket D firstLabel secondLabel ≠ 0 := by
    by_contra hall
    push Not at hall
    have := hcover [firstLabel] fun probe => ⟨firstLabel, by simp, hall probe⟩
    simp only [List.length_cons, List.length_nil] at this
    omega
  obtain ⟨secondLabel, hsecond⟩ := hone
  have htwo : ∃ thirdLabel, pairBracket D firstLabel thirdLabel ≠ 0
      ∧ pairBracket D secondLabel thirdLabel ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcoverTwo : ∀ probe : Fin atoms,
        ∃ pivot ∈ [firstLabel, secondLabel], pairBracket D pivot probe = 0 := by
      intro probe
      rcases eq_or_ne (pairBracket D firstLabel probe) 0 with hzero | hnonzero
      · exact ⟨firstLabel, by simp, hzero⟩
      · exact ⟨secondLabel, by simp, hall probe hnonzero⟩
    have := hcover [firstLabel, secondLabel] hcoverTwo
    simp only [List.length_cons, List.length_nil] at this
    omega
  obtain ⟨thirdLabel, hthirdOne, hthirdTwo⟩ := htwo
  have hthree : ∃ fourthLabel, pairBracket D firstLabel fourthLabel ≠ 0
      ∧ pairBracket D secondLabel fourthLabel ≠ 0
      ∧ pairBracket D thirdLabel fourthLabel ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcoverThree : ∀ probe : Fin atoms,
        ∃ pivot ∈ [firstLabel, secondLabel, thirdLabel], pairBracket D pivot probe = 0 := by
      intro probe
      rcases eq_or_ne (pairBracket D firstLabel probe) 0 with hzero | hfirstNonzero
      · exact ⟨firstLabel, by simp, hzero⟩
      rcases eq_or_ne (pairBracket D secondLabel probe) 0 with hzero | hsecondNonzero
      · exact ⟨secondLabel, by simp, hzero⟩
      exact ⟨thirdLabel, by simp, hall probe hfirstNonzero hsecondNonzero⟩
    have := hcover [firstLabel, secondLabel, thirdLabel] hcoverThree
    simp only [List.length_cons, List.length_nil] at this
    omega
  obtain ⟨fourthLabel, hfourthOne, hfourthTwo, hfourthThree⟩ := hthree
  have hdistinct : ∀ {leftLabel rightLabel : Fin atoms},
      pairBracket D leftLabel rightLabel ≠ 0 → leftLabel ≠ rightLabel := by
    intro leftLabel rightLabel hbracket hequal
    exact hbracket (by rw [hequal]; exact pairBracket_self D rightLabel)
  exact not_isTie_of_fourNonParallel D firstLabel secondLabel thirdLabel fourthLabel
    (hdistinct hsecond) (hdistinct hthirdOne) (hdistinct hfourthOne)
    (hdistinct hthirdTwo) (hdistinct hfourthTwo) (hdistinct hfourthThree)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hsecond)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hthirdOne)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hfourthOne)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hthirdTwo)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hfourthTwo)
    (unitPairGram_ne_one_of_pairBracket_ne_zero D _ _ hfourthThree) htie

open scoped Classical in
/-- **THE THREE-CLASS LAW.**  A rank-two tie has exactly three parallel classes
and every class defect vanishes.  The defects are nonnegative and add to
`p - 3`, while the hinge caps `p` at three. -/
theorem card_parallelClasses_eq_three_and_classDefect_eq_zero {atoms : ℕ}
    (D : WeightedDesign atoms 2) (hatoms : 2 ≤ atoms) (htie : IsTie D) :
    (parallelClasses D).card = 3
      ∧ ∀ block ∈ parallelClasses D, classDefect D block = 0 := by
  have hlive : ∀ label : Fin atoms, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D hatoms htie label)
  have hnonneg : ∀ block ∈ parallelClasses D, 0 ≤ classDefect D block :=
    fun block hblock => classDefect_nonneg D hatoms htie hblock
  have hbudget := sum_classDefect_eq D hlive
  have hcap := card_parallelClasses_le_three D hatoms htie
  have hsumNonneg : 0 ≤ ∑ block ∈ parallelClasses D, classDefect D block :=
    Finset.sum_nonneg hnonneg
  have hcardGe : 3 ≤ (parallelClasses D).card := by
    by_contra hsmall
    rw [Nat.not_le] at hsmall
    have hcast : ((parallelClasses D).card : ℝ) < 3 := by exact_mod_cast hsmall
    rw [hbudget] at hsumNonneg
    linarith
  have hcardEq : (parallelClasses D).card = 3 := le_antisymm hcap hcardGe
  refine ⟨hcardEq, ?_⟩
  have hsumZero : ∑ block ∈ parallelClasses D, classDefect D block = 0 := by
    rw [hbudget, hcardEq]
    norm_num
  exact fun block hblock =>
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumZero block hblock

open scoped Classical in
/-- **EVERY CROSS-CLASS PAIR IS TIGHT.**  A vanishing class defect forces every
off-diagonal class block to vanish, and every summand of such a block is at most
zero, so each pair gap form across two classes is exactly zero. -/
theorem pairGapForm_eq_zero_of_parallelClass_ne {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) {leftLabel rightLabel : Fin atoms}
    (hclass : rankTwoParallelClass D leftLabel ≠ rankTwoParallelClass D rightLabel) :
    pairGapForm D leftLabel rightLabel = 0 := by
  have hlive : ∀ label : Fin atoms, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D hatoms htie label)
  obtain ⟨-, hdefect⟩ := card_parallelClasses_eq_three_and_classDefect_eq_zero D hatoms htie
  have hleftMem : rankTwoParallelClass D leftLabel ∈ parallelClasses D :=
    parallelClass_mem_parallelClasses D leftLabel
  have hrightMem : rankTwoParallelClass D rightLabel ∈ parallelClasses D :=
    parallelClass_mem_parallelClasses D rightLabel
  have htotal := sum_erase_classGapForm_eq D hlive hleftMem
  rw [hdefect _ hleftMem] at htotal
  have hsumZero : ∑ other ∈ (parallelClasses D).erase (rankTwoParallelClass D leftLabel),
      classGapForm D (rankTwoParallelClass D leftLabel) other = 0 := by
    rw [htotal]; ring
  have hcross : ∀ other ∈ (parallelClasses D).erase (rankTwoParallelClass D leftLabel),
      classGapForm D (rankTwoParallelClass D leftLabel) other ≤ 0 := by
    intro other hother
    have hne : other ≠ rankTwoParallelClass D leftLabel := (Finset.mem_erase.mp hother).1
    have hotherMem : other ∈ parallelClasses D := (Finset.mem_erase.mp hother).2
    refine Finset.sum_nonpos fun probeLeft hprobeLeft =>
      Finset.sum_nonpos fun probeRight hprobeRight => ?_
    have hdistinct : probeLeft ≠ probeRight := by
      intro hequal
      subst hequal
      exact hne ((parallelClass_eq_of_mem_class D hlive hotherMem hprobeRight).symm.trans
        (parallelClass_eq_of_mem_class D hlive hleftMem hprobeLeft))
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (D.weight_pos probeLeft) (D.weight_pos probeRight)).le
      (pairGapForm_nonpos_of_isTie_rankTwo D hatoms htie hdistinct)
  have hmemErase : rankTwoParallelClass D rightLabel
      ∈ (parallelClasses D).erase (rankTwoParallelClass D leftLabel) :=
    Finset.mem_erase.mpr ⟨fun hcontra => hclass hcontra.symm, hrightMem⟩
  have hblockZero := eq_zero_of_sum_eq_zero_of_nonpos _ _ hcross hsumZero hmemErase
  simp only [classGapForm] at hblockZero
  have hrowNonpos : ∀ probeLeft ∈ rankTwoParallelClass D leftLabel,
      (∑ probeRight ∈ rankTwoParallelClass D rightLabel,
        D.weight probeLeft * D.weight probeRight * pairGapForm D probeLeft probeRight) ≤ 0 := by
    intro probeLeft hprobeLeft
    refine Finset.sum_nonpos fun probeRight hprobeRight => ?_
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (D.weight_pos probeLeft) (D.weight_pos probeRight)).le
      (pairGapForm_nonpos_of_isTie_rankTwo D hatoms htie
        (ne_of_mem_parallelClass_of_class_ne D hlive hprobeLeft hprobeRight hclass))
  have hrowZero := eq_zero_of_sum_eq_zero_of_nonpos _ _ hrowNonpos hblockZero
    (self_mem_parallelClass D leftLabel)
  have hentryNonpos : ∀ probeRight ∈ rankTwoParallelClass D rightLabel,
      D.weight leftLabel * D.weight probeRight * pairGapForm D leftLabel probeRight ≤ 0 := by
    intro probeRight hprobeRight
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (D.weight_pos leftLabel) (D.weight_pos probeRight)).le
      (pairGapForm_nonpos_of_isTie_rankTwo D hatoms htie
        (ne_of_mem_parallelClass_of_class_ne D hlive (self_mem_parallelClass D leftLabel)
          hprobeRight hclass))
  have hentryZero := eq_zero_of_sum_eq_zero_of_nonpos _ _ hentryNonpos hrowZero
    (self_mem_parallelClass D rightLabel)
  have hweights : D.weight leftLabel * D.weight rightLabel ≠ 0 :=
    (mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)).ne'
  exact (mul_eq_zero.mp hentryZero).resolve_left hweights

open scoped Classical in
/-- **THE RANK-TWO TIE DICTIONARY.**  Two atoms of a rank-two tie in different
parallel classes dominate as a pair. -/
theorem dominates_pair_of_parallelClass_ne {atoms : ℕ} (D : WeightedDesign atoms 2)
    (hatoms : 2 ≤ atoms) (htie : IsTie D) {leftLabel rightLabel : Fin atoms}
    (hclass : rankTwoParallelClass D leftLabel ≠ rankTwoParallelClass D rightLabel) :
    Dominates D {leftLabel, rightLabel} := by
  have hdistinct : leftLabel ≠ rightLabel := fun hequal => hclass (by rw [hequal])
  exact dominates_pair_of_pairGapForm_eq_zero D hatoms htie hdistinct
    (pairGapForm_eq_zero_of_parallelClass_ne D hatoms htie hclass)


/-! ## 6. The dominating family, and four triples at `(5,3)` -/

open scoped Classical in
/-- The family of dominating subsets of a design at a fixed size.  The campaign
had no such object: dominating subsets were produced one at a time and never
counted. -/
noncomputable def dominatingFamily {atoms rank : ℕ} (D : WeightedDesign atoms rank)
    (chosenSize : ℕ) : Finset (Finset (Fin atoms)) :=
  (Finset.univ.powersetCard chosenSize).filter fun selected => Dominates D selected

open scoped Classical in
theorem mem_dominatingFamily_iff {atoms rank : ℕ} (D : WeightedDesign atoms rank)
    (chosenSize : ℕ) (selected : Finset (Fin atoms)) :
    selected ∈ dominatingFamily D chosenSize
      ↔ selected.card = chosenSize ∧ Dominates D selected := by
  rw [dominatingFamily, Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨-, hcard⟩, hdominates⟩
    exact ⟨hcard, hdominates⟩
  · rintro ⟨hcard, hdominates⟩
    exact ⟨⟨Finset.subset_univ _, hcard⟩, hdominates⟩

open scoped Classical in
/-- **THE CLASS SIZES ADD TO THE ATOM COUNT.** -/
theorem sum_card_parallelClasses (D : WeightedDesign size 2)
    (hlive : ∀ label : Fin size, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0) :
    ∑ block ∈ parallelClasses D, block.card = size := by
  have hunfold : ∑ block ∈ parallelClasses D, block.card
      = ∑ block ∈ parallelClasses D, ∑ label ∈ block, 1 :=
    Finset.sum_congr rfl fun block _ => Finset.card_eq_sum_ones block
  rw [hunfold, sum_over_parallelClasses D hlive (fun _ => (1 : ℕ))]
  simp

open scoped Classical in
/-- **A FIVE-ATOM RANK-TWO TIE HAS AN ISOLATED ATOM.**  Its three classes cannot
all carry two atoms, so one of them is a singleton, and that atom sits in a
different class from each of the other four. -/
theorem exists_isolated_atom_of_isTie_fiveTwo (D : WeightedDesign 5 2) (htie : IsTie D) :
    ∃ pivot : Fin 5, ∀ other : Fin 5, other ≠ pivot →
      rankTwoParallelClass D other ≠ rankTwoParallelClass D pivot := by
  have hlive : ∀ label : Fin 5, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D (by norm_num) htie label)
  obtain ⟨hcardClasses, -⟩ :=
    card_parallelClasses_eq_three_and_classDefect_eq_zero D (by norm_num) htie
  by_contra hall
  push Not at hall
  have htwo : ∀ block ∈ parallelClasses D, 2 ≤ block.card := by
    intro block hblock
    obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hblock
    obtain ⟨other, hother, hsame⟩ := hall pivot
    have hpivotMem : pivot ∈ block := by
      rw [← hpivot]
      exact self_mem_parallelClass D pivot
    have hotherMem : other ∈ block := by
      rw [← hpivot, ← hsame]
      exact self_mem_parallelClass D other
    exact Finset.one_lt_card.mpr ⟨other, hotherMem, pivot, hpivotMem, hother⟩
  have hfloor := Finset.card_nsmul_le_sum (parallelClasses D) (fun block => block.card) 2 htwo
  rw [sum_card_parallelClasses D hlive, hcardClasses, smul_eq_mul] at hfloor
  omega

open scoped Classical in
/-- **FOUR DOMINATING PAIRS AT `(5,2)`.**  The isolated atom is cross-class to
each of the other four, and every cross-class pair of a rank-two tie
dominates. -/
theorem four_le_card_dominatingFamily_of_isTie_fiveTwo (D : WeightedDesign 5 2)
    (htie : IsTie D) : 4 ≤ (dominatingFamily D 2).card := by
  obtain ⟨pivot, hpivot⟩ := exists_isolated_atom_of_isTie_fiveTwo D htie
  have hmaps : ∀ other ∈ Finset.univ.erase pivot,
      ({pivot, other} : Finset (Fin 5)) ∈ dominatingFamily D 2 := by
    intro other hother
    have hdistinct : other ≠ pivot := (Finset.mem_erase.mp hother).1
    refine (mem_dominatingFamily_iff D 2 _).mpr
      ⟨Finset.card_pair (Ne.symm hdistinct), ?_⟩
    exact dominates_pair_of_parallelClass_ne D (by norm_num) htie
      (fun hcontra => hpivot other hdistinct hcontra.symm)
  have hinjective : Set.InjOn (fun other => ({pivot, other} : Finset (Fin 5)))
      ((Finset.univ.erase pivot : Finset (Fin 5)) : Set (Fin 5)) := by
    intro leftLabel hleft rightLabel _ hequal
    have hleftNe : leftLabel ≠ pivot :=
      (Finset.mem_erase.mp (Finset.mem_coe.mp hleft)).1
    have hbeta : ({pivot, leftLabel} : Finset (Fin 5)) = {pivot, rightLabel} := hequal
    have hmember : leftLabel ∈ ({pivot, rightLabel} : Finset (Fin 5)) := by
      rw [← hbeta]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self leftLabel)
    rcases Finset.mem_insert.mp hmember with hcontra | hmember
    · exact absurd hcontra hleftNe
    · exact Finset.mem_singleton.mp hmember
  have hcardErase : (Finset.univ.erase pivot : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ pivot), Finset.card_univ, Fintype.card_fin]
  calc (4 : ℕ) = (Finset.univ.erase pivot : Finset (Fin 5)).card := hcardErase.symm
    _ ≤ (dominatingFamily D 2).card := Finset.card_le_card_of_injOn _ hmaps hinjective

open scoped Classical in
/-- **THE COMPLEMENT CARRIES THE COUNT.**  Naimark duality in its two-sided
Loewner form turns a `(5,3)` tie into a `(5,2)` tie: the strict verdict crosses,
so the absence of a strict dominator crosses, and complementation is an injection
from the dual's dominating pairs into the primal's dominating triples. -/
theorem exists_dual_isTie_card_dominatingFamily_le_fiveThree (D : WeightedDesign 5 3)
    (htie : IsTie D) :
    ∃ dual : WeightedDesign 5 2, IsTie dual
      ∧ (dominatingFamily dual 2).card ≤ (dominatingFamily D 3).card := by
  obtain ⟨dual, -, -, hequiv⟩ :=
    exists_naimarkDual_loewnerEquiv (k := 3) (m := 5) (by norm_num) (by norm_num) D
  have hcomplTriple : ∀ selected : Finset (Fin 5), selected.card = 3 → selectedᶜ.card = 2 := by
    intro selected hcard
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hcomplPair : ∀ selected : Finset (Fin 5), selected.card = 2 → selectedᶜ.card = 3 := by
    intro selected hcard
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hdualTie : IsTie dual := by
    refine ⟨?_, ?_⟩
    · obtain ⟨selected, hcard, hdominates⟩ := htie.1
      exact ⟨selectedᶜ, hcomplTriple selected hcard, (hequiv selected hcard).1.mp hdominates⟩
    · intro selected hcard hposDef
      refine htie.2 selectedᶜ (hcomplPair selected hcard) ?_
      refine (hequiv selectedᶜ (hcomplPair selected hcard)).2.mpr ?_
      rwa [compl_compl]
  refine ⟨dual, hdualTie, ?_⟩
  have hmaps : ∀ selected ∈ dominatingFamily dual 2, selectedᶜ ∈ dominatingFamily D 3 := by
    intro selected hselected
    obtain ⟨hcard, hdominates⟩ := (mem_dominatingFamily_iff dual 2 selected).mp hselected
    refine (mem_dominatingFamily_iff D 3 _).mpr ⟨hcomplPair selected hcard, ?_⟩
    refine (hequiv selectedᶜ (hcomplPair selected hcard)).1.mpr ?_
    rwa [compl_compl]
  have hinjective : Set.InjOn (fun selected : Finset (Fin 5) => selectedᶜ)
      ((dominatingFamily dual 2 : Finset (Finset (Fin 5))) : Set (Finset (Fin 5))) := by
    intro leftSet _ rightSet _ hequal
    have hback := congrArg (fun candidate : Finset (Fin 5) => candidateᶜ) hequal
    simpa using hback
  exact Finset.card_le_card_of_injOn _ hmaps hinjective

open scoped Classical in
/-- **QUESTION 7.1, ANSWERED.**  Every `(5,3)` tie carries at least four weakly
dominating triples. -/
theorem four_le_card_dominatingFamily_of_isTie_fiveThree (D : WeightedDesign 5 3)
    (htie : IsTie D) : 4 ≤ (dominatingFamily D 3).card := by
  obtain ⟨dual, hdualTie, hcount⟩ :=
    exists_dual_isTie_card_dominatingFamily_le_fiveThree D htie
  exact le_trans (four_le_card_dominatingFamily_of_isTie_fiveTwo dual hdualTie) hcount

open scoped Classical in
/-- **Question 7.1 in the campaign's own words.**  At least four `3`-subsets of a
`(5,3)` tie have a positive semidefinite gap matrix. -/
theorem four_le_card_dominatingTriples_of_isTie_fiveThree (D : WeightedDesign 5 3)
    (htie : IsTie D) :
    4 ≤ (Finset.univ.filter fun selected : Finset (Fin 5) =>
      selected.card = 3 ∧ (subsetSum D selected - 1).PosSemidef).card := by
  have hrewrite : (Finset.univ.filter fun selected : Finset (Fin 5) =>
      selected.card = 3 ∧ (subsetSum D selected - 1).PosSemidef) = dominatingFamily D 3 := by
    ext selected
    rw [Finset.mem_filter, mem_dominatingFamily_iff]
    exact ⟨fun hmember => hmember.2, fun hmember => ⟨Finset.mem_univ selected, hmember⟩⟩
  rw [hrewrite]
  exact four_le_card_dominatingFamily_of_isTie_fiveThree D htie


/-! ## 7. The sharp count: seven -/

open scoped Classical in
/-- No parallel class of a five-atom rank-two tie carries more than three atoms:
the other two classes carry an atom each. -/
theorem card_parallelClass_le_three_fiveTwo (D : WeightedDesign 5 2) (htie : IsTie D)
    {block : Finset (Fin 5)} (hblock : block ∈ parallelClasses D) : block.card ≤ 3 := by
  have hlive : ∀ label : Fin 5, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D (by norm_num) htie label)
  obtain ⟨hcardClasses, -⟩ :=
    card_parallelClasses_eq_three_and_classDefect_eq_zero D (by norm_num) htie
  have hnonempty : ∀ other ∈ parallelClasses D, 1 ≤ other.card := by
    intro other hother
    obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hother
    refine Finset.card_pos.mpr ⟨pivot, ?_⟩
    rw [← hpivot]
    exact self_mem_parallelClass D pivot
  have htotal := sum_card_parallelClasses D hlive
  rw [← Finset.add_sum_erase _ _ hblock] at htotal
  have hrest : ((parallelClasses D).erase block).card • 1
      ≤ ∑ other ∈ (parallelClasses D).erase block, other.card :=
    Finset.card_nsmul_le_sum _ _ 1
      fun other hother => hnonempty other (Finset.mem_of_mem_erase hother)
  rw [Finset.card_erase_of_mem hblock, hcardClasses, smul_eq_mul, mul_one] at hrest
  omega

open scoped Classical in
/-- **THE NON-DOMINATING PAIRS LIVE INSIDE THE CLASSES.**  Every cross-class pair
dominates, so a pair that fails to dominate has both atoms in one class. -/
theorem nonDominating_pairs_subset_biUnion (D : WeightedDesign 5 2) (htie : IsTie D) :
    ((Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).filter
        fun selected => ¬ Dominates D selected)
      ⊆ (parallelClasses D).biUnion fun block => block.powersetCard 2 := by
  intro selected hselected
  rw [Finset.mem_filter, Finset.mem_powersetCard] at hselected
  obtain ⟨⟨-, hcard⟩, hrefuses⟩ := hselected
  obtain ⟨leftLabel, rightLabel, hdistinct, hpair⟩ := Finset.card_eq_two.mp hcard
  have hsame : rankTwoParallelClass D leftLabel = rankTwoParallelClass D rightLabel := by
    by_contra hne
    refine hrefuses ?_
    rw [hpair]
    exact dominates_pair_of_parallelClass_ne D (by norm_num) htie hne
  refine Finset.mem_biUnion.mpr ⟨rankTwoParallelClass D leftLabel,
    parallelClass_mem_parallelClasses D leftLabel, ?_⟩
  rw [Finset.mem_powersetCard]
  refine ⟨?_, hcard⟩
  rw [hpair]
  intro probe hprobe
  rcases Finset.mem_insert.mp hprobe with hleft | hright
  · rw [hleft]
    exact self_mem_parallelClass D leftLabel
  · rw [Finset.mem_singleton.mp hright, hsame]
    exact self_mem_parallelClass D rightLabel

open scoped Classical in
/-- **AT MOST THREE PAIRS REFUSE.**  Three classes of sizes at least one and at
most three, adding to five, carry at most three internal pairs: the sizes are
`(3,1,1)` or `(2,2,1)`. -/
theorem card_nonDominating_pairs_le_three (D : WeightedDesign 5 2) (htie : IsTie D) :
    (((Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).filter
        fun selected => ¬ Dominates D selected)).card ≤ 3 := by
  have hlive : ∀ label : Fin 5, D.atom label 0 ≠ 0 ∨ D.atom label 1 ≠ 0 :=
    fun label => atom_coordinate_ne_zero_of_one_le_leverage D
      (one_le_leverage_of_isTie_rankTwo D (by norm_num) htie label)
  obtain ⟨hcardClasses, -⟩ :=
    card_parallelClasses_eq_three_and_classDefect_eq_zero D (by norm_num) htie
  have hnonempty : ∀ other ∈ parallelClasses D, 1 ≤ other.card := by
    intro other hother
    obtain ⟨pivot, -, hpivot⟩ := Finset.mem_image.mp hother
    refine Finset.card_pos.mpr ⟨pivot, ?_⟩
    rw [← hpivot]
    exact self_mem_parallelClass D pivot
  have hbound : (((Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).filter
        fun selected => ¬ Dominates D selected)).card
      ≤ ∑ block ∈ parallelClasses D, (block.powersetCard 2).card :=
    le_trans (Finset.card_le_card (nonDominating_pairs_subset_biUnion D htie))
      (Finset.card_biUnion_le)
  have hchoose : ∀ block ∈ parallelClasses D,
      2 * (block.powersetCard 2).card + 3 ≤ 3 * block.card := by
    intro block hblock
    rw [Finset.card_powersetCard]
    have hlow : 1 ≤ block.card := hnonempty block hblock
    have hhigh : block.card ≤ 3 := card_parallelClass_le_three_fiveTwo D htie hblock
    obtain ⟨blockSize, hblockSize⟩ : ∃ blockSize, block.card = blockSize := ⟨_, rfl⟩
    rw [hblockSize] at hlow hhigh ⊢
    interval_cases blockSize <;> decide
  have hsum : ∑ block ∈ parallelClasses D, (2 * (block.powersetCard 2).card + 3)
      ≤ ∑ block ∈ parallelClasses D, 3 * block.card := Finset.sum_le_sum hchoose
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    smul_eq_mul, hcardClasses, sum_card_parallelClasses D hlive] at hsum
  omega

open scoped Classical in
/-- **SEVEN DOMINATING PAIRS AT `(5,2)`.**  Ten pairs, at most three of them
internal to a class, and every other pair dominates.  The bound is attained: the
sharp `(5,2)` partner of the diamond has class sizes `(1,2,2)` and eight
dominating pairs, while class sizes `(3,1,1)` give exactly seven. -/
theorem seven_le_card_dominatingFamily_of_isTie_fiveTwo (D : WeightedDesign 5 2)
    (htie : IsTie D) : 7 ≤ (dominatingFamily D 2).card := by
  have hsplit : ((Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).filter
        fun selected => Dominates D selected).card
      + (((Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).filter
        fun selected => ¬ Dominates D selected)).card
      = (Finset.univ.powersetCard 2 : Finset (Finset (Fin 5))).card :=
    Finset.card_filter_add_card_filter_not _
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hsplit
  have hbad := card_nonDominating_pairs_le_three D htie
  have hfamily : dominatingFamily D 2 = (Finset.univ.powersetCard 2).filter
      fun selected => Dominates D selected := rfl
  rw [hfamily]
  have hchoose : Nat.choose 5 2 = 10 := by decide
  rw [hchoose] at hsplit
  omega

open scoped Classical in
/-- **SEVEN DOMINATING TRIPLES AT `(5,3)`.**  The sharp form of Question 7.1: the
count is never four, five or six.  Against the swap-degree cap of three
(`Gtz.swapDegree_le_one_card_le_three`) this leaves no room at all. -/
theorem seven_le_card_dominatingFamily_of_isTie_fiveThree (D : WeightedDesign 5 3)
    (htie : IsTie D) : 7 ≤ (dominatingFamily D 3).card := by
  obtain ⟨dual, hdualTie, hcount⟩ :=
    exists_dual_isTie_card_dominatingFamily_le_fiveThree D htie
  exact le_trans (seven_le_card_dominatingFamily_of_isTie_fiveTwo dual hdualTie) hcount

open scoped Classical in
/-- Question 7.1 in the campaign's own words, sharply. -/
theorem seven_le_card_dominatingTriples_of_isTie_fiveThree (D : WeightedDesign 5 3)
    (htie : IsTie D) :
    7 ≤ (Finset.univ.filter fun selected : Finset (Fin 5) =>
      selected.card = 3 ∧ (subsetSum D selected - 1).PosSemidef).card := by
  have hrewrite : (Finset.univ.filter fun selected : Finset (Fin 5) =>
      selected.card = 3 ∧ (subsetSum D selected - 1).PosSemidef) = dominatingFamily D 3 := by
    ext selected
    rw [Finset.mem_filter, mem_dominatingFamily_iff]
    exact ⟨fun hmember => hmember.2, fun hmember => ⟨Finset.mem_univ selected, hmember⟩⟩
  rw [hrewrite]
  exact seven_le_card_dominatingFamily_of_isTie_fiveThree D htie


/-! ## 8. Light-atom deflation preserves ties -/

/-- The light atom's own Parseval block is positive definite. -/
theorem posDef_one_sub_weight_smul_atomMatrix {atoms rank : ℕ}
    (D : WeightedDesign atoms rank) (hatoms : 2 ≤ atoms) (light : Fin atoms)
    (hlight : leverageOf (D.atom light) ≤ 1) :
    (1 - D.weight light • atomMatrix (D.atom light)).PosDef := by
  have hweightPos := D.weight_pos light
  have hslack : (0 : ℝ) < 1 - D.weight light := by
    linarith [weight_lt_one D hatoms light]
  have hsymmetric : (1 - D.weight light • atomMatrix (D.atom light))ᵀ
      = 1 - D.weight light • atomMatrix (D.atom light) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom light)).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm probe (D.atom light)]
  have hcauchy : (D.atom light ⬝ᵥ probe) * (D.atom light ⬝ᵥ probe)
      ≤ leverageOf (D.atom light) * (probe ⬝ᵥ probe) := by
    have hineq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (D.atom light) probe
    rw [dotProduct, dotProduct_self_eq_sum_sq, leverageOf]
    nlinarith [hineq]
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  nlinarith [mul_le_mul_of_nonneg_left hcauchy hweightPos.le,
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hweightPos.le hlight) hprobePos.le,
    mul_pos hslack hprobePos]

/-- The deflated gap of a selection is symmetric. -/
theorem deflatedGap_transpose {atoms rank : ℕ} (D : WeightedDesign (atoms + 1) rank)
    (light : Fin (atoms + 1)) (selected : Finset (Fin (atoms + 1))) :
    ((((1 : ℝ) - D.weight light) • subsetSum D selected)
        - (1 - D.weight light • atomMatrix (D.atom light)))ᵀ
      = (((1 : ℝ) - D.weight light) • subsetSum D selected)
        - (1 - D.weight light • atomMatrix (D.atom light)) := by
  rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom light)).1]

/-- **THE DEFLATION CONGRUENCE, PER SELECTION.**  The gap matrix of a selection
in the deflated design is the congruence by `R` of the primal deflated gap at the
lifted selection.  Both Loewner verdicts therefore cross, in both directions. -/
theorem deflatedGap_congruence {atoms rank : ℕ} (D : WeightedDesign (atoms + 1) rank)
    (light : Fin (atoms + 1)) (R : Matrix (Fin rank) (Fin rank) ℝ)
    (hslack : (0 : ℝ) < 1 - D.weight light)
    (hcongruence : Rᵀ * (1 - D.weight light • atomMatrix (D.atom light)) * R = 1)
    (chosen : Finset (Fin atoms)) :
    Rᵀ * ((((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove))
        - (1 - D.weight light • atomMatrix (D.atom light))) * R
      = subsetSum (deflatedDesign D light R hslack hcongruence) chosen - 1 := by
  have hembed : Function.Injective light.succAbove := Fin.succAbove_right_injective
  have hlift : subsetSum (deflatedDesign D light R hslack hcongruence) chosen
      = Rᵀ * (((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove)) * R := by
    rw [subsetSum, subsetSum, Finset.sum_image fun left _ right _ hlr => hembed hlr,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [show (deflatedDesign D light R hslack hcongruence).atom index
        = Real.sqrt (1 - D.weight light) • (Rᵀ *ᵥ D.atom (light.succAbove index)) from rfl,
      atomMatrix_smul, Real.sq_sqrt hslack.le, transpose_mul_atomMatrix_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, hcongruence, hlift]

/-- **DEFLATED DOMINATION LIFTS.**  A dominating selection of the deflated design
lifts to a dominating selection of the primal, and a strictly dominating one
lifts strictly.  The light atom's rank-one defect `1 - g g^T` is what pays for
the lift, and it is positive semidefinite exactly because the atom is light. -/
theorem dominates_image_of_dominates_deflatedDesign {atoms rank : ℕ}
    (D : WeightedDesign (atoms + 1) rank) (light : Fin (atoms + 1)) (hlight : leverageOf (D.atom light) ≤ 1)
    (R : Matrix (Fin rank) (Fin rank) ℝ) (hunit : IsUnit R.det)
    (hslack : (0 : ℝ) < 1 - D.weight light)
    (hcongruence : Rᵀ * (1 - D.weight light • atomMatrix (D.atom light)) * R = 1)
    {chosen : Finset (Fin atoms)}
    (hdominates : Dominates (deflatedDesign D light R hslack hcongruence) chosen) :
    Dominates D (chosen.image light.succAbove) := by
  have hdefect : (1 - atomMatrix (D.atom light)).PosSemidef :=
    (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one (D.atom light)).mpr
      (by rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]; exact hlight)
  have hgap : ((((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove))
      - (1 - D.weight light • atomMatrix (D.atom light))).PosSemidef := by
    refine (posSemidef_congr_right
      (deflatedGap_transpose D light (chosen.image light.succAbove)) hunit).mpr ?_
    rw [deflatedGap_congruence D light R hslack hcongruence chosen]
    exact hdominates
  show (subsetSum D (chosen.image light.succAbove) - 1).PosSemidef
  rw [subsetSum_sub_one_eq_deflatedGap_combination D light _ hslack]
  exact (hgap.add (hdefect.smul (D.weight_pos light).le)).smul (inv_nonneg.mpr hslack.le)

/-- The strict twin of `Gtz.dominates_image_of_dominates_deflatedDesign`. -/
theorem posDef_image_of_posDef_deflatedDesign {atoms rank : ℕ}
    (D : WeightedDesign (atoms + 1) rank) (light : Fin (atoms + 1)) (hlight : leverageOf (D.atom light) ≤ 1)
    (R : Matrix (Fin rank) (Fin rank) ℝ) (hunit : IsUnit R.det)
    (hslack : (0 : ℝ) < 1 - D.weight light)
    (hcongruence : Rᵀ * (1 - D.weight light • atomMatrix (D.atom light)) * R = 1)
    {chosen : Finset (Fin atoms)}
    (hstrict : (subsetSum (deflatedDesign D light R hslack hcongruence) chosen - 1).PosDef) :
    (subsetSum D (chosen.image light.succAbove) - 1).PosDef := by
  have hdefect : (1 - atomMatrix (D.atom light)).PosSemidef :=
    (posSemidef_sub_vecMulVec_iff 1 Matrix.PosDef.one (D.atom light)).mpr
      (by rw [inv_one, Matrix.one_mulVec, dotProduct_self_eq_sum_sq]; exact hlight)
  have hgap : ((((1 : ℝ) - D.weight light) • subsetSum D (chosen.image light.succAbove))
      - (1 - D.weight light • atomMatrix (D.atom light))).PosDef := by
    refine (posDef_congr_right
      (deflatedGap_transpose D light (chosen.image light.succAbove)) hunit).mpr ?_
    rw [deflatedGap_congruence D light R hslack hcongruence chosen]
    exact hstrict
  rw [subsetSum_sub_one_eq_deflatedGap_combination D light _ hslack]
  exact Matrix.PosDef.smul (Matrix.PosDef.add_posSemidef hgap
    (hdefect.smul (D.weight_pos light).le)) (inv_pos.mpr hslack)

/-- **LIGHT-ATOM DEFLATION PRESERVES TIES.**  Weighted GTZ one size down supplies
the deflated design's own weak dominator, and the strict lift carries every
strict dominator of the deflated design back to the primal, which a tie refuses.
So the deflation of a tie at a light atom is again a tie. -/
theorem isTie_deflatedDesign {atoms rank : ℕ} (D : WeightedDesign (atoms + 1) rank)
    (hrec : GtzWeighted atoms rank) (htie : IsTie D)
    (light : Fin (atoms + 1)) (hlight : leverageOf (D.atom light) ≤ 1)
    (R : Matrix (Fin rank) (Fin rank) ℝ) (hunit : IsUnit R.det)
    (hslack : (0 : ℝ) < 1 - D.weight light)
    (hcongruence : Rᵀ * (1 - D.weight light • atomMatrix (D.atom light)) * R = 1) :
    IsTie (deflatedDesign D light R hslack hcongruence) := by
  refine ⟨hrec _, fun chosen hcard hstrict => ?_⟩
  have hembed : Function.Injective light.succAbove := Fin.succAbove_right_injective
  refine htie.2 (chosen.image light.succAbove) ?_
    (posDef_image_of_posDef_deflatedDesign D light hlight R hunit hslack
      hcongruence hstrict)
  rw [Finset.card_image_of_injective _ hembed, hcard]

/-! ## 9. The `(6,3)` cell: a tie with a light atom carries seven triples -/

open scoped Classical in
/-- **SEVEN DOMINATING TRIPLES AT A `(6,3)` TIE WITH A LIGHT ATOM, ALL AVOIDING
IT.**  Deflating the light atom leaves a `(5,3)` design which is again a tie, so
the three-class law gives it seven dominating triples, and each lifts to a
dominating triple of the `(6,3)` design that misses the light atom.

Against the swap-degree cap of three (`Gtz.swapDegree_le_one_card_le_three`),
seven leaves no room: the dominators of such a tie cannot all be one swap from at
most one other. -/
theorem seven_le_card_dominatingFamily_of_isTie_sixThree_of_light
    (D : WeightedDesign 6 3) (htie : IsTie D) (light : Fin 6)
    (hlight : leverageOf (D.atom light) ≤ 1) :
    7 ≤ ((dominatingFamily D 3).filter fun selected => light ∉ selected).card := by
  have hslack : (0 : ℝ) < 1 - D.weight light := by
    linarith [weight_lt_one D (by norm_num) light]
  obtain ⟨R, hunit, hcongruence⟩ :=
    exists_congruence_to_one (posDef_one_sub_weight_smul_atomMatrix D (by norm_num) light hlight)
  set deflated := deflatedDesign D light R hslack hcongruence with hdeflated
  have hrec : GtzWeighted 5 3 := gtzWeighted_corank_two 3 (by norm_num)
  have hdeflatedTie : IsTie deflated :=
    isTie_deflatedDesign D hrec htie light hlight R hunit hslack hcongruence
  have hcount := seven_le_card_dominatingFamily_of_isTie_fiveThree deflated hdeflatedTie
  have hembed : Function.Injective light.succAbove := Fin.succAbove_right_injective
  have hmaps : ∀ chosen ∈ dominatingFamily deflated 3,
      chosen.image light.succAbove
        ∈ (dominatingFamily D 3).filter fun selected => light ∉ selected := by
    intro chosen hchosen
    obtain ⟨hcard, hdominates⟩ := (mem_dominatingFamily_iff deflated 3 chosen).mp hchosen
    refine Finset.mem_filter.mpr ⟨(mem_dominatingFamily_iff D 3 _).mpr
      ⟨by rw [Finset.card_image_of_injective _ hembed, hcard], ?_⟩, ?_⟩
    · exact dominates_image_of_dominates_deflatedDesign D light hlight R hunit
        hslack hcongruence hdominates
    · intro hmember
      obtain ⟨index, -, hindex⟩ := Finset.mem_image.mp hmember
      exact (Fin.succAbove_ne light index) hindex
  have hinjective : Set.InjOn (fun chosen : Finset (Fin 5) => chosen.image light.succAbove)
      ((dominatingFamily deflated 3 : Finset (Finset (Fin 5))) : Set (Finset (Fin 5))) := by
    intro leftSet _ rightSet _ hequal
    exact Finset.image_injective hembed hequal
  exact le_trans hcount (Finset.card_le_card_of_injOn _ hmaps hinjective)

open scoped Classical in
/-- The same count, read on the whole family. -/
theorem seven_le_card_dominatingFamily_of_isTie_sixThree_of_light'
    (D : WeightedDesign 6 3) (htie : IsTie D) (light : Fin 6)
    (hlight : leverageOf (D.atom light) ≤ 1) :
    7 ≤ (dominatingFamily D 3).card :=
  le_trans (seven_le_card_dominatingFamily_of_isTie_sixThree_of_light D htie light hlight)
    (Finset.card_le_card (Finset.filter_subset _ _))

end Gtz
