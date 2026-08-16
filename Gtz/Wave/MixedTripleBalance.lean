import Gtz.Wave.OneLineWedgeFlatSplit
import Gtz.Wave.WedgeBalanceAdjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-
# The sharp balance is one wedge total of a SIGNED measure, and at a mixed
# triple it is negative somewhere on every plane

`Gtz.wedgeBalanceAt_of_flatSplitLead_pos` produces the wedge balance from three
inputs: a positive lead, a positive normal surplus and `0 ≤ sharpBalanceValue`.
The first two are cheap.  This file settles the third.

THE SIGNED MEASURE.  `Gtz.sharpBalanceValue` is written as two wedge totals
minus one crossing total.  Give the SHARP labels the measure

  `splitMeasure c = weightDeficit c` inside the selection, `-weight c` outside,

and the three terms collapse into ONE wedge total, because the crossing measure
product is the only one that carries a single minus sign.  So

  `sharpBalanceValue design S F n p = wedgeTotal design (splitMeasure design S) Fᶜ n p`.

Nothing here is rank three, nothing is size six, and no pattern is named.

WHAT THAT DECIDES.  A wedge total is a sum of `measure_i * measure_j * W(i,j)^2`
over unordered pairs.  So the sign of `sharpBalanceValue` is governed by the
signs of the PRODUCTS `splitMeasure i * splitMeasure j`, and those are all
nonnegative exactly when the split measure does not change sign on the sharp
set.  Two cases give that at once:

* every sharp label is selected, and then every product is a product of two
  deficits (this is the landed `Gtz.sharpBalanceValue_nonneg_of_compl_subset`),
* no sharp label is selected, and then every product is a product of two
  weights.  That case is `Gtz.sharpBalanceValue_nonneg_of_sharp_disjoint`, and
  it is new: at a one-line design it is the LINE triple.

THE REFUTATION.  A MIXED triple selects some sharp labels and leaves others.
Then the split measure changes sign, and with exactly three sharp labels exactly
ONE of the three pair products is positive.  Kill that one pair's wedge with a
probe, and the two surviving terms are both nonpositive.  At rank three such a
probe always exists, because the plane orthogonal to the normal is
two-dimensional and one linear condition never empties it.

So `0 ≤ sharpBalanceValue` FAILS at some nonzero in-plane probe at EVERY mixed
triple of EVERY design.  The producer's third hypothesis is not hard to prove:
it is false.  `Gtz.not_forall_sharpBalanceValue_nonneg_of_mixedSharpTriple`
states that, and the one-line readings name the eighteen mixed triples of the
`(6, 3)` cell.

THE PLANE DETERMINANT.  Section 8 gives the quantitative form.  The sharp
balance is the adjugate quadratic form of the split measure's own atom sum, read
at `n x p`.  Its two by two determinant on any pair of in-plane probes is

  `det(splitSum) * (normal surplus) * tripleBracket(n, p1, p2)^2`,

because the adjugate of the adjugate is the determinant times the matrix, and
because the split measure reads its own normal as exactly the normal surplus.
That last identity, `Gtz.dotProduct_splitSum_mulVec_normal_eq_surplus`, is the
reason the refutation is sharp rather than generic.
-/

namespace Gtz

open Finset Matrix

/-! ## 1.  Measure algebra for wedge totals

A wedge total and a crossing total are bilinear in the two measures through the
product `measure i * measure j` only.  Three consequences: they only see the
measure on their own support, negating a measure leaves a wedge total alone and
flips a crossing total, and a disjoint union splits into two totals plus one
crossing total. -/

/-- A crossing total only reads the measures on its own two supports. -/
theorem crossWedgeTotal_congr_measure {size rank : ℕ} (design : WeightedDesign size rank)
    {leftMeasure leftAlt rightMeasure rightAlt : Fin size → ℝ}
    (leftSupport rightSupport : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hleft : ∀ label ∈ leftSupport, leftMeasure label = leftAlt label)
    (hright : ∀ label ∈ rightSupport, rightMeasure label = rightAlt label) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = crossWedgeTotal design leftAlt rightAlt leftSupport rightSupport normalVec probeVec := by
  unfold crossWedgeTotal
  refine Finset.sum_congr rfl fun leftLabel hleftMem => Finset.sum_congr rfl fun rightLabel hrightMem
    => ?_
  rw [hleft leftLabel hleftMem, hright rightLabel hrightMem]

/-- A wedge total only reads the measure on its own support. -/
theorem wedgeTotal_congr_measure {size rank : ℕ} (design : WeightedDesign size rank)
    {measure measureAlt : Fin size → ℝ} (support : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ)
    (hagree : ∀ label ∈ support, measure label = measureAlt label) :
    wedgeTotal design measure support normalVec probeVec
      = wedgeTotal design measureAlt support normalVec probeVec := by
  rw [wedgeTotal_eq_crossWedgeTotal, wedgeTotal_eq_crossWedgeTotal,
    crossWedgeTotal_congr_measure design support support normalVec probeVec hagree hagree]

/-- Negating the measure leaves the wedge total unchanged: the measure enters
only through a product of two of its values. -/
theorem wedgeTotal_neg_measure {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (support : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design (fun label => -measure label) support normalVec probeVec
      = wedgeTotal design measure support normalVec probeVec := by
  unfold wedgeTotal
  congr 1
  exact Finset.sum_congr rfl fun leftLabel _ => Finset.sum_congr rfl fun rightLabel _ => by ring

/-- Negating one side of a crossing total negates the whole total. -/
theorem crossWedgeTotal_neg_right {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (leftSupport rightSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure (fun label => -rightMeasure label)
        leftSupport rightSupport normalVec probeVec
      = -crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport
          normalVec probeVec := by
  unfold crossWedgeTotal
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun leftLabel _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun rightLabel _ => by ring

/-- The crossing total is symmetric under exchanging the two sides together with
their measures. -/
theorem crossWedgeTotal_swap {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (leftSupport rightSupport : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSupport normalVec probeVec
      = crossWedgeTotal design rightMeasure leftMeasure rightSupport leftSupport
          normalVec probeVec := by
  unfold crossWedgeTotal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun rightLabel _ => Finset.sum_congr rfl fun leftLabel _ => ?_
  rw [wedgeShadow_swap design normalVec probeVec leftLabel rightLabel]
  ring

/-- A crossing total splits over a disjoint union on the left. -/
theorem crossWedgeTotal_union_left {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) {leftFirst leftSecond : Finset (Fin size)}
    (rightSupport : Finset (Fin size)) (hdisjoint : Disjoint leftFirst leftSecond)
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure (leftFirst ∪ leftSecond) rightSupport
        normalVec probeVec
      = crossWedgeTotal design leftMeasure rightMeasure leftFirst rightSupport normalVec probeVec
        + crossWedgeTotal design leftMeasure rightMeasure leftSecond rightSupport
            normalVec probeVec := by
  unfold crossWedgeTotal
  exact Finset.sum_union hdisjoint

/-- A crossing total splits over a disjoint union on the right. -/
theorem crossWedgeTotal_union_right {size rank : ℕ} (design : WeightedDesign size rank)
    (leftMeasure rightMeasure : Fin size → ℝ) (leftSupport : Finset (Fin size))
    {rightFirst rightSecond : Finset (Fin size)} (hdisjoint : Disjoint rightFirst rightSecond)
    (normalVec probeVec : Fin rank → ℝ) :
    crossWedgeTotal design leftMeasure rightMeasure leftSupport (rightFirst ∪ rightSecond)
        normalVec probeVec
      = crossWedgeTotal design leftMeasure rightMeasure leftSupport rightFirst normalVec probeVec
        + crossWedgeTotal design leftMeasure rightMeasure leftSupport rightSecond
            normalVec probeVec := by
  unfold crossWedgeTotal
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun leftLabel _ => Finset.sum_union hdisjoint

/-- **THE WEDGE TOTAL OF A DISJOINT UNION.**  Two totals plus one crossing
total.  No hypothesis on the measure. -/
theorem wedgeTotal_union {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) {firstPart secondPart : Finset (Fin size)}
    (hdisjoint : Disjoint firstPart secondPart) (normalVec probeVec : Fin rank → ℝ) :
    wedgeTotal design measure (firstPart ∪ secondPart) normalVec probeVec
      = wedgeTotal design measure firstPart normalVec probeVec
        + wedgeTotal design measure secondPart normalVec probeVec
        + crossWedgeTotal design measure measure firstPart secondPart normalVec probeVec := by
  rw [wedgeTotal_eq_crossWedgeTotal, wedgeTotal_eq_crossWedgeTotal, wedgeTotal_eq_crossWedgeTotal]
  rw [crossWedgeTotal_union_left design measure measure (firstPart ∪ secondPart) hdisjoint
    normalVec probeVec]
  rw [crossWedgeTotal_union_right design measure measure firstPart hdisjoint normalVec probeVec,
    crossWedgeTotal_union_right design measure measure secondPart hdisjoint normalVec probeVec]
  have hswap := crossWedgeTotal_swap design measure measure secondPart firstPart normalVec probeVec
  rw [hswap]
  ring

/-! ## 2.  The split measure, and the sharp balance as ONE wedge total

The sharp labels inside the selection pay their weight deficit, the sharp labels
outside pay MINUS their weight.  That single sign is the whole content of the
crossing term. -/

/-- The signed measure of the flat split: deficit inside the selection, minus the
weight outside it. -/
noncomputable def splitMeasure {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (label : Fin size) : ℝ :=
  if label ∈ selected then weightDeficit design label else -design.weight label

theorem splitMeasure_of_mem {size rank : ℕ} (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected) :
    splitMeasure design selected label = weightDeficit design label := by
  simp [splitMeasure, hmem]

theorem splitMeasure_of_notMem {size rank : ℕ} (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∉ selected) :
    splitMeasure design selected label = -design.weight label := by
  simp [splitMeasure, hmem]

/-- The split measure is positive on the selection and negative off it, at every
design on two or more atoms. -/
theorem splitMeasure_pos_of_mem {size rank : ℕ} (design : WeightedDesign size rank)
    (hsize : 2 ≤ size) {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected) :
    0 < splitMeasure design selected label := by
  rw [splitMeasure_of_mem design hmem]
  exact weightDeficit_pos design hsize label

theorem splitMeasure_neg_of_notMem {size rank : ℕ} (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∉ selected) :
    splitMeasure design selected label < 0 := by
  rw [splitMeasure_of_notMem design hmem]
  linarith [design.weight_pos label]

/-- The two sharp parts partition the complement of the flat set. -/
theorem sharp_union {size : ℕ} (selected flatSet : Finset (Fin size)) :
    (selected \ flatSet) ∪ (selectedᶜ \ flatSet) = flatSetᶜ := by
  classical
  ext label
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_compl]
  constructor
  · rintro (⟨_, hflat⟩ | ⟨_, hflat⟩) <;> exact hflat
  · intro hflat
    by_cases hsel : label ∈ selected
    · exact Or.inl ⟨hsel, hflat⟩
    · exact Or.inr ⟨hsel, hflat⟩

theorem sharp_disjoint {size : ℕ} (selected flatSet : Finset (Fin size)) :
    Disjoint (selected \ flatSet) (selectedᶜ \ flatSet) := by
  classical
  refine Finset.disjoint_left.mpr fun label hleft hright => ?_
  exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hright).1) (Finset.mem_sdiff.mp hleft).1

/-- **THE SHARP BALANCE IS ONE WEDGE TOTAL.**  Under the split measure the two
totals and the crossing total of `Gtz.sharpBalanceValue` become a single wedge
total over ALL the sharp labels.  No hypothesis, any rank, any size, any pair of
subsets. -/
theorem sharpBalanceValue_eq_wedgeTotal_splitMeasure {size rank : ℕ}
    (design : WeightedDesign size rank) (selected flatSet : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = wedgeTotal design (splitMeasure design selected) flatSetᶜ normalVec probeVec := by
  classical
  rw [← sharp_union selected flatSet,
    wedgeTotal_union design (splitMeasure design selected) (sharp_disjoint selected flatSet)
      normalVec probeVec]
  have hinside : ∀ label ∈ selected \ flatSet,
      splitMeasure design selected label = weightDeficit design label :=
    fun label hmem => splitMeasure_of_mem design (Finset.mem_sdiff.mp hmem).1
  have houtside : ∀ label ∈ selectedᶜ \ flatSet,
      splitMeasure design selected label = -design.weight label :=
    fun label hmem =>
      splitMeasure_of_notMem design (Finset.mem_compl.mp (Finset.mem_sdiff.mp hmem).1)
  rw [wedgeTotal_congr_measure design (selected \ flatSet) normalVec probeVec hinside]
  rw [wedgeTotal_congr_measure design (selectedᶜ \ flatSet) normalVec probeVec houtside]
  rw [wedgeTotal_neg_measure design design.weight (selectedᶜ \ flatSet) normalVec probeVec]
  rw [crossWedgeTotal_congr_measure design (selected \ flatSet) (selectedᶜ \ flatSet)
    normalVec probeVec hinside houtside]
  rw [crossWedgeTotal_neg_right design (weightDeficit design) design.weight
    (selected \ flatSet) (selectedᶜ \ flatSet) normalVec probeVec]
  unfold sharpBalanceValue
  ring

/-! ## 3.  One sign on the sharp set makes the balance nonnegative

The measure enters a wedge total only through the products `measure i * measure j`
over pairs.  A measure of ONE sign makes every such product nonnegative. -/

/-- **THE ONE-SIGN LAW.**  A measure that does not change sign on the support
gives a nonnegative wedge total.  The landed `Gtz.wedgeTotal_nonneg` asks for a
nonnegative measure, and this asks only for a constant sign. -/
theorem wedgeTotal_nonneg_of_nonpos {size rank : ℕ} (design : WeightedDesign size rank)
    (measure : Fin size → ℝ) (support : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ)
    (hnonpos : ∀ label ∈ support, measure label ≤ 0) :
    0 ≤ wedgeTotal design measure support normalVec probeVec := by
  have hneg : ∀ label ∈ support, 0 ≤ (fun rest => -measure rest) label := fun label hmem => by
    simpa using hnonpos label hmem
  have hvalue := wedgeTotal_nonneg design (fun label => -measure label) support normalVec probeVec
    hneg
  rwa [wedgeTotal_neg_measure design measure support normalVec probeVec] at hvalue

/-- **NO SHARP LABEL SELECTED, AND THE SHARP BALANCE IS NONNEGATIVE.**  The twin
of the landed `Gtz.sharpBalanceValue_nonneg_of_compl_subset`, at the opposite
end.  At a one-line design this is the LINE triple. -/
theorem sharpBalanceValue_nonneg_of_sharp_disjoint {size rank : ℕ}
    (design : WeightedDesign size rank) {selected flatSet : Finset (Fin size)}
    (hdisjoint : ∀ label ∈ flatSetᶜ, label ∉ selected) (normalVec probeVec : Fin rank → ℝ) :
    0 ≤ sharpBalanceValue design selected flatSet normalVec probeVec := by
  rw [sharpBalanceValue_eq_wedgeTotal_splitMeasure design selected flatSet normalVec probeVec]
  refine wedgeTotal_nonneg_of_nonpos design (splitMeasure design selected) flatSetᶜ
    normalVec probeVec fun label hmem => ?_
  exact (splitMeasure_neg_of_notMem design (hdisjoint label hmem)).le

/-! ## 4.  Three sharp labels: the balance as three signed pair terms

Every card-three subset of a one-line design leaves EXACTLY the three free atoms
sharp, whatever it selects.  So one formula covers all twenty subsets, and only
the three signs change. -/

/-- **THE THREE-ATOM SHARP BALANCE.**  Over a sharp set of exactly three labels
the balance is the sum of the three pair terms, each weighted by the PRODUCT of
the two split measures. -/
theorem sharpBalanceValue_of_sharp_triple {size rank : ℕ} (design : WeightedDesign size rank)
    (selected flatSet : Finset (Fin size)) {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    (normalVec probeVec : Fin rank → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = splitMeasure design selected sharpFirst * splitMeasure design selected sharpSecond
          * wedgeShadow design normalVec probeVec sharpFirst sharpSecond ^ 2
        + splitMeasure design selected sharpFirst * splitMeasure design selected sharpThird
          * wedgeShadow design normalVec probeVec sharpFirst sharpThird ^ 2
        + splitMeasure design selected sharpSecond * splitMeasure design selected sharpThird
          * wedgeShadow design normalVec probeVec sharpSecond sharpThird ^ 2 := by
  classical
  have hnotFirst : sharpFirst ∉ ({sharpSecond, sharpThird} : Finset (Fin size)) := by
    simp [hFirstSecond, hFirstThird]
  have hnotSecond : sharpSecond ∉ ({sharpThird} : Finset (Fin size)) := by
    simp [hSecondThird]
  rw [sharpBalanceValue_eq_wedgeTotal_splitMeasure design selected flatSet normalVec probeVec,
    hsharp]
  unfold wedgeTotal
  simp only [Finset.sum_insert hnotFirst, Finset.sum_insert hnotSecond, Finset.sum_singleton]
  rw [wedgeShadow_self, wedgeShadow_self, wedgeShadow_self]
  rw [wedgeShadow_swap design normalVec probeVec sharpFirst sharpSecond,
    wedgeShadow_swap design normalVec probeVec sharpFirst sharpThird,
    wedgeShadow_swap design normalVec probeVec sharpSecond sharpThird]
  ring

/-- **THE MIXED SIGN PATTERN.**  When one sharp label carries the opposite sign
to the other two, exactly one pair product is positive and the other two are
negative.  Killing the positive pair's wedge leaves a nonpositive total. -/
theorem sharpBalanceValue_nonpos_of_pair_wedge_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (selected flatSet : Finset (Fin size))
    {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    (normalVec probeVec : Fin rank → ℝ)
    (hcross : splitMeasure design selected sharpFirst * splitMeasure design selected sharpThird
      ≤ 0)
    (hcrossSecond : splitMeasure design selected sharpSecond
      * splitMeasure design selected sharpThird ≤ 0)
    (hzero : wedgeShadow design normalVec probeVec sharpFirst sharpSecond = 0) :
    sharpBalanceValue design selected flatSet normalVec probeVec ≤ 0 := by
  rw [sharpBalanceValue_of_sharp_triple design selected flatSet hFirstSecond hFirstThird
    hSecondThird hsharp normalVec probeVec, hzero]
  nlinarith [hcross, hcrossSecond,
    sq_nonneg (wedgeShadow design normalVec probeVec sharpFirst sharpThird),
    sq_nonneg (wedgeShadow design normalVec probeVec sharpSecond sharpThird)]

/-- The strict form: one surviving wedge that does not vanish makes the balance
strictly negative. -/
theorem sharpBalanceValue_neg_of_pair_wedge_zero {size rank : ℕ}
    (design : WeightedDesign size rank) (selected flatSet : Finset (Fin size))
    {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    (normalVec probeVec : Fin rank → ℝ)
    (hcross : splitMeasure design selected sharpFirst * splitMeasure design selected sharpThird
      < 0)
    (hcrossSecond : splitMeasure design selected sharpSecond
      * splitMeasure design selected sharpThird ≤ 0)
    (hzero : wedgeShadow design normalVec probeVec sharpFirst sharpSecond = 0)
    (hlive : wedgeShadow design normalVec probeVec sharpFirst sharpThird ≠ 0) :
    sharpBalanceValue design selected flatSet normalVec probeVec < 0 := by
  rw [sharpBalanceValue_of_sharp_triple design selected flatSet hFirstSecond hFirstThird
    hSecondThird hsharp normalVec probeVec, hzero]
  have hsq : 0 < wedgeShadow design normalVec probeVec sharpFirst sharpThird ^ 2 := by
    positivity
  nlinarith [hcross, hcrossSecond, hsq,
    sq_nonneg (wedgeShadow design normalVec probeVec sharpSecond sharpThird)]

/-! ## 5.  Rank three: one linear condition never empties the plane

The plane orthogonal to a nonzero normal is two-dimensional, so a single linear
condition on an in-plane probe always keeps a nonzero solution.  The whole
construction is division free and uses only the cross product. -/

/-- A nonzero vector has positive energy. -/
theorem dotProduct_self_pos_of_ne_zero {rank : ℕ} {vec : Fin rank → ℝ} (hne : vec ≠ 0) :
    0 < vec ⬝ᵥ vec := by
  obtain ⟨slot, hslot⟩ := Function.ne_iff.mp hne
  have hlive : vec slot ≠ 0 := by simpa using hslot
  simp only [dotProduct]
  exact Finset.sum_pos' (fun index _ => mul_self_nonneg _)
    ⟨slot, Finset.mem_univ slot, mul_self_pos.mpr hlive⟩

/-- **THE BRACKET IS ANTISYMMETRIC IN ITS OUTER SLOTS.**  Reading a wedge against
a third vector is the triple product, so exchanging the two outer factors flips
the sign. -/
theorem dotProduct_atomWedge_swap (leftVec midVec rightVec : Fin 3 → ℝ) :
    leftVec ⬝ᵥ atomWedge midVec rightVec = -(rightVec ⬝ᵥ atomWedge midVec leftVec) := by
  simp only [dotProduct, Fin.sum_univ_three, atomWedge, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- At rank three every vector has a nonzero orthogonal partner.  No hypothesis:
the plane orthogonal to a vector is at least two-dimensional. -/
theorem exists_nonzero_orthogonal_rankThree (normalVec : Fin 3 → ℝ) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ≠ 0 ∧ probeVec ⬝ᵥ normalVec = 0 := by
  by_cases hflatPair : normalVec 0 = 0 ∧ normalVec 1 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · intro hzero
      have hslot := congrFun hzero 0
      simp at hslot
    · simp [dotProduct, Fin.sum_univ_three, hflatPair.1]
  · refine ⟨![-normalVec 1, normalVec 0, 0], ?_, ?_⟩
    · intro hzero
      refine hflatPair ⟨?_, ?_⟩
      · have hslot := congrFun hzero 1
        simpa using hslot
      · have hslot := congrFun hzero 0
        simp at hslot
        linarith
    · simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring

/-- **THE IN-PLANE PROBE THAT KILLS ONE READING.**  At rank three, for a nonzero
normal and ANY target vector, there is a nonzero in-plane probe whose wedge with
the normal is orthogonal to the target.  No hypothesis on the target. -/
theorem exists_inPlane_probe_dotProduct_atomWedge_eq_zero {normalVec : Fin 3 → ℝ}
    (hne : normalVec ≠ 0) (targetVec : Fin 3 → ℝ) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ≠ 0 ∧ probeVec ⬝ᵥ normalVec = 0
      ∧ targetVec ⬝ᵥ atomWedge normalVec probeVec = 0 := by
  by_cases hdegenerate : atomWedge normalVec targetVec = 0
  · obtain ⟨probeVec, hprobeNe, hortho⟩ := exists_nonzero_orthogonal_rankThree normalVec
    refine ⟨probeVec, hprobeNe, hortho, ?_⟩
    rw [dotProduct_atomWedge_swap targetVec normalVec probeVec, hdegenerate]
    simp
  · set liftVec : Fin 3 → ℝ := atomWedge normalVec targetVec with hliftVec
    have hliftNormal : liftVec ⬝ᵥ normalVec = 0 := by
      rw [hliftVec, dotProduct_comm]
      exact atomWedge_dot_left normalVec targetVec
    refine ⟨atomWedge liftVec normalVec, ?_, ?_, ?_⟩
    · intro hzero
      have henergy := atomWedge_energy liftVec normalVec
      rw [hzero] at henergy
      have hliftPos : 0 < liftVec ⬝ᵥ liftVec := dotProduct_self_pos_of_ne_zero hdegenerate
      have hnormalPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos_of_ne_zero hne
      rw [hliftNormal] at henergy
      simp only [dotProduct_zero] at henergy
      nlinarith [henergy, hliftPos, hnormalPos]
    · rw [dotProduct_comm]
      exact atomWedge_dot_right liftVec normalVec
    · rw [dotProduct_atomWedge_swap targetVec normalVec (atomWedge liftVec normalVec)]
      have hkill : atomWedge liftVec normalVec ⬝ᵥ liftVec = 0 := by
        rw [dotProduct_comm]
        exact atomWedge_dot_left liftVec normalVec
      rw [← hliftVec, hkill]
      ring

/-- **A PROBE THAT KILLS ONE PAIR'S WEDGE SHADOW.**  At rank three, for any two
labels and any nonzero normal, a nonzero in-plane probe reads that pair's wedge
as zero. -/
theorem exists_inPlane_probe_wedgeShadow_eq_zero {size : ℕ} (design : WeightedDesign size 3)
    {normalVec : Fin 3 → ℝ} (hne : normalVec ≠ 0) (leftLabel rightLabel : Fin size) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ≠ 0 ∧ probeVec ⬝ᵥ normalVec = 0
      ∧ wedgeShadow design normalVec probeVec leftLabel rightLabel = 0 := by
  obtain ⟨probeVec, hprobeNe, hortho, hkill⟩ :=
    exists_inPlane_probe_dotProduct_atomWedge_eq_zero hne
      (atomWedge (design.atom leftLabel) (design.atom rightLabel))
  exact ⟨probeVec, hprobeNe, hortho, by
    rw [wedgeShadow_eq_atomWedge_dotProduct design normalVec probeVec leftLabel rightLabel]
    exact hkill⟩

/-! ## 6.  THE REFUTATION

At a sharp triple whose split measure changes sign, exactly ONE of the three
pair products is positive.  Kill that pair, and both surviving terms are
nonpositive.  The producer's third hypothesis therefore fails at some nonzero
in-plane probe, at EVERY design and EVERY normal. -/

/-- **THE SHARP BALANCE IS NONPOSITIVE SOMEWHERE.**  Whenever the split measure
of the designated sharp label has the opposite sign to the other two, a nonzero
in-plane probe drives the sharp balance to zero or below. -/
theorem exists_probe_sharpBalanceValue_nonpos {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    {normalVec : Fin 3 → ℝ} (hne : normalVec ≠ 0)
    (hcrossFirst : splitMeasure design selected sharpFirst
      * splitMeasure design selected sharpThird ≤ 0)
    (hcrossSecond : splitMeasure design selected sharpSecond
      * splitMeasure design selected sharpThird ≤ 0) :
    ∃ probeVec : Fin 3 → ℝ, probeVec ≠ 0 ∧ probeVec ⬝ᵥ normalVec = 0
      ∧ sharpBalanceValue design selected flatSet normalVec probeVec ≤ 0 := by
  obtain ⟨probeVec, hprobeNe, hortho, hkill⟩ :=
    exists_inPlane_probe_wedgeShadow_eq_zero design hne sharpFirst sharpSecond
  exact ⟨probeVec, hprobeNe, hortho,
    sharpBalanceValue_nonpos_of_pair_wedge_zero design selected flatSet hFirstSecond hFirstThird
      hSecondThird hsharp normalVec probeVec hcrossFirst hcrossSecond hkill⟩

/-- **THE SHARP BALANCE IS NEVER POSITIVE DEFINITE ON THE PLANE AT A MIXED
TRIPLE.**  Unconditional: no nondegeneracy, no independence, no pattern.  So the
sharp balance ALONE can never carry a selector at a mixed triple, and the lead
must do work at some probe. -/
theorem not_forall_sharpBalanceValue_pos {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    {normalVec : Fin 3 → ℝ} (hne : normalVec ≠ 0)
    (hcrossFirst : splitMeasure design selected sharpFirst
      * splitMeasure design selected sharpThird ≤ 0)
    (hcrossSecond : splitMeasure design selected sharpSecond
      * splitMeasure design selected sharpThird ≤ 0) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 → probeVec ≠ 0 →
        0 < sharpBalanceValue design selected flatSet normalVec probeVec := by
  intro hall
  obtain ⟨probeVec, hprobeNe, hortho, hnonpos⟩ :=
    exists_probe_sharpBalanceValue_nonpos design selected flatSet hFirstSecond hFirstThird
      hSecondThird hsharp hne hcrossFirst hcrossSecond
  exact absurd (hall probeVec hortho hprobeNe) (not_lt.mpr hnonpos)

/-- The two cross products are nonpositive as soon as the designated third label
sits on the other side of the selection from the first two. -/
theorem crossProducts_nonpos_of_two_in_one_out {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) {selected : Finset (Fin size)}
    {sharpFirst sharpSecond sharpThird : Fin size} (hFirstIn : sharpFirst ∈ selected)
    (hSecondIn : sharpSecond ∈ selected) (hThirdOut : sharpThird ∉ selected) :
    splitMeasure design selected sharpFirst * splitMeasure design selected sharpThird ≤ 0
      ∧ splitMeasure design selected sharpSecond * splitMeasure design selected sharpThird ≤ 0 := by
  have hthird := splitMeasure_neg_of_notMem design hThirdOut
  have hfirst := splitMeasure_pos_of_mem design hsize hFirstIn
  have hsecond := splitMeasure_pos_of_mem design hsize hSecondIn
  exact ⟨by nlinarith [hfirst, hthird], by nlinarith [hsecond, hthird]⟩

/-- The mirror case: one label inside, two outside.  The positive pair product is
then carried by the two OUTSIDE labels. -/
theorem crossProducts_nonpos_of_one_in_two_out {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) {selected : Finset (Fin size)}
    {sharpFirst sharpSecond sharpThird : Fin size} (hFirstOut : sharpFirst ∉ selected)
    (hSecondOut : sharpSecond ∉ selected) (hThirdIn : sharpThird ∈ selected) :
    splitMeasure design selected sharpFirst * splitMeasure design selected sharpThird ≤ 0
      ∧ splitMeasure design selected sharpSecond * splitMeasure design selected sharpThird ≤ 0 := by
  have hthird := splitMeasure_pos_of_mem design hsize hThirdIn
  have hfirst := splitMeasure_neg_of_notMem design hFirstOut
  have hsecond := splitMeasure_neg_of_notMem design hSecondOut
  exact ⟨by nlinarith [hfirst, hthird], by nlinarith [hsecond, hthird]⟩

/-! ## 7.  The split atom sum, and its adjugate

At rank three a wedge total is the adjugate quadratic form of its own measure's
atom sum, read at the cross product of the normal and the probe.  Section 2
therefore reads the sharp balance as ONE adjugate form.  Everything the rest of
the file needs is a determinant. -/

/-- The atom sum of the split measure over the sharp labels. -/
noncomputable def splitSum {size rank : ℕ} (design : WeightedDesign size rank)
    (selected sharpSet : Finset (Fin size)) : Matrix (Fin rank) (Fin rank) ℝ :=
  ∑ label ∈ sharpSet, splitMeasure design selected label • atomMatrix (design.atom label)

theorem splitSum_transpose {size rank : ℕ} (design : WeightedDesign size rank)
    (selected sharpSet : Finset (Fin size)) :
    (splitSum design selected sharpSet)ᵀ = splitSum design selected sharpSet := by
  unfold splitSum
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.transpose_smul]
  congr 1
  unfold atomMatrix
  ext leftSlot rightSlot
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- A symmetric form pairs its two arguments in either order. -/
theorem dotProduct_mulVec_comm_of_symm {rank : ℕ} {form : Matrix (Fin rank) (Fin rank) ℝ}
    (hsym : formᵀ = form) (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ (form *ᵥ rightVec) = rightVec ⬝ᵥ (form *ᵥ leftVec) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]

/-- At rank three the adjugate of the adjugate is the determinant times the
matrix. -/
theorem adjugate_adjugate_rankThree (form : Matrix (Fin 3) (Fin 3) ℝ) :
    form.adjugate.adjugate = form.det • form := by
  rw [Matrix.adjugate_adjugate form (by simp)]
  norm_num

/-- The wedge is linear in the probe. -/
theorem atomWedge_combination (normalVec probeFirst probeSecond : Fin 3 → ℝ)
    (scaleFirst scaleSecond : ℝ) :
    atomWedge normalVec (scaleFirst • probeFirst + scaleSecond • probeSecond)
      = scaleFirst • atomWedge normalVec probeFirst
        + scaleSecond • atomWedge normalVec probeSecond := by
  funext slot
  fin_cases slot <;> simp [atomWedge, Pi.smul_apply, Pi.add_apply, smul_eq_mul] <;> ring

/-- **THE DOUBLE WEDGE COLLAPSES ONTO THE NORMAL.**  Two in-plane lifts wedge to
the bracket times the normal. -/
theorem atomWedge_atomWedge_eq_bracket_smul (normalVec probeFirst probeSecond : Fin 3 → ℝ) :
    atomWedge (atomWedge normalVec probeFirst) (atomWedge normalVec probeSecond)
      = tripleBracket normalVec probeFirst probeSecond • normalVec := by
  funext slot
  fin_cases slot <;>
    simp [atomWedge, tripleBracket, Matrix.det_fin_three, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The bracket is the wedge read against the third vector. -/
theorem tripleBracket_eq_dotProduct_atomWedge (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = rightVec ⬝ᵥ atomWedge leftVec midVec := by
  simp only [tripleBracket, Matrix.det_fin_three, atomWedge, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE SHARP BALANCE IS THE ADJUGATE FORM OF THE SPLIT SUM.**  At rank three,
any subsets, any normal and any probe. -/
theorem sharpBalanceValue_eq_dotProduct_adjugate_splitSum {size : ℕ}
    (design : WeightedDesign size 3) (selected flatSet : Finset (Fin size))
    (normalVec probeVec : Fin 3 → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeVec
      = atomWedge normalVec probeVec
          ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate *ᵥ atomWedge normalVec probeVec) := by
  rw [sharpBalanceValue_eq_wedgeTotal_splitMeasure design selected flatSet normalVec probeVec]
  exact wedgeTotal_eq_dotProduct_adjugate_mulVec design (splitMeasure design selected) flatSetᶜ
    normalVec probeVec

/-- The split measure is the selection indicator minus the weight. -/
theorem splitMeasure_eq_indicator_sub_weight {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (label : Fin size) :
    splitMeasure design selected label
      = (if label ∈ selected then (1 : ℝ) else 0) - design.weight label := by
  unfold splitMeasure weightDeficit
  split <;> ring

/-- **THE SPLIT SUM READS ITS OWN NORMAL AS THE NORMAL SURPLUS.**  Weighted
Parseval removes the whole weight measure and every flat label, and what is left
is exactly the surplus that the flat split already pairs with the lead. -/
theorem dotProduct_splitSum_mulVec_normal_eq_surplus {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (normalVec : Fin 3 → ℝ)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0) :
    normalVec ⬝ᵥ (splitSum design selected flatSetᶜ *ᵥ normalVec)
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2) - normalVec ⬝ᵥ normalVec := by
  classical
  rw [splitSum, dotProduct_sum_smul_atomMatrix_mulVec]
  have hsplit : ∑ label ∈ flatSetᶜ, splitMeasure design selected label
        * (design.atom label ⬝ᵥ normalVec) ^ 2
      = (∑ label ∈ flatSetᶜ,
            (if label ∈ selected then (design.atom label ⬝ᵥ normalVec) ^ 2 else 0))
        - ∑ label ∈ flatSetᶜ, design.weight label
            * (design.atom label ⬝ᵥ normalVec) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [splitMeasure_eq_indicator_sub_weight design selected label]
    split <;> ring
  rw [hsplit, Finset.sum_ite_mem]
  have hinter : flatSetᶜ ∩ selected = selected \ flatSet := by
    rw [Finset.sdiff_eq_inter_compl, Finset.inter_comm]
  rw [hinter]
  have hselected := sum_sdiff_flat_normalSq design selected flatSet normalVec (fun _ => 1) hflat
  simp only [one_mul] at hselected
  rw [hselected]
  have hcompl : flatSetᶜ = Finset.univ \ flatSet := by rw [Finset.compl_eq_univ_sdiff]
  rw [hcompl]
  rw [sum_sdiff_flat_normalSq design Finset.univ flatSet normalVec design.weight hflat]
  rw [dotProduct_self_eq_sum_weight_mul_sq design normalVec]

/-- **THE PLANE DETERMINANT OF THE SHARP BALANCE.**  On any two probes the two by
two determinant of the sharp balance is the bracket squared, times the
determinant of the split sum, times the split sum's reading of the normal.  The
adjugate of the adjugate supplies the whole identity. -/
theorem sharpBalance_planeDeterminant {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (normalVec probeFirst probeSecond : Fin 3 → ℝ) :
    sharpBalanceValue design selected flatSet normalVec probeFirst
        * sharpBalanceValue design selected flatSet normalVec probeSecond
      - (atomWedge normalVec probeFirst
          ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate
              *ᵥ atomWedge normalVec probeSecond)) ^ 2
      = tripleBracket normalVec probeFirst probeSecond ^ 2
        * ((splitSum design selected flatSetᶜ).det
          * (normalVec ⬝ᵥ (splitSum design selected flatSetᶜ *ᵥ normalVec))) := by
  set formSum : Matrix (Fin 3) (Fin 3) ℝ := splitSum design selected flatSetᶜ with hformSum
  set liftFirst : Fin 3 → ℝ := atomWedge normalVec probeFirst with hliftFirst
  set liftSecond : Fin 3 → ℝ := atomWedge normalVec probeSecond with hliftSecond
  have hsym : formSum.adjugateᵀ = formSum.adjugate := by
    rw [Matrix.adjugate_transpose, hformSum, splitSum_transpose]
  have hborder := dotProduct_adjugate_atomWedge_mulVec formSum.adjugate liftFirst liftSecond
  rw [adjugate_adjugate_rankThree formSum,
    atomWedge_atomWedge_eq_bracket_smul normalVec probeFirst probeSecond,
    dotProduct_mulVec_comm_of_symm hsym liftSecond liftFirst] at hborder
  have hborderSq : (tripleBracket normalVec probeFirst probeSecond • normalVec)
        ⬝ᵥ ((formSum.det • formSum)
          *ᵥ (tripleBracket normalVec probeFirst probeSecond • normalVec))
      = liftFirst ⬝ᵥ (formSum.adjugate *ᵥ liftFirst)
          * (liftSecond ⬝ᵥ (formSum.adjugate *ᵥ liftSecond))
        - (liftFirst ⬝ᵥ (formSum.adjugate *ᵥ liftSecond)) ^ 2 := by
    rw [hborder]; ring
  rw [sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec
      probeFirst,
    sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec
      probeSecond, ← hborderSq]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

/-! ## 8.  The uniform refutation

The sharp balance is a binary quadratic form on the plane.  Its determinant is
the bracket squared times the determinant of the split sum times the normal
surplus.  A nonvanishing determinant therefore forces the form to be DEFINITE,
and a probe that kills the one positive pair term refuses that. -/

/-- The wedge shadow is linear in the probe. -/
theorem wedgeShadow_combination {size rank : ℕ} (design : WeightedDesign size rank)
    (normalVec probeFirst probeSecond : Fin rank → ℝ) (scaleFirst scaleSecond : ℝ)
    (leftLabel rightLabel : Fin size) :
    wedgeShadow design normalVec (scaleFirst • probeFirst + scaleSecond • probeSecond)
        leftLabel rightLabel
      = scaleFirst * wedgeShadow design normalVec probeFirst leftLabel rightLabel
        + scaleSecond * wedgeShadow design normalVec probeSecond leftLabel rightLabel := by
  unfold wedgeShadow
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

theorem sharpBalanceValue_probe_zero {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (normalVec : Fin 3 → ℝ) :
    sharpBalanceValue design selected flatSet normalVec 0 = 0 := by
  rw [sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec 0]
  have hwedge : atomWedge normalVec 0 = 0 := by
    funext slot; fin_cases slot <;> simp [atomWedge]
  rw [hwedge]
  simp

/-- **THE SHARP BALANCE IS A BINARY QUADRATIC FORM ON THE PLANE.** -/
theorem sharpBalanceValue_combination {size : ℕ} (design : WeightedDesign size 3)
    (selected flatSet : Finset (Fin size)) (normalVec probeFirst probeSecond : Fin 3 → ℝ)
    (scaleFirst scaleSecond : ℝ) :
    sharpBalanceValue design selected flatSet normalVec
        (scaleFirst • probeFirst + scaleSecond • probeSecond)
      = sharpBalanceValue design selected flatSet normalVec probeFirst * scaleFirst ^ 2
        + 2 * (atomWedge normalVec probeFirst
            ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate
              *ᵥ atomWedge normalVec probeSecond)) * scaleFirst * scaleSecond
        + sharpBalanceValue design selected flatSet normalVec probeSecond * scaleSecond ^ 2 := by
  have hsym : (splitSum design selected flatSetᶜ).adjugateᵀ
      = (splitSum design selected flatSetᶜ).adjugate := by
    rw [Matrix.adjugate_transpose, splitSum_transpose]
  rw [sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec
      (scaleFirst • probeFirst + scaleSecond • probeSecond),
    sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec probeFirst,
    sharpBalanceValue_eq_dotProduct_adjugate_splitSum design selected flatSet normalVec probeSecond,
    atomWedge_combination normalVec probeFirst probeSecond scaleFirst scaleSecond]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_symm hsym (atomWedge normalVec probeSecond)
    (atomWedge normalVec probeFirst)]
  ring

/-- A definite binary form is positive at every nonzero pair of scales. -/
theorem binaryForm_pos_of_det_pos {formFirst formCross formSecond scaleFirst scaleSecond : ℝ}
    (hfirst : 0 < formFirst) (hdet : 0 < formFirst * formSecond - formCross ^ 2)
    (hlive : scaleFirst ≠ 0 ∨ scaleSecond ≠ 0) :
    0 < formFirst * scaleFirst ^ 2 + 2 * formCross * scaleFirst * scaleSecond
      + formSecond * scaleSecond ^ 2 := by
  rcases hlive with hleft | hright
  · rcases eq_or_ne scaleSecond 0 with hzero | hlive
    · rw [hzero]
      have hsq : 0 < scaleFirst ^ 2 := by positivity
      nlinarith [hfirst, hsq]
    · have hsq : 0 < scaleSecond ^ 2 := by positivity
      nlinarith [sq_nonneg (formFirst * scaleFirst + formCross * scaleSecond), hfirst, hdet, hsq]
  · have hsq : 0 < scaleSecond ^ 2 := by positivity
    nlinarith [sq_nonneg (formFirst * scaleFirst + formCross * scaleSecond), hfirst, hdet, hsq]

/-- **THE PRODUCER'S THIRD HYPOTHESIS IS FALSE.**  At any design of rank three,
any normal with a flat set of exactly three sharp labels whose split measure
changes sign, a positive normal surplus and a nonvanishing split determinant, the
sharp balance is NOT nonnegative at every nonzero in-plane probe.  So
`Gtz.wedgeBalanceAt_of_flatSplitLead_pos` cannot be run at every probe. -/
theorem not_forall_sharpBalanceValue_nonneg_of_splitSum_det_ne_zero {size : ℕ}
    (design : WeightedDesign size 3) (selected flatSet : Finset (Fin size))
    {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird)
    (hsharp : flatSetᶜ = {sharpFirst, sharpSecond, sharpThird})
    {normalVec : Fin 3 → ℝ} (hne : normalVec ≠ 0)
    (hflat : ∀ label ∈ flatSet, design.atom label ⬝ᵥ normalVec = 0)
    (hsurplus : normalVec ⬝ᵥ normalVec
      < ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
    (hdet : (splitSum design selected flatSetᶜ).det ≠ 0)
    (hcrossFirst : splitMeasure design selected sharpFirst
      * splitMeasure design selected sharpThird ≤ 0)
    (hcrossSecond : splitMeasure design selected sharpSecond
      * splitMeasure design selected sharpThird ≤ 0) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ normalVec = 0 → probeVec ≠ 0 →
        0 ≤ sharpBalanceValue design selected flatSet normalVec probeVec := by
  intro hall
  obtain ⟨probeFirst, hfirstNe, hfirstOrth⟩ := exists_nonzero_orthogonal_rankThree normalVec
  set probeSecond : Fin 3 → ℝ := atomWedge normalVec probeFirst with hprobeSecond
  have hsecondOrth : probeSecond ⬝ᵥ normalVec = 0 := by
    rw [hprobeSecond, dotProduct_comm]
    exact atomWedge_dot_left normalVec probeFirst
  have hbracket : tripleBracket normalVec probeFirst probeSecond = probeSecond ⬝ᵥ probeSecond := by
    rw [tripleBracket_eq_dotProduct_atomWedge normalVec probeFirst probeSecond, hprobeSecond]
  have hnormalPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos_of_ne_zero hne
  have hfirstPos : 0 < probeFirst ⬝ᵥ probeFirst := dotProduct_self_pos_of_ne_zero hfirstNe
  have hsecondEnergy : probeSecond ⬝ᵥ probeSecond
      = (normalVec ⬝ᵥ normalVec) * (probeFirst ⬝ᵥ probeFirst)
        - (normalVec ⬝ᵥ probeFirst) ^ 2 := atomWedge_energy normalVec probeFirst
  have hnormalFirst : normalVec ⬝ᵥ probeFirst = 0 := by
    rw [dotProduct_comm]; exact hfirstOrth
  rw [hnormalFirst] at hsecondEnergy
  have hsecondPos : 0 < probeSecond ⬝ᵥ probeSecond := by
    rw [hsecondEnergy]; nlinarith [hnormalPos, hfirstPos]
  have hsecondNe : probeSecond ≠ 0 := by
    intro hzero
    rw [hzero] at hsecondPos
    simp at hsecondPos
  have hform : ∀ scaleFirst scaleSecond : ℝ,
      0 ≤ sharpBalanceValue design selected flatSet normalVec probeFirst * scaleFirst ^ 2
        + 2 * (atomWedge normalVec probeFirst
            ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate
              *ᵥ atomWedge normalVec probeSecond)) * scaleFirst * scaleSecond
        + sharpBalanceValue design selected flatSet normalVec probeSecond * scaleSecond ^ 2 := by
    intro scaleFirst scaleSecond
    rw [← sharpBalanceValue_combination design selected flatSet normalVec probeFirst probeSecond
      scaleFirst scaleSecond]
    by_cases hzero : scaleFirst • probeFirst + scaleSecond • probeSecond = 0
    · rw [hzero, sharpBalanceValue_probe_zero]
    · refine hall _ ?_ hzero
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hfirstOrth, hsecondOrth]
      ring
  have hdiscriminant := nonneg_det_of_nonneg_binaryForm hform
  have hmaster := sharpBalance_planeDeterminant design selected flatSet normalVec probeFirst
    probeSecond
  rw [dotProduct_splitSum_mulVec_normal_eq_surplus design selected flatSet normalVec hflat,
    hbracket] at hmaster
  have hsurplusPos : 0 < (∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2)
      - normalVec ⬝ᵥ normalVec := by linarith
  have hbracketPos : 0 < (probeSecond ⬝ᵥ probeSecond) ^ 2 := by positivity
  have hdetPos : 0 < (splitSum design selected flatSetᶜ).det := by
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · exfalso
      have hproduct := mul_neg_of_neg_of_pos hneg hsurplusPos
      have hnegative := mul_neg_of_pos_of_neg hbracketPos hproduct
      linarith [hdiscriminant, hmaster, hnegative]
    · exact hpos
  have hplanePos : 0 < sharpBalanceValue design selected flatSet normalVec probeFirst
      * sharpBalanceValue design selected flatSet normalVec probeSecond
      - (atomWedge normalVec probeFirst
          ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate
            *ᵥ atomWedge normalVec probeSecond)) ^ 2 := by
    rw [hmaster]
    exact mul_pos hbracketPos (mul_pos hdetPos hsurplusPos)
  have hfirstValue : 0 ≤ sharpBalanceValue design selected flatSet normalVec probeFirst :=
    hall probeFirst hfirstOrth hfirstNe
  have hfirstStrict : 0 < sharpBalanceValue design selected flatSet normalVec probeFirst := by
    rcases hfirstValue.lt_or_eq with hpos | hzero
    · exact hpos
    · exfalso
      rw [← hzero] at hplanePos
      nlinarith [hplanePos, sq_nonneg (atomWedge normalVec probeFirst
        ⬝ᵥ ((splitSum design selected flatSetᶜ).adjugate *ᵥ atomWedge normalVec probeSecond))]
  set wedgeFirst : ℝ := wedgeShadow design normalVec probeFirst sharpFirst sharpSecond
    with hwedgeFirst
  set wedgeSecond : ℝ := wedgeShadow design normalVec probeSecond sharpFirst sharpSecond
    with hwedgeSecond
  have hkill : wedgeShadow design normalVec
      (wedgeSecond • probeFirst + (-wedgeFirst) • probeSecond) sharpFirst sharpSecond = 0 := by
    rw [wedgeShadow_combination design normalVec probeFirst probeSecond wedgeSecond
      (-wedgeFirst) sharpFirst sharpSecond, ← hwedgeFirst, ← hwedgeSecond]
    ring
  have hnonpos := sharpBalanceValue_nonpos_of_pair_wedge_zero design selected flatSet
    hFirstSecond hFirstThird hSecondThird hsharp normalVec
    (wedgeSecond • probeFirst + (-wedgeFirst) • probeSecond) hcrossFirst hcrossSecond hkill
  rw [sharpBalanceValue_combination design selected flatSet normalVec probeFirst probeSecond
    wedgeSecond (-wedgeFirst)] at hnonpos
  have hbothZero : wedgeSecond = 0 ∧ wedgeFirst = 0 := by
    by_contra hlive
    have hne' : wedgeSecond ≠ 0 ∨ (-wedgeFirst) ≠ 0 := by
      rcases not_and_or.mp hlive with hleft | hright
      · exact Or.inl hleft
      · exact Or.inr (by simpa using hright)
    exact absurd (binaryForm_pos_of_det_pos hfirstStrict hplanePos hne') (not_lt.mpr hnonpos)
  have hfirstNonpos := sharpBalanceValue_nonpos_of_pair_wedge_zero design selected flatSet
    hFirstSecond hFirstThird hSecondThird hsharp normalVec probeFirst hcrossFirst hcrossSecond
    hbothZero.2
  linarith [hfirstStrict, hfirstNonpos]

/-! ## 9.  The determinant at a sharp triple, and the one-line reading -/

/-- The determinant of three signed rank ones is the product of the three signs
times the bracket squared.  Cauchy-Binet at rank three. -/
theorem det_three_smul_atomMatrix (scaleFirst scaleSecond scaleThird : ℝ)
    (vecFirst vecSecond vecThird : Fin 3 → ℝ) :
    (scaleFirst • atomMatrix vecFirst + (scaleSecond • atomMatrix vecSecond
        + scaleThird • atomMatrix vecThird)).det
      = scaleFirst * scaleSecond * scaleThird
        * tripleBracket vecFirst vecSecond vecThird ^ 2 := by
  simp [Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply, tripleBracket]
  ring

/-- **THE SPLIT DETERMINANT AT A SHARP TRIPLE.** -/
theorem det_splitSum_of_triple {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) {sharpFirst sharpSecond sharpThird : Fin size}
    (hFirstSecond : sharpFirst ≠ sharpSecond) (hFirstThird : sharpFirst ≠ sharpThird)
    (hSecondThird : sharpSecond ≠ sharpThird) :
    (splitSum design selected {sharpFirst, sharpSecond, sharpThird}).det
      = splitMeasure design selected sharpFirst * splitMeasure design selected sharpSecond
          * splitMeasure design selected sharpThird
        * tripleBracket (design.atom sharpFirst) (design.atom sharpSecond)
            (design.atom sharpThird) ^ 2 := by
  classical
  have hnotFirst : sharpFirst ∉ ({sharpSecond, sharpThird} : Finset (Fin size)) := by
    simp [hFirstSecond, hFirstThird]
  have hnotSecond : sharpSecond ∉ ({sharpThird} : Finset (Fin size)) := by simp [hSecondThird]
  rw [splitSum, Finset.sum_insert hnotFirst, Finset.sum_insert hnotSecond, Finset.sum_singleton]
  exact det_three_smul_atomMatrix _ _ _ _ _ _

/-- The one-line reading of the split determinant: the sharp set is the free
triple `{3, 4, 5}`. -/
theorem oneLine_det_splitSum (design : WeightedDesign 6 3) (selected : Finset (Fin 6)) :
    (splitSum design selected ((({0, 1, 2} : Finset (Fin 6)))ᶜ)).det
      = splitMeasure design selected 3 * splitMeasure design selected 4
          * splitMeasure design selected 5
        * tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ^ 2 := by
  rw [oneLine_lineSet_compl]
  exact det_splitSum_of_triple design selected (by decide) (by decide) (by decide)

/-- **THE SPLIT DETERMINANT DOES NOT VANISH AT A MIXED TRIPLE.**  Independence of
the three free atoms is the only input. -/
theorem oneLine_det_splitSum_ne_zero (design : WeightedDesign 6 3) (selected : Finset (Fin 6))
    (hbracket : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0) :
    (splitSum design selected ((({0, 1, 2} : Finset (Fin 6)))ᶜ)).det ≠ 0 := by
  rw [oneLine_det_splitSum design selected]
  have hsq : 0 < tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ^ 2 := by
    positivity
  have hthree : splitMeasure design selected 3 ≠ 0 := by
    by_cases hmem : (3 : Fin 6) ∈ selected
    · exact ne_of_gt (splitMeasure_pos_of_mem design (by norm_num) hmem)
    · exact ne_of_lt (splitMeasure_neg_of_notMem design hmem)
  have hfour : splitMeasure design selected 4 ≠ 0 := by
    by_cases hmem : (4 : Fin 6) ∈ selected
    · exact ne_of_gt (splitMeasure_pos_of_mem design (by norm_num) hmem)
    · exact ne_of_lt (splitMeasure_neg_of_notMem design hmem)
  have hfive : splitMeasure design selected 5 ≠ 0 := by
    by_cases hmem : (5 : Fin 6) ∈ selected
    · exact ne_of_gt (splitMeasure_pos_of_mem design (by norm_num) hmem)
    · exact ne_of_lt (splitMeasure_neg_of_notMem design hmem)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hthree hfour) hfive) (ne_of_gt hsq)

/-! ## 10.  The one-line headline

At the one-line pattern the flat set is the line `{0, 1, 2}` and the sharp set is
the free triple `{3, 4, 5}`.  Every card-three subset leaves the same three sharp
labels, and only their signs change.  The eighteen MIXED subsets are exactly the
ones whose split measure changes sign there, and each of them refuses the
producer. -/

/-- **THE MIXED TRIPLE REFUSES THE PRODUCER.**  Under the producer's own normal
surplus hypothesis, and independence of the three free atoms, the hypothesis
`0 ≤ sharpBalanceValue` is FALSE at some nonzero in-plane probe. -/
theorem oneLine_not_forall_sharpBalanceValue_nonneg (design : WeightedDesign 6 3)
    (selected : Finset (Fin 6)) {unitNormal : Fin 3 → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hbracket : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    {freeFirst freeSecond freeThird : Fin 6}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (hperm : ((({0, 1, 2} : Finset (Fin 6)))ᶜ) = {freeFirst, freeSecond, freeThird})
    (hcrossFirst : splitMeasure design selected freeFirst
      * splitMeasure design selected freeThird ≤ 0)
    (hcrossSecond : splitMeasure design selected freeSecond
      * splitMeasure design selected freeThird ≤ 0) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6))
              unitNormal probeVec := by
  have hne : unitNormal ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp at hunit
  refine not_forall_sharpBalanceValue_nonneg_of_splitSum_det_ne_zero design selected
    ({0, 1, 2} : Finset (Fin 6)) hFirstSecond hFirstThird hSecondThird hperm hne hlineFlat ?_
    (oneLine_det_splitSum_ne_zero design selected hbracket) hcrossFirst hcrossSecond
  rw [hunit]
  exact hsurplus

/-- **COUNT ONE.**  Two free atoms selected and one left outside.  These are the
nine mixed triples that hold exactly one line label. -/
theorem oneLine_countOne_not_forall_sharpBalanceValue_nonneg (design : WeightedDesign 6 3)
    (selected : Finset (Fin 6)) {unitNormal : Fin 3 → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hbracket : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    {freeFirst freeSecond freeThird : Fin 6}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (hperm : ((({0, 1, 2} : Finset (Fin 6)))ᶜ) = {freeFirst, freeSecond, freeThird})
    (hFirstIn : freeFirst ∈ selected) (hSecondIn : freeSecond ∈ selected)
    (hThirdOut : freeThird ∉ selected) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6))
              unitNormal probeVec := by
  obtain ⟨hcrossFirst, hcrossSecond⟩ := crossProducts_nonpos_of_two_in_one_out design
    (by norm_num) hFirstIn hSecondIn hThirdOut
  exact oneLine_not_forall_sharpBalanceValue_nonneg design selected hunit hlineFlat hbracket
    hsurplus hFirstSecond hFirstThird hSecondThird hperm hcrossFirst hcrossSecond

/-- **COUNT TWO.**  One free atom selected and two left outside.  These are the
nine mixed triples that hold two line labels. -/
theorem oneLine_countTwo_not_forall_sharpBalanceValue_nonneg (design : WeightedDesign 6 3)
    (selected : Finset (Fin 6)) {unitNormal : Fin 3 → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (hbracket : tripleBracket (design.atom 3) (design.atom 4) (design.atom 5) ≠ 0)
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    {freeFirst freeSecond freeThird : Fin 6}
    (hFirstSecond : freeFirst ≠ freeSecond) (hFirstThird : freeFirst ≠ freeThird)
    (hSecondThird : freeSecond ≠ freeThird)
    (hperm : ((({0, 1, 2} : Finset (Fin 6)))ᶜ) = {freeFirst, freeSecond, freeThird})
    (hFirstOut : freeFirst ∉ selected) (hSecondOut : freeSecond ∉ selected)
    (hThirdIn : freeThird ∈ selected) :
    ¬ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
        0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6))
              unitNormal probeVec := by
  obtain ⟨hcrossFirst, hcrossSecond⟩ := crossProducts_nonpos_of_one_in_two_out design
    (by norm_num) hFirstOut hSecondOut hThirdIn
  exact oneLine_not_forall_sharpBalanceValue_nonneg design selected hunit hlineFlat hbracket
    hsurplus hFirstSecond hFirstThird hSecondThird hperm hcrossFirst hcrossSecond

/-- **THE FREE TRIPLE AND THE LINE TRIPLE ARE THE ONLY SURVIVORS.**  At a one-line
design the split measure keeps one sign on `{3, 4, 5}` exactly when the selection
holds all three free atoms or none of them.  Those are the free triple and the
line triple, and section 3 gives their balance a sign. -/
theorem oneLine_sharpBalanceValue_nonneg_of_lineTriple (design : WeightedDesign 6 3)
    {selected : Finset (Fin 6)} (hdisjoint : ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      freeLabel ∉ selected) (unitNormal probeVec : Fin 3 → ℝ) :
    0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal probeVec := by
  refine sharpBalanceValue_nonneg_of_sharp_disjoint design ?_ unitNormal probeVec
  intro freeLabel hmem
  exact hdisjoint freeLabel (by rwa [oneLine_lineSet_compl] at hmem)

end Gtz
