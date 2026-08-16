import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.KFourBandAtlas

/-!
# The selection margin, its caps, and the extremal graphic point

The objective picks a rank-sized selection whose projection block beats the
weight diagonal.  This module measures HOW MUCH it beats it by, and proves the
elementary caps on that quantity.  Nothing here needs an eigenvalue, a matrix
square root, or a spectral theorem.

The margin object is `Gtz.MarginReaches`: some injective selection keeps its
block gap positive definite after a scalar floor is removed.

Four laws.

* `Gtz.diag_lt_of_posDef_blockMarginGap` -- the DIAGONAL CAP.  Every label of a
  selection that reaches the floor carries leverage above its own weight plus
  the floor.
* `Gtz.pair_cap_of_posDef_blockMarginGap` -- the PAIR CAP.  Every PAIR inside
  such a selection obeys `2 |P a b| < (P a a - w a - t) + (P b b - w b - t)`.
  This strictly refines the diagonal cap and it is what decides the graphic
  point.
* `Gtz.exists_diag_ge_quarter_of_card_four` -- the LEVERAGE PIGEONHOLE.  Any
  four labels of a rank-three projection on six labels contain one of leverage
  at least a quarter, because a trace of three cannot fit inside four small
  entries and two unit entries.

The pigeonhole and the diagonal cap together give
`Gtz.exists_three_diagonal_admissible`: when every weight plus the floor stays
below a quarter, three labels always pass the diagonal test.  So the DIAGONAL
channel cannot by itself refuse the margin at such weights, and every refusal
there is an off-diagonal fact.  That is the structural dichotomy of the margin.

The last section computes the margin EXACTLY at the graphic point of `K4`, the
rigid stratum.  `Gtz.kfourEdgeProjection` is the six-by-six rational projection
of the six edges of `K4`.  At uniform weight its margin is exactly one twelfth
(`Gtz.marginReaches_kfourEdgeProjection_iff`).  The refusal costs one pair minor
and one counting fact: three edges of `K4` never form a matching, so every
selection carries two edges through a common vertex, and that pair alone pins
the floor.  Its diagonal cap reads `1/3`, four times the true margin, so the
graphic point's whole difficulty is off-diagonal.
-/

namespace Gtz

open scoped BigOperators

open Matrix

variable {size : ℕ}

/-! ## 1. The diagonal of a symmetric idempotent -/

/-- The diagonal entry of a symmetric idempotent is its own row's squared
length.  The whole diagonal layer rests on this one computation. -/
theorem sum_sq_row_eq_diag_of_symm_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form) (label : Fin size) :
    ∑ other, form label other ^ 2 = form label label := by
  have hentry := congrFun (congrFun hidempotent label) label
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun other _ => ?_
  have hflip : form other label = form label other := by
    have := congrFun (congrFun hsymmetric label) other
    simpa [Matrix.transpose_apply] using this
  rw [hflip]
  ring

/-- Every diagonal entry of a symmetric idempotent is non-negative. -/
theorem diag_nonneg_of_symm_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form) (label : Fin size) :
    0 ≤ form label label := by
  rw [← sum_sq_row_eq_diag_of_symm_idempotent form hsymmetric hidempotent label]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Every diagonal entry of a symmetric idempotent is at most one.  The row's
own square is one term of a sum that equals the entry itself. -/
theorem diag_le_one_of_symm_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form) (label : Fin size) :
    form label label ≤ 1 := by
  have hsum := sum_sq_row_eq_diag_of_symm_idempotent form hsymmetric hidempotent label
  have hterm : form label label ^ 2 ≤ ∑ other, form label other ^ 2 :=
    Finset.single_le_sum (f := fun other => form label other ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ label)
  rw [hsum] at hterm
  nlinarith [hterm]

/-! ## 2. The leverage pigeonhole -/

/-- The trace splits across a label set and its complement, with the diagonal
cap on one side and the unit bound on the other. -/
theorem trace_split_le_of_diag_le_on (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    (lightSet : Finset (Fin size)) (bound : ℝ)
    (hlight : ∀ label ∈ lightSet, form label label ≤ bound) :
    Matrix.trace form
      ≤ (lightSet.card : ℝ) * bound + ((Finset.univ \ lightSet).card : ℝ) := by
  have hsplit : Matrix.trace form
      = (∑ label ∈ lightSet, form label label)
        + ∑ label ∈ Finset.univ \ lightSet, form label label := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [← Finset.sum_sdiff (Finset.subset_univ lightSet)]
    ring
  have hleft : (∑ label ∈ lightSet, form label label) ≤ (lightSet.card : ℝ) * bound := by
    calc (∑ label ∈ lightSet, form label label) ≤ ∑ _label ∈ lightSet, bound :=
          Finset.sum_le_sum hlight
      _ = (lightSet.card : ℝ) * bound := by rw [Finset.sum_const, nsmul_eq_mul]
  have hright : (∑ label ∈ Finset.univ \ lightSet, form label label)
      ≤ ((Finset.univ \ lightSet).card : ℝ) := by
    calc (∑ label ∈ Finset.univ \ lightSet, form label label)
        ≤ ∑ _label ∈ Finset.univ \ lightSet, (1 : ℝ) :=
          Finset.sum_le_sum fun label _ =>
            diag_le_one_of_symm_idempotent form hsymmetric hidempotent label
      _ = ((Finset.univ \ lightSet).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsplit]
  linarith

/-- **THE LEVERAGE PIGEONHOLE.**  In a rank-three projection on six labels, any
four labels contain one whose leverage is at least a quarter.

A trace of three cannot fit inside four entries below a quarter together with
two entries below one.  This is the structural reason the diagonal channel
alone cannot drive the margin to zero. -/
theorem exists_diag_ge_quarter_of_card_four (form : Matrix (Fin 6) (Fin 6) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    (htrace : Matrix.trace form = 3) (lightSet : Finset (Fin 6)) (hcard : lightSet.card = 4) :
    ∃ label ∈ lightSet, (1 : ℝ) / 4 ≤ form label label := by
  by_contra hcontra
  push Not at hcontra
  have hnonempty : lightSet.Nonempty := Finset.card_pos.mp (by rw [hcard]; norm_num)
  have hcompl : (Finset.univ \ lightSet).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, hcard]
    simp
  have hsplit : Matrix.trace form
      = (∑ label ∈ lightSet, form label label)
        + ∑ label ∈ Finset.univ \ lightSet, form label label := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [← Finset.sum_sdiff (Finset.subset_univ lightSet)]
    ring
  have hleft : (∑ label ∈ lightSet, form label label) < (4 : ℝ) * ((1 : ℝ) / 4) := by
    calc (∑ label ∈ lightSet, form label label)
        < ∑ _label ∈ lightSet, (1 : ℝ) / 4 :=
          Finset.sum_lt_sum_of_nonempty hnonempty fun label hlabel => hcontra label hlabel
      _ = (4 : ℝ) * ((1 : ℝ) / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; norm_num
  have hright : (∑ label ∈ Finset.univ \ lightSet, form label label) ≤ (2 : ℝ) := by
    calc (∑ label ∈ Finset.univ \ lightSet, form label label)
        ≤ ∑ _label ∈ Finset.univ \ lightSet, (1 : ℝ) :=
          Finset.sum_le_sum fun label _ =>
            diag_le_one_of_symm_idempotent form hsymmetric hidempotent label
      _ = (2 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcompl]; norm_num
  rw [hsplit] at htrace
  linarith

/-- **AT MOST THREE LIGHT LABELS.**  The pigeonhole, read as a cardinality
bound: the labels of leverage below a quarter never number four. -/
theorem card_light_labels_le_three (form : Matrix (Fin 6) (Fin 6) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    (htrace : Matrix.trace form = 3) :
    (Finset.univ.filter fun label => form label label < (1 : ℝ) / 4).card ≤ 3 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨fourLabels, hsubset, hcard⟩ :=
    Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ.filter fun label => form label label < (1 : ℝ) / 4).card by omega)
  obtain ⟨label, hlabel, hheavy⟩ :=
    exists_diag_ge_quarter_of_card_four form hsymmetric hidempotent htrace fourLabels hcard
  have hlight := Finset.mem_filter.mp (hsubset hlabel)
  linarith [hlight.2]

/-! ## 3. The margin object and its two caps -/

/-- The block gap of a selection with a scalar floor removed.  Floor and weight
enter the same diagonal, so the object stays a single subtraction. -/
def blockMarginGap (form : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    {chosen : ℕ} (pick : Fin chosen → Fin size) (floorValue : ℝ) :
    Matrix (Fin chosen) (Fin chosen) ℝ :=
  form.submatrix pick pick - Matrix.diagonal (fun slot => weight (pick slot) + floorValue)

theorem blockMarginGap_diag (form : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    {chosen : ℕ} (pick : Fin chosen → Fin size) (floorValue : ℝ) (slot : Fin chosen) :
    blockMarginGap form weight pick floorValue slot slot
      = form (pick slot) (pick slot) - (weight (pick slot) + floorValue) := by
  simp [blockMarginGap]

theorem blockMarginGap_offDiag (form : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    {chosen : ℕ} (pick : Fin chosen → Fin size) (floorValue : ℝ)
    {leftSlot rightSlot : Fin chosen} (hne : leftSlot ≠ rightSlot) :
    blockMarginGap form weight pick floorValue leftSlot rightSlot
      = form (pick leftSlot) (pick rightSlot) := by
  simp [blockMarginGap, Matrix.diagonal_apply_ne _ hne]

theorem blockMarginGap_symm (form : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    {chosen : ℕ} (pick : Fin chosen → Fin size) (floorValue : ℝ) (hsymmetric : formᵀ = form) :
    (blockMarginGap form weight pick floorValue)ᵀ
      = blockMarginGap form weight pick floorValue := by
  ext leftSlot rightSlot
  rw [Matrix.transpose_apply]
  rcases eq_or_ne rightSlot leftSlot with rfl | hne
  · rfl
  · rw [blockMarginGap_offDiag _ _ _ _ hne, blockMarginGap_offDiag _ _ _ _ hne.symm]
    have := congrFun (congrFun hsymmetric (pick leftSlot)) (pick rightSlot)
    simpa [Matrix.transpose_apply] using this

/-- **THE MARGIN.**  The selection margin reaches `floorValue` when some
injective selection of the given size keeps its block gap positive definite
after that floor is removed. -/
def MarginReaches (form : Matrix (Fin size) (Fin size) ℝ) (weight : Fin size → ℝ)
    (chosen : ℕ) (floorValue : ℝ) : Prop :=
  ∃ pick : Fin chosen → Fin size, Function.Injective pick ∧
    (blockMarginGap form weight pick floorValue).PosDef

/-- A scalar helper: two one-sided bounds give an absolute-value bound. -/
theorem abs_lt_of_add_pos {value bound : ℝ} (hplus : 0 < bound + value)
    (hminus : 0 < bound - value) : |value| < bound := by
  rcases abs_cases value with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> linarith

/-- **THE QUADRATIC FORM ENGINE.**  Positive definiteness of a three-by-three
form read at an explicit probe.  Everything downstream is an instance. -/
theorem quadForm_pos_of_posDef {gap : Matrix (Fin 3) (Fin 3) ℝ} (hposDef : gap.PosDef)
    (first second third : ℝ) (hnonzero : ¬(first = 0 ∧ second = 0 ∧ third = 0)) :
    0 < first ^ 2 * gap 0 0 + second ^ 2 * gap 1 1 + third ^ 2 * gap 2 2
      + first * second * (gap 0 1 + gap 1 0)
      + first * third * (gap 0 2 + gap 2 0)
      + second * third * (gap 1 2 + gap 2 1) := by
  have hvec : (![first, second, third] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    refine hnonzero ⟨?_, ?_, ?_⟩
    · simpa using congrFun hzero 0
    · simpa using congrFun hzero 1
    · simpa using congrFun hzero 2
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hvec
  rw [star_trivial] at hform
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hform
  nlinarith [hform]

/-- **THE TWO-SLOT CAP.**  Positive definiteness at a two-coordinate probe: the
off-diagonal pair is dominated by the two diagonal entries.  One dot product, no
minors, no eigenvalue. -/
theorem two_slot_cap_of_posDef {gap : Matrix (Fin 3) (Fin 3) ℝ} (hposDef : gap.PosDef)
    {leftSlot rightSlot : Fin 3} (hne : leftSlot ≠ rightSlot) :
    |gap leftSlot rightSlot + gap rightSlot leftSlot| < gap leftSlot leftSlot
      + gap rightSlot rightSlot := by
  have hq := quadForm_pos_of_posDef hposDef
  have h01p := hq 1 1 0 (by norm_num)
  have h01m := hq 1 (-1) 0 (by norm_num)
  have h02p := hq 1 0 1 (by norm_num)
  have h02m := hq 1 0 (-1) (by norm_num)
  have h12p := hq 0 1 1 (by norm_num)
  have h12m := hq 0 1 (-1) (by norm_num)
  fin_cases leftSlot <;> fin_cases rightSlot <;> simp_all
  all_goals refine abs_lt_of_add_pos ?_ ?_
  all_goals nlinarith

/-- A positive definite three-by-three form has a positive diagonal, probed by
one coordinate vector.  No eigenvalue appears. -/
theorem posDef_diag_pos {gap : Matrix (Fin 3) (Fin 3) ℝ} (hposDef : gap.PosDef)
    (slot : Fin 3) : 0 < gap slot slot := by
  have hq := quadForm_pos_of_posDef hposDef
  have h0 := hq 1 0 0 (by norm_num)
  have h1 := hq 0 1 0 (by norm_num)
  have h2 := hq 0 0 1 (by norm_num)
  fin_cases slot <;> simp_all

/-- **THE DIAGONAL CAP.**  Every label of a selection that reaches the floor
carries leverage strictly above its own weight plus the floor. -/
theorem diag_lt_of_posDef_blockMarginGap (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {pick : Fin 3 → Fin size} {floorValue : ℝ}
    (hposDef : (blockMarginGap form weight pick floorValue).PosDef) (slot : Fin 3) :
    weight (pick slot) + floorValue < form (pick slot) (pick slot) := by
  have hdiag := posDef_diag_pos hposDef slot
  rw [blockMarginGap_diag] at hdiag
  linarith

/-- **THE PAIR CAP.**  Every pair inside a selection that reaches the floor
obeys `2 |P a b| < (P a a - w a - t) + (P b b - w b - t)`.  This strictly
refines the diagonal cap: it charges the off-diagonal entry against the two
diagonal gaps together, and it is the law that decides the graphic point. -/
theorem pair_cap_of_posDef_blockMarginGap (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {pick : Fin 3 → Fin size} {floorValue : ℝ}
    (hsymmetric : formᵀ = form)
    (hposDef : (blockMarginGap form weight pick floorValue).PosDef)
    {leftSlot rightSlot : Fin 3} (hne : leftSlot ≠ rightSlot) :
    2 * |form (pick leftSlot) (pick rightSlot)|
      < (form (pick leftSlot) (pick leftSlot) - weight (pick leftSlot) - floorValue)
        + (form (pick rightSlot) (pick rightSlot) - weight (pick rightSlot) - floorValue) := by
  have hflip : form (pick rightSlot) (pick leftSlot) = form (pick leftSlot) (pick rightSlot) := by
    have := congrFun (congrFun hsymmetric (pick leftSlot)) (pick rightSlot)
    simpa [Matrix.transpose_apply] using this
  have hcap := two_slot_cap_of_posDef hposDef hne
  rw [blockMarginGap_diag, blockMarginGap_diag, blockMarginGap_offDiag _ _ _ _ hne,
    blockMarginGap_offDiag _ _ _ _ hne.symm, hflip] at hcap
  have hdouble : form (pick leftSlot) (pick rightSlot)
      + form (pick leftSlot) (pick rightSlot)
      = 2 * form (pick leftSlot) (pick rightSlot) := by ring
  rw [hdouble, abs_mul, abs_two] at hcap
  linarith

/-- The pair cap, read off the margin predicate itself. -/
theorem pair_cap_of_marginReaches (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {floorValue : ℝ} (hsymmetric : formᵀ = form)
    (hmargin : MarginReaches form weight 3 floorValue) :
    ∃ pick : Fin 3 → Fin size, Function.Injective pick ∧
      ∀ leftSlot rightSlot : Fin 3, leftSlot ≠ rightSlot →
        2 * |form (pick leftSlot) (pick rightSlot)|
          < (form (pick leftSlot) (pick leftSlot) - weight (pick leftSlot) - floorValue)
            + (form (pick rightSlot) (pick rightSlot) - weight (pick rightSlot)
              - floorValue) := by
  obtain ⟨pick, hinjective, hposDef⟩ := hmargin
  exact ⟨pick, hinjective, fun leftSlot rightSlot hne =>
    pair_cap_of_posDef_blockMarginGap form weight hsymmetric hposDef hne⟩

/-- **THE THIRD-LARGEST CAP.**  A margin that reaches the floor exhibits three
labels whose leverage clears their own weight plus the floor.  So the margin
never exceeds the third largest of `P c c - w c`. -/
theorem exists_three_labels_of_marginReaches (form : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) {floorValue : ℝ}
    (hmargin : MarginReaches form weight 3 floorValue) :
    ∃ heavySet : Finset (Fin size), heavySet.card = 3 ∧
      ∀ label ∈ heavySet, weight label + floorValue < form label label := by
  obtain ⟨pick, hinjective, hposDef⟩ := hmargin
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective]
    simp
  · intro label hlabel
    obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hlabel
    rw [← hslot]
    exact diag_lt_of_posDef_blockMarginGap form weight hposDef slot

/-- **THE DIAGONAL CHANNEL CLOSES.**  When every weight plus the floor stays
below a quarter, three labels always pass the diagonal test, because at most
three labels carry leverage below a quarter.

So the diagonal cap can never by itself refuse the margin at such weights, and
every refusal there is an off-diagonal fact.  This is the structural dichotomy:
the weight channel and the direction channel are genuinely different, and the
pigeonhole is what separates them. -/
theorem exists_three_diagonal_admissible (form : Matrix (Fin 6) (Fin 6) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    (htrace : Matrix.trace form = 3) (weight : Fin 6 → ℝ) (floorValue : ℝ)
    (hlight : ∀ label : Fin 6, weight label + floorValue < (1 : ℝ) / 4) :
    ∃ heavySet : Finset (Fin 6), heavySet.card = 3 ∧
      ∀ label ∈ heavySet, weight label + floorValue < form label label := by
  have hcard := card_light_labels_le_three form hsymmetric hidempotent htrace
  set lightSet := Finset.univ.filter fun label => form label label < (1 : ℝ) / 4 with hlightSet
  have hcomplCard : 3 ≤ (Finset.univ \ lightSet).card := by
    have hsd : (Finset.univ \ lightSet).card = 6 - lightSet.card := by
      rw [Finset.card_sdiff, Finset.inter_univ]
      simp
    omega
  obtain ⟨heavySet, hsubset, hcardHeavy⟩ := Finset.exists_subset_card_eq hcomplCard
  refine ⟨heavySet, hcardHeavy, fun label hlabel => ?_⟩
  have hmem := hsubset hlabel
  have hnotLight : label ∉ lightSet := (Finset.mem_sdiff.mp hmem).2
  have hquarter : (1 : ℝ) / 4 ≤ form label label := by
    by_contra hcontra
    push Not at hcontra
    exact hnotLight (Finset.mem_filter.mpr ⟨Finset.mem_univ label, hcontra⟩)
  linarith [hlight label]

/-! ## 4. The graphic point of `K4`, exactly -/

/-- Four times the Gram entry of two edges of `K4`, as an integer.  Edges are
indexed `12, 13, 14, 23, 24, 34`.  Two equal edges read `2`, the three disjoint
pairs read `0`, and a meeting pair reads `1` or `-1` by orientation. -/
def kfourGramInt (leftEdge rightEdge : Fin 6) : ℤ :=
  if leftEdge = rightEdge then 2
  else if (leftEdge = 0 ∧ rightEdge = 5) ∨ (leftEdge = 5 ∧ rightEdge = 0)
      ∨ (leftEdge = 1 ∧ rightEdge = 4) ∨ (leftEdge = 4 ∧ rightEdge = 1)
      ∨ (leftEdge = 2 ∧ rightEdge = 3) ∨ (leftEdge = 3 ∧ rightEdge = 2) then 0
  else if (leftEdge = 0 ∧ rightEdge = 3) ∨ (leftEdge = 3 ∧ rightEdge = 0)
      ∨ (leftEdge = 0 ∧ rightEdge = 4) ∨ (leftEdge = 4 ∧ rightEdge = 0)
      ∨ (leftEdge = 1 ∧ rightEdge = 5) ∨ (leftEdge = 5 ∧ rightEdge = 1)
      ∨ (leftEdge = 3 ∧ rightEdge = 5) ∨ (leftEdge = 5 ∧ rightEdge = 3) then -1
  else 1

theorem kfourGramInt_symm (leftEdge rightEdge : Fin 6) :
    kfourGramInt leftEdge rightEdge = kfourGramInt rightEdge leftEdge := by
  fin_cases leftEdge <;> fin_cases rightEdge <;> decide

theorem kfourGramInt_diag (edge : Fin 6) : kfourGramInt edge edge = 2 := by
  fin_cases edge <;> decide

/-- The integer core is idempotent up to the factor four.  Thirty-six decidable
identities over six-term sums. -/
theorem kfourGramInt_mul_self (leftEdge rightEdge : Fin 6) :
    (∑ middle, kfourGramInt leftEdge middle * kfourGramInt middle rightEdge)
      = 4 * kfourGramInt leftEdge rightEdge := by
  fin_cases leftEdge <;> fin_cases rightEdge <;> decide

/-- **THE MATCHING COUNT.**  Three distinct edges of `K4` never form a matching:
some two of them meet at a vertex.  Four vertices cannot carry three pairwise
disjoint edges, and the Gram entry records exactly that. -/
theorem kfourGramInt_exists_meeting_pair (firstEdge secondEdge thirdEdge : Fin 6)
    (hfs : firstEdge ≠ secondEdge) (hft : firstEdge ≠ thirdEdge)
    (hst : secondEdge ≠ thirdEdge) :
    kfourGramInt firstEdge secondEdge ≠ 0 ∨ kfourGramInt firstEdge thirdEdge ≠ 0
      ∨ kfourGramInt secondEdge thirdEdge ≠ 0 := by
  fin_cases firstEdge <;> fin_cases secondEdge <;> fin_cases thirdEdge <;> revert hfs hft hst <;>
    decide

/-- A meeting pair reads plus or minus one, never anything else. -/
theorem kfourGramInt_eq_one_or_neg_one {leftEdge rightEdge : Fin 6}
    (hne : leftEdge ≠ rightEdge) (hmeet : kfourGramInt leftEdge rightEdge ≠ 0) :
    kfourGramInt leftEdge rightEdge = 1 ∨ kfourGramInt leftEdge rightEdge = -1 := by
  fin_cases leftEdge <;> fin_cases rightEdge <;> revert hne hmeet <;> decide

/-- **THE GRAPHIC POINT.**  The rank-three projection of the six edges of `K4`,
the rigid stratum of the campaign, as an explicit rational matrix. -/
noncomputable def kfourEdgeProjection : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun leftEdge rightEdge => (kfourGramInt leftEdge rightEdge : ℝ) / 4

theorem kfourEdgeProjection_apply (leftEdge rightEdge : Fin 6) :
    kfourEdgeProjection leftEdge rightEdge = (kfourGramInt leftEdge rightEdge : ℝ) / 4 := rfl

theorem kfourEdgeProjection_symm : kfourEdgeProjectionᵀ = kfourEdgeProjection := by
  ext leftEdge rightEdge
  rw [Matrix.transpose_apply, kfourEdgeProjection_apply, kfourEdgeProjection_apply,
    kfourGramInt_symm]

theorem kfourEdgeProjection_idempotent :
    kfourEdgeProjection * kfourEdgeProjection = kfourEdgeProjection := by
  ext leftEdge rightEdge
  rw [Matrix.mul_apply, kfourEdgeProjection_apply]
  have hcore := kfourGramInt_mul_self leftEdge rightEdge
  have hcast : (∑ middle, (kfourGramInt leftEdge middle : ℝ) * (kfourGramInt middle rightEdge : ℝ))
      = ((∑ middle, kfourGramInt leftEdge middle * kfourGramInt middle rightEdge : ℤ) : ℝ) := by
    push_cast
    ring
  simp only [kfourEdgeProjection_apply]
  rw [show (∑ middle, (kfourGramInt leftEdge middle : ℝ) / 4 * ((kfourGramInt middle rightEdge : ℝ) / 4))
      = (∑ middle, (kfourGramInt leftEdge middle : ℝ) * (kfourGramInt middle rightEdge : ℝ)) / 16 by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun middle _ => by ring]
  rw [hcast, hcore]
  push_cast
  ring

theorem kfourEdgeProjection_diag (edge : Fin 6) : kfourEdgeProjection edge edge = 1 / 2 := by
  rw [kfourEdgeProjection_apply, kfourGramInt_diag]
  norm_num

theorem kfourEdgeProjection_trace : Matrix.trace kfourEdgeProjection = 3 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, kfourEdgeProjection_diag, Fin.sum_univ_six]
  norm_num

/-- A meeting pair of edges gives a projection entry of absolute value exactly a
quarter. -/
theorem abs_kfourEdgeProjection_of_meeting {leftEdge rightEdge : Fin 6}
    (hne : leftEdge ≠ rightEdge) (hmeet : kfourGramInt leftEdge rightEdge ≠ 0) :
    |kfourEdgeProjection leftEdge rightEdge| = 1 / 4 := by
  rw [kfourEdgeProjection_apply]
  rcases kfourGramInt_eq_one_or_neg_one hne hmeet with hvalue | hvalue <;> rw [hvalue] <;>
    norm_num

/-- The uniform weight on six labels. -/
noncomputable def uniformSixWeight : Fin 6 → ℝ := fun _ => 1 / 6

theorem uniformSixWeight_apply (label : Fin 6) : uniformSixWeight label = 1 / 6 := rfl

/-- The star of the first vertex of `K4`: its three edges are the labels `0, 1,
2`, taken by the order-preserving inclusion of `Fin 3` into `Fin 6`. -/
def kfourStarPick : Fin 3 → Fin 6 := Fin.castLE (by norm_num)

theorem kfourStarPick_injective : Function.Injective kfourStarPick :=
  fun _ _ heq => Fin.castLE_injective _ heq

theorem kfourStarPick_gram (leftSlot rightSlot : Fin 3) :
    kfourGramInt (kfourStarPick leftSlot) (kfourStarPick rightSlot)
      = if leftSlot = rightSlot then 2 else 1 := by
  fin_cases leftSlot <;> fin_cases rightSlot <;> decide

/-- **THE STAR REACHES ONE TWELFTH.**  The three edges at a vertex of `K4` keep
their block gap positive definite for every floor strictly below one twelfth.
The block is a quarter of `1 + J`, and its third leading minor factors as
`(a - 1/4)^2 (a + 1/2)` with `a = 1/3 - t`. -/
theorem marginReaches_kfourEdgeProjection {floorValue : ℝ} (hfloor : floorValue < 1 / 12) :
    MarginReaches kfourEdgeProjection uniformSixWeight 3 floorValue := by
  refine ⟨kfourStarPick, kfourStarPick_injective, ?_⟩
  have hdiag : ∀ slot : Fin 3,
      blockMarginGap kfourEdgeProjection uniformSixWeight kfourStarPick floorValue slot slot
        = 1 / 3 - floorValue := by
    intro slot
    rw [blockMarginGap_diag, kfourEdgeProjection_diag, uniformSixWeight_apply]
    linarith
  have hoff : ∀ leftSlot rightSlot : Fin 3, leftSlot ≠ rightSlot →
      blockMarginGap kfourEdgeProjection uniformSixWeight kfourStarPick floorValue
        leftSlot rightSlot = 1 / 4 := by
    intro leftSlot rightSlot hne
    rw [blockMarginGap_offDiag _ _ _ _ hne, kfourEdgeProjection_apply, kfourStarPick_gram,
      if_neg hne]
    norm_num
  refine (posDef_finThree_iff_leadingMinors _ ?_).mpr ?_
  · ext leftSlot rightSlot
    rw [Matrix.transpose_apply]
    rcases eq_or_ne leftSlot rightSlot with rfl | hne
    · rfl
    · rw [hoff _ _ hne, hoff _ _ hne.symm]
  · rw [hdiag 0, hdiag 1, hdiag 2, hoff 0 1 (by decide), hoff 0 2 (by decide),
      hoff 1 2 (by decide)]
    have hgap : (0 : ℝ) < (1 / 3 - floorValue) - 1 / 4 := by linarith
    have hsum : (0 : ℝ) < (1 / 3 - floorValue) + 1 / 2 := by linarith
    refine ⟨by linarith, by nlinarith [hgap, hsum], ?_⟩
    nlinarith [mul_pos (mul_pos hgap hgap) hsum, hgap, hsum]

/-- **THE GRAPHIC POINT IS EXACTLY ONE TWELFTH.**  No selection reaches a floor
at or above one twelfth.  Every three edges of `K4` carry a meeting pair, that
pair's projection entry has absolute value a quarter, and the pair cap turns the
two diagonal gaps of `1/3 - t` into `1/2 < 2/3 - 2 t`.

The margin of the rigid stratum at uniform weight is therefore exactly `1/12`,
and this is the first exactly-computed value of the selection margin. -/
theorem not_marginReaches_kfourEdgeProjection {floorValue : ℝ} (hfloor : 1 / 12 ≤ floorValue) :
    ¬ MarginReaches kfourEdgeProjection uniformSixWeight 3 floorValue := by
  rintro hmargin
  obtain ⟨pick, hinjective, hcaps⟩ :=
    pair_cap_of_marginReaches kfourEdgeProjection uniformSixWeight
      kfourEdgeProjection_symm hmargin
  have hne01 : pick 0 ≠ pick 1 := fun heq => by simpa using hinjective heq
  have hne02 : pick 0 ≠ pick 2 := fun heq => by simpa using hinjective heq
  have hne12 : pick 1 ≠ pick 2 := fun heq => by simpa using hinjective heq
  have hfinish : ∀ leftSlot rightSlot : Fin 3, leftSlot ≠ rightSlot →
      pick leftSlot ≠ pick rightSlot →
      kfourGramInt (pick leftSlot) (pick rightSlot) ≠ 0 → False := by
    intro leftSlot rightSlot hslots hlabels hmeet
    have hcap := hcaps leftSlot rightSlot hslots
    rw [abs_kfourEdgeProjection_of_meeting hlabels hmeet, kfourEdgeProjection_diag,
      kfourEdgeProjection_diag, uniformSixWeight_apply, uniformSixWeight_apply] at hcap
    linarith
  obtain hmeet | hmeet | hmeet :=
    kfourGramInt_exists_meeting_pair (pick 0) (pick 1) (pick 2) hne01 hne02 hne12
  · exact hfinish 0 1 (by decide) hne01 hmeet
  · exact hfinish 0 2 (by decide) hne02 hmeet
  · exact hfinish 1 2 (by decide) hne12 hmeet

/-- The margin of the graphic point at uniform weight, both halves together. -/
theorem marginReaches_kfourEdgeProjection_iff (floorValue : ℝ) :
    MarginReaches kfourEdgeProjection uniformSixWeight 3 floorValue ↔ floorValue < 1 / 12 :=
  ⟨fun hmargin => by
    by_contra hcontra
    push Not at hcontra
    exact not_marginReaches_kfourEdgeProjection hcontra hmargin,
   marginReaches_kfourEdgeProjection⟩

/-- The graphic point is a genuine rank-three projection, collected. -/
theorem kfourEdgeProjection_isProjection :
    kfourEdgeProjectionᵀ = kfourEdgeProjection
      ∧ kfourEdgeProjection * kfourEdgeProjection = kfourEdgeProjection
      ∧ Matrix.trace kfourEdgeProjection = 3 :=
  ⟨kfourEdgeProjection_symm, kfourEdgeProjection_idempotent, kfourEdgeProjection_trace⟩

/-- **THE DIAGONAL CAP IS NOT SHARP AT THE GRAPHIC POINT.**  Its leverages are
all a half, so the diagonal cap reads `1/3`, four times the true margin `1/12`.
The graphic point's whole difficulty is off-diagonal, which is exactly what the
pair cap sees and the diagonal cap does not. -/
theorem kfourEdgeProjection_diagonalCap_not_sharp :
    (∀ label : Fin 6, kfourEdgeProjection label label - uniformSixWeight label = 1 / 3)
      ∧ ¬ MarginReaches kfourEdgeProjection uniformSixWeight 3 (1 / 3) := by
  refine ⟨fun label => ?_, not_marginReaches_kfourEdgeProjection (by norm_num)⟩
  rw [kfourEdgeProjection_diag, uniformSixWeight_apply]
  norm_num

/-- **THE DIAGONAL CHANNEL IS OPEN AT THE GRAPHIC POINT.**  The pigeonhole fires
there at every floor below a quarter less a sixth, so the diagonal test alone
never refuses the graphic point in that range, while the true margin stops at
one twelfth.  The gap between the two is the whole content of the pair cap. -/
theorem kfourEdgeProjection_diagonal_channel_open {floorValue : ℝ}
    (hfloor : floorValue < 1 / 4 - 1 / 6) :
    ∃ heavySet : Finset (Fin 6), heavySet.card = 3 ∧
      ∀ label ∈ heavySet,
        uniformSixWeight label + floorValue < kfourEdgeProjection label label := by
  refine exists_three_diagonal_admissible kfourEdgeProjection kfourEdgeProjection_symm
    kfourEdgeProjection_idempotent kfourEdgeProjection_trace uniformSixWeight floorValue
    fun label => ?_
  rw [uniformSixWeight_apply]
  linarith

end Gtz
