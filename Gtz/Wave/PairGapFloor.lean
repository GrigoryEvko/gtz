import Gtz.Wave.SelectionMarginLaws
import Gtz.Wave.ProjectionMinorShift

/-!
# The pair gap: the primitivity channel, and the two-point marginal

The campaign carries three clearance functionals and every one of them is
restricted to the line-free off-conic stratum.  `Gtz.wallClearanceOf` is a `min`
of a mass leg, a conic leg and `Gtz.bracketClearanceOf`, and the bracket leg is a
minimum over distinct TRIPLES of a squared bracket.  So it measures COPLANARITY,
and it vanishes on every stratum that carries a line.

The consumer `Gtz.ProjectionBlockSelects` quantifies over PRIMITIVE designs at all
five strata.  Primitivity is a statement about PAIRS -- no atom is a scalar
multiple of another -- and no landed functional measures it.  This file supplies
that functional on the projection form, with no root and no eigenvalue, and then
proves the identity that connects it to the block determinants the landed cells
consume.

## The centrepiece

`Gtz.sum_shadowTriple_through_pair` is new:

    ∑ over the third slot of  det P[{c, d, e}]  =  (rank - 2) * pairMinorAt P c d.

It is the two-point marginal of the determinantal measure, read with no cross
product, no Cauchy-Binet and no Plücker coordinate.  The proof is `det_fin_three`
against three landed row identities -- the row energy law, the idempotence
identity `∑ P c e * P d e = P c d`, and the trace law `∑ P e e = rank` -- and
then `ring`.  RANK enters exactly once, through the trace, and it enters as the
coefficient `rank - 2`.

Consequences.  The pair minor is the total determinantal mass of the triples
through that pair (`Gtz.pairMinorAt_eq_sum_shadowTriple`), so a pair gap is a
LOWER bound on that mass and, by pigeonhole, on a single block determinant
(`Gtz.exists_shadowTriple_ge_of_pairGapReaches`).  Chained through the landed
determinant cell that gives a selection theorem reading one pair minor and the
weights (`Gtz.exists_posDef_subsetSum_of_pairMinor_gt_weights`).

## What the functional cannot do, proved

`Gtz.pairGapReaches_le_of_projection` bounds any reachable level by
`(rank - 1) * rank / (size * (size - 1))`, which is `1 / 5` at `(6, 3)`.  With
the selection theorem's threshold that pins the cell's window exactly, and
`Gtz.not_pairGap_cell_at_uniformSixWeight` proves the window is EMPTY at the
uniform weight.  A pair gap alone cannot carry the objective at `(6, 3)`, and the
reason is quantitative, not incidental.
-/

namespace Gtz

open scoped BigOperators

open Matrix

variable {size rank : ℕ}

/-! ## Part 1 — the pair Gram determinant, and the weights factoring out -/

/-- The Gram determinant of a pair of vectors, `|u|^2 |v|^2 - (u . v)^2`. -/
def pairGramDet (leftVec rightVec : Fin rank → ℝ) : ℝ :=
  (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2

/-- The pair Gram determinant is non-negative: this is Cauchy-Schwarz. -/
theorem pairGramDet_nonneg (leftVec rightVec : Fin rank → ℝ) :
    0 ≤ pairGramDet leftVec rightVec := by
  have hcs := dotProduct_sq_le_mul leftVec rightVec
  simp only [pairGramDet]
  linarith

/-- The pair Gram determinant is symmetric in its two arguments. -/
theorem pairGramDet_comm (leftVec rightVec : Fin rank → ℝ) :
    pairGramDet leftVec rightVec = pairGramDet rightVec leftVec := by
  simp only [pairGramDet, dotProduct_comm leftVec rightVec]
  ring

/-- A scalar multiple kills the pair Gram determinant, at every rank. -/
theorem pairGramDet_smul_self (baseVec : Fin rank → ℝ) (ratio : ℝ) :
    pairGramDet baseVec (ratio • baseVec) = 0 := by
  have hright : (ratio • baseVec) ⬝ᵥ (ratio • baseVec)
      = ratio * ratio * (baseVec ⬝ᵥ baseVec) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coord _ => by ring
  have hcross : baseVec ⬝ᵥ (ratio • baseVec) = ratio * (baseVec ⬝ᵥ baseVec) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun coord _ => by ring
  simp only [pairGramDet, hright, hcross]
  ring

/-- **THE WEIGHTS FACTOR OUT OF THE PAIR MINOR.**  On a design's projection form
the landed two-by-two principal minor splits as a weight product times the atoms'
own Gram determinant.  The square roots cancel in pairs, so nothing irrational
survives, and the direction channel sits alone in the second factor. -/
theorem pairMinorAt_projectionOfDesign (design : WeightedDesign size rank)
    (first second : Fin size) :
    pairMinorAt (projectionOfDesign design) first second
      = design.weight first * design.weight second
        * pairGramDet (design.atom first) (design.atom second) := by
  have hfirst : Real.sqrt (design.weight first) * Real.sqrt (design.weight first)
      = design.weight first := Real.mul_self_sqrt (design.weight_pos first).le
  have hsecond : Real.sqrt (design.weight second) * Real.sqrt (design.weight second)
      = design.weight second := Real.mul_self_sqrt (design.weight_pos second).le
  simp only [pairMinorAt, projectionOfDesign_apply, pairGramDet]
  linear_combination (Real.sqrt (design.weight second) * Real.sqrt (design.weight second)
      * ((design.atom first ⬝ᵥ design.atom first) * (design.atom second ⬝ᵥ design.atom second)
        - (design.atom first ⬝ᵥ design.atom second) ^ 2)) * hfirst
    + (design.weight first
      * ((design.atom first ⬝ᵥ design.atom first) * (design.atom second ⬝ᵥ design.atom second)
        - (design.atom first ⬝ᵥ design.atom second) ^ 2)) * hsecond

/-- The pair minor of a design's projection is non-negative at every pair. -/
theorem pairMinorAt_projectionOfDesign_nonneg (design : WeightedDesign size rank)
    (first second : Fin size) :
    0 ≤ pairMinorAt (projectionOfDesign design) first second := by
  rw [pairMinorAt_projectionOfDesign]
  exact mul_nonneg (mul_nonneg (design.weight_pos first).le (design.weight_pos second).le)
    (pairGramDet_nonneg _ _)

/-! ## Part 2 — the zero locus at rank three, by Lagrange -/

/-- **LAGRANGE'S IDENTITY AT RANK THREE.**  The pair Gram determinant is the sum
of the squares of the three two-by-two minors.  This is what makes the vanishing
locus explicit with no inner-product-space machinery. -/
theorem pairGramDet_eq_sum_sq_minors (leftVec rightVec : Fin 3 → ℝ) :
    pairGramDet leftVec rightVec
      = (leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0) ^ 2
        + (leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0) ^ 2
        + (leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1) ^ 2 := by
  simp only [pairGramDet, dotProduct, Fin.sum_univ_three]
  ring

/-- A vanishing pair Gram determinant kills each of the three minors. -/
theorem minors_eq_zero_of_pairGramDet_eq_zero {leftVec rightVec : Fin 3 → ℝ}
    (hzero : pairGramDet leftVec rightVec = 0) :
    leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0 = 0
      ∧ leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0 = 0
      ∧ leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1 = 0 := by
  rw [pairGramDet_eq_sum_sq_minors] at hzero
  have hone := sq_nonneg (leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0)
  have htwo := sq_nonneg (leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0)
  have hthree := sq_nonneg (leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hone, htwo, hthree]
  · nlinarith [hone, htwo, hthree]
  · nlinarith [hone, htwo, hthree]

/-- **THE RATIO, IN PLAIN COORDINATES.**  Three vanishing two-by-two minors and a
non-zero base coordinate produce the scalar.  Stated over six real variables so
that the ratio arithmetic never meets a `Fin` literal. -/
theorem smul_of_minors_eq_zero {baseZero baseOne baseTwo topZero topOne topTwo : ℝ}
    (minorOne : baseZero * topOne - baseOne * topZero = 0)
    (minorTwo : baseZero * topTwo - baseTwo * topZero = 0)
    (minorThree : baseOne * topTwo - baseTwo * topOne = 0)
    (hbase : baseZero ≠ 0 ∨ baseOne ≠ 0 ∨ baseTwo ≠ 0) :
    ∃ ratio : ℝ, topZero = ratio * baseZero ∧ topOne = ratio * baseOne
      ∧ topTwo = ratio * baseTwo := by
  rcases hbase with hbase | hbase | hbase
  · refine ⟨topZero / baseZero, by field_simp, ?_, ?_⟩
    · field_simp
      linear_combination minorOne
    · field_simp
      linear_combination minorTwo
  · refine ⟨topOne / baseOne, ?_, by field_simp, ?_⟩
    · field_simp
      linear_combination -minorOne
    · field_simp
      linear_combination minorThree
  · refine ⟨topTwo / baseTwo, ?_, ?_, by field_simp⟩
    · field_simp
      linear_combination -minorTwo
    · field_simp
      linear_combination -minorThree

/-- **THE CONVERSE AT RANK THREE.**  A vanishing pair Gram determinant against a
non-zero vector exhibits the ratio.  Lagrange kills the three minors and the
plain-coordinate lemma reads the ratio off a non-zero slot. -/
theorem exists_smul_of_pairGramDet_eq_zero {leftVec rightVec : Fin 3 → ℝ}
    (hne : leftVec ≠ 0) (hzero : pairGramDet leftVec rightVec = 0) :
    ∃ ratio : ℝ, rightVec = ratio • leftVec := by
  obtain ⟨minorOne, minorTwo, minorThree⟩ := minors_eq_zero_of_pairGramDet_eq_zero hzero
  have hbase : leftVec 0 ≠ 0 ∨ leftVec 1 ≠ 0 ∨ leftVec 2 ≠ 0 := by
    by_contra hall
    have hzeroZero : leftVec 0 = 0 := not_not.mp fun hslot => hall (Or.inl hslot)
    have hzeroOne : leftVec 1 = 0 := not_not.mp fun hslot => hall (Or.inr (Or.inl hslot))
    have hzeroTwo : leftVec 2 = 0 := not_not.mp fun hslot => hall (Or.inr (Or.inr hslot))
    refine hne (funext fun coord => ?_)
    fin_cases coord
    · exact hzeroZero
    · exact hzeroOne
    · exact hzeroTwo
  obtain ⟨ratio, hratioZero, hratioOne, hratioTwo⟩ :=
    smul_of_minors_eq_zero minorOne minorTwo minorThree hbase
  refine ⟨ratio, funext fun slot => ?_⟩
  fin_cases slot
  · simpa using hratioZero
  · simpa using hratioOne
  · simpa using hratioTwo

/-- Two distinct labels force at least two labels.  The landed
`Gtz.atom_ne_zero_of_isPrimitiveDesign` asks for that count, and a distinct pair
is exactly what supplies it. -/
theorem two_le_size_of_ne {first second : Fin size} (hne : first ≠ second) : 2 ≤ size := by
  have hfirst := first.isLt
  have hsecond := second.isLt
  have hvals : first.val ≠ second.val := fun heq => hne (Fin.ext heq)
  omega

/-! ## Part 3 — the pair gap, and primitivity -/

/-- **THE PAIR GAP REACHES A LEVEL.**  Every distinct pair of labels carries a
principal two-by-two minor of at least `level`.  Stated as a reachability
predicate rather than an infimum, exactly like the landed `Gtz.MarginReaches`, so
it needs no non-emptiness side condition and holds at every size. -/
def PairGapReaches (form : Matrix (Fin size) (Fin size) ℝ) (level : ℝ) : Prop :=
  ∀ first second : Fin size, first ≠ second → level ≤ pairMinorAt form first second

/-- A reachable pair gap is inherited downward. -/
theorem PairGapReaches.mono {form : Matrix (Fin size) (Fin size) ℝ} {level lower : ℝ}
    (hreach : PairGapReaches form level) (hle : lower ≤ level) :
    PairGapReaches form lower :=
  fun first second hne => le_trans hle (hreach first second hne)

/-- **A POSITIVE PAIR GAP FORCES PRIMITIVITY.**  One direction of the headline,
and it needs no rank hypothesis: a parallel pair kills its own minor. -/
theorem isPrimitiveDesign_of_pairGapReaches_pos {design : WeightedDesign size rank}
    {level : ℝ} (hpos : 0 < level)
    (hreach : PairGapReaches (projectionOfDesign design) level) :
    IsPrimitiveDesign design := by
  intro keptLabel dropLabel ratio hne hparallel
  have hminor : pairMinorAt (projectionOfDesign design) keptLabel dropLabel = 0 := by
    rw [pairMinorAt_projectionOfDesign, hparallel, pairGramDet_smul_self]
    ring
  have hlevel := hreach keptLabel dropLabel hne
  rw [hminor] at hlevel
  linarith

/-- **PRIMITIVITY FORCES A POSITIVE PAIR GAP AT RANK THREE.**  The other
direction.  Lagrange supplies the ratio whenever a minor vanishes, so a vanishing
minor contradicts primitivity, and the finitely many pairs then have a positive
common lower bound. -/
theorem exists_pos_pairGapReaches_of_isPrimitiveDesign {design : WeightedDesign size 3}
    (hprimitive : IsPrimitiveDesign design) :
    ∃ level : ℝ, 0 < level ∧ PairGapReaches (projectionOfDesign design) level := by
  classical
  have hpairPos : ∀ leftLabel rightLabel : Fin size, leftLabel ≠ rightLabel →
      0 < pairMinorAt (projectionOfDesign design) leftLabel rightLabel := by
    intro leftLabel rightLabel hne
    rcases lt_or_eq_of_le (pairMinorAt_projectionOfDesign_nonneg design leftLabel rightLabel) with
      hlt | heq
    · exact hlt
    · exfalso
      have hsplit := pairMinorAt_projectionOfDesign design leftLabel rightLabel
      rw [← heq] at hsplit
      have hprod : design.weight leftLabel * design.weight rightLabel ≠ 0 :=
        (mul_pos (design.weight_pos leftLabel) (design.weight_pos rightLabel)).ne'
      have hgram : pairGramDet (design.atom leftLabel) (design.atom rightLabel) = 0 := by
        rcases mul_eq_zero.mp hsplit.symm with hcase | hcase
        · exact absurd hcase hprod
        · exact hcase
      obtain ⟨ratio, hratio⟩ :=
        exists_smul_of_pairGramDet_eq_zero
          (atom_ne_zero_of_isPrimitiveDesign (two_le_size_of_ne hne) design hprimitive leftLabel)
          hgram
      exact hprimitive leftLabel rightLabel ratio hne hratio
  rcases Nat.eq_zero_or_pos size with hzero | hpos
  · subst hzero
    exact ⟨1, one_pos, fun leftLabel _ _ => absurd leftLabel.isLt (by omega)⟩
  · haveI hnonemptyType : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hpos
    refine ⟨(Finset.univ : Finset (Fin size × Fin size)).inf' Finset.univ_nonempty
      fun labels => if labels.1 = labels.2 then 1
        else pairMinorAt (projectionOfDesign design) labels.1 labels.2, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro labels _
      by_cases hcase : labels.1 = labels.2
      · rw [if_pos hcase]
        exact one_pos
      · rw [if_neg hcase]
        exact hpairPos labels.1 labels.2 hcase
    · intro leftLabel rightLabel hne
      have hstep := Finset.inf'_le
        (fun labels : Fin size × Fin size => if labels.1 = labels.2 then 1
          else pairMinorAt (projectionOfDesign design) labels.1 labels.2)
        (Finset.mem_univ (leftLabel, rightLabel))
      rw [if_neg hne] at hstep
      exact hstep

/-- **THE HEADLINE.**  At rank three a design is primitive exactly when its
projection form carries a strictly positive pair gap.  This is the functional the
consumer needs and the landed clearance family does not supply, because that
family measures triple coplanarity and dies on every stratum with a line. -/
theorem pairGapReaches_pos_iff_isPrimitiveDesign (design : WeightedDesign size 3) :
    IsPrimitiveDesign design
      ↔ ∃ level : ℝ, 0 < level ∧ PairGapReaches (projectionOfDesign design) level :=
  ⟨exists_pos_pairGapReaches_of_isPrimitiveDesign,
    fun ⟨_, hpos, hreach⟩ => isPrimitiveDesign_of_pairGapReaches_pos hpos hreach⟩

/-! ## Part 4 — the two-point marginal -/

/-- The idempotence identity read on a pair of rows: the row inner product of a
symmetric idempotent reproduces its own entry. -/
theorem sum_row_mul_row_of_symm_idempotent (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    (first second : Fin size) :
    ∑ other, form first other * form second other = form first second := by
  have hentry := congrFun (congrFun hidempotent first) second
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl fun other _ => ?_
  have hflip : form other second = form second other := by
    have := congrFun (congrFun hsymmetric second) other
    simpa only [Matrix.transpose_apply] using this
  rw [hflip]

/-- The three-slot block of a form along an explicit pick. -/
def tripleBlock (form : Matrix (Fin size) (Fin size) ℝ) (first second third : Fin size) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  form.submatrix ![first, second, third] ![first, second, third]

/-- The three-slot block determinant, expanded on the entries of the form. -/
theorem det_tripleBlock (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form first second third).det
      = form first first * (form second second * form third third - form second third ^ 2)
        - form first second
          * (form first second * form third third - form second third * form first third)
        + form first third
          * (form first second * form second third - form second second * form first third) := by
  have hflip : ∀ leftLabel rightLabel : Fin size,
      form rightLabel leftLabel = form leftLabel rightLabel := by
    intro leftLabel rightLabel
    have := congrFun (congrFun hsymmetric leftLabel) rightLabel
    simpa only [Matrix.transpose_apply] using this
  simp only [tripleBlock, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [hflip second first, hflip third first, hflip third second]
  ring

/-- **THE TWO-POINT MARGINAL, AND IT IS NEW.**  For a symmetric idempotent whose
diagonal totals `traceValue`, the block determinants of the triples through a
fixed pair add to `(traceValue - 2)` times that pair's own minor:

    ∑ over the third slot of det P[{c, d, e}] = (traceValue - 2) * pairMinorAt P c d.

The proof is the three-by-three expansion against three row identities -- the row
energy law, the idempotence identity, and the trace law -- and then `ring`.  No
cross product, no Cauchy-Binet, no Plücker coordinate.  RANK enters exactly once,
through the trace, and it appears as the coefficient. -/
theorem sum_det_tripleBlock_through_pair (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (hidempotent : form * form = form)
    {traceValue : ℝ} (htrace : ∑ other, form other other = traceValue)
    (first second : Fin size) :
    ∑ third, (tripleBlock form first second third).det
      = (traceValue - 2) * pairMinorAt form first second := by
  have hrowFirst : ∑ other, form first other ^ 2 = form first first :=
    sum_sq_row_eq_diag_of_symm_idempotent form hsymmetric hidempotent first
  have hrowSecond : ∑ other, form second other ^ 2 = form second second :=
    sum_sq_row_eq_diag_of_symm_idempotent form hsymmetric hidempotent second
  have hcross : ∑ other, form first other * form second other = form first second :=
    sum_row_mul_row_of_symm_idempotent form hsymmetric hidempotent first second
  have hexpand : ∀ third : Fin size, (tripleBlock form first second third).det
      = form third third * (form first first * form second second - form first second ^ 2)
        - form first first * form second third ^ 2
        - form second second * form first third ^ 2
        + 2 * form first second * (form first third * form second third) := by
    intro third
    rw [det_tripleBlock form hsymmetric first second third]
    ring
  rw [Finset.sum_congr rfl fun third _ => hexpand third]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  rw [htrace, hrowFirst, hrowSecond]
  have hcrossSum : ∑ third, form first third * form second third = form first second := hcross
  rw [hcrossSum]
  simp only [pairMinorAt]
  ring

/-- **THE MARGINAL AT RANK THREE.**  The coefficient is one, so the pair minor of
a design's projection IS the total determinantal mass of the triples through that
pair.  The pair gap is therefore a lower bound on a mass the landed determinant
cell consumes directly. -/
theorem pairMinorAt_eq_sum_det_tripleBlock (design : WeightedDesign size 3)
    (first second : Fin size) :
    ∑ third, (tripleBlock (projectionOfDesign design) first second third).det
      = pairMinorAt (projectionOfDesign design) first second := by
  have htrace : ∑ other, projectionOfDesign design other other = (3 : ℝ) := by
    have := sum_projectionDiagonal_eq_rank design
    simpa using this
  rw [sum_det_tripleBlock_through_pair (projectionOfDesign design)
    (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) htrace first second]
  norm_num

/-- A repeated slot makes the block determinant vanish, so the marginal is
carried entirely by the third slots outside the pair. -/
theorem det_tripleBlock_self_left (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second : Fin size) :
    (tripleBlock form first second first).det = 0 := by
  have hflip : form second first = form first second := by
    have hentry := congrFun (congrFun hsymmetric first) second
    simpa only [Matrix.transpose_apply] using hentry
  rw [det_tripleBlock form hsymmetric first second first, hflip]
  ring

/-- The same with the repeat in the second slot. -/
theorem det_tripleBlock_self_right (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second : Fin size) :
    (tripleBlock form first second second).det = 0 := by
  rw [det_tripleBlock form hsymmetric first second second]
  ring

/-! ## Part 4b — the two calibrations against landed totals -/

/-- The trace law in the shape the marginal consumes. -/
theorem sum_projectionDiagonal_cast (design : WeightedDesign size rank) :
    ∑ other : Fin size, projectionOfDesign design other other = (rank : ℝ) := by
  have hrank := sum_projectionDiagonal_eq_rank design
  simpa using hrank

/-- **THE ONE-POINT CALIBRATION.**  Summing the two-point marginal over the second
slot returns the landed row law, so the triple blocks through one label total
`(rank - 2) * (rank - 1)` times that label's leverage.  At `(6, 3)` that is
`2 * P c c`, and the factor two is the ordered overcount of each triple through
`c` -- which is exactly the landed one-point marginal
`Gtz.sum_shadowDeterminant_mem_eq_diag`.  So the new identity reproduces a landed
total rather than merely being consistent with it. -/
theorem sum_sum_det_tripleBlock_through_label (design : WeightedDesign size rank)
    (label : Fin size) :
    ∑ second : Fin size, ∑ third : Fin size,
        (tripleBlock (projectionOfDesign design) label second third).det
      = ((rank : ℝ) - 2) * (((rank : ℝ) - 1) * projectionOfDesign design label label) := by
  have hinner : ∀ second : Fin size,
      ∑ third : Fin size, (tripleBlock (projectionOfDesign design) label second third).det
        = ((rank : ℝ) - 2) * pairMinorAt (projectionOfDesign design) label second := fun second =>
    sum_det_tripleBlock_through_pair (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design)
      (sum_projectionDiagonal_cast design) label second
  rw [Finset.sum_congr rfl fun second _ => hinner second, ← Finset.mul_sum,
    sum_pairMinor_projection design label]

/-- **THE TOTAL CALIBRATION.**  Summing again over the first slot gives
`(rank - 2) * (rank - 1) * rank`.  At `(6, 3)` that is `6`, and six is exactly the
number of ordered readings of one unordered triple -- so the total agrees with the
landed `Gtz.sum_shadowDeterminant_eq_one`, which puts the unordered total at one. -/
theorem sum_sum_sum_det_tripleBlock (design : WeightedDesign size rank) :
    ∑ first : Fin size, ∑ second : Fin size, ∑ third : Fin size,
        (tripleBlock (projectionOfDesign design) first second third).det
      = ((rank : ℝ) - 2) * ((rank : ℝ) - 1) * (rank : ℝ) := by
  rw [Finset.sum_congr rfl fun label _ => sum_sum_det_tripleBlock_through_label design label]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_projectionDiagonal_cast design]
  ring

/-- The total at `(6, 3)` is six, the ordered overcount of the unordered one. -/
theorem sum_sum_sum_det_tripleBlock_sixThree (design : WeightedDesign 6 3) :
    ∑ first : Fin (6 : ℕ), ∑ second : Fin (6 : ℕ), ∑ third : Fin (6 : ℕ),
        (tripleBlock (projectionOfDesign design) first second third).det
      = 6 := by
  rw [sum_sum_sum_det_tripleBlock design]
  norm_num

/-! ## Part 5 — the pigeonhole, off the pair -/

/-- The marginal is carried entirely off the pair: deleting the two repeated
slots changes nothing, because both of their blocks are singular. -/
theorem sum_det_tripleBlock_erase (design : WeightedDesign size 3)
    (first second : Fin size) :
    ∑ third ∈ (Finset.univ.erase first).erase second,
        (tripleBlock (projectionOfDesign design) first second third).det
      = pairMinorAt (projectionOfDesign design) first second := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have houter : ∑ third ∈ (Finset.univ.erase first).erase second,
      (tripleBlock (projectionOfDesign design) first second third).det
      = ∑ third ∈ Finset.univ.erase first,
        (tripleBlock (projectionOfDesign design) first second third).det :=
    Finset.sum_erase _
      (det_tripleBlock_self_right (projectionOfDesign design) hsymm first second)
  have hinner : ∑ third ∈ Finset.univ.erase first,
      (tripleBlock (projectionOfDesign design) first second third).det
      = ∑ third, (tripleBlock (projectionOfDesign design) first second third).det :=
    Finset.sum_erase _
      (det_tripleBlock_self_left (projectionOfDesign design) hsymm first second)
  rw [houter, hinner]
  exact pairMinorAt_eq_sum_det_tripleBlock design first second

/-- The off-pair slot set has `size - 2` members. -/
theorem card_erase_pair {first second : Fin size} (hne : first ≠ second) :
    ((Finset.univ.erase first).erase second).card = size - 2 := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ second⟩),
    Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
  omega

/-- **THE PIGEONHOLE, OFF THE PAIR.**  Some third slot outside the pair carries a
block determinant at least the pair's minor divided by `size - 2`.  Dividing by
`size - 2` rather than by `size` is what keeps the cell below from being vacuous:
the two repeated slots contribute nothing and must not be counted. -/
theorem exists_det_tripleBlock_ge (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second) (hthree : 3 ≤ size) :
    ∃ third : Fin size, third ≠ first ∧ third ≠ second ∧
      pairMinorAt (projectionOfDesign design) first second / ((size : ℝ) - 2)
        ≤ (tripleBlock (projectionOfDesign design) first second third).det := by
  classical
  set slots := (Finset.univ.erase first).erase second with hslots
  have hcard : slots.card = size - 2 := card_erase_pair hne
  have hnonempty : slots.Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have hcastCard : (slots.card : ℝ) = (size : ℝ) - 2 := by
    rw [hcard]
    have : (2 : ℕ) ≤ size := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hcardPos : (0 : ℝ) < (size : ℝ) - 2 := by
    rw [← hcastCard]
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hconst : ∑ _third ∈ slots,
      pairMinorAt (projectionOfDesign design) first second / ((size : ℝ) - 2)
      = pairMinorAt (projectionOfDesign design) first second := by
    rw [Finset.sum_const, nsmul_eq_mul, hcastCard, mul_div_cancel₀ _ hcardPos.ne']
  have hle : ∑ _third ∈ slots,
      pairMinorAt (projectionOfDesign design) first second / ((size : ℝ) - 2)
      ≤ ∑ third ∈ slots, (tripleBlock (projectionOfDesign design) first second third).det := by
    rw [hconst, sum_det_tripleBlock_erase design first second]
  obtain ⟨third, hmem, hbound⟩ := Finset.exists_le_of_sum_le hnonempty hle
  exact ⟨third, (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmem)).1,
    (Finset.mem_erase.mp hmem).1, hbound⟩

/-- Three pairwise distinct labels give an injective three-slot pick. -/
theorem injective_triplePick {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hthirdFirst : third ≠ first)
    (hthirdSecond : third ≠ second) :
    Function.Injective ![first, second, third] := by
  intro leftSlot rightSlot hslots
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **THE SELECTION CELL, READING ONE PAIR MINOR.**  If every weight is strictly
below one pair's minor divided by `size - 2`, then the objective's selection
exists.  The block supplied by the pigeonhole beats each of its own three
weights, so the landed determinant cell fires on it. -/
theorem exists_posDef_subsetSum_of_pairMinor_gt_weights (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second) (hthree : 3 ≤ size)
    (hweights : ∀ label : Fin size,
      design.weight label
        < pairMinorAt (projectionOfDesign design) first second / ((size : ℝ) - 2)) :
    ∃ selected : Finset (Fin size), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  classical
  obtain ⟨third, hthirdFirst, hthirdSecond, hbound⟩ :=
    exists_det_tripleBlock_ge design hne hthree
  refine exists_posDef_subsetSum_of_forall_weight_lt_det design ![first, second, third]
    (injective_triplePick hne hthirdFirst hthirdSecond) fun slot => ?_
  have hblock : ((projectionOfDesign design).submatrix ![first, second, third]
      ![first, second, third]).det
      = (tripleBlock (projectionOfDesign design) first second third).det := rfl
  rw [hblock]
  exact lt_of_lt_of_le (hweights _) hbound

/-! ## Part 6 — the ceiling, and the exact window the cell leaves -/

/-- Every diagonal entry of a design's projection lies in the unit interval. -/
theorem projectionDiagonal_mem_unitInterval (design : WeightedDesign size rank)
    (label : Fin size) :
    0 ≤ projectionOfDesign design label label
      ∧ projectionOfDesign design label label ≤ 1 :=
  ⟨projectionOfDesign_diagonal_nonneg design label, projectionDiagonal_le_one' design label⟩

/-- **THE PAIR MINOR NEVER EXCEEDS ONE.**  Both diagonal factors sit in the unit
interval and the squared off-diagonal is subtracted. -/
theorem pairMinorAt_projectionOfDesign_le_one (design : WeightedDesign size rank)
    (first second : Fin size) :
    pairMinorAt (projectionOfDesign design) first second ≤ 1 := by
  obtain ⟨hfirstNonneg, hfirstLe⟩ := projectionDiagonal_mem_unitInterval design first
  obtain ⟨hsecondNonneg, hsecondLe⟩ := projectionDiagonal_mem_unitInterval design second
  have hsq : 0 ≤ projectionOfDesign design first second ^ 2 := sq_nonneg _
  simp only [pairMinorAt]
  nlinarith [hfirstNonneg, hfirstLe, hsecondNonneg, hsecondLe, hsq]

/-- **THE PAIR GAP IS CAPPED BY THE ROW LAW.**  A reachable level survives the
landed row sum `∑ pairMinorAt P c d = (rank - 1) * P c c`, and the diagonal is at
most one, so no level above `(rank - 1) / (size - 1)` is reachable.  At `(6, 3)`
that is `2 / 5`. -/
theorem pairGapReaches_le_of_projection (design : WeightedDesign size rank) {level : ℝ}
    (hreach : PairGapReaches (projectionOfDesign design) level) (hlabel : Fin size)
    (hrank : 1 ≤ rank) :
    level * ((size : ℝ) - 1) ≤ (rank : ℝ) - 1 := by
  classical
  have hrow := sum_pairMinor_projection design hlabel
  have hsplit : ∑ other ∈ Finset.univ.erase hlabel,
      pairMinorAt (projectionOfDesign design) hlabel other
      = ∑ other : Fin size, pairMinorAt (projectionOfDesign design) hlabel other :=
    Finset.sum_erase _ (pairMinorAt_self (projectionOfDesign design) hlabel)
  have hlower : ∑ _other ∈ Finset.univ.erase hlabel, level
      ≤ ∑ other ∈ Finset.univ.erase hlabel,
          pairMinorAt (projectionOfDesign design) hlabel other :=
    Finset.sum_le_sum fun other hmem =>
      hreach hlabel other (Ne.symm (Finset.mem_erase.mp hmem).1)
  have hcard : ((Finset.univ.erase hlabel).card : ℝ) = (size : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ hlabel), Finset.card_univ, Fintype.card_fin]
    have hone : (1 : ℕ) ≤ size := Fin.pos_iff_nonempty.mpr ⟨hlabel⟩
    push_cast [Nat.cast_sub hone]
    ring
  rw [Finset.sum_const, nsmul_eq_mul, hcard, hsplit, hrow] at hlower
  have hdiag := (projectionDiagonal_mem_unitInterval design hlabel).2
  have hdiagNonneg := (projectionDiagonal_mem_unitInterval design hlabel).1
  have hrankCast : (1 : ℝ) ≤ (rank : ℝ) := by exact_mod_cast hrank
  nlinarith [hlower, hdiag, hdiagNonneg, hrankCast]

/-- **THE CAP AT `(6, 3)`.**  No pair gap above `2 / 5` is reachable. -/
theorem pairGapReaches_le_twoFifths (design : WeightedDesign 6 3) {level : ℝ}
    (hreach : PairGapReaches (projectionOfDesign design) level) :
    level ≤ 2 / 5 := by
  have hbound := pairGapReaches_le_of_projection design hreach 0 (by norm_num)
  norm_num at hbound
  linarith

/-- **THE CAP AND THE WINDOW ARE INCOMPATIBLE AT `(6, 3)`, ON THE GAP.**  A
uniform pair gap can never reach the level the cell needs, because the cell wants
a pair minor above `2 / 3` and no reachable gap passes `2 / 5`.  So the cell can
only ever fire at a pair whose minor beats the gap -- it is never a consequence of
the gap alone.  This is the exact sense in which the primitivity channel does not
carry the objective by itself. -/
theorem not_pairGapReaches_cell_threshold (design : WeightedDesign 6 3) {level : ℝ}
    (hreach : PairGapReaches (projectionOfDesign design) level) :
    ¬ (2 / 3 < level) := by
  intro hbig
  have hcap := pairGapReaches_le_twoFifths design hreach
  linarith

/-- **THE WINDOW, EXACTLY.**  At `(6, 3)` the weights sum to one over six labels,
so some weight is at least `1 / 6`, and the cell of Part 5 needs every weight
strictly below `pairMinorAt / 4`.  So the cell can only ever fire at a pair whose
minor exceeds `2 / 3`.  Together with `Gtz.pairMinorAt_projectionOfDesign_le_one`
this pins the cell's whole window to the interval `(2 / 3, 1]` on a single pair
minor -- and nothing in the campaign forces a pair to reach it. -/
theorem pairMinor_gt_twoThirds_of_cell_fires (design : WeightedDesign 6 3)
    {first second : Fin (6 : ℕ)}
    (hweights : ∀ label : Fin 6,
      design.weight label
        < pairMinorAt (projectionOfDesign design) first second / ((6 : ℝ) - 2)) :
    2 / 3 < pairMinorAt (projectionOfDesign design) first second := by
  classical
  by_contra hcontra
  have hsmall : pairMinorAt (projectionOfDesign design) first second ≤ 2 / 3 := not_lt.mp hcontra
  have hsum : ∑ label : Fin 6, design.weight label = 1 := design.weight_sum_one
  have hbound : ∀ label : Fin 6,
      design.weight label < pairMinorAt (projectionOfDesign design) first second / 4 := by
    intro label
    have := hweights label
    norm_num at this ⊢
    linarith
  have hstrict : ∑ label : Fin 6, design.weight label
      < ∑ _label : Fin 6, pairMinorAt (projectionOfDesign design) first second / 4 := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun label _ => hbound label
    exact Finset.univ_nonempty
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hstrict
  norm_num at hstrict
  linarith

/-- **THE UNIFORM WEIGHT IS OUTSIDE THE WINDOW.**  At the uniform weight every
label carries `1 / 6`, so the cell needs a pair minor above `2 / 3` there too.
Recorded separately because the uniform weight is the point at which three
independent certificate families have been measured. -/
theorem pairMinor_gt_twoThirds_of_cell_at_uniform (design : WeightedDesign 6 3)
    (huniform : ∀ label : Fin 6, design.weight label = 1 / 6)
    {first second : Fin (6 : ℕ)}
    (hcell : ∀ label : Fin 6, design.weight label
        < pairMinorAt (projectionOfDesign design) first second / ((6 : ℝ) - 2)) :
    2 / 3 < pairMinorAt (projectionOfDesign design) first second := by
  have hslot := hcell 0
  rw [huniform 0] at hslot
  norm_num at hslot
  linarith

end Gtz
