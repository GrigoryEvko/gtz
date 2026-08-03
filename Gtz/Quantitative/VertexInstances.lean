/-
# The exact objects of vertex exclusion

`Gtz/Quantitative/VertexExclusion.lean` isolates a residue: an admissible
phase-free point outside `Gtz.PhaseFreeData.IsExceptional` carries the covering
witness, and a design outside it dominates.  A conditional theorem is worth what
its hypotheses are worth, so this file supplies the objects.

**The uniform point, at every size.**  Fix the weight, the excess and every
off-diagonal squared overlap to be constant.  Admissibility then FORCES all
three values: `weight = 1/size`, `excess = 2`, and

  `overlap = 3 (size − 3) / (size − 1)`

(`Gtz.forced_of_uniform`), which at `size = 6` is `9/5` — the maximal real
equiangular design's squared overlap, so the uniform slice at the rank-three top
carries exactly `Gtz.icosaDesign`'s moduli.  `parsevalPair` then forces the
Bargmann triangle as well (`Gtz.forced_bargmann_of_uniform`), to
`(size − 6) · overlap / (size − 2)`.  Nothing is left free, so
`Gtz.equiangularPoint` is THE uniform admissible point at each size, and its
determinant leg has the closed form

  `determinantLeg · (size − 1)(size − 2) = −4 (size − 4)(size + 1)`.

That is zero at `size = 4` — the regular tetrahedron, the campaign's
zero-margin boundary object — and strictly negative at every larger size.  So

  **`Gtz.not_phaseFreeCovering_of_five_le`: the phase-free relaxation is FALSE
  at EVERY size from five up**,

from one witness, subsuming the shipped `Gtz.not_phaseFreeCovering_six` and
`Gtz.not_phaseFreeCovering_seven`, which used two ad-hoc points at two sizes.
At `size = 6` the sharpest reading: `Gtz.equiangularPoint 6` and
`Gtz.phaseFreeOfDesign Gtz.icosaDesign` have IDENTICAL weight, excess and
pairing and differ ONLY in the triangle, yet the first fails every triple while
the second dominates.  The moduli decide nothing at the rank-three top; the
Bargmann triangle carries the entire verdict.

The family also outruns realizability.  A uniform admissible point exists at
every size, but by the shipped `Gtz.not_equiangular_uniformShare_sevenThree` —
Gerzon's bound, no seven equiangular lines in `R^3` — no real design carries
these moduli beyond `size = 6`.  The relaxation cannot see that.

**The saturated engine.**  The residue's second clause is broken by any light
edge whose star is banded, and `Gtz.PhaseFreeData.HasSaturatedTriangleCap` — the
torsion equality `triangle^2 = pairing · pairing · pairing`, automatic at every
design image by `Gtz.phaseFreeOfDesign_triangle_sq` — is exactly what licenses
reading that band off the MODULI.  Off the saturated locus the moduli reading is
not merely weaker but unsound (`Gtz.not_forall_exists_star_determinantLeg_nonneg_of_moduliBand`).
`Gtz.not_isExceptional_of_saturatedLightEdge` is that engine, at general size,
and two instances run it:

* `Gtz.not_isExceptional_phaseFreeOfDesign_icosaDesign`.  Every icosahedral edge
  is light on the nose and every gap is `−14/5` against box radius `4·(9/5)^3`,
  so the residue misses the maximal real equiangular design.  Note which clause
  does the work: clause ONE holds there, by the shipped
  `Gtz.icosaDesign_no_isSignBlindGoodTriple`, so only the edge mechanism can
  exclude it.

* `Gtz.not_isExceptional_of_trineSixModuli`.  `Gtz.trineSixData` fails all twenty
  triples over `C`, yet EVERY saturated point over its moduli dominates.  This is
  the sharpest form of "the torsion consumes the field": the phase defect is the
  only thing keeping the trine alive, and `Gtz.not_hasSaturatedTriangleCap_trineSixData`
  confirms the trine itself is outside the hypothesis rather than a witness for
  it.  MEASURED, not proved here: over trine's moduli the saturated locus
  contains exactly TWO sign words, negatives of one another, and NEITHER is a
  two-graph coboundary — so no real design and no cocycle-consistent point
  carries those moduli.  The same scan at icosahedral moduli returns twelve, all
  twelve coboundaries.
-/
import Mathlib
import Gtz.Quantitative.VertexExclusion
import Gtz.Quantitative.GoodTripleGraph

namespace Gtz

open Finset

variable {size : ℕ}

/-! ## The uniform triangle table

Keying the triangle on how many DISTINCT atoms the triple carries makes its `S3`
symmetry a property of the underlying `Finset`, so both symmetry axioms cost one
rewrite instead of a case analysis. -/

/-- The triangle of a uniform point: `27` on the diagonal, `3 · overlap` when
exactly two atoms coincide (forced by `IsPhaseFreeAdmissible.triangleCollapse`),
and the free parameter `bargmann` at a triple of distinct atoms. -/
noncomputable def uniformTriangleTable (overlap bargmann : ℝ) {size : ℕ}
    (first second third : Fin size) : ℝ :=
  if ({first, second, third} : Finset (Fin size)).card = 1 then 27
  else if ({first, second, third} : Finset (Fin size)).card = 2 then 3 * overlap
  else bargmann

theorem uniformTriangleTable_swap (overlap bargmann : ℝ) (first second third : Fin size) :
    uniformTriangleTable overlap bargmann first second third
      = uniformTriangleTable overlap bargmann second first third := by
  rw [uniformTriangleTable, uniformTriangleTable, Finset.insert_comm]

theorem uniformTriangleTable_rotate (overlap bargmann : ℝ) (first second third : Fin size) :
    uniformTriangleTable overlap bargmann first second third
      = uniformTriangleTable overlap bargmann second third first := by
  have hset : ({first, second, third} : Finset (Fin size)) = {second, third, first} := by
    ext atomIndex; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [uniformTriangleTable, uniformTriangleTable, hset]

theorem uniformTriangleTable_repeat_left (overlap bargmann : ℝ) (first second : Fin size) :
    uniformTriangleTable overlap bargmann first first second
      = if first = second then 27 else 3 * overlap := by
  rw [uniformTriangleTable, Finset.insert_idem]
  by_cases hpair : first = second
  · subst hpair; simp
  · rw [Finset.card_insert_of_notMem (by simpa using hpair), Finset.card_singleton]
    simp [hpair]

theorem uniformTriangleTable_of_distinct (overlap bargmann : ℝ) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    uniformTriangleTable overlap bargmann first second third = bargmann := by
  have hcard : ({first, second, third} : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  rw [uniformTriangleTable, hcard]
  norm_num

/-- The star of an edge, read off the table: the two atoms of the edge itself
give the collapsed value, everything else gives the free parameter. -/
theorem uniformTriangleTable_star (overlap bargmann : ℝ) {first second : Fin size}
    (hdistinct : first ≠ second) (other : Fin size) :
    uniformTriangleTable overlap bargmann first second other
      = if other = first ∨ other = second then 3 * overlap else bargmann := by
  by_cases hotherFirst : other = first
  · subst hotherFirst
    rw [uniformTriangleTable_rotate, uniformTriangleTable_rotate,
      uniformTriangleTable_repeat_left, if_neg hdistinct, if_pos (Or.inl rfl)]
  · by_cases hotherSecond : other = second
    · subst hotherSecond
      rw [uniformTriangleTable_rotate, uniformTriangleTable_repeat_left,
        if_neg (Ne.symm hdistinct), if_pos (Or.inr rfl)]
    · rw [uniformTriangleTable_of_distinct overlap bargmann hdistinct
        (fun hcollide => hotherFirst hcollide.symm) (fun hcollide => hotherSecond hcollide.symm),
        if_neg (fun hor => hor.elim hotherFirst hotherSecond)]

/-- **The box, at the table.**  Every degenerate triple saturates it — the
collapsed value `3 · overlap` squares to exactly `9 · overlap^2` — so the only
content is the free parameter's own bound.  Positivity of `overlap` is NOT
needed. -/
theorem uniformTriangleTable_cap (overlap bargmann : ℝ)
    (hbargmannCap : bargmann ^ 2 ≤ overlap ^ 3) (first second third : Fin size) :
    uniformTriangleTable overlap bargmann first second third ^ 2
      ≤ (if first = second then (9 : ℝ) else overlap)
        * (if second = third then (9 : ℝ) else overlap)
        * (if first = third then (9 : ℝ) else overlap) := by
  rcases eq_or_ne first second with hfirstSecond | hfirstSecond
  · subst hfirstSecond
    rw [uniformTriangleTable_repeat_left]
    rcases eq_or_ne first third with hfirstThird | hfirstThird
    · subst hfirstThird; norm_num
    · simp only [if_neg hfirstThird, ite_true]
      nlinarith
  · rcases eq_or_ne second third with hsecondThird | hsecondThird
    · subst hsecondThird
      rw [uniformTriangleTable_rotate, uniformTriangleTable_repeat_left]
      simp only [if_neg hfirstSecond, if_neg (Ne.symm hfirstSecond), ite_true]
      nlinarith
    · rcases eq_or_ne first third with hfirstThird | hfirstThird
      · subst hfirstThird
        rw [uniformTriangleTable_swap, uniformTriangleTable_rotate,
          uniformTriangleTable_repeat_left]
        simp only [if_neg hfirstSecond, if_neg (Ne.symm hfirstSecond), ite_true]
        nlinarith
      · rw [uniformTriangleTable_of_distinct overlap bargmann hfirstSecond hfirstThird
          hsecondThird]
        simp only [if_neg hfirstSecond, if_neg hsecondThird, if_neg hfirstThird]
        nlinarith [hbargmannCap]

/-! ## Two constant-plus-exception sums

Every Parseval relation at a uniform point is one of these two shapes. -/

theorem sum_single_exception (constantValue exceptionValue : ℝ) (marked : Fin size) :
    ∑ other : Fin size, (if marked = other then exceptionValue else constantValue)
      = (size : ℝ) * constantValue + (exceptionValue - constantValue) := by
  classical
  have hrewrite : ∀ other : Fin size,
      (if marked = other then exceptionValue else constantValue)
        = constantValue + (if marked = other then exceptionValue - constantValue else 0) := by
    intro other; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun other _ => hrewrite other), Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_ite_eq]
  simp

theorem sum_double_exception (constantValue exceptionValue : ℝ)
    (markedFirst markedSecond : Fin size) (hdistinct : markedFirst ≠ markedSecond) :
    ∑ other : Fin size,
        (if other = markedFirst ∨ other = markedSecond then exceptionValue else constantValue)
      = (size : ℝ) * constantValue + 2 * (exceptionValue - constantValue) := by
  classical
  have hrewrite : ∀ other : Fin size,
      (if other = markedFirst ∨ other = markedSecond then exceptionValue else constantValue)
        = constantValue + (if other = markedFirst then exceptionValue - constantValue else 0)
            + (if other = markedSecond then exceptionValue - constantValue else 0) := by
    intro other
    by_cases hfirst : other = markedFirst
    · subst hfirst
      rw [if_pos (Or.inl rfl), if_pos rfl, if_neg hdistinct]
      ring
    · by_cases hsecond : other = markedSecond
      · subst hsecond
        rw [if_pos (Or.inr rfl), if_neg hfirst, if_pos rfl]
        ring
      · rw [if_neg (fun hor => hor.elim hfirst hsecond), if_neg hfirst, if_neg hsecond]
        ring
  rw [Finset.sum_congr rfl (fun other _ => hrewrite other), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
  ring

/-! ## The uniform point -/

/-- **The uniform phase-free point.**  Constant weight, constant excess `2`,
constant off-diagonal squared overlap, constant Bargmann triangle.  Written with
`overlap` and `bargmann` free so that `Gtz.uniformPoint_isPhaseFreeAdmissible`
records exactly which relations pin them. -/
noncomputable def uniformPoint (size : ℕ) (overlap bargmann : ℝ) : PhaseFreeData size where
  weight := fun _ => 1 / (size : ℝ)
  excess := fun _ => 2
  pairing := fun first second => if first = second then 9 else overlap
  triangle := uniformTriangleTable overlap bargmann

@[simp] theorem uniformPoint_weight (overlap bargmann : ℝ) (atomIndex : Fin size) :
    (uniformPoint size overlap bargmann).weight atomIndex = 1 / (size : ℝ) := rfl

@[simp] theorem uniformPoint_excess (overlap bargmann : ℝ) (atomIndex : Fin size) :
    (uniformPoint size overlap bargmann).excess atomIndex = 2 := rfl

@[simp] theorem uniformPoint_pairing (overlap bargmann : ℝ) (first second : Fin size) :
    (uniformPoint size overlap bargmann).pairing first second
      = if first = second then 9 else overlap := rfl

@[simp] theorem uniformPoint_triangle (overlap bargmann : ℝ) (first second third : Fin size) :
    (uniformPoint size overlap bargmann).triangle first second third
      = uniformTriangleTable overlap bargmann first second third := rfl

/-- **The uniform point is admissible** exactly when the two Parseval relations
hold — and those are two LINEAR equations, one pinning `overlap` and one pinning
`bargmann`.  The remaining hypotheses are the box (`triangleCap`) and the two
elementary bounds on `overlap`. -/
theorem uniformPoint_isPhaseFreeAdmissible (overlap bargmann : ℝ) (hsize : 3 ≤ size)
    (hoverlapNonneg : 0 ≤ overlap) (hoverlapCap : overlap ≤ 9)
    (hbargmannCap : bargmann ^ 2 ≤ overlap ^ 3)
    (hdiagonal : 9 + ((size : ℝ) - 1) * overlap = 3 * (size : ℝ))
    (hpair : 6 * overlap + ((size : ℝ) - 2) * bargmann = (size : ℝ) * overlap) :
    IsPhaseFreeAdmissible (uniformPoint size overlap bargmann) := by
  classical
  have hsizeReal : (3 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have hsizePos : (0 : ℝ) < (size : ℝ) := by linarith
  have hsizeNe : (size : ℝ) ≠ 0 := ne_of_gt hsizePos
  refine
    { weightPos := fun _ => by simp only [uniformPoint_weight]; positivity
      weightSumOne := ?_
      excessPos := fun _ => by norm_num
      traceEqRank := ?_
      pairingSymm := fun first second => by
        simp only [uniformPoint_pairing, eq_comm (a := first) (b := second)]
      pairingDiag := fun atomIndex => by
        show (if atomIndex = atomIndex then (9 : ℝ) else overlap) = (2 + 1) ^ 2
        norm_num
      pairingNonneg := fun first second => by
        simp only [uniformPoint_pairing]
        split_ifs
        · norm_num
        · exact hoverlapNonneg
      pairingCap := fun first second => by
        simp only [uniformPoint_pairing, uniformPoint_excess]
        split_ifs
        · norm_num
        · linarith
      triangleSwap := fun first second third =>
        uniformTriangleTable_swap overlap bargmann first second third
      triangleRotate := fun first second third =>
        uniformTriangleTable_rotate overlap bargmann first second third
      triangleCollapse := ?_
      parsevalDiag := ?_
      parsevalPair := ?_
      triangleCap := fun first second third => by
        simpa only [uniformPoint_triangle, uniformPoint_pairing] using
          uniformTriangleTable_cap overlap bargmann hbargmannCap first second third
      leverageCap := fun _ => by
        simp only [uniformPoint_weight, uniformPoint_excess]
        rw [div_mul_eq_mul_div, div_le_one hsizePos]
        linarith }
  · simp only [uniformPoint_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  · simp only [uniformPoint_weight, uniformPoint_excess, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro first second
    simp only [uniformPoint_triangle, uniformPoint_pairing, uniformPoint_excess,
      uniformTriangleTable_repeat_left]
    by_cases hpairEq : first = second
    · rw [if_pos hpairEq, if_pos hpairEq]; norm_num
    · rw [if_neg hpairEq, if_neg hpairEq]; ring
  · intro atomIndex
    simp only [uniformPoint_weight, uniformPoint_pairing, uniformPoint_excess, ← Finset.mul_sum]
    rw [sum_single_exception overlap 9 atomIndex]
    field_simp
    linarith
  · intro first second
    simp only [uniformPoint_weight, uniformPoint_triangle, uniformPoint_pairing,
      ← Finset.mul_sum]
    by_cases hpairEq : first = second
    · subst hpairEq
      rw [Finset.sum_congr rfl (fun other _ =>
        uniformTriangleTable_repeat_left overlap bargmann first other),
        sum_single_exception (3 * overlap) 27 first, if_pos rfl]
      field_simp
      linarith
    · rw [Finset.sum_congr rfl (fun other _ =>
        uniformTriangleTable_star overlap bargmann hpairEq other),
        sum_double_exception bargmann (3 * overlap) first second hpairEq, if_neg hpairEq]
      field_simp
      linarith

/-- The determinant leg at a triple of pairwise distinct atoms.  Both free
parameters enter, and they enter linearly. -/
theorem uniformPoint_determinantLeg_of_distinct (overlap bargmann : ℝ)
    {first second third : Fin size} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third) :
    (uniformPoint size overlap bargmann).determinantLeg first second third
      = 8 - 6 * overlap + 2 * bargmann := by
  simp only [PhaseFreeData.determinantLeg, uniformPoint_excess, uniformPoint_pairing,
    uniformPoint_triangle, if_neg hfirstSecond, if_neg hfirstThird, if_neg hsecondThird,
    uniformTriangleTable_of_distinct overlap bargmann hfirstSecond hfirstThird hsecondThird]
  ring

/-! ## Uniformity forces every coordinate

The converse of the construction, and the reason the family is canonical: a
uniform admissible point has NO free parameters. -/

/-- **UNIFORMITY FORCES THE COORDINATES.**  An admissible point whose weight,
excess and off-diagonal pairing are each constant has `weight = 1/size`,
`excess = 2` — independent of the size — and `overlap` pinned by one linear
equation.  At `size = 6` that equation reads `5 · overlap = 9`, so the uniform
slice at the rank-three top carries exactly `Gtz.icosaDesign`'s squared overlap
`9/5`; see `Gtz.forced_overlap_six`. -/
theorem forced_of_uniform {point : PhaseFreeData size} (hadmissible : IsPhaseFreeAdmissible point)
    (weightValue excessValue overlapValue : ℝ) (someAtom : Fin size)
    (hweight : ∀ atomIndex, point.weight atomIndex = weightValue)
    (hexcess : ∀ atomIndex, point.excess atomIndex = excessValue)
    (hpairing : ∀ first second, first ≠ second → point.pairing first second = overlapValue) :
    (size : ℝ) * weightValue = 1 ∧ excessValue = 2
      ∧ 9 + ((size : ℝ) - 1) * overlapValue = 3 * (size : ℝ) := by
  classical
  have hsizePos : (0 : ℝ) < (size : ℝ) := by
    have : 0 < size := Fin.pos_iff_nonempty.mpr ⟨someAtom⟩
    exact_mod_cast this
  have hweightTotal : (size : ℝ) * weightValue = 1 := by
    have hsum := hadmissible.weightSumOne
    rw [Finset.sum_congr rfl (fun atomIndex _ => hweight atomIndex), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact hsum
  have hexcessTwo : excessValue = 2 := by
    have hsum := hadmissible.traceEqRank
    rw [Finset.sum_congr rfl (fun atomIndex _ => by
        rw [hweight atomIndex, hexcess atomIndex]), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith [hsum, hweightTotal]
  refine ⟨hweightTotal, hexcessTwo, ?_⟩
  have hdiag := hadmissible.parsevalDiag someAtom
  have hrewrite : ∀ other : Fin size, point.weight other * point.pairing someAtom other
      = weightValue * (if someAtom = other then (excessValue + 1) ^ 2 else overlapValue) := by
    intro other
    rw [hweight other]
    by_cases hcollide : someAtom = other
    · subst hcollide
      rw [if_pos rfl, hadmissible.pairingDiag someAtom, hexcess someAtom]
    · rw [if_neg hcollide, hpairing someAtom other hcollide]
  rw [Finset.sum_congr rfl (fun other _ => hrewrite other), ← Finset.mul_sum,
    sum_single_exception overlapValue ((excessValue + 1) ^ 2) someAtom,
    hexcess someAtom, hexcessTwo] at hdiag
  nlinarith [hdiag, hweightTotal, hsizePos]

/-- **UNIFORMITY FORCES THE TRIANGLE TOO.**  The companion of
`Gtz.forced_of_uniform`, and what makes the family canonical rather than merely
convenient: once the moduli are uniform, `parsevalPair` on a single edge pins the
Bargmann triangle by a linear equation.  Nothing about the point is free.

Only the triangles on ONE edge's star are assumed uniform, so the hypothesis is
weaker than full uniformity of the triangle. -/
theorem forced_bargmann_of_uniform {point : PhaseFreeData size}
    (hadmissible : IsPhaseFreeAdmissible point)
    (weightValue excessValue overlapValue bargmannValue : ℝ)
    {someAtom otherAtom : Fin size} (hdistinct : someAtom ≠ otherAtom)
    (hweight : ∀ atomIndex, point.weight atomIndex = weightValue)
    (hexcess : ∀ atomIndex, point.excess atomIndex = excessValue)
    (hpairing : ∀ first second, first ≠ second → point.pairing first second = overlapValue)
    (htriangle : ∀ third, third ≠ someAtom → third ≠ otherAtom →
      point.triangle someAtom otherAtom third = bargmannValue) :
    6 * overlapValue + ((size : ℝ) - 2) * bargmannValue = (size : ℝ) * overlapValue := by
  classical
  obtain ⟨hweightTotal, hexcessTwo, -⟩ :=
    forced_of_uniform hadmissible weightValue excessValue overlapValue someAtom hweight hexcess
      hpairing
  have hpairSum := hadmissible.parsevalPair someAtom otherAtom
  have hrewrite : ∀ third : Fin size, point.weight third * point.triangle someAtom otherAtom third
      = weightValue * (if third = someAtom ∨ third = otherAtom
          then (excessValue + 1) * overlapValue else bargmannValue) := by
    intro third
    rw [hweight third]
    by_cases hthirdSome : third = someAtom
    · subst hthirdSome
      rw [if_pos (Or.inl rfl), PhaseFreeData.triangle_repeat_first point hadmissible,
        hexcess third, hpairing third otherAtom hdistinct]
    · by_cases hthirdOther : third = otherAtom
      · subst hthirdOther
        rw [if_pos (Or.inr rfl), PhaseFreeData.triangle_repeat_second point hadmissible,
          hexcess third, hpairing someAtom third hdistinct]
      · rw [if_neg (fun hor => hor.elim hthirdSome hthirdOther),
          htriangle third hthirdSome hthirdOther]
  rw [Finset.sum_congr rfl (fun third _ => hrewrite third), ← Finset.mul_sum,
    sum_double_exception bargmannValue ((excessValue + 1) * overlapValue) someAtom otherAtom
      hdistinct, hpairing someAtom otherAtom hdistinct, hexcessTwo] at hpairSum
  -- scale the edge relation by the atom count and cancel `size · weight = 1`
  linear_combination (size : ℝ) * hpairSum
    - (((size : ℝ) - 2) * bargmannValue + 6 * overlapValue) * hweightTotal

/-! ## The equiangular point: its coordinates are forced at every size -/

/-- The forced off-diagonal squared overlap, `3 (size − 3) / (size − 1)`.  It is
`1` at `size = 4` (the regular tetrahedron), `9/5` at `size = 6` (the maximal
real equiangular design), and increases to `3` in the limit. -/
noncomputable def equiangularOverlap (size : ℕ) : ℝ :=
  3 * ((size : ℝ) - 3) / ((size : ℝ) - 1)

/-- The forced Bargmann triangle, `(size − 6) · overlap / (size − 2)`.  It
vanishes exactly at `size = 6`: at the rank-three top the uniform point is
totally phase-defective. -/
noncomputable def equiangularBargmann (size : ℕ) : ℝ :=
  ((size : ℝ) - 6) * equiangularOverlap size / ((size : ℝ) - 2)

/-- **The equiangular point.**  The unique uniform admissible phase-free point at
its size, by `Gtz.forced_of_uniform` together with the pair relation. -/
noncomputable def equiangularPoint (size : ℕ) : PhaseFreeData size :=
  uniformPoint size (equiangularOverlap size) (equiangularBargmann size)

theorem equiangularOverlap_nonneg (hsize : 4 ≤ size) : 0 ≤ equiangularOverlap size := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  rw [equiangularOverlap]
  apply div_nonneg <;> linarith

theorem equiangularOverlap_le_nine (hsize : 4 ≤ size) : equiangularOverlap size ≤ 9 := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  rw [equiangularOverlap, div_le_iff₀ (by linarith)]
  linarith

theorem equiangularOverlap_diagonal (hsize : 4 ≤ size) :
    9 + ((size : ℝ) - 1) * equiangularOverlap size = 3 * (size : ℝ) := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have hone : ((size : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith)
  rw [equiangularOverlap]
  field_simp
  ring

theorem equiangularBargmann_pair (hsize : 4 ≤ size) :
    6 * equiangularOverlap size + ((size : ℝ) - 2) * equiangularBargmann size
      = (size : ℝ) * equiangularOverlap size := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have htwo : ((size : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  rw [equiangularBargmann]
  field_simp
  ring

/-- **The box is respected exactly for `4 ≤ size`.**  Clearing denominators, the
cap deficit is `2 · size^2 · (size − 4)`, so the equiangular point is admissible
from the tetrahedron up and the tetrahedron is the equality case. -/
theorem equiangularBargmann_cap (hsize : 4 ≤ size) :
    equiangularBargmann size ^ 2 ≤ equiangularOverlap size ^ 3 := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have honePos : (0 : ℝ) < (size : ℝ) - 1 := by linarith
  have htwoPos : (0 : ℝ) < (size : ℝ) - 2 := by linarith
  have htwoNe : ((size : ℝ) - 2) ≠ 0 := ne_of_gt htwoPos
  have hsquarePos : (0 : ℝ) < ((size : ℝ) - 2) ^ 2 := by positivity
  have hcleared : ((size : ℝ) - 6) ^ 2 ≤ ((size : ℝ) - 2) ^ 2 * equiangularOverlap size := by
    rw [equiangularOverlap, mul_div_assoc', le_div_iff₀ honePos]
    nlinarith [hsizeReal, sq_nonneg ((size : ℝ) - 4)]
  have hscaled : equiangularBargmann size * ((size : ℝ) - 2)
      = ((size : ℝ) - 6) * equiangularOverlap size := by
    rw [equiangularBargmann]; field_simp
  refine le_of_mul_le_mul_right ?_ hsquarePos
  calc equiangularBargmann size ^ 2 * ((size : ℝ) - 2) ^ 2
      = ((size : ℝ) - 6) ^ 2 * equiangularOverlap size ^ 2 := by
        rw [← mul_pow, hscaled]; ring
    _ ≤ (((size : ℝ) - 2) ^ 2 * equiangularOverlap size) * equiangularOverlap size ^ 2 :=
        mul_le_mul_of_nonneg_right hcleared (sq_nonneg _)
    _ = equiangularOverlap size ^ 3 * ((size : ℝ) - 2) ^ 2 := by ring

theorem equiangularPoint_isPhaseFreeAdmissible (hsize : 4 ≤ size) :
    IsPhaseFreeAdmissible (equiangularPoint size) :=
  uniformPoint_isPhaseFreeAdmissible _ _ (by omega) (equiangularOverlap_nonneg hsize)
    (equiangularOverlap_le_nine hsize) (equiangularBargmann_cap hsize)
    (equiangularOverlap_diagonal hsize) (equiangularBargmann_pair hsize)

/-- **THE CLOSED FORM.**  Cleared of denominators, the determinant leg at every
triple of distinct atoms is `−4 (size − 4)(size + 1)`.  One polynomial decides
the whole family. -/
theorem equiangularPoint_determinantLeg_mul (hsize : 4 ≤ size) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (equiangularPoint size).determinantLeg first second third
        * (((size : ℝ) - 1) * ((size : ℝ) - 2))
      = -4 * ((size : ℝ) - 4) * ((size : ℝ) + 1) := by
  have hsizeReal : (4 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have hone : ((size : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith)
  have htwo : ((size : ℝ) - 2) ≠ 0 := ne_of_gt (by linarith)
  rw [equiangularPoint, uniformPoint_determinantLeg_of_distinct _ _ hfirstSecond hfirstThird
    hsecondThird, equiangularBargmann, equiangularOverlap]
  field_simp
  ring

theorem equiangularOverlap_four : equiangularOverlap 4 = 1 := by
  rw [equiangularOverlap]; norm_num

theorem equiangularBargmann_four : equiangularBargmann 4 = -1 := by
  rw [equiangularBargmann, equiangularOverlap]; norm_num

/-- **THE TETRAHEDRON IS THE ZERO-MARGIN CASE.**  At `size = 4` every triple of
the equiangular point has determinant leg exactly `0`.  Its coordinates are
`overlap = 1` and `bargmann = −1` (`Gtz.equiangularOverlap_four`,
`Gtz.equiangularBargmann_four`) — squared overlap `1` at leverage `3` is squared
cosine `1/9`, which is the regular tetrahedron by the shipped
`Gtz.tetraAtom_isEquiangular`, and `(−1)^3 = −1` is its Bargmann triangle.  So the
equality case of the whole family is realized by a genuine real design, which is
the campaign's boundary condition B2: zero margin, attained. -/
theorem equiangularPoint_determinantLeg_eq_zero_four {first second third : Fin 4}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (equiangularPoint 4).determinantLeg first second third = 0 := by
  have hmul := equiangularPoint_determinantLeg_mul (size := 4) (by omega) hfirstSecond
    hfirstThird hsecondThird
  norm_num at hmul
  linarith

/-- **EVERY TRIPLE FAILS, AT EVERY SIZE FROM FIVE UP.** -/
theorem equiangularPoint_determinantLeg_neg (hsize : 5 ≤ size) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (equiangularPoint size).determinantLeg first second third < 0 := by
  have hsizeReal : (5 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  have hmul := equiangularPoint_determinantLeg_mul (by omega) hfirstSecond hfirstThird
    hsecondThird
  have hfactorPos : (0 : ℝ) < ((size : ℝ) - 1) * ((size : ℝ) - 2) := by nlinarith
  have hvalueNeg : -4 * ((size : ℝ) - 4) * ((size : ℝ) + 1) < 0 := by nlinarith
  by_contra hcontra
  push Not at hcontra
  have hproduct := mul_nonneg hcontra hfactorPos.le
  rw [hmul] at hproduct
  linarith

/-- **THE PHASE-FREE RELAXATION IS FALSE AT EVERY SIZE FROM FIVE UP.**  One
witness, one closed form, every size — subsuming the shipped
`Gtz.not_phaseFreeCovering_six` and `Gtz.not_phaseFreeCovering_seven`, each of
which used a separate ad-hoc point.  Via
`Gtz.discriminantCovering_of_phaseFreeCovering` this is the statement that no
phase-free certificate can prove the discriminant covering at any of those
sizes. -/
theorem not_phaseFreeCovering_of_five_le (hsize : 5 ≤ size) : ¬ PhaseFreeCovering size := by
  intro hcover
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, -,
    hdeterminant⟩ :=
    hcover (equiangularPoint size) (equiangularPoint_isPhaseFreeAdmissible (by omega))
  exact absurd hdeterminant (not_le.mpr (equiangularPoint_determinantLeg_neg hsize hpivotFirst
    hpivotSecond hpairDistinct))

/-- **THE RESIDUE IS INHABITED AT EVERY SIZE FROM FIVE UP.**  A third family of
witnesses for `Gtz.PhaseFreeData.IsExceptional`, structurally unlike the shipped
`Gtz.trineSixData` and `Gtz.trineSevenData`: those have a three-valued pairing
table, this one is constant. -/
theorem equiangularPoint_isExceptional (hsize : 5 ≤ size) :
    (equiangularPoint size).IsExceptional := by
  refine isExceptional_of_not_exists_covering_witness
    (equiangularPoint_isPhaseFreeAdmissible (by omega)) (by omega) ?_
  rintro pivot pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct ⟨-, hdeterminant⟩
  exact absurd hdeterminant (not_le.mpr (equiangularPoint_determinantLeg_neg hsize hpivotFirst
    hpivotSecond hpairDistinct))

theorem exists_isExceptional_of_five_le (hsize : 5 ≤ size) :
    ∃ point : PhaseFreeData size, IsPhaseFreeAdmissible point ∧ point.IsExceptional :=
  ⟨equiangularPoint size, equiangularPoint_isPhaseFreeAdmissible (by omega),
    equiangularPoint_isExceptional hsize⟩

/-! ## The rank-three top

`Gtz.forced_of_uniform` at `size = 6`, and the object it produces. -/

/-- **THE UNIFORM SLICE AT THE RANK-THREE TOP CARRIES ICOSAHEDRAL MODULI.**
Admissibility alone forces `overlap = 9/5` — no design, no realness, no choice.
This is the squared overlap of the maximal real equiangular design
(`Gtz.icosaDesign_atomPairing_sq_of_ne`). -/
theorem forced_overlap_six {point : PhaseFreeData 6} (hadmissible : IsPhaseFreeAdmissible point)
    (weightValue excessValue overlapValue : ℝ)
    (hweight : ∀ atomIndex, point.weight atomIndex = weightValue)
    (hexcess : ∀ atomIndex, point.excess atomIndex = excessValue)
    (hpairing : ∀ first second, first ≠ second → point.pairing first second = overlapValue) :
    weightValue = 1 / 6 ∧ excessValue = 2 ∧ overlapValue = 9 / 5 := by
  obtain ⟨hweightTotal, hexcessTwo, hoverlap⟩ :=
    forced_of_uniform hadmissible weightValue excessValue overlapValue 0 hweight hexcess hpairing
  norm_num at hweightTotal hoverlap
  exact ⟨by linarith, hexcessTwo, by linarith⟩

theorem equiangularOverlap_six : equiangularOverlap 6 = 9 / 5 := by
  rw [equiangularOverlap]; norm_num

/-- **THE PHASE DEFECT IS TOTAL AT THE TOP.**  `Gtz.equiangularPoint 6` has every
Bargmann triangle of distinct atoms equal to `0` — `parsevalPair` forces it — so
at `size = 6` the uniform point is maximally far from any real design. -/
theorem equiangularBargmann_six : equiangularBargmann 6 = 0 := by
  rw [equiangularBargmann]; norm_num

/-! ## The saturated locus

The torsion equality.  Over `R` the cap of `IsPhaseFreeAdmissible` holds with
equality; the deficit over `C` is the squared imaginary part of the Bargmann
invariant.  Saturation is what licenses reading the band off the moduli. -/

/-- **THE TORSION EQUALITY**, as a predicate on points.  The campaign's "vertex
point": the triangle sits at an endpoint of the box the cap allows.  Every design
image satisfies it (`Gtz.phaseFreeOfDesign_hasSaturatedTriangleCap`); the
shipped complex counterexamples do not
(`Gtz.not_hasSaturatedTriangleCap_trineSixData`). -/
def PhaseFreeData.HasSaturatedTriangleCap (point : PhaseFreeData size) : Prop :=
  ∀ first second third : Fin size,
    point.triangle first second third ^ 2
      = point.pairing first second * point.pairing second third * point.pairing first third

/-- Every design image is saturated — this is `Gtz.phaseFreeOfDesign_triangle_sq`
packaged as the hypothesis the engine below consumes. -/
theorem phaseFreeOfDesign_hasSaturatedTriangleCap (D : WeightedDesign size 3) :
    (phaseFreeOfDesign D).HasSaturatedTriangleCap :=
  fun first second third => phaseFreeOfDesign_triangle_sq D first second third

/-- **THE ENGINE.**  On the saturated locus a light edge whose star is banded in
the MODULI and lies in the nonneg-trace class puts the point outside the residue.

Saturation is doing precise work: by `Gtz.zero_le_add_two_mul_abs_iff_of_sq_eq`
it turns the field-blind band into the pointwise one that
`Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge` needs, and
without it the implication is FALSE — see
`Gtz.not_forall_exists_star_determinantLeg_nonneg_of_moduliBand`, refuted by
`Gtz.trineSixData`.  No rank, no size and no nonemptiness hypothesis enters. -/
theorem not_isExceptional_of_saturatedLightEdge {point : PhaseFreeData size}
    (hsaturated : point.HasSaturatedTriangleCap) {first second : Fin size}
    (hdistinct : first ≠ second)
    (hlight : point.atomShare first + point.atomShare second ≤ 1)
    (hmoduli : ∀ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.excessGap first second other
        ∨ point.excessGap first second other ^ 2
            ≤ 4 * (point.pairing first second * point.pairing second other
                * point.pairing first other))
    (htrace : ∀ other ∈ (Finset.univ.erase first).erase second,
      point.HasNonnegTraceLeg first second other) :
    ¬ point.IsExceptional := by
  intro hexceptional
  obtain ⟨other, hmember, hbad⟩ := hexceptional.2 first second hdistinct hlight
  rcases hbad with hbadTrace | hbadBand
  · exact hbadTrace (htrace other hmember)
  · exact absurd ((zero_le_add_two_mul_abs_iff_of_sq_eq _ _ _
      (hsaturated first second other)).mpr (hmoduli other hmember)) (not_le.mpr hbadBand)

/-- **THE ENGINE, ON DESIGNS.**  Saturation is free at a design image, so an
all-heavy design with one moduli-banded light edge dominates.  Every hypothesis
here is a statement about squared overlaps and leverages — the signs of the Gram
entries never appear. -/
theorem exists_dominates_of_saturatedLightEdge (D : WeightedDesign size 3) (hheavy : AllHeavy D)
    (hsize : 3 ≤ size) {first second : Fin size} (hdistinct : first ≠ second)
    (hlight : (phaseFreeOfDesign D).atomShare first
      + (phaseFreeOfDesign D).atomShare second ≤ 1)
    (hmoduli : ∀ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ (phaseFreeOfDesign D).excessGap first second other
        ∨ (phaseFreeOfDesign D).excessGap first second other ^ 2
            ≤ 4 * ((phaseFreeOfDesign D).pairing first second
                * (phaseFreeOfDesign D).pairing second other
                * (phaseFreeOfDesign D).pairing first other))
    (htrace : ∀ other ∈ (Finset.univ.erase first).erase second,
      (phaseFreeOfDesign D).HasNonnegTraceLeg first second other) :
    ∃ selected : Finset (Fin size), selected.card = 3 ∧ Dominates D selected :=
  exists_dominates_of_not_isExceptional D hheavy hsize
    (not_isExceptional_of_saturatedLightEdge (phaseFreeOfDesign_hasSaturatedTriangleCap D)
      hdistinct hlight hmoduli htrace)

/-! ## Instance one: the uniform slice at the rank-three top

`Gtz.forced_overlap_six` says a uniform admissible point at size six has
icosahedral moduli, and those moduli clear the band with room to spare:
`(−14/5)^2 = 196/25` against a box of `4 · (9/5)^3 = 2916/125`.  Every edge is
light on the nose.  So the residue misses the ENTIRE uniform slice — every sign
pattern, every relabelling — provided the cap is saturated. -/

/-- **THE UNIFORM SLICE AT SIZE SIX IS OUTSIDE THE RESIDUE.**  Only the moduli
are named, so this covers all sectors at once. -/
theorem not_isExceptional_of_uniformModuli_six {point : PhaseFreeData 6}
    (hadmissible : IsPhaseFreeAdmissible point) (hsaturated : point.HasSaturatedTriangleCap)
    (weightValue excessValue overlapValue : ℝ)
    (hweight : ∀ atomIndex, point.weight atomIndex = weightValue)
    (hexcess : ∀ atomIndex, point.excess atomIndex = excessValue)
    (hpairing : ∀ first second, first ≠ second → point.pairing first second = overlapValue) :
    ¬ point.IsExceptional := by
  obtain ⟨hweightValue, hexcessValue, hoverlapValue⟩ :=
    forced_overlap_six hadmissible weightValue excessValue overlapValue hweight hexcess hpairing
  refine not_isExceptional_of_saturatedLightEdge hsaturated (first := 0) (second := 1)
    (by decide) ?_ ?_ ?_
  · simp only [PhaseFreeData.atomShare, hweight, hexcess, hweightValue, hexcessValue]
    norm_num
  · intro other hmember
    have hotherFirst : other ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
    have hotherSecond : other ≠ 1 := (Finset.mem_erase.mp hmember).1
    refine Or.inr ?_
    rw [PhaseFreeData.excessGap, hpairing 0 1 (by decide),
      hpairing 0 other (Ne.symm hotherFirst), hpairing 1 other (Ne.symm hotherSecond)]
    simp only [hexcess, hexcessValue, hoverlapValue]
    norm_num
  · intro other hmember
    have hotherFirst : other ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
    refine Or.inl ?_
    rw [PhaseFreeData.traceLeg, hpairing 0 1 (by decide),
      hpairing 0 other (Ne.symm hotherFirst)]
    simp only [hexcess, hexcessValue, hoverlapValue]
    norm_num

/-- **THE RESIDUE MISSES THE MAXIMAL REAL EQUIANGULAR DESIGN.**  Note which
mechanism does the work.  Clause ONE of `Gtz.PhaseFreeData.IsExceptional` HOLDS
at the icosahedron — that is the shipped
`Gtz.icosaDesign_no_isSignBlindGoodTriple`, every gap being `−14/5 < 0` — so the
sign-blind certificate cannot exclude it and only the edge mechanism can.
Through `Gtz.exists_dominates_of_not_isExceptional` this recovers the shipped
`Gtz.icosaDesign_dominates` by a route that never reads a Gram sign. -/
theorem not_isExceptional_phaseFreeOfDesign_icosaDesign :
    ¬ (phaseFreeOfDesign icosaDesign).IsExceptional :=
  not_isExceptional_of_uniformModuli_six
    (isPhaseFreeAdmissible_of_design icosaDesign icosaDesign_allHeavy)
    (phaseFreeOfDesign_hasSaturatedTriangleCap icosaDesign) (1 / 6) 2 (9 / 5)
    (fun _ => rfl) icosaDesign_heavyExcess
    (fun _ _ hne => icosaDesign_atomPairing_sq_of_ne hne)

/-- **EVERY EQUIANGULAR DESIGN AT SIZE SIX DOMINATES.**  Uniform weight, uniform
leverage and uniform SQUARED overlap — the signs are never read — force the
moduli to be icosahedral and the domination follows.  Beyond size six the
hypothesis is empty: by the shipped `Gtz.not_equiangular_uniformShare_sevenThree`
there are no seven equiangular lines in `R^3`, which is exactly the realizability
fact the phase-free relaxation cannot see (`Gtz.equiangularPoint` is admissible at
every size). -/
theorem exists_dominates_of_uniformModuli_six (D : WeightedDesign 6 3) (hheavy : AllHeavy D)
    (weightValue excessValue overlapValue : ℝ)
    (hweight : ∀ atomIndex, D.weight atomIndex = weightValue)
    (hexcess : ∀ atomIndex, heavyExcess D atomIndex = excessValue)
    (hpairing : ∀ first second, first ≠ second → atomPairing D first second ^ 2 = overlapValue) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates D selected :=
  exists_dominates_of_not_isExceptional D hheavy (by omega)
    (not_isExceptional_of_uniformModuli_six (isPhaseFreeAdmissible_of_design D hheavy)
      (phaseFreeOfDesign_hasSaturatedTriangleCap D) weightValue excessValue overlapValue
      hweight hexcess hpairing)

/-- **THE MODULI DECIDE NOTHING AT THE RANK-THREE TOP.**  Two admissible points
at size six agreeing in EVERY field-blind coordinate — weight, excess and all
fifteen squared overlaps — of which one is in the residue and the other is not.

They are `Gtz.equiangularPoint 6` and `Gtz.phaseFreeOfDesign Gtz.icosaDesign`:
`Gtz.forced_overlap_six` leaves the uniform slice no choice of moduli, so both
sit at `weight 1/6`, `excess 2`, `overlap 9/5`, and the ONLY coordinate left in
which they can differ is the Bargmann triangle — `0` at the first, `±(9/5)^{3/2}`
at the second.  That single coordinate flips the verdict.

This is the campaign's boundary condition B1 in its sharpest form and at its most
symmetric point: no certificate reading squared moduli alone can decide the
rank-three top, because the squared moduli of a total failure and of the maximal
real equiangular design are literally equal. -/
theorem exists_isExceptional_and_not_of_equal_moduli :
    ∃ leftPoint rightPoint : PhaseFreeData 6,
      IsPhaseFreeAdmissible leftPoint ∧ IsPhaseFreeAdmissible rightPoint
        ∧ (∀ atomIndex, leftPoint.weight atomIndex = rightPoint.weight atomIndex)
        ∧ (∀ atomIndex, leftPoint.excess atomIndex = rightPoint.excess atomIndex)
        ∧ (∀ first second, first ≠ second →
            leftPoint.pairing first second = rightPoint.pairing first second)
        ∧ leftPoint.IsExceptional ∧ ¬ rightPoint.IsExceptional := by
  refine ⟨equiangularPoint 6, phaseFreeOfDesign icosaDesign,
    equiangularPoint_isPhaseFreeAdmissible (by omega),
    isPhaseFreeAdmissible_of_design icosaDesign icosaDesign_allHeavy, ?_, ?_, ?_,
    equiangularPoint_isExceptional (by omega), not_isExceptional_phaseFreeOfDesign_icosaDesign⟩
  · intro atomIndex
    show (1 : ℝ) / ((6 : ℕ) : ℝ) = 1 / 6
    norm_num
  · intro atomIndex
    rw [phaseFreeOfDesign_excess, icosaDesign_heavyExcess]
    rfl
  · intro first second hdistinct
    rw [phaseFreeOfDesign_pairing, icosaDesign_atomPairing_sq_of_ne hdistinct]
    show (if first = second then (9 : ℝ) else equiangularOverlap 6) = 9 / 5
    rw [if_neg hdistinct, equiangularOverlap_six]

/-! ## Instance two: the trine moduli, where the torsion consumes the field

`Gtz.trineSixData` fails all twenty triples and refutes `Gtz.PhaseFreeCovering 6`.
Its moduli are not the obstruction: saturate the cap and every one of the fifteen
edges closes.  So at those moduli the phase defect is the ONLY thing keeping the
counterexample alive — the sharpest instance in the campaign of realness being
consumed. -/

/-- The trine itself is NOT a witness for the saturated hypothesis: at the triple
`(0,1,2)` its Bargmann triangle is `0` while the box radius is `27`.  Without this
the theorem below would read as if it applied to `Gtz.trineSixData`. -/
theorem not_hasSaturatedTriangleCap_trineSixData :
    ¬ trineSixData.HasSaturatedTriangleCap := by
  intro hsaturated
  have hvalue := hsaturated 0 1 2
  simp only [trineSixData, trinePoint_triangle, trinePoint_pairing, id_eq] at hvalue
  norm_num [trineTriangleTable, trineOverlap, trineFamily, Fin.ext_iff] at hvalue

/-- **EVERY SATURATED POINT OVER THE TRINE'S MODULI IS OUTSIDE THE RESIDUE.**
The gaps are `−10` against a box of `4 · 27 = 108` inside a coplanar family and
`−2` against `4 · 3 = 12` across, so the edge `(0,1)` closes at every phase the
torsion permits.

Admissibility is not a hypothesis — the argument only unpacks the residue's
second clause — so the bundle is inhabited outright.  MEASURED, not proved here:
among the ADMISSIBLE points the saturated locus over these moduli contains
exactly TWO, negatives of one another (the global-flip degeneracy, every share
being `1/2`), and NEITHER carries a two-graph sign structure — so the locus is
inhabited but holds no design image and no cocycle-consistent point.  The same
exhaustive scan at icosahedral moduli returns twelve, all twelve two-graphs. -/
theorem not_isExceptional_of_trineSixModuli {point : PhaseFreeData 6}
    (hweight : ∀ atomIndex, point.weight atomIndex = 1 / 6)
    (hexcess : ∀ atomIndex, point.excess atomIndex = 2)
    (hpairing : ∀ first second, point.pairing first second = trineOverlap first second)
    (hsaturated : point.HasSaturatedTriangleCap) :
    ¬ point.IsExceptional := by
  refine not_isExceptional_of_saturatedLightEdge hsaturated (first := 0) (second := 1)
    (by decide) ?_ ?_ ?_
  · simp only [PhaseFreeData.atomShare, hweight, hexcess]
    norm_num
  · intro other hmember
    have hotherFirst : other ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
    have hotherSecond : other ≠ 1 := (Finset.mem_erase.mp hmember).1
    clear hmember
    refine Or.inr ?_
    simp only [PhaseFreeData.excessGap, hexcess, hpairing]
    fin_cases other <;> revert hotherFirst hotherSecond <;>
      norm_num [trineOverlap, trineFamily, Fin.ext_iff]
  · intro other hmember
    have hotherFirst : other ≠ 0 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
    have hotherSecond : other ≠ 1 := (Finset.mem_erase.mp hmember).1
    clear hmember
    refine Or.inl ?_
    simp only [PhaseFreeData.traceLeg, hexcess, hpairing]
    fin_cases other <;> revert hotherFirst hotherSecond <;>
      norm_num [trineOverlap, trineFamily, Fin.ext_iff]

end Gtz
