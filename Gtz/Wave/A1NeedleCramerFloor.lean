import Gtz.Wave.A1NeedleCollapse
import Gtz.Design.LineClassObstructions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The Cramer floor: a two-sided reading of the smallest triple eigenvalue

`Gtz.heavyNeedleResidual_iff_lineFreeOffConicTieFree` reduces the A1 registry
axiom to one question about a card-three subset: does its atom sum beat the
identity strictly?  The landed decision procedure
`Gtz.subsetSum_posDef_iff_tripleInvariants` answers it with THREE polynomial
inequalities.  This module answers it, on both sides, with ONE comparison
between two of the invariants.

## The identity

Three vectors that span carry a dual basis made of their pairwise wedges.  Read
against a probe, that is the Cramer expansion

  `[a,b,c] * u = (a.u) * (b x c) + (b.u) * (c x a) + (c.u) * (a x b)`

componentwise, with no hypothesis at all.  One Cauchy-Schwarz per coordinate
turns it into the FLOOR

  `[a,b,c]^2 * |u|^2 <= pairAreaSum * u^T S u`,

so `S >= ([a,b,c]^2 / pairAreaSum) * I` in the Loewner order.  Each wedge is
also an eigen-probe of its own: at `u = b x c` the form reads `[a,b,c]^2` and
the probe norm reads the single pair area, which gives the CEILING.  Together:

  `bracket^2 / pairAreaSum  <=  lambda_min (S)  <=  bracket^2 / (each pair area)`.

The two ends differ by at most a factor of three, because the pair-area sum has
three terms.

## What the two ends produce

- The floor is a STRICT DOMINATION PRODUCER.  One inequality
  `pairAreaSum < bracket^2` forces `S - I` positive definite.  No Sylvester
  chain, no positivity of the lower minors, no line-freeness.
- The ceiling is a NON-DOMINATION WITNESS.  One inequality
  `bracket^2 < crossNormSq` at a single pair refutes strict domination, and the
  refuting direction is that pair's own wedge, written down explicitly.

Both feed the axiom through the collapse.  The floor closes a cell of the class
statement outright.  The ceiling is the first cheap sufficient condition in the
tree for BEING a tie, which is what a counterexample hunt needs.
-/

namespace Gtz

open Matrix Finset

/-! ## The Cramer expansion -/

/-- **THE CRAMER IDENTITY AT RANK THREE.**  The bracket times the probe is the
probe's expansion in the wedge dual basis.  It holds for every four vectors,
with no independence hypothesis. -/
theorem tripleBracket_smul_eq_wedgeExpansion (firstVec secondVec thirdVec probe : Fin 3 → ℝ) :
    (tripleBracket firstVec secondVec thirdVec * probe 0
        = (firstVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 0
          + (secondVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 0
          + (thirdVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 0)
      ∧ (tripleBracket firstVec secondVec thirdVec * probe 1
        = (firstVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 1
          + (secondVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 1
          + (thirdVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 1)
      ∧ (tripleBracket firstVec secondVec thirdVec * probe 2
        = (firstVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 2
          + (secondVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 2
          + (thirdVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [tripleBracket, Matrix.det_fin_three, bracketNormal, dotProduct,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue] <;>
    ring

/-- The pair area is symmetric in its two slots. -/
theorem crossNormSq_comm (leftVec rightVec : Fin 3 → ℝ) :
    crossNormSq leftVec rightVec = crossNormSq rightVec leftVec := by
  simp only [crossNormSq, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The pair-area sum, split over the three coordinates of the three wedges. -/
theorem triplePairAreaSum_eq_slotSum (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    triplePairAreaSum firstVec secondVec thirdVec
      = (bracketNormal secondVec thirdVec 0 ^ 2 + bracketNormal thirdVec firstVec 0 ^ 2
          + bracketNormal firstVec secondVec 0 ^ 2)
        + (bracketNormal secondVec thirdVec 1 ^ 2 + bracketNormal thirdVec firstVec 1 ^ 2
            + bracketNormal firstVec secondVec 1 ^ 2)
        + (bracketNormal secondVec thirdVec 2 ^ 2 + bracketNormal thirdVec firstVec 2 ^ 2
            + bracketNormal firstVec secondVec 2 ^ 2) := by
  simp only [triplePairAreaSum, crossNormSq, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The pair-area sum is never negative. -/
theorem triplePairAreaSum_nonneg (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    0 ≤ triplePairAreaSum firstVec secondVec thirdVec := by
  rw [triplePairAreaSum_eq_slotSum]
  positivity

/-! ## The floor -/

/-- **THE CRAMER FLOOR.**  One Cauchy-Schwarz per coordinate of the Cramer
identity.  The three atoms' quadratic form dominates the identity at the ratio
of the squared bracket to the pair-area sum, at every probe and with no
hypothesis. -/
theorem sq_tripleBracket_mul_normSq_le_pairAreaSum_mul_form
    (firstVec secondVec thirdVec probe : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2 * (probe ⬝ᵥ probe)
      ≤ triplePairAreaSum firstVec secondVec thirdVec
          * ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2) := by
  obtain ⟨hcramerZero, hcramerOne, hcramerTwo⟩ :=
    tripleBracket_smul_eq_wedgeExpansion firstVec secondVec thirdVec probe
  have hzero : (tripleBracket firstVec secondVec thirdVec * probe 0) ^ 2
      ≤ ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 0 ^ 2 + bracketNormal thirdVec firstVec 0 ^ 2
              + bracketNormal firstVec secondVec 0 ^ 2) := by
    rw [hcramerZero]
    nlinarith [sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 0
        - (secondVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 0),
      sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 0
        - (thirdVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 0),
      sq_nonneg ((secondVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 0
        - (thirdVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 0)]
  have hone : (tripleBracket firstVec secondVec thirdVec * probe 1) ^ 2
      ≤ ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 1 ^ 2 + bracketNormal thirdVec firstVec 1 ^ 2
              + bracketNormal firstVec secondVec 1 ^ 2) := by
    rw [hcramerOne]
    nlinarith [sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 1
        - (secondVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 1),
      sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 1
        - (thirdVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 1),
      sq_nonneg ((secondVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 1
        - (thirdVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 1)]
  have htwo : (tripleBracket firstVec secondVec thirdVec * probe 2) ^ 2
      ≤ ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 2 ^ 2 + bracketNormal thirdVec firstVec 2 ^ 2
              + bracketNormal firstVec secondVec 2 ^ 2) := by
    rw [hcramerTwo]
    nlinarith [sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 2
        - (secondVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 2),
      sq_nonneg ((firstVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 2
        - (thirdVec ⬝ᵥ probe) * bracketNormal secondVec thirdVec 2),
      sq_nonneg ((secondVec ⬝ᵥ probe) * bracketNormal firstVec secondVec 2
        - (thirdVec ⬝ᵥ probe) * bracketNormal thirdVec firstVec 2)]
  have hleft : tripleBracket firstVec secondVec thirdVec ^ 2 * (probe ⬝ᵥ probe)
      = (tripleBracket firstVec secondVec thirdVec * probe 0) ^ 2
        + (tripleBracket firstVec secondVec thirdVec * probe 1) ^ 2
        + (tripleBracket firstVec secondVec thirdVec * probe 2) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have hright : triplePairAreaSum firstVec secondVec thirdVec
        * ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
      = ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 0 ^ 2 + bracketNormal thirdVec firstVec 0 ^ 2
              + bracketNormal firstVec secondVec 0 ^ 2)
        + ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 1 ^ 2 + bracketNormal thirdVec firstVec 1 ^ 2
              + bracketNormal firstVec secondVec 1 ^ 2)
        + ((firstVec ⬝ᵥ probe) ^ 2 + (secondVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2)
          * (bracketNormal secondVec thirdVec 2 ^ 2 + bracketNormal thirdVec firstVec 2 ^ 2
              + bracketNormal firstVec secondVec 2 ^ 2) := by
    rw [triplePairAreaSum_eq_slotSum]
    ring
  rw [hleft, hright]
  linarith [hzero, hone, htwo]

/-! ## The triple form of a subset sum -/

/-- The quadratic form of a card-three subset sum, in the three atoms. -/
theorem subsetSum_triple_form {size : ℕ} (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (subsetSum design
        ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) *ᵥ probe)
      = (design.atom firstLabel ⬝ᵥ probe) ^ 2 + (design.atom secondLabel ⬝ᵥ probe) ^ 2
        + (design.atom thirdLabel ⬝ᵥ probe) ^ 2 := by
  rw [subsetSum_form_eq_sum_sq, Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-! ## The strict domination producer -/

/-- **ONE INEQUALITY DECIDES STRICT DOMINATION.**  A card-three subset whose
squared bracket exceeds its pair-area sum dominates the identity strictly.  The
Sylvester chain of `Gtz.subsetSum_posDef_iff_tripleInvariants` is not read, and
neither is line-freeness. -/
theorem posDef_subsetSum_of_pairAreaSum_lt_sq_atomBracket {size : ℕ}
    (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hbeats : triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
        (design.atom thirdLabel) < atomBracket design firstLabel secondLabel thirdLabel ^ 2) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).PosDef := by
  set areaSum := triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
    (design.atom thirdLabel) with hareaSum
  set bracketValue := atomBracket design firstLabel secondLabel thirdLabel with hbracketValue
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one design _),
      fun probe hprobeNe => ?_⟩
  have hnormPos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  have hfloor := sq_tripleBracket_mul_normSq_le_pairAreaSum_mul_form
    (design.atom firstLabel) (design.atom secondLabel) (design.atom thirdLabel) probe
  have hform := subsetSum_triple_form design hfirstSecond hfirstThird hsecondThird probe
  have hbracketEq : tripleBracket (design.atom firstLabel) (design.atom secondLabel)
      (design.atom thirdLabel) = bracketValue := rfl
  rw [hbracketEq, ← hareaSum] at hfloor
  have hareaPos : 0 < areaSum := by
    rcases lt_or_eq_of_le (triplePairAreaSum_nonneg (design.atom firstLabel)
      (design.atom secondLabel) (design.atom thirdLabel)) with hpos | hzero
    · exact hpos
    · exfalso
      rw [← hareaSum] at hzero
      rw [← hzero] at hfloor
      nlinarith [hfloor, hnormPos, sq_nonneg bracketValue]
  have hgap : probe ⬝ᵥ ((subsetSum design
      ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1) *ᵥ probe)
      = ((design.atom firstLabel ⬝ᵥ probe) ^ 2 + (design.atom secondLabel ⬝ᵥ probe) ^ 2
          + (design.atom thirdLabel ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hform]
  rw [star_trivial, hgap]
  nlinarith [hfloor, hareaPos, hnormPos, hbeats]

/-- **THE FLOOR IN THE LOEWNER ORDER.**  The headline form: the atom sum of a
card-three subset dominates the identity at the ratio of its squared bracket to
its pair-area sum.  The bound reads only the three directions, and no weight
enters it. -/
theorem posSemidef_subsetSum_sub_cramerRatio_smul_one {size : ℕ}
    (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hareaPos : 0 < triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
      (design.atom thirdLabel)) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size))
        - (atomBracket design firstLabel secondLabel thirdLabel ^ 2
            / triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
              (design.atom thirdLabel)) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq ?_, fun probe => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    congr 1
    exact transpose_subsetSum design _
  · have hfloor := sq_tripleBracket_mul_normSq_le_pairAreaSum_mul_form
      (design.atom firstLabel) (design.atom secondLabel) (design.atom thirdLabel) probe
    have hform := subsetSum_triple_form design hfirstSecond hfirstThird hsecondThird probe
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, Matrix.one_mulVec, hform, smul_eq_mul, sub_nonneg,
      div_mul_eq_mul_div, div_le_iff₀ hareaPos]
    have hbracketEq : tripleBracket (design.atom firstLabel) (design.atom secondLabel)
        (design.atom thirdLabel) = atomBracket design firstLabel secondLabel thirdLabel := rfl
    rw [hbracketEq] at hfloor
    nlinarith [hfloor]

/-! ## The non-domination witness -/

/-- The wedge of two atoms reads the subset form as the squared bracket alone:
the other two atoms are orthogonal to it. -/
theorem subsetSum_triple_form_at_wedge {size : ℕ} (design : WeightedDesign size 3)
    (firstLabel secondLabel thirdLabel : Fin size) :
    design.atom firstLabel ⬝ᵥ bracketNormal (design.atom secondLabel) (design.atom thirdLabel)
        = atomBracket design firstLabel secondLabel thirdLabel
      ∧ design.atom secondLabel
          ⬝ᵥ bracketNormal (design.atom secondLabel) (design.atom thirdLabel) = 0
      ∧ design.atom thirdLabel
          ⬝ᵥ bracketNormal (design.atom secondLabel) (design.atom thirdLabel) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [atomBracket, tripleBracket, Matrix.det_fin_three, bracketNormal, dotProduct,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue] <;>
    ring

/-- **THE CRAMER CEILING.**  A single pair whose area beats the squared bracket
refutes strict domination, and the refuting direction is that pair's own wedge.
This is the cheapest non-domination test in the tree, and it names its
witness. -/
theorem not_posDef_subsetSum_of_sq_atomBracket_lt_crossNormSq {size : ℕ}
    (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hpairBeats : atomBracket design firstLabel secondLabel thirdLabel ^ 2
      < crossNormSq (design.atom secondLabel) (design.atom thirdLabel)) :
    ¬ (subsetSum design
        ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).PosDef := by
  intro hposDef
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    subsetSum_triple_form_at_wedge design firstLabel secondLabel thirdLabel
  set witness := bracketNormal (design.atom secondLabel) (design.atom thirdLabel) with hwitness
  have hnormEq : witness ⬝ᵥ witness
      = crossNormSq (design.atom secondLabel) (design.atom thirdLabel) := rfl
  have hnormPos : 0 < witness ⬝ᵥ witness := by
    rw [hnormEq]
    exact lt_of_le_of_lt (sq_nonneg _) hpairBeats
  have hwitnessNe : witness ≠ 0 := by
    intro hzero
    rw [hzero] at hnormPos
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hnormPos
    exact lt_irrefl 0 hnormPos
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hwitnessNe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    subsetSum_triple_form design hfirstSecond hfirstThird hsecondThird witness,
    hfirst, hsecond, hthird, hnormEq] at hvalue
  nlinarith [hvalue, hpairBeats]

/-! ## The reading at a tie -/

/-- **EVERY TRIPLE OF A TIE IS AREA-DOMINANT.**  At a tie no card-three subset
dominates strictly, so the floor forces the pair-area sum to carry the squared
bracket at all twenty triples. -/
theorem sq_atomBracket_le_triplePairAreaSum_of_noStrictTriple {size : ℕ}
    (design : WeightedDesign size 3)
    (hnoStrict : ∀ selected : Finset (Fin size), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    atomBracket design firstLabel secondLabel thirdLabel ^ 2
      ≤ triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel) := by
  by_contra hbeats
  push Not at hbeats
  refine hnoStrict ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) ?_
    (posDef_subsetSum_of_pairAreaSum_lt_sq_atomBracket design hfirstSecond hfirstThird
      hsecondThird hbeats)
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
    Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]

/-- **A BRACKET-DOMINANT TRIPLE FORBIDS A TIE.**  One triple whose squared
bracket beats its pair-area sum is already a strict dominator. -/
theorem not_isTie_of_pairAreaSum_lt_sq_atomBracket {size : ℕ} (design : WeightedDesign size 3)
    {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hbeats : triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
        (design.atom thirdLabel) < atomBracket design firstLabel secondLabel thirdLabel ^ 2) :
    ¬ IsTie design := by
  intro htie
  refine htie.2 ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) ?_
    (posDef_subsetSum_of_pairAreaSum_lt_sq_atomBracket design hfirstSecond hfirstThird
      hsecondThird hbeats)
  rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
    Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]

/-! ## The new cell of the registry axiom -/

/-- **A NEW CLOSED CELL OF A1.**  Through the collapse, the registry axiom holds
on every line-free off-conic design that carries one bracket-dominant triple.
The cell is decided by a single polynomial comparison, with no selector and no
tight direction. -/
theorem heavyNeedleResidual_of_bracketDominantCell
    (hcell : ∀ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
      HasNoCommonQuadric design.atom →
      ∃ firstLabel secondLabel thirdLabel : Fin 6,
        firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧ secondLabel ≠ thirdLabel ∧
        triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
            (design.atom thirdLabel)
          < atomBracket design firstLabel secondLabel thirdLabel ^ 2) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  refine heavyNeedleResidual_of_pinnedStratumTieFree ?_
  intro design hlineFree hoffConic
  obtain ⟨firstLabel, secondLabel, thirdLabel, hfirstSecond, hfirstThird, hsecondThird,
    hbeats⟩ := hcell design hlineFree hoffConic
  exact not_isTie_of_pairAreaSum_lt_sq_atomBracket design hfirstSecond hfirstThird
    hsecondThird hbeats

/-- **THE COUNTEREXAMPLE IS AREA-DOMINANT AT ALL TWENTY TRIPLES.**  Any design
refuting the registry axiom obeys the area bound everywhere, so the search for
one is confined to that semialgebraic set. -/
theorem sq_atomBracket_le_triplePairAreaSum_of_lineFreeOffConicTie
    (design : WeightedDesign 6 3)
    (_hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (_hoffConic : HasNoCommonQuadric design.atom) (htie : IsTie design)
    {firstLabel secondLabel thirdLabel : Fin 6}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    atomBracket design firstLabel secondLabel thirdLabel ^ 2
      ≤ triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel) :=
  sq_atomBracket_le_triplePairAreaSum_of_noStrictTriple design htie.2 hfirstSecond
    hfirstThird hsecondThird

/-! ## The floor cell is inhabited

An open condition needs a witness before anyone spends a fork on it.  The
design below is exact in rationals: three coordinate directions at length two,
each shadowed by the same direction at length one, with weights `2/9` and `1/9`.
Parseval is exact because `(2/9)*4 + (1/9)*1 = 1` on each axis.  The long triple
reads bracket squared `64` against pair-area sum `48`, so the floor fires and
the triple dominates strictly.

The witness has parallel atoms, so it is NOT line-free.  It shows the CELL is
inhabited, not that the cell meets the line-free stratum.  The criterion is an
open condition on the atoms, so a generic perturbation stays in the cell, but no
such perturbation is landed here.
-/

/-- Three coordinate directions at length two, each shadowed at length one. -/
noncomputable def cramerCellAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![2, 0, 0]
  | 1 => ![1, 0, 0]
  | 2 => ![0, 2, 0]
  | 3 => ![0, 1, 0]
  | 4 => ![0, 0, 2]
  | 5 => ![0, 0, 1]

/-- Weight `2/9` on each long atom and `1/9` on each shadow. -/
noncomputable def cramerCellWeight : Fin 6 → ℝ
  | 0 => 2 / 9
  | 1 => 1 / 9
  | 2 => 2 / 9
  | 3 => 1 / 9
  | 4 => 2 / 9
  | 5 => 1 / 9

/-- The non-vacuity witness of the floor cell. -/
noncomputable def cramerCellDesign : WeightedDesign 6 3 where
  atom := cramerCellAtom
  weight := cramerCellWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [cramerCellWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [cramerCellWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [cramerCellAtom, cramerCellWeight, atomMatrix, Matrix.cons_val_two] <;> norm_num

/-- **THE FLOOR CELL IS INHABITED.**  The long triple beats its pair-area sum by
sixteen. -/
theorem cramerCellDesign_bracketDominant :
    triplePairAreaSum (cramerCellDesign.atom 0) (cramerCellDesign.atom 2)
        (cramerCellDesign.atom 4)
      < atomBracket cramerCellDesign 0 2 4 ^ 2 := by
  simp only [atomBracket, tripleBracket, triplePairAreaSum, crossNormSq, bracketNormal,
    cramerCellDesign, cramerCellAtom, Matrix.det_fin_three, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The floor fires at the witness, with no Sylvester chain read. -/
theorem cramerCellDesign_posDef_longTriple :
    (subsetSum cramerCellDesign ({0, 2, 4} : Finset (Fin 6)) - 1).PosDef :=
  posDef_subsetSum_of_pairAreaSum_lt_sq_atomBracket cramerCellDesign (by decide) (by decide)
    (by decide) cramerCellDesign_bracketDominant

/-- The witness is not a tie. -/
theorem cramerCellDesign_not_isTie : ¬ IsTie cramerCellDesign :=
  not_isTie_of_pairAreaSum_lt_sq_atomBracket cramerCellDesign (by decide) (by decide)
    (by decide) cramerCellDesign_bracketDominant

/-! ## The tie construction criterion -/

/-- **A CHEAP SUFFICIENT CONDITION FOR BEING A TIE.**  A design with one weakly
dominating card-three subset, all of whose card-three subsets carry a pair whose
area beats the squared bracket, is an exact tie.  Every refusal comes with the
wedge that witnesses it, so no eigenvalue computation is read. -/
theorem isTie_of_dominates_of_forall_pairArea_beats_sq_atomBracket
    {size : ℕ} (design : WeightedDesign size 3)
    {weakSet : Finset (Fin size)} (hweakCard : weakSet.card = 3)
    (hweakDominates : Dominates design weakSet)
    (hrefusals : ∀ selected : Finset (Fin size), selected.card = 3 →
      ∃ firstLabel secondLabel thirdLabel : Fin size,
        selected = {firstLabel, secondLabel, thirdLabel} ∧
        firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧ secondLabel ≠ thirdLabel ∧
        atomBracket design firstLabel secondLabel thirdLabel ^ 2
          < crossNormSq (design.atom secondLabel) (design.atom thirdLabel)) :
    IsTie design := by
  refine ⟨⟨weakSet, hweakCard, hweakDominates⟩, ?_⟩
  intro selected hcard
  obtain ⟨firstLabel, secondLabel, thirdLabel, hselected, hfirstSecond, hfirstThird,
    hsecondThird, hpairBeats⟩ := hrefusals selected hcard
  rw [hselected]
  exact not_posDef_subsetSum_of_sq_atomBracket_lt_crossNormSq design hfirstSecond
    hfirstThird hsecondThird hpairBeats

end Gtz
