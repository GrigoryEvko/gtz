/-
# The triple Gram form of strict domination: a pair-only coordinate system

`Gtz.subsetSum` of a card-three subset is `G Gᵀ` for the `3 x 3` matrix `G` whose
columns are the three atoms.  At rank three that matrix is SQUARE, so the landed
commutation `Gtz.posDef_transpose_mul_sub_one_comm` moves the whole question to
`Gᵀ G`, the Gram matrix of the three chosen atoms:

  `S_C - 1` positive definite  <->  `Gram(C) - 1` positive definite.

`Gtz.subsetSum`'s own docstring asserts this reading ("for `|C| = k` this says the
`k x k` block Gram of the selected vectors has all eigenvalues at least one").  No
theorem stated it.  The equivalence CONSUMES rank three: `G` is square exactly
when the selection size equals the ambient dimension.

What the Gram side buys is a change of coordinates.  The corpus decides a triple
by `Gtz.subsetSum_posDef_iff_tripleInvariants`, three elementary symmetric
functions of `S_C - 1` built from `Gtz.tripleLeverageSum`,
`Gtz.triplePairAreaSum` and `Gtz.atomBracket`.  Every one of those reads all
three atoms, and the last reads an orientation.  On the Gram side the same
question becomes SYLVESTER's chain in leverages and pairwise inner products
alone:

  `0 < l_a - 1`
  `0 < (l_a - 1)(l_b - 1) - <a,b>^2`
  `0 < (l_a-1)(l_b-1)(l_c-1) - (l_a-1)<b,c>^2 - (l_b-1)<a,c>^2 - (l_c-1)<a,b>^2
        + 2<a,b><a,c><b,c>`

THE BRACKET IS GONE.  `tripleGapDet_eq_thirdInvariant` proves the third
line equals the corpus's bracket-carrying third invariant identically, so the
orientation the bracket records is not information the criterion needs — it is
recoverable from the six pair readings.  That is the content of this file.

The second line is the other gain: it is a PAIR condition, mentioning the third
atom nowhere.  `pairMinor_sum_eq_secondInvariant` shows the corpus's second
invariant is the SUM of the three pair minors, so the symmetric form spends three
pair facts where Sylvester spends one.

Sections: the Gram matrix and its entries; the outer-square identity and the
criterion; the Lagrange identity and the pair-local minor; the bracket-free
determinant; the pair-only criterion; and a diagonal-dominance cell that
consumes the landed `Gtz.posDef_of_diagonallyDominant` and reads no determinant.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.RigidityBridge
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Design.LineClassObstructions
import Gtz.Design.KFourBandAtlas
import Gtz.LinAlg.ProjectionDiagonalDominance
import Gtz.Design.TightAntecedentMining

namespace Gtz

open Matrix

/-! ## 1. The triple Gram matrix -/

/-- The Gram matrix of three atoms, as `Gᵀ G` for the column matrix `G`. -/
noncomputable def tripleGram (a b c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (columnMatrix a b c)ᵀ * columnMatrix a b c

theorem tripleGram_apply (a b c : Fin 3 → ℝ) (i j : Fin 3) :
    tripleGram a b c i j = (![a, b, c] i) ⬝ᵥ (![a, b, c] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [tripleGram, columnMatrix, Matrix.mul_apply, dotProduct, Matrix.transpose_apply,
      Fin.sum_univ_three]

theorem tripleGram_zero_zero (a b c : Fin 3 → ℝ) : tripleGram a b c 0 0 = leverageOf a := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, leverageOf, Matrix.transpose_apply,
    Fin.sum_univ_three]; ring

theorem tripleGram_one_one (a b c : Fin 3 → ℝ) : tripleGram a b c 1 1 = leverageOf b := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, leverageOf, Matrix.transpose_apply,
    Fin.sum_univ_three]; ring

theorem tripleGram_two_two (a b c : Fin 3 → ℝ) : tripleGram a b c 2 2 = leverageOf c := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, leverageOf, Matrix.transpose_apply,
    Fin.sum_univ_three]; ring

theorem tripleGram_zero_one (a b c : Fin 3 → ℝ) : tripleGram a b c 0 1 = a ⬝ᵥ b := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three]

theorem tripleGram_zero_two (a b c : Fin 3 → ℝ) : tripleGram a b c 0 2 = a ⬝ᵥ c := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three]

theorem tripleGram_one_two (a b c : Fin 3 → ℝ) : tripleGram a b c 1 2 = b ⬝ᵥ c := by
  simp [tripleGram, columnMatrix, Matrix.mul_apply, dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three]

theorem tripleGram_symm (a b c : Fin 3 → ℝ) : (tripleGram a b c)ᵀ = tripleGram a b c := by
  rw [tripleGram, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem tripleGram_sub_one_symm (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1)ᵀ = tripleGram a b c - 1 := by
  rw [Matrix.transpose_sub, tripleGram_symm, Matrix.transpose_one]

/-! ### The gap entries, once and for all -/

theorem gap_zero_zero (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1) 0 0 = leverageOf a - 1 := by
  simp [Matrix.sub_apply, tripleGram_zero_zero]

theorem gap_one_one (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1) 1 1 = leverageOf b - 1 := by
  simp [Matrix.sub_apply, tripleGram_one_one]

theorem gap_two_two (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1) 2 2 = leverageOf c - 1 := by
  simp [Matrix.sub_apply, tripleGram_two_two]

theorem gap_zero_one (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 0 1 = a ⬝ᵥ b := by
  simp [Matrix.sub_apply, tripleGram_zero_one]

theorem gap_zero_two (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 0 2 = a ⬝ᵥ c := by
  simp [Matrix.sub_apply, tripleGram_zero_two]

theorem gap_one_two (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 1 2 = b ⬝ᵥ c := by
  simp [Matrix.sub_apply, tripleGram_one_two]

theorem gap_one_zero (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 1 0 = a ⬝ᵥ b := by
  have := congrFun (congrFun (tripleGram_sub_one_symm a b c) 0) 1
  rw [Matrix.transpose_apply] at this
  rw [this, gap_zero_one]

theorem gap_two_zero (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 2 0 = a ⬝ᵥ c := by
  have := congrFun (congrFun (tripleGram_sub_one_symm a b c) 0) 2
  rw [Matrix.transpose_apply] at this
  rw [this, gap_zero_two]

theorem gap_two_one (a b c : Fin 3 → ℝ) : (tripleGram a b c - 1) 2 1 = b ⬝ᵥ c := by
  have := congrFun (congrFun (tripleGram_sub_one_symm a b c) 1) 2
  rw [Matrix.transpose_apply] at this
  rw [this, gap_one_two]

/-! ## 2. The subset sum is the outer square, and the criterion -/

/-- `S_C = G Gᵀ` at a card-three selection. -/
theorem subsetSum_triple_eq_mul_transpose {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D ({x, y, z} : Finset (Fin m))
      = columnMatrix (D.atom x) (D.atom y) (D.atom z)
        * (columnMatrix (D.atom x) (D.atom y) (D.atom z))ᵀ := by
  rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton]
  ext i j
  simp [columnMatrix, Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    Fin.sum_univ_three, Matrix.transpose_apply]
  ring

/-- **THE GRAM CRITERION.**  Strict domination by a card-three selection is
positive definiteness of the selected atoms' Gram matrix minus the identity.
Rank three is consumed: the column matrix is square exactly here. -/
theorem subsetSum_posDef_iff_tripleGram {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1).PosDef := by
  rw [subsetSum_triple_eq_mul_transpose D x y z hxy hxz hyz, tripleGram]
  exact (posDef_transpose_mul_sub_one_comm _).symm

/-! ## 3. The Lagrange identity, and the pair-local minor -/

theorem crossNormSq_eq_leverage_mul_sub_sq (a b : Fin 3 → ℝ) :
    crossNormSq a b = leverageOf a * leverageOf b - (a ⬝ᵥ b) ^ 2 := by
  rw [crossNormSq, bracketNormal_lagrange]
  simp only [leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- The second Sylvester minor of the Gram gap, in pair vocabulary. -/
noncomputable def pairGapMinor (a b : Fin 3 → ℝ) : ℝ :=
  (leverageOf a - 1) * (leverageOf b - 1) - (a ⬝ᵥ b) ^ 2

/-- **THE PAIR MINOR IS PAIR-LOCAL.**  It equals the pair's squared area less the
sum of its two leverages plus one, and mentions no third atom. -/
theorem pairGapMinor_eq_crossNormSq (a b : Fin 3 → ℝ) :
    pairGapMinor a b = crossNormSq a b - leverageOf a - leverageOf b + 1 := by
  rw [pairGapMinor, crossNormSq_eq_leverage_mul_sub_sq]; ring

theorem pairGapMinor_comm (a b : Fin 3 → ℝ) : pairGapMinor a b = pairGapMinor b a := by
  rw [pairGapMinor, pairGapMinor, dotProduct_comm]; ring

/-- The corpus's second invariant is the SUM of the three pair minors, so the
symmetric form spends three pair facts where Sylvester spends one. -/
theorem pairMinor_sum_eq_secondInvariant (a b c : Fin 3 → ℝ) :
    pairGapMinor a b + pairGapMinor a c + pairGapMinor b c
      = triplePairAreaSum a b c - 2 * tripleLeverageSum a b c + 3 := by
  rw [pairGapMinor_eq_crossNormSq, pairGapMinor_eq_crossNormSq, pairGapMinor_eq_crossNormSq]
  simp only [triplePairAreaSum, tripleLeverageSum]
  ring

/-! ## 4. The bracket-free determinant -/

/-- The third Sylvester minor of the Gram gap, in pair vocabulary. -/
noncomputable def tripleGapDet (a b c : Fin 3 → ℝ) : ℝ :=
  (leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1)
    - (leverageOf a - 1) * (b ⬝ᵥ c) ^ 2
    - (leverageOf b - 1) * (a ⬝ᵥ c) ^ 2
    - (leverageOf c - 1) * (a ⬝ᵥ b) ^ 2
    + 2 * (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)

/-- **THE GRAM DETERMINANT FORMULA.**  The squared bracket is the determinant of
the inner-product matrix. -/
theorem sq_tripleBracket_eq_gramDet (a b c : Fin 3 → ℝ) :
    tripleBracket a b c ^ 2
      = leverageOf a * leverageOf b * leverageOf c
        - leverageOf a * (b ⬝ᵥ c) ^ 2 - leverageOf b * (a ⬝ᵥ c) ^ 2
        - leverageOf c * (a ⬝ᵥ b) ^ 2 + 2 * (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) := by
  simp only [tripleBracket, Matrix.det_fin_three, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE BRACKET IS NOT INFORMATION.**  The corpus's third invariant, which
reads an orientation through `Gtz.atomBracket`, equals a polynomial in the three
leverages and the three pairwise inner products.  The orientation is recoverable
from the six pair readings, so no criterion needs it. -/
theorem tripleGapDet_eq_thirdInvariant (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleBracket a b c ^ 2 - triplePairAreaSum a b c + tripleLeverageSum a b c - 1 := by
  rw [tripleGapDet, sq_tripleBracket_eq_gramDet]
  simp only [triplePairAreaSum, tripleLeverageSum, crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-! ## 5. The pair-only criterion -/

/-- **THE CRITERION IN PAIR VOCABULARY.**  Strict domination is decided by three
polynomial inequalities in the three leverages and the three pairwise inner
products.  No bracket, no cross norm, no area sum, no determinant of a matrix. -/
theorem tripleGram_posDef_iff_pairVocabulary (a b c : Fin 3 → ℝ) :
    (tripleGram a b c - 1).PosDef
      ↔ 0 < leverageOf a - 1 ∧ 0 < pairGapMinor a b ∧ 0 < tripleGapDet a b c := by
  rw [posDef_finThree_iff_leadingMinors _ (tripleGram_sub_one_symm a b c),
    gap_zero_zero, gap_one_one, gap_two_two, gap_zero_one, gap_zero_two, gap_one_two]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, by rw [pairGapMinor]; linarith, by rw [tripleGapDet]; nlinarith [h3]⟩
  · rintro ⟨h1, h2, h3⟩
    rw [pairGapMinor] at h2
    rw [tripleGapDet] at h3
    exact ⟨h1, by linarith, by nlinarith [h3]⟩

/-- The design-level reading of the pair-only criterion. -/
theorem subsetSum_posDef_iff_pairVocabulary {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ 0 < leverageOf (D.atom x) - 1
        ∧ 0 < pairGapMinor (D.atom x) (D.atom y)
        ∧ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz,
    tripleGram_posDef_iff_pairVocabulary]

/-- **THE PAIR MINOR IS NECESSARY.**  Every pair inside a strict dominator has
squared area beating the sum of its leverages less one. -/
theorem pairGapMinor_pos_of_subsetSum_posDef {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    0 < crossNormSq (D.atom x) (D.atom y)
      - leverageOf (D.atom x) - leverageOf (D.atom y) + 1 := by
  have := ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mp hpos).2.1
  rwa [pairGapMinor_eq_crossNormSq] at this

/-! ## 6. The diagonal-dominance cell -/

/-- Each atom's leverage surplus beats the two absolute inner products in its
row.  Reads no bracket and no determinant. -/
def TripleGramDiagonallyDominant (a b c : Fin 3 → ℝ) : Prop :=
  |a ⬝ᵥ b| + |a ⬝ᵥ c| < leverageOf a - 1
    ∧ |a ⬝ᵥ b| + |b ⬝ᵥ c| < leverageOf b - 1
    ∧ |a ⬝ᵥ c| + |b ⬝ᵥ c| < leverageOf c - 1

/-- **THE DIAGONAL-DOMINANCE CELL.**  Consumes the landed general lemma
`Gtz.posDef_of_diagonallyDominant`. -/
theorem tripleGram_posDef_of_diagonallyDominant (a b c : Fin 3 → ℝ)
    (hdom : TripleGramDiagonallyDominant a b c) :
    (tripleGram a b c - 1).PosDef := by
  obtain ⟨hA, hB, hC⟩ := hdom
  refine posDef_of_diagonallyDominant _ (tripleGram_sub_one_symm a b c) ?_
  intro row
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ row), Fin.sum_univ_three]
  rcases (show row = 0 ∨ row = 1 ∨ row = 2 by fin_cases row <;> simp) with rfl | rfl | rfl <;>
    simp only [gap_zero_zero, gap_zero_one, gap_zero_two, gap_one_zero, gap_one_one,
      gap_one_two, gap_two_zero, gap_two_one, gap_two_two,
      add_sub_cancel_right]
  · linarith [abs_nonneg (a ⬝ᵥ b), abs_nonneg (a ⬝ᵥ c),
      abs_of_nonneg (by linarith [abs_nonneg (a ⬝ᵥ b), abs_nonneg (a ⬝ᵥ c)] :
        (0:ℝ) ≤ leverageOf a - 1)]
  · linarith [abs_nonneg (a ⬝ᵥ b), abs_nonneg (b ⬝ᵥ c),
      abs_of_nonneg (by linarith [abs_nonneg (a ⬝ᵥ b), abs_nonneg (b ⬝ᵥ c)] :
        (0:ℝ) ≤ leverageOf b - 1)]
  · linarith [abs_nonneg (a ⬝ᵥ c), abs_nonneg (b ⬝ᵥ c),
      abs_of_nonneg (by linarith [abs_nonneg (a ⬝ᵥ c), abs_nonneg (b ⬝ᵥ c)] :
        (0:ℝ) ≤ leverageOf c - 1)]

/-- The cell at the design level. -/
theorem subsetSum_posDef_of_diagonallyDominant {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : TripleGramDiagonallyDominant (D.atom x) (D.atom y) (D.atom z)) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  (subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr
    (tripleGram_posDef_of_diagonallyDominant _ _ _ hdom)

/-! ## 7. The pair poison rule

The corpus prunes with the LEVERAGE FLOOR: a member of a strict dominator is
strictly heavy, so a light atom poisons the ten triples containing it.  The pair
minor prunes harder.  Every pair inside a strict dominator satisfies its own
two-atom inequality, so a bad PAIR poisons the four triples containing it, and a
pair can be bad while both its atoms are heavy. -/

/-- The selection is a set, so the criterion reads any ordering of it. -/
theorem subsetSum_posDef_iff_tripleGram_swap {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (tripleGram (D.atom x) (D.atom z) (D.atom y) - 1).PosDef := by
  have hset : ({x, y, z} : Finset (Fin m)) = {x, z, y} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset]
  exact subsetSum_posDef_iff_tripleGram D x z y hxz hxy hyz.symm

/-- The second and third labels also form a readable ordering. -/
theorem subsetSum_posDef_iff_tripleGram_rotate {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (tripleGram (D.atom y) (D.atom z) (D.atom x) - 1).PosDef := by
  have hset : ({x, y, z} : Finset (Fin m)) = {y, z, x} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset]
  exact subsetSum_posDef_iff_tripleGram D y z x hyz hxy.symm hxz.symm

/-- **ALL THREE PAIRS ARE CONSTRAINED.**  Every pair inside a strict dominator
satisfies the pair inequality, not merely the leading one. -/
theorem forall_pairGapMinor_pos_of_subsetSum_posDef {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    0 < pairGapMinor (D.atom x) (D.atom y)
      ∧ 0 < pairGapMinor (D.atom x) (D.atom z)
      ∧ 0 < pairGapMinor (D.atom y) (D.atom z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz).mp hpos).2.1
  · have := (subsetSum_posDef_iff_tripleGram_swap D x y z hxy hxz hyz).mp hpos
    exact ((tripleGram_posDef_iff_pairVocabulary _ _ _).mp this).2.1
  · have := (subsetSum_posDef_iff_tripleGram_rotate D x y z hxy hxz hyz).mp hpos
    exact ((tripleGram_posDef_iff_pairVocabulary _ _ _).mp this).2.1

/-- A pair is ADMISSIBLE when its own two-atom inequality holds. -/
def AdmissiblePair (a b : Fin 3 → ℝ) : Prop := 0 < pairGapMinor a b

/-- **THE PAIR POISON RULE.**  A pair that fails its own inequality lies in no
strict dominator.  The two atoms may both be strictly heavy: heaviness is a
diagonal fact and this is an off-diagonal one. -/
theorem not_subsetSum_posDef_of_not_admissiblePair {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbad : ¬ AdmissiblePair (D.atom x) (D.atom y)) :
    ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  intro hpos
  exact hbad (forall_pairGapMinor_pos_of_subsetSum_posDef D x y z hxy hxz hyz hpos).1

/-- The poison rule in the corpus's cross-norm vocabulary: a pair whose squared
area fails to beat the sum of its leverages less one is dead in every triple. -/
theorem not_subsetSum_posDef_of_crossNormSq_le {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbad : crossNormSq (D.atom x) (D.atom y)
      ≤ leverageOf (D.atom x) + leverageOf (D.atom y) - 1) :
    ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef := by
  refine not_subsetSum_posDef_of_not_admissiblePair D x y z hxy hxz hyz ?_
  rw [AdmissiblePair, pairGapMinor_eq_crossNormSq]
  linarith

/-- **THE PAIR MINOR TRANSPORTS HEAVINESS.**  An admissible pair carries strict
heaviness from either atom to the other.  It does NOT force heaviness on its own:
both leverages below one also give a positive product, which is why Sylvester
spends the first minor before the second. -/
theorem one_lt_leverage_of_admissiblePair (a b : Fin 3 → ℝ)
    (hadm : AdmissiblePair a b) (hheavy : 1 < leverageOf a) : 1 < leverageOf b := by
  rw [AdmissiblePair, pairGapMinor] at hadm
  have hsq : 0 ≤ (a ⬝ᵥ b) ^ 2 := sq_nonneg _
  nlinarith [hadm, hsq, hheavy]

/-- The strict dominator's full necessary package in pair vocabulary: every atom
heavy and every pair admissible. -/
theorem admissible_package_of_subsetSum_posDef {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    (1 < leverageOf (D.atom x) ∧ 1 < leverageOf (D.atom y) ∧ 1 < leverageOf (D.atom z))
      ∧ AdmissiblePair (D.atom x) (D.atom y)
      ∧ AdmissiblePair (D.atom x) (D.atom z)
      ∧ AdmissiblePair (D.atom y) (D.atom z) := by
  obtain ⟨hxy', hxz', hyz'⟩ :=
    forall_pairGapMinor_pos_of_subsetSum_posDef D x y z hxy hxz hyz hpos
  have hx : 1 < leverageOf (D.atom x) := one_lt_leverage_of_posDef D x y z hpos
  exact ⟨⟨hx, one_lt_leverage_of_admissiblePair _ _ hxy' hx,
    one_lt_leverage_of_admissiblePair _ _ hxz' hx⟩, hxy', hxz', hyz'⟩

end Gtz
