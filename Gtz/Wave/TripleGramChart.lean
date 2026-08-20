import Gtz.Wave.ErasedWitnessGram
import Gtz.Wave.InvariantBudgets
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The triple Gram chart

Every corner analysis so far runs through a chart with an inverse in it:
the pencil frame needs `W⁻¹`, the dual frame needs `Mo⁻¹`, the floors are
diagonal entries of inverted gaps.  This module builds the chart with NO
inverse anywhere, on top of the landed Gram criterion.

The chart of a triple `(a,b,c)` is its Gram `P` (landed as
`Gtz.tripleGram`) together with the WITNESS MAP `ω(v) = (a·v, b·v, c·v)`.
Both are plain dot products.

* `Gtz.tripleWitness_dotProduct` — `ω(v)·ω(w) = vᵀ(aaᵀ+bbᵀ+ccᵀ)w`: the
  witness inner product IS the moment reading.
* `Gtz.tripleGram_mulVec_witness` — `P·ω(v) = ω(S·v)`: the Gram IS the
  moment matrix, read in witness coordinates.
* `Gtz.tripleGram_adjugate_polarization` — THE MASTER IDENTITY,
  `ω(v)ᵀ(adj P)ω(w) = det P·(v·w)`: the adjugate undoes the witness map at
  the price of one determinant, with no invertibility hypothesis.
* `Gtz.columnGram_adjugate_sandwich` — its matrix form,
  `V·(adj P)·Vᵀ = det P·1`.

Then the determinant transfers, which make every gap of the campaign
polynomial in dot products:

* `Gtz.columnMatrix_gapDet_comm` — SYLVESTER AT THREE:
  `det(VVᵀ − 1) = det(VᵀV − 1)`.
* `Gtz.subsetSum_gapDet_eq_tripleGapDet` — hence `det(S_T − 1)` is the
  landed `Gtz.tripleGapDet`, an explicit polynomial in the six dot
  products of the triple.
* `Gtz.fourSet_member_floor_iff_tripleGapDet_nonpos` — THE FLOOR
  DICTIONARY: a member floor of a four-set gap is one polynomial sign
  condition on the triple that survives the erasure.  The seven floors of
  the both-light cell become seven polynomial inequalities in ambient dot
  products.

The payload is `Gtz.parseval_tripleGram_identity`: at `(6,3)` Parseval
itself is ONE `3×3` matrix identity in the chart,

  `t_x·ωωᵀ + t_y·ω^yω^yᵀ + t_z·ω^zω^zᵀ + P·T·P = P` ,

with `T` the diagonal of outside weights.  Read against the adjugate at
the erased witness it gives the chart witness pin
(`Gtz.corner_chart_witness_pin`).
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The literal form of the landed Gram -/

/-- The landed Gram, entry by entry. -/
theorem tripleGram_eq_literal (a b c : Fin 3 → ℝ) :
    tripleGram a b c
      = !![a ⬝ᵥ a, a ⬝ᵥ b, a ⬝ᵥ c;
           a ⬝ᵥ b, b ⬝ᵥ b, b ⬝ᵥ c;
           a ⬝ᵥ c, b ⬝ᵥ c, c ⬝ᵥ c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tripleGram, columnMatrix, Matrix.mul_apply, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_three] <;> ring

/-- The column matrix against its transpose is the triple's atom sum. -/
theorem columnMatrix_mul_transpose (a b c : Fin 3 → ℝ) :
    columnMatrix a b c * (columnMatrix a b c)ᵀ
      = atomMatrix a + atomMatrix b + atomMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columnMatrix, atomMatrix, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.transpose_apply, Fin.sum_univ_three]

/-- The weighted triple sum through the columns. -/
theorem columnMatrix_diagonal_mul_transpose (a b c : Fin 3 → ℝ)
    (t4 t5 t6 : ℝ) :
    columnMatrix a b c * Matrix.diagonal ![t4, t5, t6]
        * (columnMatrix a b c)ᵀ
      = t4 • atomMatrix a + t5 • atomMatrix b + t6 • atomMatrix c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [columnMatrix, atomMatrix, Matrix.mul_apply,
        Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
        Fin.sum_univ_three]
      ring

/-! ## 2. The witness map -/

/-- The witness of a probe against an ordered triple. -/
def tripleWitness (a b c v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a ⬝ᵥ v, b ⬝ᵥ v, c ⬝ᵥ v]

/-- **THE WITNESS IS A TRANSPOSE ACTION.** -/
theorem tripleWitness_eq_mulVec (a b c v : Fin 3 → ℝ) :
    tripleWitness a b c v = (columnMatrix a b c)ᵀ *ᵥ v := by
  funext i
  fin_cases i <;>
    simp [tripleWitness, columnMatrix, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_three]

/-- **THE WITNESS INNER PRODUCT IS A MOMENT READING.** -/
theorem tripleWitness_dotProduct (a b c v w : Fin 3 → ℝ) :
    tripleWitness a b c v ⬝ᵥ tripleWitness a b c w
      = v ⬝ᵥ ((atomMatrix a + atomMatrix b + atomMatrix c) *ᵥ w) := by
  simp only [tripleWitness, atomMatrix, Matrix.vecMulVec_apply,
    Matrix.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE GRAM IS THE MOMENT MATRIX IN WITNESS COORDINATES.** -/
theorem tripleGram_mulVec_witness (a b c v : Fin 3 → ℝ) :
    tripleGram a b c *ᵥ tripleWitness a b c v
      = tripleWitness a b c
        ((atomMatrix a + atomMatrix b + atomMatrix c) *ᵥ v) := by
  rw [tripleGram, tripleWitness_eq_mulVec, tripleWitness_eq_mulVec,
    ← columnMatrix_mul_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- The Gram form of two witnesses is the squared-moment reading. -/
theorem tripleGram_quadForm_witness (a b c v w : Fin 3 → ℝ) :
    tripleWitness a b c v ⬝ᵥ (tripleGram a b c *ᵥ tripleWitness a b c w)
      = v ⬝ᵥ (((atomMatrix a + atomMatrix b + atomMatrix c)
          * (atomMatrix a + atomMatrix b + atomMatrix c)) *ᵥ w) := by
  rw [tripleGram_mulVec_witness, tripleWitness_dotProduct,
    ← Matrix.mulVec_mulVec]

/-! ## 3. The master identity -/

/-- **THE MASTER IDENTITY OF THE CHART.**  The adjugate of the Gram undoes
the witness map, at the price of one determinant:

  `ω(v)ᵀ(adj P)ω(w) = det P·(v·w)` .

A polynomial identity in twelve variables — no invertibility, no
positivity, no hypothesis at all.  Every corner relation of the campaign
(unit norms, orthogonalities, inside Grams) becomes polynomial through
this one law. -/
theorem tripleGram_adjugate_polarization (a b c v w : Fin 3 → ℝ) :
    tripleWitness a b c v ⬝ᵥ
        ((tripleGram a b c).adjugate *ᵥ tripleWitness a b c w)
      = (tripleGram a b c).det * (v ⬝ᵥ w) := by
  rw [tripleGram_eq_literal]
  simp only [tripleWitness, Matrix.adjugate_fin_three, Matrix.det_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.of_apply]
  ring

/-- **THE MASTER IDENTITY, MATRIX FORM.**  The adjugate sandwiched between
the columns is the determinant: `V·(adj P)·Vᵀ = det P·1`. -/
theorem columnGram_adjugate_sandwich (a b c : Fin 3 → ℝ) :
    columnMatrix a b c * (tripleGram a b c).adjugate * (columnMatrix a b c)ᵀ
      = (tripleGram a b c).det • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hEntry : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3),
      M i j = Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single j 1) := by
    intro M i j
    rw [Matrix.mulVec_single_one, single_one_dotProduct]
    simp
  have hform : ∀ u w : Fin 3 → ℝ,
      u ⬝ᵥ ((columnMatrix a b c * (tripleGram a b c).adjugate
          * (columnMatrix a b c)ᵀ) *ᵥ w)
        = (tripleGram a b c).det * (u ⬝ᵥ w) := by
    intro u w
    have h := tripleGram_adjugate_polarization a b c u w
    rw [tripleWitness_eq_mulVec, tripleWitness_eq_mulVec] at h
    rw [← h]
    rw [show (columnMatrix a b c * (tripleGram a b c).adjugate
        * (columnMatrix a b c)ᵀ) *ᵥ w
        = columnMatrix a b c *ᵥ ((tripleGram a b c).adjugate
          *ᵥ ((columnMatrix a b c)ᵀ *ᵥ w)) from by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  ext i j
  rw [hEntry (columnMatrix a b c * (tripleGram a b c).adjugate
      * (columnMatrix a b c)ᵀ) i j, hform, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hdelta : (Pi.single i (1 : ℝ)) ⬝ᵥ (Pi.single j (1 : ℝ))
      = if i = j then (1 : ℝ) else 0 := by
    rw [single_one_dotProduct, Pi.single_apply]
  rw [hdelta]

/-! ## 4. The determinant transfers -/

/-- The adjugate of the negated identity at three. -/
theorem neg_one_adjugate_fin_three :
    ((-1 : Matrix (Fin 3) (Fin 3) ℝ)).adjugate = 1 := by
  simp [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of the negated identity at three. -/
theorem neg_one_det_fin_three :
    ((-1 : Matrix (Fin 3) (Fin 3) ℝ)).det = -1 := by
  simp [Matrix.det_fin_three]

/-- **THE TRIPLE GAP DETERMINANT IS A POLYNOMIAL IN DOT PRODUCTS.**  The gap
determinant of three atoms is the landed `Gtz.tripleGapDet` — leverages and
pairings only, no matrix and no inverse:

  `det(aaᵀ + bbᵀ + ccᵀ − 1) = tripleGapDet a b c` .

The route is the landed three-atom expansion at the base `−1`: the base
determinant is `−1`, its adjugate is the identity, so the three adjugate
readings are the leverages, the three cross readings are minus the squared
areas, and the triple product is the squared bracket.  Lagrange and the
Gram form of the bracket finish it. -/
theorem gapDet_triple_eq_tripleGapDet (a b c : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1).det
      = tripleGapDet a b c := by
  have hform : atomMatrix a + atomMatrix b + atomMatrix c - 1
      = (-1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 : ℝ) • atomMatrix a
        + (1 : ℝ) • atomMatrix b + (1 : ℝ) • atomMatrix c := by
    simp only [one_smul]
    abel
  rw [hform, det_add_three_atomMatrix_fin_three, neg_one_det_fin_three,
    neg_one_adjugate_fin_three]
  simp only [Matrix.one_mulVec, one_mul, mul_one]
  have hneg : ∀ v : Fin 3 → ℝ,
      v ⬝ᵥ ((-1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v) = -(v ⬝ᵥ v) := by
    intro v
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg]
  rw [hneg, hneg, hneg, cross_dotProduct_self, cross_dotProduct_self,
    cross_dotProduct_self]
  have hbr : (crossProduct a b ⬝ᵥ c) ^ 2 = tripleBracket a b c ^ 2 := by
    rw [tripleBracket_eq]
    simp only [cross_apply, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hbr, sq_tripleBracket_eq_gramDet, tripleGapDet]
  simp only [leverageOf, dotProduct, Fin.sum_univ_three]
  ring

/-- **THE GAP DETERMINANT OF A SELECTED TRIPLE.**  Every triple gap
determinant of the campaign is polynomial in the six dot products. -/
theorem subsetSum_gapDet_eq_tripleGapDet {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).det
      = tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [show subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z)
    from by
      rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
      abel,
    gapDet_triple_eq_tripleGapDet]

/-- **THE FLOOR DICTIONARY.**  A member floor of a four-set gap is one
polynomial sign condition on the triple that survives the erasure:

  `r_s ≥ 1  ↔  tripleGapDet(the other three atoms) ≤ 0` .

The whole floor system of the both-light cell — the `y`-floor and the six
outside floors — becomes seven polynomial inequalities in the ambient dot
products, with no inverse and no matrix. -/
theorem fourSet_member_floor_iff_tripleGapDet_nonpos {m : ℕ}
    (D : WeightedDesign m 3) {F : Finset (Fin m)}
    (hpd : (subsetSum D F - 1).PosDef) {s x y z : Fin m} (hs : s ∈ F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (herase : F.erase s = ({x, y, z} : Finset (Fin m))) :
    1 ≤ D.atom s ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom s)
      ↔ tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  rw [member_floor_iff_gapDet_erase_nonpos D hpd hs, herase,
    subsetSum_gapDet_eq_tripleGapDet D x y z hxy hxz hyz]

/-! ## 5. Parseval in the chart -/

/-- **PARSEVAL IN THE TRIPLE GRAM CHART.**  At `(6,3)` the whole Parseval
condition of a corner design is ONE `3×3` matrix identity in the chart:

  `t_x·ωωᵀ + t_y·ω^yω^yᵀ + t_z·ω^zω^zᵀ + P·T·P = P` ,

with `T = diag(t₄,t₅,t₆)` the outside weights.  Polynomial, inverse-free,
symmetric — six scalar equations in the fifteen ambient scalars of the
chart.  Every constraint of the corner cell is a polynomial consequence of
this identity together with the corner relations. -/
theorem parseval_tripleGram_identity (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6}) :
    D.weight x • atomMatrix
          (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x))
        + D.weight y • atomMatrix
          (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom y))
        + D.weight z • atomMatrix
          (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom z))
        + tripleGram (D.atom d4) (D.atom d5) (D.atom d6)
          * Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
          * tripleGram (D.atom d4) (D.atom d5) (D.atom d6)
      = tripleGram (D.atom d4) (D.atom d5) (D.atom d6) := by
  classical
  set a := D.atom d4 with ha
  set b := D.atom d5 with hb
  set c := D.atom d6 with hc
  set V : Matrix (Fin 3) (Fin 3) ℝ := columnMatrix a b c with hV
  have hpars : D.weight x • atomMatrix (D.atom x)
      + D.weight y • atomMatrix (D.atom y)
      + D.weight z • atomMatrix (D.atom z)
      + (D.weight d4 • atomMatrix a + D.weight d5 • atomMatrix b
        + D.weight d6 • atomMatrix c) = 1 := by
    have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
      (fun cc => D.weight cc • atomMatrix (D.atom cc))
    rw [D.isParseval, hcompl, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
      Finset.sum_insert (by simp [h45, h46]),
      Finset.sum_insert (by simp [h56]), Finset.sum_singleton] at hsplit
    rw [← hsplit, ha, hb, hc]
    abel
  have hwit : ∀ v : Fin 3 → ℝ,
      atomMatrix (tripleWitness a b c v) = Vᵀ * atomMatrix v * V := by
    intro v
    rw [tripleWitness_eq_mulVec, ← hV, ← congr_atomMatrix (Vᵀ) v,
      Matrix.transpose_transpose]
  have hout : tripleGram a b c
        * Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6]
        * tripleGram a b c
      = Vᵀ * (D.weight d4 • atomMatrix a + D.weight d5 • atomMatrix b
          + D.weight d6 • atomMatrix c) * V := by
    rw [← columnMatrix_diagonal_mul_transpose a b c, tripleGram, ← hV]
    simp only [Matrix.mul_assoc]
  rw [hwit, hwit, hwit, hout, tripleGram, ← hV]
  have hcollapse : D.weight x • (Vᵀ * atomMatrix (D.atom x) * V)
      + D.weight y • (Vᵀ * atomMatrix (D.atom y) * V)
      + D.weight z • (Vᵀ * atomMatrix (D.atom z) * V)
      + Vᵀ * (D.weight d4 • atomMatrix a + D.weight d5 • atomMatrix b
          + D.weight d6 • atomMatrix c) * V
      = Vᵀ * (D.weight x • atomMatrix (D.atom x)
          + D.weight y • atomMatrix (D.atom y)
          + D.weight z • atomMatrix (D.atom z)
          + (D.weight d4 • atomMatrix a + D.weight d5 • atomMatrix b
            + D.weight d6 • atomMatrix c)) * V := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [hcollapse, hpars, Matrix.mul_one]

/-! ## 6. The corner in the chart -/

/-- **THE ERASED NORMALIZATION IN THE CHART.** -/
theorem corner_witness_normalization {m : ℕ} (D : WeightedDesign m 3)
    {x d4 d5 d6 : Fin m} (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x) ⬝ᵥ
        ((tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).adjugate
          *ᵥ tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x))
      = (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det := by
  rw [tripleGram_adjugate_polarization, hxunit, mul_one]

/-- **THE CORNER ORTHOGONALITY IN THE CHART.** -/
theorem corner_witness_orthogonality {m : ℕ} (D : WeightedDesign m 3)
    {x y d4 d5 d6 : Fin m} (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) :
    tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x) ⬝ᵥ
        ((tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).adjugate
          *ᵥ tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom y))
      = 0 := by
  rw [tripleGram_adjugate_polarization, hxy0, mul_zero]

/-- **THE INSIDE GRAM IN THE CHART.** -/
theorem corner_inside_witness_gram {m : ℕ} (D : WeightedDesign m 3)
    {y z d4 d5 d6 : Fin m} :
    tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom y) ⬝ᵥ
        ((tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).adjugate
          *ᵥ tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom z))
      = (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det
        * (D.atom y ⬝ᵥ D.atom z) :=
  tripleGram_adjugate_polarization _ _ _ _ _

/-- The outside atom sum of a `(6,3)` corner, in triple form. -/
theorem corner_outside_atomSum {m : ℕ} (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6}) :
    subsetSum D (({x, y, z} : Finset (Fin m))ᶜ)
      = atomMatrix (D.atom d4) + atomMatrix (D.atom d5)
        + atomMatrix (D.atom d6) := by
  rw [hcompl, subsetSum, Finset.sum_insert (by simp [h45, h46]),
    Finset.sum_insert (by simp [h56]), Finset.sum_singleton]
  abel

/-- **THE ERASED ENERGY IN THE CHART.**  `kxx = |ω|² − 1`. -/
theorem corner_erased_energy_witness {m : ℕ} (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m} (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.atom x ⬝ᵥ ((subsetSum D (({x, y, z} : Finset (Fin m))ᶜ) - 1)
        *ᵥ D.atom x)
      = tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x) ⬝ᵥ
          tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x)
        - 1 := by
  rw [tripleWitness_dotProduct,
    ← corner_outside_atomSum D h45 h46 h56 hcompl, Matrix.sub_mulVec,
    dotProduct_sub, Matrix.one_mulVec, hxunit]

/-- **THE WITNESS PIN IN THE CHART.**  Reading the chart identity against
the adjugate at the erased witness kills both inside terms and collapses
the outside block:

  `det P·(ωᵀ·P·T·ω) = det P·(1 − t_x)·|ω|²` .

Inverse-free, polynomial, and exactly the erased-energy pin in chart
coordinates: the weighted outside block reads the erased witness at the
erased weight slack.  The two inside witnesses drop out by adjugate
orthogonality, and the erased normalization supplies the determinant. -/
theorem corner_chart_witness_pin (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hxunit : D.atom x ⬝ᵥ D.atom x = 1)
    (hxy0 : D.atom x ⬝ᵥ D.atom y = 0) (hxz0 : D.atom x ⬝ᵥ D.atom z = 0) :
    (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det
        * (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x) ⬝ᵥ
          ((tripleGram (D.atom d4) (D.atom d5) (D.atom d6)
              * Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6])
            *ᵥ tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x)))
      = (tripleGram (D.atom d4) (D.atom d5) (D.atom d6)).det
        * ((1 - D.weight x)
          * (tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x) ⬝ᵥ
            tripleWitness (D.atom d4) (D.atom d5) (D.atom d6) (D.atom x))) := by
  classical
  set a := D.atom d4 with ha
  set b := D.atom d5 with hb
  set c := D.atom d6 with hc
  set P : Matrix (Fin 3) (Fin 3) ℝ := tripleGram a b c with hP
  set T : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal ![D.weight d4, D.weight d5, D.weight d6] with hT
  set om : Fin 3 → ℝ := tripleWitness a b c (D.atom x) with hom
  set omy : Fin 3 → ℝ := tripleWitness a b c (D.atom y) with homy
  set omz : Fin 3 → ℝ := tripleWitness a b c (D.atom z) with homz
  have hid := parseval_tripleGram_identity D hxy hxz hyz h45 h46 h56 hcompl
  rw [← ha, ← hb, ← hc, ← hP, ← hT, ← hom, ← homy, ← homz] at hid
  have hread := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => om ⬝ᵥ ((M * P.adjugate) *ᵥ om)) hid
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.add_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul] at hread
  have hfac : ∀ w : Fin 3 → ℝ,
      om ⬝ᵥ ((atomMatrix w * P.adjugate) *ᵥ om)
        = (om ⬝ᵥ w) * (w ⬝ᵥ (P.adjugate *ᵥ om)) := by
    intro w
    rw [← Matrix.mulVec_mulVec,
      show atomMatrix w *ᵥ (P.adjugate *ᵥ om)
        = (w ⬝ᵥ (P.adjugate *ᵥ om)) • w from vecMulVec_mulVec_eq _ _ _,
      dotProduct_smul, smul_eq_mul]
    ring
  have hpolY : omy ⬝ᵥ (P.adjugate *ᵥ om) = 0 := by
    rw [homy, hom, hP, tripleGram_adjugate_polarization,
      dotProduct_comm (D.atom y) (D.atom x), hxy0, mul_zero]
  have hpolZ : omz ⬝ᵥ (P.adjugate *ᵥ om) = 0 := by
    rw [homz, hom, hP, tripleGram_adjugate_polarization,
      dotProduct_comm (D.atom z) (D.atom x), hxz0, mul_zero]
  have hnorm : om ⬝ᵥ (P.adjugate *ᵥ om) = P.det := by
    rw [hom, hP, tripleGram_adjugate_polarization, hxunit, mul_one]
  rw [hfac, hfac, hfac, hpolY, hpolZ, hnorm] at hread
  have hblock : om ⬝ᵥ ((P * T * P * P.adjugate) *ᵥ om)
      = P.det * (om ⬝ᵥ ((P * T) *ᵥ om)) := by
    rw [Matrix.mul_assoc (P * T) P P.adjugate, Matrix.mul_adjugate,
      Matrix.mul_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  have hrhs : om ⬝ᵥ ((P * P.adjugate) *ᵥ om) = P.det * (om ⬝ᵥ om) := by
    rw [Matrix.mul_adjugate, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.one_mulVec]
  rw [hblock, hrhs] at hread
  linarith [hread]

end Gtz
