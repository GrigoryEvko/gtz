/-
# Phase rigidity: the third compound of the projection has rank one

The projection of a design is `Π = M Mᵀ` for the scaled frame `M`, an `m × 3`
matrix.  A `3 × 3` block of `Π` taken at ROW triple `C` and COLUMN triple `D`
is therefore a product of two SQUARE blocks of `M`,

  `Π[C,D] = M[C]·M[D]ᵀ` ,

and its determinant splits.  Each factor is the weighted bracket of its own
triple, so with `b_C := √(t_at_bt_c)·[abc]`:

  `det Π[C,D] = b_C·b_D`   (`Gtz.det_projectionBlock_pair`).

Every consequence below is that one factorization read differently.

* **THE RANK-ONE LAW** (`Gtz.bracketMass_phase_rigidity`):
  `(det Π[C,D])² = m_C·m_D`, where `m_C = t_at_bt_c·[abc]²` is the bracket mass
  of `Gtz.PairBracketMass`.  The third compound `Λ³Π` is the rank-one
  projection `bbᵀ`, its diagonal is the twenty bracket masses, and the bracket
  budget `Σm_C = 1` is exactly `|b| = 1`.  So the masses are a PROBABILITY
  DISTRIBUTION on the twenty triples and the off-diagonals are pinned to
  `±√(m_Cm_D)` — no freedom at all.

* **THE THREE-CYCLE LAW** (`Gtz.bracket_threeCycle`): any cycle of three
  off-diagonal blocks multiplies to a product of masses,
  `det Π[C,D]·det Π[D,E]·det Π[E,C] = m_C·m_D·m_E ≥ 0`.  This is the
  chirotope's content as a single identity, and it is the sharpest realness
  statement of the lane: over `ℝ` the cycle is a product of three squares and
  cannot be negative, while over `ℂ` the same algebra holds with the
  nonnegativity gone.  Realness is spent HERE and at
  `Gtz.pair_mass_nonneg`, nowhere else.

* **A VANISHING BRACKET EMPTIES ITS WHOLE ROW**
  (`Gtz.bracketMass_eq_zero_kills_row`): if one triple carries no bracket
  mass then every off-diagonal block through it is singular.  Since the hinge
  drives a PAIR mass to zero and a pair mass is the sum of its triples'
  masses, the hinge empties four rows at once at `(6,3)`.

The diagonal case `D = C` returns `Gtz.projectionBlock_det_eq`, so this is the
strict generalization of the bracket-mass calculus from one triple to two.
-/
import Gtz.Wave.PairMassRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The block factorization -/

/-- A rectangular block of the projection is the product of the two square
blocks of the scaled frame that carry its row and column triples. -/
theorem projectionBlock_pair_eq_mul (D : WeightedDesign m 3)
    (pickC pickD : Fin 3 → Fin m) :
    (projectionOfDesign D).submatrix pickC pickD
      = ((scaledAtomRows D).submatrix pickC id)
        * ((scaledAtomRows D).submatrix pickD id)ᵀ := by
  ext i j
  simp only [projectionOfDesign, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, id_eq]

/-- The determinant of a square block of the scaled frame is the weighted
bracket of its triple: the three row scalings come out as a product. -/
theorem det_scaledRows_block (D : WeightedDesign m 3) (pick : Fin 3 → Fin m) :
    ((scaledAtomRows D).submatrix pick id).det
      = Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 1))
        * Real.sqrt (D.weight (pick 2))
        * tripleBracket (D.atom (pick 0)) (D.atom (pick 1)) (D.atom (pick 2)) := by
  simp only [Matrix.det_fin_three, tripleBracket_eq, Matrix.submatrix_apply,
    scaledAtomRows, Matrix.of_apply, id_eq]
  ring

/-- **THE PAIRED BLOCK DETERMINANT.**  The determinant of the block of `Π` at
row triple `C` and column triple `D` is the product of the two weighted
brackets — the factorization every law below reads. -/
theorem det_projectionBlock_pair (D : WeightedDesign m 3)
    (pickC pickD : Fin 3 → Fin m) :
    ((projectionOfDesign D).submatrix pickC pickD).det
      = (Real.sqrt (D.weight (pickC 0)) * Real.sqrt (D.weight (pickC 1))
          * Real.sqrt (D.weight (pickC 2))
          * tripleBracket (D.atom (pickC 0)) (D.atom (pickC 1)) (D.atom (pickC 2)))
        * (Real.sqrt (D.weight (pickD 0)) * Real.sqrt (D.weight (pickD 1))
          * Real.sqrt (D.weight (pickD 2))
          * tripleBracket (D.atom (pickD 0)) (D.atom (pickD 1)) (D.atom (pickD 2))) := by
  rw [projectionBlock_pair_eq_mul, Matrix.det_mul, Matrix.det_transpose,
    det_scaledRows_block, det_scaledRows_block]

/-! ## 2. The rank-one law -/

/-- The square of a weighted bracket is the bracket mass of its triple. -/
theorem sq_weighted_bracket (D : WeightedDesign m 3) (pick : Fin 3 → Fin m) :
    (Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 1))
        * Real.sqrt (D.weight (pick 2))
        * tripleBracket (D.atom (pick 0)) (D.atom (pick 1)) (D.atom (pick 2))) ^ 2
      = D.weight (pick 0) * (D.weight (pick 1) * (D.weight (pick 2)
        * atomBracket D (pick 0) (pick 1) (pick 2) ^ 2)) := by
  have h0 : Real.sqrt (D.weight (pick 0)) ^ 2 = D.weight (pick 0) :=
    Real.sq_sqrt (D.weight_pos _).le
  have h1 : Real.sqrt (D.weight (pick 1)) ^ 2 = D.weight (pick 1) :=
    Real.sq_sqrt (D.weight_pos _).le
  have h2 : Real.sqrt (D.weight (pick 2)) ^ 2 = D.weight (pick 2) :=
    Real.sq_sqrt (D.weight_pos _).le
  rw [atomBracket]
  calc (Real.sqrt (D.weight (pick 0)) * Real.sqrt (D.weight (pick 1))
        * Real.sqrt (D.weight (pick 2))
        * tripleBracket (D.atom (pick 0)) (D.atom (pick 1)) (D.atom (pick 2))) ^ 2
      = Real.sqrt (D.weight (pick 0)) ^ 2 * (Real.sqrt (D.weight (pick 1)) ^ 2
          * (Real.sqrt (D.weight (pick 2)) ^ 2
            * tripleBracket (D.atom (pick 0)) (D.atom (pick 1))
                (D.atom (pick 2)) ^ 2)) := by ring
    _ = _ := by rw [h0, h1, h2]

/-- **PHASE RIGIDITY — THE RANK-ONE LAW OF THE THIRD COMPOUND.**  The squared
determinant of any paired block of the projection is the PRODUCT OF THE TWO
BRACKET MASSES:

  `(det Π[C,D])² = m_C·m_D` .

The third compound `Λ³Π` is therefore the rank-one projection `bbᵀ`: its
diagonal is the twenty bracket masses, its trace is the bracket budget one,
and every off-diagonal is pinned to `±√(m_Cm_D)`.  Over `ℂ` the same algebra
delivers only an inequality, because the two factors need not have equal
modulus — this identity is where the field enters the bracket calculus. -/
theorem bracketMass_phase_rigidity (D : WeightedDesign m 3)
    (pickC pickD : Fin 3 → Fin m) :
    (((projectionOfDesign D).submatrix pickC pickD).det) ^ 2
      = (D.weight (pickC 0) * (D.weight (pickC 1) * (D.weight (pickC 2)
          * atomBracket D (pickC 0) (pickC 1) (pickC 2) ^ 2)))
        * (D.weight (pickD 0) * (D.weight (pickD 1) * (D.weight (pickD 2)
          * atomBracket D (pickD 0) (pickD 1) (pickD 2) ^ 2))) := by
  rw [det_projectionBlock_pair, mul_pow, sq_weighted_bracket, sq_weighted_bracket]

/-- **THE THREE-CYCLE LAW — THE CHIROTOPE AS ONE IDENTITY.**  A cycle of three
paired blocks multiplies to the product of the three bracket masses:

  `det Π[C,D]·det Π[D,E]·det Π[E,C] = m_C·m_D·m_E` .

Each mass is a square, so over `ℝ` the cycle is NONNEGATIVE
(`Gtz.bracket_threeCycle_nonneg`).  That sign is the whole content of the
chirotope, and it is the sharpest field-sensitive statement of this lane: the
identity itself is field-blind, the nonnegativity is not. -/
theorem bracket_threeCycle (D : WeightedDesign m 3)
    (pickC pickD pickE : Fin 3 → Fin m) :
    ((projectionOfDesign D).submatrix pickC pickD).det
        * ((projectionOfDesign D).submatrix pickD pickE).det
        * ((projectionOfDesign D).submatrix pickE pickC).det
      = (D.weight (pickC 0) * (D.weight (pickC 1) * (D.weight (pickC 2)
          * atomBracket D (pickC 0) (pickC 1) (pickC 2) ^ 2)))
        * (D.weight (pickD 0) * (D.weight (pickD 1) * (D.weight (pickD 2)
          * atomBracket D (pickD 0) (pickD 1) (pickD 2) ^ 2)))
        * (D.weight (pickE 0) * (D.weight (pickE 1) * (D.weight (pickE 2)
          * atomBracket D (pickE 0) (pickE 1) (pickE 2) ^ 2))) := by
  rw [det_projectionBlock_pair, det_projectionBlock_pair, det_projectionBlock_pair,
    ← sq_weighted_bracket D pickC, ← sq_weighted_bracket D pickD,
    ← sq_weighted_bracket D pickE]
  ring

/-- **THE CYCLE IS NONNEGATIVE OVER `ℝ`.**  The realness carrier of the
bracket calculus, as `Gtz.pair_mass_nonneg` is the realness carrier of the
wedge calculus. -/
theorem bracket_threeCycle_nonneg (D : WeightedDesign m 3)
    (pickC pickD pickE : Fin 3 → Fin m) :
    0 ≤ ((projectionOfDesign D).submatrix pickC pickD).det
        * ((projectionOfDesign D).submatrix pickD pickE).det
        * ((projectionOfDesign D).submatrix pickE pickC).det := by
  rw [bracket_threeCycle]
  have hnn : ∀ pick : Fin 3 → Fin m, 0 ≤ D.weight (pick 0) * (D.weight (pick 1)
      * (D.weight (pick 2) * atomBracket D (pick 0) (pick 1) (pick 2) ^ 2)) :=
    fun pick => mul_nonneg (D.weight_pos _).le (mul_nonneg (D.weight_pos _).le
      (mul_nonneg (D.weight_pos _).le (sq_nonneg _)))
  exact mul_nonneg (mul_nonneg (hnn pickC) (hnn pickD)) (hnn pickE)

/-! ## 3. A vanishing bracket empties its row -/

/-- **A TRIPLE WITH NO BRACKET MASS MAKES EVERY BLOCK THROUGH IT SINGULAR.**
Rank one leaves no room: if the diagonal entry of `Λ³Π` at `C` vanishes then
the whole row does.  The hinge drives a PAIR mass to zero, and a pair mass is
the total of its triples' masses, so the hinge empties every row through that
pair at once. -/
theorem bracketMass_eq_zero_kills_row (D : WeightedDesign m 3)
    {pickC : Fin 3 → Fin m}
    (hzero : D.weight (pickC 0) * (D.weight (pickC 1) * (D.weight (pickC 2)
      * atomBracket D (pickC 0) (pickC 1) (pickC 2) ^ 2)) = 0)
    (pickD : Fin 3 → Fin m) :
    ((projectionOfDesign D).submatrix pickC pickD).det = 0 := by
  have hsq := bracketMass_phase_rigidity D pickC pickD
  rw [hzero, zero_mul] at hsq
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

/-- **THE BRACKET MASS IS A SQUARE.**  Every diagonal entry of the third
compound is the square of the weighted bracket, hence nonnegative: the twenty
masses are a nonnegative family totalling the bracket budget, so they are a
probability distribution on the triples. -/
theorem bracketMass_nonneg (D : WeightedDesign m 3) (a b c : Fin m) :
    0 ≤ D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2)) :=
  mul_nonneg (D.weight_pos a).le (mul_nonneg (D.weight_pos b).le
    (mul_nonneg (D.weight_pos c).le (sq_nonneg _)))

/-- **THE MASS OF A TRIPLE IS BELOW THE MASS OF ITS PAIR.**  A single triple's
bracket mass never exceeds the pair mass of any of its pairs, because the pair
mass totals the masses of ALL triples through that pair and every term is
nonnegative.  With `Gtz.isTie_lightest_pair_bracket_mass_cap` this transfers
the tie's pair cap to every individual triple through the lightest pair. -/
theorem bracketMass_le_pair_mass (D : WeightedDesign m 3) (a b c : Fin m) :
    D.weight a * (D.weight b * (D.weight c * atomBracket D a b c ^ 2))
      ≤ D.weight a * (D.weight b
        * (leverageOf (D.atom a) * leverageOf (D.atom b)
          - atomPairing D a b ^ 2)) := by
  classical
  rw [← pair_bracket_mass D a b]
  exact Finset.single_le_sum
    (fun e _ => bracketMass_nonneg D a b e) (Finset.mem_univ c)

end Gtz
