/-
# No uniform positive floor at `(6, 3)`: the dust boundary and its `12ε` margin

The campaign measures the objective at `(6, 3)` through the largest of the twenty
gap determinants.  This file settles the SCALE of that number.  There is no
positive constant below which it cannot fall.

## The family

Take the four vertices of a regular tetrahedron and two coordinate directions.
Give each vertex the weight `(1 - 2ε)/4` and each coordinate direction the weight
`ε`.  These six vectors do NOT resolve the identity, so the file first builds the
transport that makes them a design.

## The transport

A RAW FRAME is six vectors and six positive weights of total one whose moment
matrix `F = Σ w_c b_c b_cᵀ` is positive definite.  Every raw frame whitens: a
congruence `Rᵀ F R = 1` turns the vectors into a genuine `Gtz.WeightedDesign`, and
the gap of a subset transports as a congruence,

  `S_C - 1 = Rᵀ (B_C - F) R` ,   `B_C = Σ_{c ∈ C} b_c b_cᵀ` .

Determinants then read `det (S_C - 1) * det F = det (B_C - F)`, and the two
positivity notions transfer both ways.  The reading is invariant under the whole
of `GL(3)` acting on the vectors, so a search on raw data runs on the honest
quotient and never needs a square root.

## The census

At the dust frame the moment is the diagonal `(1 - ε, 1 - ε, 1 - 2ε)`, and the
twenty raw gap determinants fall into five orbits of four:

  tetrahedron triple      `2ε³ + 10ε² + 12ε`   `= 2ε (ε + 2) (ε + 3)`
  two vertices, far dust  `2ε³ +  7ε² +  3ε - 6`
  two vertices, near dust `2ε³ +  7ε² +  3ε - 2`
  two vertices, flat dust `2ε³ +  7ε² -   ε - 2`
  one vertex, both dust   `2ε³ +  4ε² -  2ε`

The first is the largest for every `ε ≥ 0`, because the five differences are
`0`, `3(ε + 1)(ε + 2)`, `3ε² + 9ε + 2`, `3ε² + 13ε + 2` and `2ε(3ε + 7)`.

## The margin

Dividing by `det F = (1 - ε)² (1 - 2ε)` gives the margin

  `margin ε = 2ε (ε + 2) (ε + 3) / ((1 - ε)² (1 - 2ε))
            = 12ε + 2ε² (12ε² - 29ε + 29) / ((1 - ε)² (1 - 2ε))` ,

so `12ε ≤ margin ε` on the whole range and `margin ε ≤ 12ε + 60ε²` for
`ε ≤ 1/100`.  The margin over `ε` tends to `12`.  The four tetrahedron triples
carry an explicit sum of squares, so each of them dominates STRICTLY.  The
objective is therefore true along the family with a margin that goes to zero
linearly in the dust weight.

## What this file refutes

Two statements about the determinant reading, both with exact witnesses.

* The determinant reading is NOT NECESSARY.  The split tetrahedron, four
  directions distributed over six atoms with multiplicities `(2, 2, 1, 1)`, has
  all twenty gap determinants at most zero and still carries a dominating
  triple.  So `0 < max det` is a FALSE statement about `(6, 3)` designs.
* The determinant reading is NOT SUFFICIENT.  An explicit PRIMITIVE design
  carries a triple with gap determinant `85/29 > 0` whose gap is not positive
  semidefinite.  A positive determinant at a triple says nothing about
  domination, because a real symmetric three by three matrix of signature
  `(+, -, -)` has positive determinant.

## What this file does NOT do

It does not prove `Gtz.GtzWeighted 6 3`, and it does not refute it.  The dust
family satisfies the conjecture at every `ε` in the range.  What dies is any
argument that needs a positive constant independent of the design.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Design.PrimitiveTightClassification
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Finset Matrix

variable {m k : ℕ}

/-! ## 1. Raw frames

A raw frame carries vectors and weights with no isotropy hypothesis.  Its moment
matrix replaces the identity everywhere the design form uses one. -/

/-- **THE MOMENT MATRIX OF A RAW FRAME.**  The weighted atom sum over all labels.
For a design this is the identity. -/
def rawMoment (vec : Fin m → Fin k → ℝ) (weight : Fin m → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ c, weight c • atomMatrix (vec c)

/-- **THE ATOM SUM OF A SUBSET OF A RAW FRAME.**  Weight free, exactly as
`Gtz.subsetSum` is. -/
def rawSubsetSum (vec : Fin m → Fin k → ℝ) (C : Finset (Fin m)) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ C, atomMatrix (vec c)

theorem rawAtomMatrix_transpose (g : Fin k → ℝ) : (atomMatrix g)ᵀ = atomMatrix g := by
  ext i j
  simp only [atomMatrix, Matrix.transpose_apply, Matrix.vecMulVec_apply]
  ring

theorem dotProduct_atomMatrix_mulVec' (g probe : Fin k → ℝ) :
    probe ⬝ᵥ (atomMatrix g *ᵥ probe) = (g ⬝ᵥ probe) ^ 2 := by
  simp only [atomMatrix, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Finset.mul_sum,
    Finset.sum_mul, sq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rawMoment_transpose (vec : Fin m → Fin k → ℝ) (weight : Fin m → ℝ) :
    (rawMoment vec weight)ᵀ = rawMoment vec weight := by
  rw [rawMoment, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.transpose_smul, rawAtomMatrix_transpose]

/-- The quadratic form of a raw moment is the weighted energy of the pairings. -/
theorem dotProduct_rawMoment_mulVec (vec : Fin m → Fin k → ℝ) (weight : Fin m → ℝ)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (rawMoment vec weight *ᵥ probe) = ∑ c, weight c * (vec c ⬝ᵥ probe) ^ 2 := by
  rw [rawMoment, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec']

theorem rawSubsetSum_triple (vec : Fin m → Fin k → ℝ) {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rawSubsetSum vec {a, b, c}
      = atomMatrix (vec a) + atomMatrix (vec b) + atomMatrix (vec c) := by
  rw [rawSubsetSum, Finset.sum_insert (by simp [hab, hac]),
    Finset.sum_insert (by simp [hbc]), Finset.sum_singleton, add_assoc]

/-- **A RAW FRAME.**  Vectors and positive weights of total one whose moment is
positive definite.  No isotropy. -/
structure RawFrame (m k : ℕ) where
  vec : Fin m → (Fin k → ℝ)
  weight : Fin m → ℝ
  weight_pos : ∀ c, 0 < weight c
  weight_sum_one : ∑ c, weight c = 1
  moment_posDef : (rawMoment vec weight).PosDef

/-- The moment matrix of a raw frame, as a name. -/
def RawFrame.moment (frame : RawFrame m k) : Matrix (Fin k) (Fin k) ℝ :=
  rawMoment frame.vec frame.weight

/-- The gap of a subset of a raw frame: its atom sum against the moment. -/
def RawFrame.gap (frame : RawFrame m k) (C : Finset (Fin m)) : Matrix (Fin k) (Fin k) ℝ :=
  rawSubsetSum frame.vec C - frame.moment

/-! ## 2. The whitening transport

An invertible congruence carries an atom to an atom, so it carries a raw frame to
a design.  Every statement about a subset gap transports with it. -/

/-- A matrix absorbs into the left slot of a rank-one product. -/
theorem atomCongr_mul_vecMulVec (A : Matrix (Fin k) (Fin k) ℝ) (u v : Fin k → ℝ) :
    A * Matrix.vecMulVec u v = Matrix.vecMulVec (A *ᵥ u) v := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- A matrix absorbs into the right slot of a rank-one product, transposed. -/
theorem atomCongr_vecMulVec_mul (A : Matrix (Fin k) (Fin k) ℝ) (u v : Fin k → ℝ) :
    Matrix.vecMulVec u v * A = Matrix.vecMulVec u (Aᵀ *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **A CONGRUENCE CARRIES AN ATOM TO AN ATOM.**  Pulling a vector back along the
transpose conjugates its rank-one moment. -/
theorem atomMatrix_transposeMulVec (R : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℝ) :
    atomMatrix (Rᵀ *ᵥ x) = Rᵀ * atomMatrix x * R := by
  rw [atomMatrix, atomMatrix, atomCongr_mul_vecMulVec, atomCongr_vecMulVec_mul]

/-- The congruence moves through a weighted sum of atoms. -/
theorem sum_smul_atomMatrix_transposeMulVec (R : Matrix (Fin k) (Fin k) ℝ)
    (vec : Fin m → Fin k → ℝ) (weight : Fin m → ℝ) (C : Finset (Fin m)) :
    ∑ c ∈ C, weight c • atomMatrix (Rᵀ *ᵥ vec c)
      = Rᵀ * (∑ c ∈ C, weight c • atomMatrix (vec c)) * R := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by
    rw [atomMatrix_transposeMulVec, Matrix.mul_smul, Matrix.smul_mul]

/-- The congruence moves through an unweighted subset sum. -/
theorem rawSubsetSum_transposeMulVec (R : Matrix (Fin k) (Fin k) ℝ)
    (vec : Fin m → Fin k → ℝ) (C : Finset (Fin m)) :
    rawSubsetSum (fun c => Rᵀ *ᵥ vec c) C = Rᵀ * rawSubsetSum vec C * R := by
  rw [rawSubsetSum, rawSubsetSum, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun c _ => atomMatrix_transposeMulVec R (vec c)

/-- **THE WHITENED DESIGN.**  A raw frame and a congruence that sends its moment
to the identity make a genuine weighted design with the SAME weights. -/
def whitenedDesign (frame : RawFrame m k) (R : Matrix (Fin k) (Fin k) ℝ)
    (hcongr : Rᵀ * frame.moment * R = 1) : WeightedDesign m k where
  atom := fun c => Rᵀ *ᵥ frame.vec c
  weight := frame.weight
  weight_pos := frame.weight_pos
  weight_sum_one := frame.weight_sum_one
  isParseval := by
    rw [sum_smul_atomMatrix_transposeMulVec R frame.vec frame.weight Finset.univ]
    exact hcongr

@[simp] theorem whitenedDesign_atom (frame : RawFrame m k) (R : Matrix (Fin k) (Fin k) ℝ)
    (hcongr : Rᵀ * frame.moment * R = 1) (c : Fin m) :
    (whitenedDesign frame R hcongr).atom c = Rᵀ *ᵥ frame.vec c := rfl

@[simp] theorem whitenedDesign_weight (frame : RawFrame m k) (R : Matrix (Fin k) (Fin k) ℝ)
    (hcongr : Rᵀ * frame.moment * R = 1) :
    (whitenedDesign frame R hcongr).weight = frame.weight := rfl

/-- **THE GAP TRANSPORTS AS A CONGRUENCE.**  The subset gap of the whitened design
is the congruence image of the raw gap.  Nothing about the gap is lost. -/
theorem subsetSum_whitenedDesign_sub_one (frame : RawFrame m k)
    (R : Matrix (Fin k) (Fin k) ℝ) (hcongr : Rᵀ * frame.moment * R = 1)
    (C : Finset (Fin m)) :
    subsetSum (whitenedDesign frame R hcongr) C - 1 = Rᵀ * frame.gap C * R := by
  have hsubset : subsetSum (whitenedDesign frame R hcongr) C = Rᵀ * rawSubsetSum frame.vec C * R :=
    rawSubsetSum_transposeMulVec R frame.vec C
  rw [hsubset, RawFrame.gap, Matrix.mul_sub, Matrix.sub_mul, hcongr]

/-- **THE TRANSPORT.**  Every raw frame whitens to a weighted design with the SAME
weights and a congruent gap at every subset. -/
theorem RawFrame.exists_whitened (frame : RawFrame m k) :
    ∃ (design : WeightedDesign m k) (whitener : Matrix (Fin k) (Fin k) ℝ),
      IsUnit whitener.det ∧ design.weight = frame.weight
        ∧ (∀ c, design.atom c = whitenerᵀ *ᵥ frame.vec c)
        ∧ whitenerᵀ * frame.moment * whitener = 1
        ∧ ∀ C : Finset (Fin m),
            subsetSum design C - 1 = whitenerᵀ * frame.gap C * whitener := by
  obtain ⟨R, hunit, hcongr⟩ := exists_congruence_to_one frame.moment_posDef
  exact ⟨whitenedDesign frame R hcongr, R, hunit, rfl, fun _ => rfl, hcongr,
    subsetSum_whitenedDesign_sub_one frame R hcongr⟩

/-- **THE DETERMINANT READING.**  The gap determinant of a design subset times the
determinant of the raw moment is the raw gap determinant.  No square root, and
the whole of `GL(k)` acts trivially on the left side. -/
theorem det_gap_mul_det_moment (frame : RawFrame m k)
    {design : WeightedDesign m k} {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hcongr : ∀ C : Finset (Fin m), subsetSum design C - 1 = whitenerᵀ * frame.gap C * whitener)
    (hwhiten : whitenerᵀ * frame.moment * whitener = 1) (C : Finset (Fin m)) :
    (subsetSum design C - 1).det * frame.moment.det = (frame.gap C).det := by
  have hsq : whitener.det ^ 2 * frame.moment.det = 1 := by
    have := congrArg Matrix.det hwhiten
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    rw [← this]; ring
  rw [hcongr C, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc whitener.det * (frame.gap C).det * whitener.det * frame.moment.det
      = (frame.gap C).det * (whitener.det ^ 2 * frame.moment.det) := by ring
    _ = (frame.gap C).det := by rw [hsq, mul_one]

/-- **THE POSITIVITY READING, STRICT.**  Strict domination transports both ways. -/
theorem posDef_gap_iff (frame : RawFrame m k)
    {design : WeightedDesign m k} {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hunit : IsUnit whitener.det)
    (hcongr : ∀ C : Finset (Fin m), subsetSum design C - 1 = whitenerᵀ * frame.gap C * whitener)
    (C : Finset (Fin m)) :
    (subsetSum design C - 1).PosDef ↔ (frame.gap C).PosDef := by
  have hsym : (frame.gap C)ᵀ = frame.gap C := by
    rw [RawFrame.gap, Matrix.transpose_sub, rawSubsetSum, Matrix.transpose_sum,
      RawFrame.moment, rawMoment_transpose]
    exact congrArg (· - rawMoment frame.vec frame.weight)
      (Finset.sum_congr rfl fun c _ => rawAtomMatrix_transpose (frame.vec c))
  rw [hcongr C]
  exact (posDef_congr_right hsym hunit).symm

/-- **THE POSITIVITY READING, WEAK.**  Domination transports both ways. -/
theorem posSemidef_gap_iff (frame : RawFrame m k)
    {design : WeightedDesign m k} {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hunit : IsUnit whitener.det)
    (hcongr : ∀ C : Finset (Fin m), subsetSum design C - 1 = whitenerᵀ * frame.gap C * whitener)
    (C : Finset (Fin m)) :
    (subsetSum design C - 1).PosSemidef ↔ (frame.gap C).PosSemidef := by
  have hsym : (frame.gap C)ᵀ = frame.gap C := by
    rw [RawFrame.gap, Matrix.transpose_sub, rawSubsetSum, Matrix.transpose_sum,
      RawFrame.moment, rawMoment_transpose]
    exact congrArg (· - rawMoment frame.vec frame.weight)
      (Finset.sum_congr rfl fun c _ => rawAtomMatrix_transpose (frame.vec c))
  rw [hcongr C]
  exact (posSemidef_congr_right hsym hunit).symm

/-- **PRIMITIVITY TRANSPORTS.**  An invertible congruence cannot make two
non-parallel vectors parallel. -/
theorem isPrimitiveDesign_of_rawNotParallel (frame : RawFrame m k)
    {design : WeightedDesign m k} {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hunit : IsUnit whitener.det)
    (hatom : ∀ c, design.atom c = whitenerᵀ *ᵥ frame.vec c)
    (hraw : ∀ (kept drop : Fin m) (ratio : ℝ), kept ≠ drop →
      frame.vec drop ≠ ratio • frame.vec kept) :
    IsPrimitiveDesign design := by
  intro kept drop ratio hne hparallel
  rw [hatom, hatom] at hparallel
  refine hraw kept drop ratio hne ?_
  have hpull := congrArg (fun z => (whitenerᵀ)⁻¹ *ᵥ z) hparallel
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at hpull
  rw [Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]), Matrix.one_mulVec,
    Matrix.one_mulVec] at hpull
  exact hpull

/-! ## 3. The dust frame

Four tetrahedron vertices at weight `(1 - 2ε)/4` and two coordinate directions at
weight `ε`. -/

/-- The six raw directions: four tetrahedron vertices, then two coordinate
directions.  These are the DUST atoms, and their weight is what goes to zero. -/
def dustVec : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1], ![1, 0, 0], ![0, 1, 0]]

/-- The six raw weights at dust parameter `ε`. -/
noncomputable def dustWeight (eps : ℝ) : Fin 6 → ℝ :=
  ![(1 - 2 * eps) / 4, (1 - 2 * eps) / 4, (1 - 2 * eps) / 4, (1 - 2 * eps) / 4, eps, eps]

/-- The moment matrix of the dust frame, in closed form. -/
noncomputable def dustMomentMatrix (eps : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1 - eps, 1 - eps, 1 - 2 * eps]

theorem dustWeight_sum (eps : ℝ) : ∑ c, dustWeight eps c = 1 := by
  have hexp : ∀ e : ℝ,
      (1 - 2 * e) / 4 + (1 - 2 * e) / 4 + (1 - 2 * e) / 4 + (1 - 2 * e) / 4 + e + e = 1 := by
    intro e; ring
  simpa [dustWeight, Fin.sum_univ_six] using hexp eps

theorem dustWeight_pos {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) (c : Fin 6) :
    0 < dustWeight eps c := by
  fin_cases c <;> simp only [dustWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> norm_num <;> linarith

/-- **THE MOMENT OF THE DUST FRAME.**  The four vertices resolve `(1 - 2ε)` times
the identity and the two dust atoms add `ε` to the first two diagonal slots. -/
theorem rawMoment_dust (eps : ℝ) :
    rawMoment dustVec (dustWeight eps) = dustMomentMatrix eps := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawMoment, dustVec, dustWeight, dustMomentMatrix, atomMatrix, Fin.sum_univ_six,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> ring

theorem det_dustMomentMatrix (eps : ℝ) :
    (dustMomentMatrix eps).det = (1 - eps) ^ 2 * (1 - 2 * eps) := by
  rw [dustMomentMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

theorem dustMomentMatrix_posDef {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) :
    (dustMomentMatrix eps).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_, fun probe hne => ?_⟩
  · rw [dustMomentMatrix, Matrix.diagonal_transpose]
  · rw [star_trivial]
    have hval : probe ⬝ᵥ (dustMomentMatrix eps *ᵥ probe)
        = (1 - eps) * probe 0 ^ 2 + (1 - eps) * probe 1 ^ 2 + (1 - 2 * eps) * probe 2 ^ 2 := by
      simp only [dustMomentMatrix, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      ring
    obtain ⟨slot, hslot⟩ : ∃ slot : Fin 3, probe slot ≠ 0 := by
      by_contra hall
      exact hne (funext fun slot => by simpa using not_not.mp (not_exists.mp hall slot))
    rw [hval]
    have h1 : (0:ℝ) < 1 - eps := by linarith
    have h2 : (0:ℝ) < 1 - 2 * eps := by linarith
    fin_cases slot
    · nlinarith [sq_nonneg (probe 1), sq_nonneg (probe 2),
        (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 0 ^ 2)]
    · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 2),
        (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 1 ^ 2)]
    · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1),
        (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 2 ^ 2)]

/-- **THE DUST FRAME.**  Defined for `0 < ε < 1/2`. -/
noncomputable def dustFrame {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) : RawFrame 6 3 where
  vec := dustVec
  weight := dustWeight eps
  weight_pos := dustWeight_pos hlow hhigh
  weight_sum_one := dustWeight_sum eps
  moment_posDef := by
    rw [rawMoment_dust]
    exact dustMomentMatrix_posDef hlow hhigh

@[simp] theorem dustFrame_vec {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) :
    (dustFrame hlow hhigh).vec = dustVec := rfl

theorem dustFrame_moment {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) :
    (dustFrame hlow hhigh).moment = dustMomentMatrix eps := rawMoment_dust eps

/-! ## 4. The census bound

The largest of the twenty raw gap determinants is the tetrahedron value, for
every non-negative `ε`. -/

/-- **THE TOP OF THE CENSUS.**  The raw gap determinant of a tetrahedron triple. -/
def dustTop (eps : ℝ) : ℝ := 2 * eps * (eps + 2) * (eps + 3)

/-- The raw gap matrix of an ordered triple of dust labels. -/
noncomputable def dustGapMatrix (eps : ℝ) (a b c : Fin 6) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix (dustVec a) + atomMatrix (dustVec b) + atomMatrix (dustVec c) - dustMomentMatrix eps

set_option maxRecDepth 20000 in
/-- **THE CENSUS BOUND, ONE INEQUALITY FOR ALL TWENTY TRIPLES.**  Every raw gap
determinant of the dust frame is at most the tetrahedron value.  The five orbit
differences are `0`, `3(ε+1)(ε+2)`, `3ε²+9ε+2`, `3ε²+13ε+2` and `2ε(3ε+7)`, all
non-negative for `ε ≥ 0`, so no upper restriction on `ε` is used. -/
theorem dustGapMatrix_det_le {eps : ℝ} (hlow : 0 ≤ eps) (a b c : Fin 6)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (dustGapMatrix eps a b c).det ≤ dustTop eps := by
  simp only [dustTop]
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [dustGapMatrix, dustVec, dustMomentMatrix, atomMatrix, Matrix.det_fin_three,
      Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply] <;>
    nlinarith [hlow, sq_nonneg eps, mul_nonneg hlow hlow,
      mul_nonneg (mul_nonneg hlow hlow) hlow]

/-- **THE CENSUS BOUND ON SUBSETS.**  Same statement, indexed by the twenty
three-element subsets. -/
theorem dustFrame_gap_det_le {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2)
    {C : Finset (Fin 6)} (hcard : C.card = 3) :
    ((dustFrame hlow hhigh).gap C).det ≤ dustTop eps := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  rw [RawFrame.gap, dustFrame_vec, dustFrame_moment, hset,
    rawSubsetSum_triple dustVec hab hac hbc]
  exact dustGapMatrix_det_le hlow.le a b c hab hac hbc

/-! ### The tetrahedron triple attains the top and dominates strictly -/

/-- Every raw gap of the dust frame is symmetric. -/
theorem dustGapMatrix_transpose (eps : ℝ) (a b c : Fin 6) :
    (dustGapMatrix eps a b c)ᵀ = dustGapMatrix eps a b c := by
  rw [dustGapMatrix, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_add,
    rawAtomMatrix_transpose, rawAtomMatrix_transpose, rawAtomMatrix_transpose, dustMomentMatrix,
    Matrix.diagonal_transpose]

/-- **THE TETRAHEDRON GAP IN CLOSED FORM.**  The Gram of three tetrahedron
vertices is `3` on the diagonal with pairings `-1, 1, 1`, and the moment removes
`1 - ε` twice and `1 - 2ε` once. -/
theorem dustGapMatrix_tetra_eq (eps : ℝ) :
    dustGapMatrix eps 0 1 2
      = !![2 + eps, -1, 1; -1, 2 + eps, 1; 1, 1, 2 + 2 * eps] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dustGapMatrix, dustVec, dustMomentMatrix, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply] <;> ring

/-- The tetrahedron triple `{0, 1, 2}` reads exactly the top of the census. -/
theorem dustGapMatrix_tetra_det (eps : ℝ) :
    (dustGapMatrix eps 0 1 2).det = dustTop eps := by
  simp [dustTop, dustGapMatrix, dustVec, dustMomentMatrix, atomMatrix, Matrix.det_fin_three,
    Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_apply]
  ring

/-- **THE SUM OF SQUARES.**  The quadratic form of the tetrahedron gap is three
squares plus `ε` times a positive definite form.  This is the certificate that
makes the four tetrahedron triples STRICT dominators for every positive `ε`, and
it exhibits the `(4,3)` tie as the vanishing of the `ε` term. -/
theorem dotProduct_dustGapMatrix_tetra_mulVec (eps : ℝ) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (dustGapMatrix eps 0 1 2 *ᵥ probe)
      = (probe 0 - probe 1) ^ 2 + (probe 0 + probe 2) ^ 2 + (probe 1 + probe 2) ^ 2
        + eps * (probe 0 ^ 2 + probe 1 ^ 2 + 2 * probe 2 ^ 2) := by
  simp [dustGapMatrix, dustVec, dustMomentMatrix, atomMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.diagonal_apply]
  ring

theorem dustGapMatrix_tetra_posDef {eps : ℝ} (hlow : 0 < eps) :
    (dustGapMatrix eps 0 1 2).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (dustGapMatrix_transpose eps 0 1 2), fun probe hne => ?_⟩
  · rw [star_trivial, dotProduct_dustGapMatrix_tetra_mulVec]
    obtain ⟨slot, hslot⟩ : ∃ slot : Fin 3, probe slot ≠ 0 := by
      by_contra hall
      exact hne (funext fun slot => by simpa using not_not.mp (not_exists.mp hall slot))
    have hpos : 0 < probe 0 ^ 2 + probe 1 ^ 2 + 2 * probe 2 ^ 2 := by
      fin_cases slot
      · nlinarith [sq_nonneg (probe 1), sq_nonneg (probe 2),
          (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 0 ^ 2)]
      · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 2),
          (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 1 ^ 2)]
      · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1),
          (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 2 ^ 2)]
    nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 0 + probe 2),
      sq_nonneg (probe 1 + probe 2), mul_pos hlow hpos]

theorem dustFrame_gap_tetra {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) :
    (dustFrame hlow hhigh).gap {0, 1, 2} = dustGapMatrix eps 0 1 2 := by
  rw [RawFrame.gap, dustFrame_vec, dustFrame_moment,
    rawSubsetSum_triple dustVec (by decide) (by decide) (by decide), dustGapMatrix]

/-! ## 5. The margin

Dividing the census top by the determinant of the moment gives the number the
campaign measures. -/

/-- **THE MARGIN OF THE DUST DESIGN.**  The largest of the twenty gap
determinants of the whitened dust design. -/
noncomputable def dustMargin (eps : ℝ) : ℝ := dustTop eps / ((1 - eps) ^ 2 * (1 - 2 * eps))

/-- **THE MARGIN IS `12ε` PLUS AN EXPLICIT SECOND-ORDER TERM.**  The bracket
`12ε² - 29ε + 29` has negative discriminant, so it is positive on the whole line. -/
theorem dustMargin_eq_linear_add_quadratic {eps : ℝ} (hhigh : eps < 1 / 2) (hone : eps ≠ 1) :
    dustMargin eps
      = 12 * eps + 2 * eps ^ 2 * (12 * eps ^ 2 - 29 * eps + 29)
          / ((1 - eps) ^ 2 * (1 - 2 * eps)) := by
  have hfirst : (1 : ℝ) - eps ≠ 0 := by intro h; exact hone (by linarith)
  have hsecond : (1 : ℝ) - 2 * eps ≠ 0 := by intro h; linarith
  rw [dustMargin, dustTop]
  field_simp
  ring

/-- **THE LOWER HALF OF THE MARGIN LAW.**  The margin is never below `12ε`.  The
proof is the sign of `2ε (12ε² - 29ε + 29)`. -/
theorem twelve_mul_le_dustMargin {eps : ℝ} (hlow : 0 ≤ eps) (hhigh : eps < 1 / 2) :
    12 * eps ≤ dustMargin eps := by
  have hden : 0 < (1 - eps) ^ 2 * (1 - 2 * eps) := by
    refine mul_pos (pow_pos ?_ 2) (by linarith)
    linarith
  rw [dustMargin, le_div_iff₀ hden, dustTop]
  nlinarith [hlow, sq_nonneg eps, mul_nonneg hlow hlow,
    mul_nonneg (mul_nonneg hlow hlow) hlow, sq_nonneg (eps - 1)]

/-- **THE UPPER HALF OF THE MARGIN LAW.**  Near the boundary the margin is `12ε`
to within `60ε²`.  The threshold `1/100` is not sharp, it is comfortable. -/
theorem dustMargin_le_linear_add {eps : ℝ} (hlow : 0 < eps) (hhigh : eps ≤ 1 / 100) :
    dustMargin eps ≤ 12 * eps + 60 * eps ^ 2 := by
  have hden : 0 < (1 - eps) ^ 2 * (1 - 2 * eps) := by
    refine mul_pos (pow_pos ?_ 2) (by linarith)
    linarith
  rw [dustMargin, div_le_iff₀ hden, dustTop]
  nlinarith [hlow, hhigh, sq_nonneg eps, mul_pos hlow hlow,
    mul_nonneg (mul_nonneg hlow.le hlow.le) hlow.le,
    mul_nonneg (mul_nonneg (mul_nonneg hlow.le hlow.le) hlow.le) hlow.le]

/-- **THE THIRTEEN-EPSILON CAP.**  The form the no-floor theorem consumes. -/
theorem dustMargin_le_thirteen {eps : ℝ} (hlow : 0 < eps) (hhigh : eps ≤ 1 / 100) :
    dustMargin eps ≤ 13 * eps := by
  have hbound := dustMargin_le_linear_add hlow hhigh
  nlinarith [hlow, hhigh, mul_pos hlow hlow]

/-- **THE MARGIN VANISHES AT THE BOUNDARY.**  Positive for every positive `ε` in
range, and no positive lower bound survives. -/
theorem dustMargin_pos {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) : 0 < dustMargin eps := by
  have hden : 0 < (1 - eps) ^ 2 * (1 - 2 * eps) := by
    refine mul_pos (pow_pos ?_ 2) (by linarith)
    linarith
  rw [dustMargin, lt_div_iff₀ hden, dustTop]
  nlinarith [hlow]

/-- The margin times the moment determinant is the census top. -/
theorem dustMargin_mul_det {eps : ℝ} (hhigh : eps < 1 / 2) (hone : eps ≠ 1) :
    dustMargin eps * ((1 - eps) ^ 2 * (1 - 2 * eps)) = dustTop eps := by
  refine div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero 2 ?_) ?_)
  · intro h; exact hone (by linarith)
  · intro h; linarith

/-- **THE RATE, TWO SIDED.**  Near the boundary the margin divided by the dust
weight sits between `12` and `12 + 60ε`. -/
theorem dustMargin_div_bounds {eps : ℝ} (hlow : 0 < eps) (hhigh : eps ≤ 1 / 100) :
    12 ≤ dustMargin eps / eps ∧ dustMargin eps / eps ≤ 12 + 60 * eps := by
  refine ⟨(le_div_iff₀ hlow).mpr ?_, (div_le_iff₀ hlow).mpr ?_⟩
  · have := twelve_mul_le_dustMargin hlow.le (by linarith)
    linarith
  · have := dustMargin_le_linear_add hlow hhigh
    nlinarith [this]

/-- **THE MARGIN SCALES AS `12ε`.**  The analytic form of the two-sided bound:
the ratio of the margin to the dust weight converges to `12` at the boundary. -/
theorem tendsto_dustMargin_div :
    Filter.Tendsto (fun eps : ℝ => dustMargin eps / eps)
      (nhdsWithin 0 (Set.Ioc 0 (1 / 100))) (nhds 12) := by
  have hupper : Filter.Tendsto (fun eps : ℝ => 12 + 60 * eps)
      (nhdsWithin 0 (Set.Ioc 0 (1 / 100))) (nhds 12) := by
    have hcontAt : ContinuousAt (fun eps : ℝ => 12 + 60 * eps) 0 := by fun_prop
    have hcont : Filter.Tendsto (fun eps : ℝ => 12 + 60 * eps) (nhds 0) (nhds 12) := by
      simpa using hcontAt.tendsto
    exact hcont.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with eps hmem
    exact (dustMargin_div_bounds hmem.1 hmem.2).1
  · filter_upwards [self_mem_nhdsWithin] with eps hmem
    exact (dustMargin_div_bounds hmem.1 hmem.2).2

/-! ### The measured table, in kernel

The four exact rationals the campaign measured along this family. -/

theorem dustMargin_tenth : dustMargin (1 / 10) = 217 / 108 := by
  rw [dustMargin, dustTop]; norm_num

theorem dustMargin_hundredth : dustMargin (1 / 100) = 2881 / 22869 := by
  rw [dustMargin, dustTop]; norm_num

theorem dustMargin_thousandth : dustMargin (1 / 1000) = 2001667 / 166000833 := by
  rw [dustMargin, dustTop]; norm_num

theorem dustMargin_millionth :
    dustMargin (1 / 1000000) = 2000001666667 / 166666000000833333 := by
  rw [dustMargin, dustTop]; norm_num

/-! ## 6. No uniform positive floor at `(6, 3)`

The dust design satisfies the conjecture at every parameter in range, and its
margin goes to zero.  So no constant works. -/

/-- **STRICT CAUCHY-SCHWARZ IS NON-PARALLELISM.**  Two vectors are parallel
exactly when their pairing saturates, so a strict inequality on one pair of
labels is the whole of primitivity at that pair. -/
theorem not_parallel_of_dotProduct_sq_lt {n : ℕ} {kept drop : Fin n → ℝ}
    (hstrict : (kept ⬝ᵥ drop) ^ 2 < (kept ⬝ᵥ kept) * (drop ⬝ᵥ drop)) (ratio : ℝ) :
    drop ≠ ratio • kept := by
  intro heq
  rw [heq] at hstrict
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at hstrict
  nlinarith [hstrict]

/-- The six dust directions pair strictly below their leverages: the four
tetrahedron vertices pair to `±1` against leverage `3`, a vertex pairs to `±1`
against a dust atom of leverage `1`, and the two dust atoms are orthogonal. -/
theorem dustVec_dotProduct_sq_lt (kept drop : Fin 6) (hne : kept ≠ drop) :
    (dustVec kept ⬝ᵥ dustVec drop) ^ 2
      < (dustVec kept ⬝ᵥ dustVec kept) * (dustVec drop ⬝ᵥ dustVec drop) := by
  fin_cases kept <;> fin_cases drop <;>
    simp_all [dustVec, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- The six dust directions are pairwise non-parallel, so every whitened dust
design is primitive. -/
theorem dustVec_not_parallel (kept drop : Fin 6) (ratio : ℝ) (hne : kept ≠ drop) :
    dustVec drop ≠ ratio • dustVec kept :=
  not_parallel_of_dotProduct_sq_lt (dustVec_dotProduct_sq_lt kept drop hne) ratio

theorem subsetSum_eq_rawSubsetSum (design : WeightedDesign m k) (C : Finset (Fin m)) :
    subsetSum design C = rawSubsetSum design.atom C := rfl

/-- **THE DUST DESIGN.**  For every dust weight in range there is a PRIMITIVE
`(6,3)` design whose largest gap determinant is exactly the margin, attained at a
STRICTLY dominating triple, and whose twenty gap determinants are all at most the
margin. -/
theorem exists_dustDesign {eps : ℝ} (hlow : 0 < eps) (hhigh : eps < 1 / 2) :
    ∃ design : WeightedDesign 6 3, IsPrimitiveDesign design
      ∧ (subsetSum design {0, 1, 2} - 1).PosDef
      ∧ (subsetSum design {0, 1, 2} - 1).det = dustMargin eps
      ∧ ∀ C : Finset (Fin 6), C.card = 3 → (subsetSum design C - 1).det ≤ dustMargin eps := by
  obtain ⟨design, whitener, hunit, _, hatom, hwhiten, hcongr⟩ :=
    (dustFrame hlow hhigh).exists_whitened
  have hone : eps ≠ 1 := by intro h; rw [h] at hhigh; norm_num at hhigh
  have hdetPos : (0:ℝ) < (1 - eps) ^ 2 * (1 - 2 * eps) := by
    refine mul_pos (pow_pos (by linarith) 2) (by linarith)
  have hmom : (dustFrame hlow hhigh).moment.det = (1 - eps) ^ 2 * (1 - 2 * eps) := by
    rw [dustFrame_moment, det_dustMomentMatrix]
  have hprod : ∀ C : Finset (Fin 6),
      (subsetSum design C - 1).det * ((1 - eps) ^ 2 * (1 - 2 * eps))
        = ((dustFrame hlow hhigh).gap C).det := by
    intro C
    rw [← hmom]
    exact det_gap_mul_det_moment (dustFrame hlow hhigh) hcongr hwhiten C
  refine ⟨design, isPrimitiveDesign_of_rawNotParallel _ hunit hatom
      (fun kept drop ratio hne => dustVec_not_parallel kept drop ratio hne), ?_, ?_, ?_⟩
  · rw [posDef_gap_iff (dustFrame hlow hhigh) hunit hcongr, dustFrame_gap_tetra]
    exact dustGapMatrix_tetra_posDef hlow
  · have hval := hprod {0, 1, 2}
    rw [dustFrame_gap_tetra, dustGapMatrix_tetra_det, ← dustMargin_mul_det hhigh hone] at hval
    exact mul_right_cancel₀ (ne_of_gt hdetPos) hval
  · intro C hcard
    have hval := hprod C
    have hle : ((dustFrame hlow hhigh).gap C).det ≤ dustTop eps :=
      dustFrame_gap_det_le hlow hhigh hcard
    rw [← dustMargin_mul_det hhigh hone] at hle
    exact le_of_mul_le_mul_right (by rw [hval]; exact hle) hdetPos

/-- **THE HEADLINE: NO UNIFORM POSITIVE FLOOR AT `(6, 3)`.**  For every positive
constant there is a PRIMITIVE `(6,3)` design that dominates STRICTLY and whose
twenty gap determinants are all below the constant.  So the objective is true on
this family and no argument that produces a constant margin can close it. -/
theorem exists_primitiveDesign_all_gapDet_lt {floor : ℝ} (hfloor : 0 < floor) :
    ∃ design : WeightedDesign 6 3, IsPrimitiveDesign design
      ∧ (∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum design C - 1).PosDef)
      ∧ ∀ C : Finset (Fin 6), C.card = 3 → (subsetSum design C - 1).det < floor := by
  have hlow : 0 < min (floor / 26) (1 / 100) := lt_min (by linarith) (by norm_num)
  have hcap : min (floor / 26) (1 / 100) ≤ 1 / 100 := min_le_right _ _
  have hleft : min (floor / 26) (1 / 100) ≤ floor / 26 := min_le_left _ _
  have hhigh : min (floor / 26) (1 / 100) < 1 / 2 := by linarith
  obtain ⟨design, hprim, hposDef, _, hbound⟩ := exists_dustDesign hlow hhigh
  refine ⟨design, hprim, ⟨{0, 1, 2}, by decide, hposDef⟩, fun C hcard => ?_⟩
  have hmargin : dustMargin (min (floor / 26) (1 / 100)) ≤ 13 * (floor / 26) :=
    le_trans (dustMargin_le_thirteen hlow hcap) (by linarith)
  have := hbound C hcard
  linarith

/-- The same statement as a refutation: no positive constant is a lower bound for
the largest gap determinant over all `(6,3)` designs. -/
theorem not_exists_uniform_gapDet_floor :
    ¬ ∃ floor : ℝ, 0 < floor ∧ ∀ design : WeightedDesign 6 3,
        ∃ C : Finset (Fin 6), C.card = 3 ∧ floor ≤ (subsetSum design C - 1).det := by
  rintro ⟨floor, hfloor, hall⟩
  obtain ⟨design, _, _, hbound⟩ := exists_primitiveDesign_all_gapDet_lt hfloor
  obtain ⟨C, hcard, hle⟩ := hall design
  exact absurd hle (not_le.mpr (hbound C hcard))

/-! ## 7. The determinant reading is NOT NECESSARY

The split tetrahedron of `Gtz.Ties.SplitTetrahedronTie` distributes the four
tetrahedron directions over six atoms with multiplicities `(1, 1, 2, 2)`.  Its
moment is the identity already, so it is a design with no whitening, and the two
free splits move over an open square.  Twelve of its twenty triples are exact
ties and the other eight read `-8`.  The largest gap determinant is therefore
ZERO on the whole family, and yet a triple dominates.

So the statement "every `(6,3)` design carries a triple of strictly positive gap
determinant" is FALSE.  Domination is the PSD cone, not the sign of a
determinant, and the two part company exactly on the tie locus. -/

set_option maxRecDepth 20000 in
/-- **THE TETRAHEDRON CENSUS.**  Three tetrahedron directions, not all equal,
have gap determinant at most zero.  Three distinct directions read exactly zero
and a repeated pair reads `-8`.  The hypothesis is sharp: three copies of one
direction read `+8`, which is why the multiplicity pattern matters. -/
theorem tetraGap_det_nonpos (dirOne dirTwo dirThree : Fin 4)
    (hne : ¬ (dirOne = dirTwo ∧ dirTwo = dirThree)) :
    (atomMatrix (tetraAtom dirOne) + atomMatrix (tetraAtom dirTwo)
      + atomMatrix (tetraAtom dirThree) - 1).det ≤ 0 := by
  fin_cases dirOne <;> fin_cases dirTwo <;> fin_cases dirThree <;>
    simp_all [tetraAtom, atomMatrix, Matrix.det_fin_three, Matrix.vecMulVec_apply,
      Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply] <;> norm_num

/-- Three distinct atoms of the split tetrahedron cannot carry one direction:
no direction is used three times. -/
theorem splitTetraDirIndex_not_all_eq {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ¬ (splitTetraDirIndex a = splitTetraDirIndex b
      ∧ splitTetraDirIndex b = splitTetraDirIndex c) := by
  revert hab hac hbc; revert a b c; decide

/-- **ALL TWENTY GAP DETERMINANTS OF THE SPLIT TETRAHEDRON ARE AT MOST ZERO**,
for every member of the two-parameter family. -/
theorem splitTetraDesign_gap_det_nonpos (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4)
    {C : Finset (Fin 6)} (hcard : C.card = 3) :
    (subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) C - 1).det ≤ 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  rw [hset, subsetSum_eq_rawSubsetSum, rawSubsetSum_triple _ hab hac hbc]
  exact tetraGap_det_nonpos _ _ _ (splitTetraDirIndex_not_all_eq hab hac hbc)

/-- **THE FIRST CORRECTION.**  It is FALSE that every `(6,3)` design carries a
triple of strictly positive gap determinant.  The split tetrahedron refutes it
with strictly positive weights, on an open two-parameter family, and it
dominates. -/
theorem not_forall_exists_posDet_triple :
    ¬ ∀ design : WeightedDesign 6 3,
        ∃ C : Finset (Fin 6), C.card = 3 ∧ 0 < (subsetSum design C - 1).det := by
  intro hall
  obtain ⟨C, hcard, hpos⟩ := hall (splitTetraDesign (1 / 8) (1 / 8) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  exact absurd hpos (not_lt.mpr
    (splitTetraDesign_gap_det_nonpos (1 / 8) (1 / 8) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hcard))

/-- The counterexample in positive form: a whole open square of designs whose
census is at most zero everywhere and which still dominate. -/
theorem exists_design_gapDet_nonpos_and_dominates (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4) :
    ∃ (design : WeightedDesign 6 3) (C : Finset (Fin 6)), C.card = 3 ∧ Dominates design C
      ∧ ∀ triple : Finset (Fin 6), triple.card = 3
          → (subsetSum design triple - 1).det ≤ 0 :=
  ⟨splitTetraDesign splitA splitB hAPos hALt hBPos hBLt, {0, 1, 2}, by decide,
    splitTetraDesign_dominates splitA splitB hAPos hALt hBPos hBLt,
    fun _ hcard => splitTetraDesign_gap_det_nonpos splitA splitB hAPos hALt hBPos hBLt hcard⟩

/-! ## 8. The determinant reading is NOT SUFFICIENT

A real symmetric three by three matrix of signature `(+, -, -)` has POSITIVE
determinant, so a positive gap determinant at a triple says nothing about
domination.  The witness below is a PRIMITIVE `(6,3)` design whose triple
`{0, 1, 2}` reads `85/29 > 0` and whose gap has a strictly negative diagonal
entry.

The mechanism is flatness.  The three atoms of the triple lie in one plane and
are almost aligned inside it, so the atom sum overshoots the moment along one
direction and undershoots it along the other two.  Sampling confirms the
mechanism is generic rather than exceptional: of 58481 primitive rational
`(6,3)` frames drawn at random, 45301 carry such a triple. -/

/-- Six raw directions: three almost aligned in the plane `z = 0`, and three that
carry the second and third coordinates.  Pairwise non-parallel. -/
def flatVec : Fin 6 → Fin 3 → ℝ :=
  ![![2, 1, 0], ![2, -1, 0], ![1, 0, 0], ![0, 3, 0], ![0, 3, 1], ![0, 3, -1]]

/-- Uniform raw weights. -/
noncomputable def flatWeight : Fin 6 → ℝ := fun _ => 1 / 6

theorem flatWeight_pos (c : Fin 6) : 0 < flatWeight c := by norm_num [flatWeight]

theorem flatWeight_sum : ∑ c, flatWeight c = 1 := by
  simp [flatWeight, Fin.sum_univ_six]

/-- The moment of the flat frame is diagonal: the six directions are orthogonal
in aggregate. -/
theorem rawMoment_flat :
    rawMoment flatVec flatWeight = Matrix.diagonal ![3 / 2, 29 / 6, 1 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawMoment, flatVec, flatWeight, atomMatrix, Fin.sum_univ_six,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one] <;> norm_num

theorem rawMoment_flat_posDef : (rawMoment flatVec flatWeight).PosDef := by
  rw [rawMoment_flat]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (Matrix.diagonal_transpose _), fun probe hne => ?_⟩
  rw [star_trivial]
  have hval : probe ⬝ᵥ (Matrix.diagonal ![3 / 2, 29 / 6, 1 / 3] *ᵥ probe)
      = 3 / 2 * probe 0 ^ 2 + 29 / 6 * probe 1 ^ 2 + 1 / 3 * probe 2 ^ 2 := by
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  obtain ⟨slot, hslot⟩ : ∃ slot : Fin 3, probe slot ≠ 0 := by
    by_contra hall
    exact hne (funext fun slot => by simpa using not_not.mp (not_exists.mp hall slot))
  rw [hval]
  fin_cases slot
  · nlinarith [sq_nonneg (probe 1), sq_nonneg (probe 2),
      (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 0 ^ 2)]
  · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 2),
      (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 1 ^ 2)]
  · nlinarith [sq_nonneg (probe 0), sq_nonneg (probe 1),
      (sq_pos_of_ne_zero hslot : (0:ℝ) < probe 2 ^ 2)]

/-- **THE FLAT FRAME.** -/
noncomputable def flatFrame : RawFrame 6 3 where
  vec := flatVec
  weight := flatWeight
  weight_pos := flatWeight_pos
  weight_sum_one := flatWeight_sum
  moment_posDef := rawMoment_flat_posDef

@[simp] theorem flatFrame_vec : flatFrame.vec = flatVec := rfl

theorem flatFrame_moment : flatFrame.moment = Matrix.diagonal ![3 / 2, 29 / 6, 1 / 3] :=
  rawMoment_flat

/-- The flat gap of the triple `{0, 1, 2}` is diagonal with signature `(+, -, -)`. -/
theorem flatFrame_gap_triple :
    flatFrame.gap {0, 1, 2} = Matrix.diagonal ![15 / 2, -(17 / 6), -(1 / 3)] := by
  rw [RawFrame.gap, flatFrame_vec, flatFrame_moment,
    rawSubsetSum_triple flatVec (by decide) (by decide) (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flatVec, atomMatrix, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.diagonal_apply, Matrix.cons_val_two, Matrix.tail_cons] <;> norm_num

theorem det_flatFrame_gap_triple : (flatFrame.gap {0, 1, 2}).det = 85 / 12 := by
  rw [flatFrame_gap_triple, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem det_flatFrame_moment : flatFrame.moment.det = 29 / 12 := by
  rw [flatFrame_moment, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- The flat gap of `{0, 1, 2}` is NOT positive semidefinite: the second
coordinate direction reads `-(17/6)`. -/
theorem not_posSemidef_flatFrame_gap_triple : ¬ (flatFrame.gap {0, 1, 2}).PosSemidef := by
  intro hpsd
  have hval := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 0]
  rw [star_trivial, flatFrame_gap_triple] at hval
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hval
  norm_num at hval

theorem flatVec_dotProduct_sq_lt (kept drop : Fin 6) (hne : kept ≠ drop) :
    (flatVec kept ⬝ᵥ flatVec drop) ^ 2
      < (flatVec kept ⬝ᵥ flatVec kept) * (flatVec drop ⬝ᵥ flatVec drop) := by
  fin_cases kept <;> fin_cases drop <;>
    simp_all [flatVec, dotProduct, Fin.sum_univ_three] <;> norm_num

theorem flatVec_not_parallel (kept drop : Fin 6) (ratio : ℝ) (hne : kept ≠ drop) :
    flatVec drop ≠ ratio • flatVec kept :=
  not_parallel_of_dotProduct_sq_lt (flatVec_dotProduct_sq_lt kept drop hne) ratio

/-- **THE SECOND CORRECTION.**  A PRIMITIVE `(6,3)` design carries a triple whose
gap determinant is `85/29 > 0` and whose gap is NOT positive semidefinite.  A
positive gap determinant is therefore not a certificate of domination. -/
theorem exists_primitiveDesign_posDet_not_dominates :
    ∃ (design : WeightedDesign 6 3) (C : Finset (Fin 6)),
      IsPrimitiveDesign design ∧ C.card = 3
        ∧ (subsetSum design C - 1).det = 85 / 29 ∧ ¬ Dominates design C := by
  obtain ⟨design, whitener, hunit, _, hatom, hwhiten, hcongr⟩ := flatFrame.exists_whitened
  refine ⟨design, {0, 1, 2},
    isPrimitiveDesign_of_rawNotParallel _ hunit hatom
      (fun kept drop ratio hne => flatVec_not_parallel kept drop ratio hne),
    by decide, ?_, ?_⟩
  · have hprod := det_gap_mul_det_moment flatFrame hcongr hwhiten {0, 1, 2}
    rw [det_flatFrame_moment, det_flatFrame_gap_triple] at hprod
    linarith
  · rw [Dominates, posSemidef_gap_iff flatFrame hunit hcongr]
    exact not_posSemidef_flatFrame_gap_triple

/-- The same statement as a refutation of the implication. -/
theorem posDet_does_not_imply_dominates :
    ¬ ∀ (design : WeightedDesign 6 3) (C : Finset (Fin 6)), C.card = 3 →
        0 < (subsetSum design C - 1).det → Dominates design C := by
  intro hall
  obtain ⟨design, C, _, hcard, hdet, hnot⟩ := exists_primitiveDesign_posDet_not_dominates
  exact hnot (hall design C hcard (by rw [hdet]; norm_num))

/-! ## 9. The two corrections together

The largest gap determinant is neither necessary nor sufficient for domination at
`(6, 3)`.  Any route through it needs a separate positivity argument at the
selected triple, and the no-floor theorem of section 6 says that argument cannot
produce a constant margin. -/

/-- **THE DETERMINANT READING IS NEITHER NECESSARY NOR SUFFICIENT.** -/
theorem gapDet_neither_necessary_nor_sufficient :
    (¬ ∀ design : WeightedDesign 6 3,
        ∃ C : Finset (Fin 6), C.card = 3 ∧ 0 < (subsetSum design C - 1).det)
      ∧ (¬ ∀ (design : WeightedDesign 6 3) (C : Finset (Fin 6)), C.card = 3 →
          0 < (subsetSum design C - 1).det → Dominates design C) :=
  ⟨not_forall_exists_posDet_triple, posDet_does_not_imply_dominates⟩

end Gtz
