import Gtz.Wave.InvolutionBlockForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# Complementary cut selection at the balanced six-three cell

This module spends the involution block laws at the spectral parameter that
the cell actually asks for.

* `atomTripleDet_uniform_complement` upgrades the determinant-only Jacobi law
  to every spectral parameter.
* `atomShiftBlockDet_balanced_twin` shows that complementary shifted blocks
  carry the same square mass and opposite triangle cycle.
* `atomBalancedCutDetWin_iff` identifies the exact unsigned cut obstruction:
  `squareMass - 3 * |cycle| > 4/9`.
* `atomBalancedCutDetWin_of_sqSum_le` closes every cut whose internal squared
  doubled correlations total at most `4/9`.
* `exists_atomBalancedDetWin_of_heavyEdge` combines that cut law with the
  landed heavy-edge escape, closing the whole balanced heavy-edge region.
* `atomBalancedDetWin_of_subcritical` leaves only frames whose every distinct
  edge has squared doubled correlation strictly below `2/3`.
* The final matrix layer proves that this determinant conclusion is exactly
  the sharp `1/6` spectral floor and produces the carrier required by the
  atom cell.

All results are unconditional real linear algebra over the Parseval frame law.
-/

namespace Gtz

open Matrix

theorem det_mul_sub_scalar_comm_fin_three (A B : Matrix (Fin 3) (Fin 3) ℝ) (level : ℝ) :
    (A * B - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      (B * A - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
  have hchar := congrArg (Polynomial.eval level) (Matrix.charpoly_mul_comm A B)
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly] at hchar
  have hleft : (A * B - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)) =
      -((Matrix.scalar (Fin 3)) level - A * B) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  have hright : (B * A - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)) =
      -((Matrix.scalar (Fin 3)) level - B * A) := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  rw [hleft, hright, Matrix.det_neg, Matrix.det_neg]
  norm_num
  exact hchar

theorem det_scalar_sub_mul_comm_fin_three (A B : Matrix (Fin 3) (Fin 3) ℝ) (level : ℝ) :
    (level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A * B).det =
      (level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - B * A).det := by
  have hchar := congrArg (Polynomial.eval level) (Matrix.charpoly_mul_comm A B)
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly] at hchar
  have hleft : level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - A * B =
      (Matrix.scalar (Fin 3)) level - A * B := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  have hright : level • (1 : Matrix (Fin 3) (Fin 3) ℝ) - B * A =
      (Matrix.scalar (Fin 3)) level - B * A := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  rw [hleft, hright]
  exact hchar

theorem atomTripleRows_cut_split (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (σ : Equiv.Perm (Fin 6)) :
    (atomTripleRows atom (σ 0) (σ 1) (σ 2))ᵀ *
          atomTripleRows atom (σ 0) (σ 1) (σ 2)
      + (atomTripleRows atom (σ 3) (σ 4) (σ 5))ᵀ *
          atomTripleRows atom (σ 3) (σ 4) (σ 5) = 1 := by
  ext rowIndex colIndex
  rw [Matrix.add_apply, atomTripleRows_transpose_mul, atomTripleRows_transpose_mul]
  have hentry := atomFrame_entry atom hframe rowIndex colIndex
  have hperm : (∑ slot, atom slot rowIndex * atom slot colIndex)
      = ∑ k, atom (σ k) rowIndex * atom (σ k) colIndex :=
    (Equiv.sum_comp σ fun slot => atom slot rowIndex * atom slot colIndex).symm
  rw [hperm, Fin.sum_univ_six] at hentry
  have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex
      = if rowIndex = colIndex then 1 else 0 := Matrix.one_apply
  rw [hone]
  linarith

theorem atomTripleRows_shiftDet (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (level : ℝ) :
    (atomTripleRows atom slotOne slotTwo slotThree *
          (atomTripleRows atom slotOne slotTwo slotThree)ᵀ
        - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = atomTripleDet atom (fun _ => level) slotOne slotTwo slotThree := by
  have hvec0 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 0 = slotOne := rfl
  have hvec1 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 1 = slotTwo := rfl
  have hvec2 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 2 = slotThree := rfl
  rw [Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    atomTripleRows_mul_transpose, hvec0, hvec1, hvec2]
  norm_num [Fin.ext_iff]
  simp only [atomTripleDet, atomShiftedDiag]
  rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  ring

/-- The Jacobi block law at every spectral parameter. -/
theorem atomTripleDet_uniform_complement (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (σ : Equiv.Perm (Fin 6)) (level : ℝ) :
    atomTripleDet atom (fun _ => level) (σ 3) (σ 4) (σ 5)
      = (((1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
          - atomTripleRows atom (σ 0) (σ 1) (σ 2) *
              (atomTripleRows atom (σ 0) (σ 1) (σ 2))ᵀ).det := by
  let R := atomTripleRows atom (σ 0) (σ 1) (σ 2)
  let S := atomTripleRows atom (σ 3) (σ 4) (σ 5)
  have hsplit := atomTripleRows_cut_split atom hframe σ
  change Rᵀ * R + Sᵀ * S = 1 at hsplit
  have hS : Sᵀ * S = 1 - Rᵀ * R := by
    rw [← hsplit]
    abel
  rw [← atomTripleRows_shiftDet atom (σ 3) (σ 4) (σ 5) level]
  change (S * Sᵀ - level • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = _
  rw [det_mul_sub_scalar_comm_fin_three, hS]
  have hrearrange :
      (1 - Rᵀ * R - level • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        = (1 - level) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Rᵀ * R := by
    ext i j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> ring
  rw [hrearrange, det_scalar_sub_mul_comm_fin_three]

theorem atomShiftBlockDet_eq_atomTripleDet (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    atomShiftBlockDet atom slotOne slotTwo slotThree =
      atomTripleDet atom (fun _ => (1 : ℝ) / 6) slotOne slotTwo slotThree := by
  simp only [atomShiftBlockDet, atomTripleDet, atomShiftedDiag]

/-- The complementary shifted determinant reads the same three doubled
correlations with the cycle sign reversed. -/
theorem atomShiftBlockDet_balanced_twin (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6)) :
    216 * atomShiftBlockDet atom (σ 3) (σ 4) (σ 5)
      = 8 - 18 * ((2 * atomGram atom (σ 0) (σ 1)) ^ 2
            + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
            + (2 * atomGram atom (σ 1) (σ 2)) ^ 2)
        - 54 * ((2 * atomGram atom (σ 0) (σ 1))
            * (2 * atomGram atom (σ 0) (σ 2))
            * (2 * atomGram atom (σ 1) (σ 2))) := by
  have hvec0 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 0 = σ 0 := rfl
  have hvec1 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 1 = σ 1 := rfl
  have hvec2 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 2 = σ 2 := rfl
  have hcomp := atomTripleDet_uniform_complement atom hframe σ ((1 : ℝ) / 6)
  rw [← atomShiftBlockDet_eq_atomTripleDet] at hcomp
  rw [Matrix.det_fin_three] at hcomp
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    atomTripleRows_mul_transpose, hvec0, hvec1, hvec2] at hcomp
  norm_num [Fin.ext_iff] at hcomp
  rw [hbal (σ 0), hbal (σ 1), hbal (σ 2),
    atomGram_comm atom (σ 1) (σ 0), atomGram_comm atom (σ 2) (σ 0),
    atomGram_comm atom (σ 2) (σ 1)] at hcomp
  nlinarith

/-- **THE EXACT UNSIGNED CUT CRITERION.**  On a balanced frame, one side of
the cut has nonnegative shifted determinant exactly when the internal square
mass, reduced by three times the absolute cycle, is at most `4/9`.

The absolute value is not a relaxation: complementation reverses the cycle
and preserves the square mass, so it records the better of the two sides.
This is the sharp residual form for the balanced cell. -/
theorem atomBalancedCutDetWin_iff (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6)) :
    (0 ≤ atomShiftBlockDet atom (σ 0) (σ 1) (σ 2)
        ∨ 0 ≤ atomShiftBlockDet atom (σ 3) (σ 4) (σ 5))
      ↔ (2 * atomGram atom (σ 0) (σ 1)) ^ 2
          + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
          + (2 * atomGram atom (σ 1) (σ 2)) ^ 2
          - 3 * |(2 * atomGram atom (σ 0) (σ 1))
              * (2 * atomGram atom (σ 0) (σ 2))
              * (2 * atomGram atom (σ 1) (σ 2))| ≤ 4 / 9 := by
  let squareMass := (2 * atomGram atom (σ 0) (σ 1)) ^ 2
      + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
      + (2 * atomGram atom (σ 1) (σ 2)) ^ 2
  let cycle := (2 * atomGram atom (σ 0) (σ 1))
      * (2 * atomGram atom (σ 0) (σ 2))
      * (2 * atomGram atom (σ 1) (σ 2))
  have hleft :
      0 ≤ atomShiftBlockDet atom (σ 0) (σ 1) (σ 2)
        ↔ squareMass - 3 * cycle ≤ 4 / 9 := by
    simpa only [squareMass, cycle] using
      atomShiftBlockDet_balanced_nonneg_iff atom hbal (σ 0) (σ 1) (σ 2)
  have htwin := atomShiftBlockDet_balanced_twin atom hframe hbal σ
  have hright :
      0 ≤ atomShiftBlockDet atom (σ 3) (σ 4) (σ 5)
        ↔ squareMass + 3 * cycle ≤ 4 / 9 := by
    constructor <;> intro h
    · nlinarith
    · nlinarith
  rw [hleft, hright]
  by_cases hcycle : 0 ≤ cycle
  · rw [abs_of_nonneg hcycle]
    constructor
    · rintro (h | h) <;> nlinarith
    · intro h
      exact Or.inl h
  · have hcycle' : cycle ≤ 0 := le_of_not_ge hcycle
    rw [abs_of_nonpos hcycle']
    constructor
    · rintro (h | h) <;> nlinarith
    · intro h
      exact Or.inr (by nlinarith)

/-- A cut whose three internal squared doubled correlations total at most
`4/9` has a winning side.  The cycle chooses which side: the complementary
shifted determinant carries the opposite cycle sign. -/
theorem atomBalancedCutDetWin_of_sqSum_le (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6))
    (hsum : (2 * atomGram atom (σ 0) (σ 1)) ^ 2
          + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
          + (2 * atomGram atom (σ 1) (σ 2)) ^ 2 ≤ 4 / 9) :
    0 ≤ atomShiftBlockDet atom (σ 0) (σ 1) (σ 2)
      ∨ 0 ≤ atomShiftBlockDet atom (σ 3) (σ 4) (σ 5) := by
  let cycle := (2 * atomGram atom (σ 0) (σ 1))
      * (2 * atomGram atom (σ 0) (σ 2))
      * (2 * atomGram atom (σ 1) (σ 2))
  by_cases hcycle : 0 ≤ cycle
  · left
    rw [atomShiftBlockDet_balanced_nonneg_iff atom hbal]
    dsimp only [cycle] at hcycle
    nlinarith
  · right
    have htwin := atomShiftBlockDet_balanced_twin atom hframe hbal σ
    have hcycle' : cycle < 0 := lt_of_not_ge hcycle
    dsimp only [cycle] at hcycle'
    nlinarith

/-- Three pairwise distinct labels can be installed as the first three entries
of a permutation. -/
theorem exists_triplePerm {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree)
    (hthree : slotTwo ≠ slotThree) :
    ∃ σ : Equiv.Perm (Fin 6),
      σ 0 = slotOne ∧ σ 1 = slotTwo ∧ σ 2 = slotThree := by
  let source : Fin 3 → Fin 6 := ![0, 1, 2]
  let target : Fin 3 → Fin 6 := ![slotOne, slotTwo, slotThree]
  have hsource : Function.Injective source := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [source]
  have htarget : Function.Injective target := by
    have heno : slotTwo ≠ slotOne := Ne.symm hone
    have heot : slotThree ≠ slotOne := Ne.symm htwo
    have hett : slotThree ≠ slotTwo := Ne.symm hthree
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [target, hone, htwo, hthree, heno, heot, hett]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair source target hsource htarget
  refine ⟨σ, ?_, ?_, ?_⟩
  · simpa [source, target] using hσ 0
  · simpa [source, target] using hσ 1
  · simpa [source, target] using hσ 2

/-- **THE HEAVY-EDGE REGION IS CLOSED.**  A balanced frame containing an edge
whose squared doubled correlation is at least `2/3` has a triple with
nonnegative shifted determinant.  The row-law escape produces a cut with
square mass at most `4/9`; the full Jacobi law chooses the winning side. -/
theorem exists_atomBalancedDetWin_of_heavyEdge (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6))
    (hheavy : 2 / 3 ≤ (2 * atomGram atom (σ 0) (σ 1)) ^ 2) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 ≤ atomShiftBlockDet atom slotOne slotTwo slotThree := by
  obtain ⟨slotTwo, slotThree, htwoThree, hzeroTwo, hzeroThree, -, -, hsum⟩ :=
    atomHeavyEdgeEscape atom hframe hbal σ hheavy
  obtain ⟨cut, hcutZero, hcutOne, hcutTwo⟩ :=
    exists_triplePerm hzeroTwo hzeroThree htwoThree
  have hsumCut : (2 * atomGram atom (cut 0) (cut 1)) ^ 2
        + (2 * atomGram atom (cut 0) (cut 2)) ^ 2
        + (2 * atomGram atom (cut 1) (cut 2)) ^ 2 ≤ 4 / 9 := by
    simpa only [hcutZero, hcutOne, hcutTwo] using hsum
  rcases atomBalancedCutDetWin_of_sqSum_le atom hframe hbal cut hsumCut with hleft | hright
  · exact ⟨cut 0, cut 1, cut 2, cut.injective.ne (by decide),
      cut.injective.ne (by decide), cut.injective.ne (by decide), hleft⟩
  · exact ⟨cut 3, cut 4, cut 5, cut.injective.ne (by decide),
      cut.injective.ne (by decide), cut.injective.ne (by decide), hright⟩

/-- Pairwise-distinct two-point transitivity, used to state the heavy-edge
closure without a preselected relabelling. -/
theorem exists_pairPermOfDistinct {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo) :
    ∃ σ : Equiv.Perm (Fin 6), σ 0 = slotOne ∧ σ 1 = slotTwo := by
  let source : Fin 2 → Fin 6 := ![0, 1]
  let target : Fin 2 → Fin 6 := ![slotOne, slotTwo]
  have hsource : Function.Injective source := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [source]
  have htarget : Function.Injective target := by
    have hne' : slotTwo ≠ slotOne := Ne.symm hne
    intro i j
    fin_cases i <;> fin_cases j <;> simp [target, hne, hne']
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair source target hsource htarget
  exact ⟨σ, by simpa [source, target] using hσ 0,
    by simpa [source, target] using hσ 1⟩

theorem exists_atomBalancedDetWin_of_heavyPair (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (hheavy : 2 / 3 ≤ (2 * atomGram atom slotOne slotTwo) ^ 2) :
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 0 ≤ atomShiftBlockDet atom first second third := by
  obtain ⟨σ, hzero, hone⟩ := exists_pairPermOfDistinct hne
  apply exists_atomBalancedDetWin_of_heavyEdge atom hframe hbal σ
  simpa only [hzero, hone] using hheavy

/-- The strict subcritical residue of the balanced determinant problem.  Every
distinct edge has squared doubled correlation below `2/3`; the complementary
Jacobi argument has removed the entire opposite region. -/
def AtomBalancedSubcriticalDetWin : Prop :=
  ∀ atom : Fin 6 → (Fin 3 → ℝ),
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ y : Fin 6, atomGram atom y y = 1 / 2) →
    (∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      (2 * atomGram atom slotOne slotTwo) ^ 2 < 2 / 3) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 ≤ atomShiftBlockDet atom slotOne slotTwo slotThree

/-- Closing only the strict subcritical edge region closes the whole balanced
determinant target: heavy edges are unconditional by the preceding theorem. -/
theorem atomBalancedDetWin_of_subcritical
    (hsubcritical : AtomBalancedSubcriticalDetWin) : AtomBalancedDetWin := by
  intro atom hframe hbal
  by_cases hheavy : ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 2 / 3 ≤ (2 * atomGram atom slotOne slotTwo) ^ 2
  · obtain ⟨slotOne, slotTwo, hne, hlarge⟩ := hheavy
    exact exists_atomBalancedDetWin_of_heavyPair atom hframe hbal hne hlarge
  · apply hsubcritical atom hframe hbal
    intro slotOne slotTwo hne
    have hnot : ¬ 2 / 3 ≤ (2 * atomGram atom slotOne slotTwo) ^ 2 := by
      intro hlarge
      exact hheavy ⟨slotOne, slotTwo, hne, hlarge⟩
    exact lt_of_not_ge hnot

/-! ## The determinant target really is the balanced spectral target -/

/-- The shifted Gram matrix of a named triple at the mass-one scale `1/6`. -/
noncomputable def atomShiftBlockMatrix (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomTripleRows atom slotOne slotTwo slotThree *
      (atomTripleRows atom slotOne slotTwo slotThree)ᵀ
    - ((1 : ℝ) / 6) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

theorem atomShiftBlockMatrix_apply (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (i j : Fin 3) :
    atomShiftBlockMatrix atom slotOne slotTwo slotThree i j
      = atomGram atom (![slotOne, slotTwo, slotThree] i)
          (![slotOne, slotTwo, slotThree] j) - if i = j then (1 : ℝ) / 6 else 0 := by
  simp [atomShiftBlockMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    atomTripleRows_mul_transpose]

theorem atomShiftBlockMatrix_symmetric (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    (atomShiftBlockMatrix atom slotOne slotTwo slotThree)ᵀ
      = atomShiftBlockMatrix atom slotOne slotTwo slotThree := by
  ext i j
  rw [Matrix.transpose_apply, atomShiftBlockMatrix_apply, atomShiftBlockMatrix_apply,
    atomGram_comm]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Ne.symm hij]

theorem atomShiftBlockMatrix_first_balanced (atom : Fin 6 → (Fin 3 → ℝ))
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (slotOne slotTwo slotThree : Fin 6) :
    atomShiftBlockMatrix atom slotOne slotTwo slotThree 0 0
        + atomShiftBlockMatrix atom slotOne slotTwo slotThree 1 1
        + atomShiftBlockMatrix atom slotOne slotTwo slotThree 2 2 = 1 := by
  simp only [atomShiftBlockMatrix_apply]
  norm_num [Fin.ext_iff, hbal]

theorem atomShiftBlockMatrix_second_balanced (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree)
    (hthree : slotTwo ≠ slotThree) :
    1 / 12 ≤
      (atomShiftBlockMatrix atom slotOne slotTwo slotThree 0 0
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 1 1
        - atomShiftBlockMatrix atom slotOne slotTwo slotThree 0 1
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 1 0)
      + (atomShiftBlockMatrix atom slotOne slotTwo slotThree 0 0
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 2 2
        - atomShiftBlockMatrix atom slotOne slotTwo slotThree 0 2
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 2 0)
      + (atomShiftBlockMatrix atom slotOne slotTwo slotThree 1 1
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 2 2
        - atomShiftBlockMatrix atom slotOne slotTwo slotThree 1 2
          * atomShiftBlockMatrix atom slotOne slotTwo slotThree 2 1) := by
  have hvec0 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 0 = slotOne := rfl
  have hvec1 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 1 = slotTwo := rfl
  have hvec2 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 2 = slotThree := rfl
  obtain ⟨σ, hzero, hone', htwo'⟩ := exists_triplePerm hone htwo hthree
  have hsecond := atomBalancedShiftSecond atom hframe hbal σ
  simp only [hzero, hone', htwo'] at hsecond
  simp only [atomShiftBlockMatrix_apply, hvec0, hvec1, hvec2]
  norm_num [Fin.ext_iff]
  rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  simpa only [pow_two] using hsecond

theorem atomShiftBlockMatrix_det (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) :
    (atomShiftBlockMatrix atom slotOne slotTwo slotThree).det
      = atomShiftBlockDet atom slotOne slotTwo slotThree := by
  rw [atomShiftBlockMatrix, atomTripleRows_shiftDet,
    atomShiftBlockDet_eq_atomTripleDet]

/-- At balance the determinant is the only non-free elementary-symmetric leg:
nonnegative shifted determinant implies the whole shifted block is PSD. -/
theorem atomShiftBlockMatrix_posSemidef_of_balanced_det_nonneg
    (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree)
    (hthree : slotTwo ≠ slotThree)
    (hdet : 0 ≤ atomShiftBlockDet atom slotOne slotTwo slotThree) :
    (atomShiftBlockMatrix atom slotOne slotTwo slotThree).PosSemidef := by
  apply posSemidef_three_of_elementarySymmetric
  · exact atomShiftBlockMatrix_symmetric atom slotOne slotTwo slotThree
  · rw [atomShiftBlockMatrix_first_balanced atom hbal]
    norm_num
  · have hsecond := atomShiftBlockMatrix_second_balanced atom hframe hbal hone htwo hthree
    linarith
  · rw [atomShiftBlockMatrix_det]
    exact hdet

/-- The concrete spectral meaning of the determinant target: at balance, one
nonnegative shifted determinant supplies the sharp blend floor `1/6`. -/
theorem atomBlendFloor_sixth_of_balanced_det_nonneg
    (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    {slotOne slotTwo slotThree : Fin 6}
    (hone : slotOne ≠ slotTwo) (htwo : slotOne ≠ slotThree)
    (hthree : slotTwo ≠ slotThree)
    (hdet : 0 ≤ atomShiftBlockDet atom slotOne slotTwo slotThree) :
    AtomBlendFloor atom slotOne slotTwo slotThree (1 / 6) := by
  intro weightOne weightTwo weightThree
  let weights : Fin 3 → ℝ := ![weightOne, weightTwo, weightThree]
  have hpsd := atomShiftBlockMatrix_posSemidef_of_balanced_det_nonneg
    atom hframe hbal hone htwo hthree hdet
  have hquad := hpsd.dotProduct_mulVec_nonneg weights
  have hvec0 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 0 = slotOne := rfl
  have hvec1 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 1 = slotTwo := rfl
  have hvec2 : (![slotOne, slotTwo, slotThree] : Fin 3 → Fin 6) 2 = slotThree := rfl
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, atomShiftBlockMatrix_apply,
    hvec0, hvec1, hvec2, weights, star_id_of_comm] at hquad
  simp at hquad
  have henergy := atomSlotBlend_energy atom slotOne slotTwo slotThree
    weightOne weightTwo weightThree
  rw [henergy]
  rw [atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo] at hquad
  nlinarith

/-- `AtomBalancedDetWin` is not merely a determinant surrogate: it supplies
the exact sharp spectral floor on every balanced frame. -/
theorem exists_atomBlendFloor_sixth_of_balancedDetWin
    (hwin : AtomBalancedDetWin) (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ AtomBlendFloor atom slotOne slotTwo slotThree (1 / 6) := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hdet⟩ :=
    hwin atom hframe hbal
  exact ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree,
    atomBlendFloor_sixth_of_balanced_det_nonneg atom hframe hbal hone htwo hthree hdet⟩

/-- The heavy-edge closure already reaches the sharp spectral language used by
the cell, with no open proposition in its hypotheses. -/
theorem exists_atomBlendFloor_sixth_of_balanced_heavyEdge
    (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6))
    (hheavy : 2 / 3 ≤ (2 * atomGram atom (σ 0) (σ 1)) ^ 2) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ AtomBlendFloor atom slotOne slotTwo slotThree (1 / 6) := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hdet⟩ :=
    exists_atomBalancedDetWin_of_heavyEdge atom hframe hbal σ hheavy
  exact ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree,
    atomBlendFloor_sixth_of_balanced_det_nonneg atom hframe hbal hone htwo hthree hdet⟩

/-- The cell-level payoff of the heavy-edge theorem.  Every scale bounded by
`1/6` has a three-slot carrier whenever the balanced frame has a heavy edge. -/
theorem exists_atomCarrier_of_balanced_heavyEdge
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (hlight : ∀ slot, scale slot ≤ 1 / 6)
    (σ : Equiv.Perm (Fin 6))
    (hheavy : 2 / 3 ≤ (2 * atomGram atom (σ 0) (σ 1)) ^ 2) :
    ∃ car : Finset (Fin 6), car.card = 3
      ∧ ∀ probe : Fin 6 → ℝ, (∀ slot ∉ car, probe slot = 0) →
          (∑ slot, scale slot * probe slot ^ 2)
            ≤ atomBlend atom probe ⬝ᵥ atomBlend atom probe := by
  obtain ⟨slotOne, slotTwo, slotThree, hone, htwo, hthree, hfloor⟩ :=
    exists_atomBlendFloor_sixth_of_balanced_heavyEdge atom hframe hbal σ hheavy
  exact exists_atomCarrier_of_blendFloor atom scale hone htwo hthree hfloor hlight

end Gtz
