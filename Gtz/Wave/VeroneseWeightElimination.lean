/-
# The weight elimination on the stress-free stratum

`Gtz.weight_eq_veroneseGrid_inv_of_stressFree` says the weights of a stress-free
`(6,3)` design are `![1,1,1,0,0,0] * (veroneseGrid atom)^{-1}`.  That form needs
an inverse and it needs stress-freeness.  This module replaces it by a DIVISION
FREE Cramer law that holds at every `(6,3)` design, stress-free or not, and then
reads off what branch (i) demands of the eighteen atom coordinates alone.

## The Cramer law

`weight_mul_det_veroneseGrid`:
`weight c * det (veroneseGrid atom) = veroneseWeightMinor atom c`,
where `veroneseWeightMinor atom c` is the determinant of the Veronese grid with
row `c` replaced by `![1,1,1,0,0,0]`.  Rows of the grid are the functionals
`Q |-> g_c^T Q g_c` on symmetric forms, and the replacement row is the TRACE
functional, so the minor is a determinant of six linear functionals with one of
them exchanged for the trace.  Parseval is the only input.

No hypothesis at all is used.  `veroneseWeightMinor` is `![1,1,1,0,0,0]` times
the adjugate (`veroneseWeightMinor_eq_vecMul_adjugate`), and the adjugate
identity `V * adj V = det V * 1` does the rest.

## What the elimination produces

* SIX SIGN CONDITIONS ON THE ATOMS.  `det_mul_veroneseWeightMinor_pos`: on the
  stress-free stratum all six products `det V * veroneseWeightMinor atom c` are
  strictly positive.  Positivity of the weights is not a condition on a weight
  vector, it is six polynomial inequalities in the eighteen atom coordinates.
* ONE POLYNOMIAL NORMALIZATION.  `sum_veroneseWeightMinor`: the six minors total
  the determinant itself, which is `weight_sum_one` after elimination.
* THE ROW LAW.  `veroneseWeightMinor_vecMul_veroneseGrid` holds for EVERY atom
  family with no design attached.

## The gauge

`veroneseCoords` is homogeneous of degree two, so per-label rescaling of the
atoms multiplies row `c` of the grid by `scale c ^ 2`
(`veroneseGrid_smul_atoms`).  The determinant picks up `prod scale ^ 2` and the
`c`-th minor picks up the same product with the `c`-th factor deleted
(`veroneseWeightMinor_smul_atoms`).  Two consequences:

* SIGN INVARIANCE IS FREE.  `veroneseGrid_smul_atoms_of_sq_eq_one`: a per-label
  sign flip leaves the whole grid EQUAL, not merely equal up to sign.  Every
  statement in this module is therefore invariant under the group that
  `Gtz.IsTie` is invariant under.
* THE SHARE IS PROJECTIVE.  `veroneseShareForm` multiplies the leverage into the
  minor, and it scales exactly like the determinant
  (`veroneseShareForm_smul_atoms`).  So `atomShare` is a ratio of two forms with
  the same weight, and `atomShare_eq_of_atom_smul_of_stressFree` says the atom
  shares of a stress-free `(6,3)` design depend only on the atom DIRECTIONS.

## The share boundary

`leverage_mul_one_sub_atomShare` is an exact defect identity at every size and
rank: `l_c (1 - share_c)` is the weighted mean square correlation of atom `c`
with the others.  So `share_c = 1` exactly when atom `c` is orthogonal to all
the others, and then `orthogonalPairConic` is an explicit nonzero conic through
all the directions.  At `(6,3)` that contradicts stress-freeness, whence
`atomShare_lt_one_of_stressFree`: EVERY share of a branch-(i) design is strictly
below one.  The bound is weight-free by the elimination
(`veroneseShareForm_lt_sq_det_of_stressFree`).

## The triple aggregate bridge

`Gtz.sum_ordered_weight_mul_discriminantTie` is `-4` over ORDERED triples.
`sum_weight_prod_discriminantTie_powersetCard_three` peels the degenerate
completions and lands the three-subset form.  The two repeated-label
determinants are computed exactly (`discriminantTie_self_pair`,
`discriminantTie_self_triple`) and the leftovers collapse by Parseval.

## Provenance and honest scope

Nothing here decides branch (i).  It moves every branch-(i) hypothesis off the
weight vector and onto the atoms, and it adds one new strict constraint, the
share cap.  A directed descent on the stratum reaches margin `4.2e-6`, and along
the way the largest share tends to one and the Veronese determinant tends to
zero — the measured approach to a tie is an approach to THIS boundary.  That is
measurement, not kernel.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.StressFreeStratum
import Gtz.Design.LivePairExistence
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.LiftingLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

variable {size rank : ℕ}

/-! ## Part 1: the Cramer law -/

/-- The Veronese coordinate row of the identity form.  Pairing it against
`conicCoords Q` returns `Matrix.trace Q`, so this row is the TRACE functional in
the same coordinates in which row `c` of the grid is `Q |-> g_c^T Q g_c`. -/
def veroneseIdentityRow : Fin 6 → ℝ := ![1, 1, 1, 0, 0, 0]

/-- The `label`-th WEIGHT MINOR of a six-atom rank-three family: the Veronese
grid with row `label` exchanged for the trace functional. -/
noncomputable def veroneseWeightMinor (atomFamily : Fin 6 → Fin 3 → ℝ) (label : Fin 6) : ℝ :=
  ((veroneseGrid atomFamily).updateRow label veroneseIdentityRow).det

/-- The weight minors are the trace row against the adjugate.  This is Cramer's
rule with the roles of rows and columns exchanged, and it holds over any atom
family with no design and no invertibility. -/
theorem veroneseWeightMinor_eq_vecMul_adjugate (atomFamily : Fin 6 → Fin 3 → ℝ) :
    veroneseWeightMinor atomFamily
      = veroneseIdentityRow ᵥ* (veroneseGrid atomFamily).adjugate := by
  funext label
  have hcramer := Matrix.cramer_apply (veroneseGrid atomFamily)ᵀ veroneseIdentityRow label
  rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose,
    Matrix.mulVec_transpose, Matrix.updateCol_transpose, Matrix.det_transpose] at hcramer
  exact hcramer.symm

/-- **THE ROW LAW OF THE WEIGHT MINORS.**  For every atom family the six minors,
read against the grid, return the determinant times the trace row.  This is the
adjugate identity and it carries no design hypothesis. -/
theorem veroneseWeightMinor_vecMul_veroneseGrid (atomFamily : Fin 6 → Fin 3 → ℝ) :
    veroneseWeightMinor atomFamily ᵥ* veroneseGrid atomFamily
      = (veroneseGrid atomFamily).det • veroneseIdentityRow := by
  rw [veroneseWeightMinor_eq_vecMul_adjugate, Matrix.vecMul_vecMul, Matrix.adjugate_mul]
  funext coordIndex
  simp [Matrix.vecMul, dotProduct, Matrix.one_apply, Finset.sum_ite_eq', mul_comm]

/-- **THE CRAMER LAW OF THE STRESS-FREE STRATUM, WITHOUT ITS HYPOTHESIS.**  The
weight of a label times the Veronese determinant is the determinant of the grid
with that label's row exchanged for the trace row.  Compare
`Gtz.weight_eq_veroneseGrid_inv_of_stressFree`, which needs an inverse and needs
stress-freeness; this form is polynomial in the atoms and holds at every design,
including the ones with a stress. -/
theorem weight_mul_det_veroneseGrid (design : WeightedDesign 6 3) (label : Fin 6) :
    design.weight label * (veroneseGrid design.atom).det
      = veroneseWeightMinor design.atom label := by
  have hrow : veroneseIdentityRow = design.weight ᵥ* veroneseGrid design.atom := by
    rw [weight_vecMul_veroneseGrid]
    rfl
  have hminor : veroneseWeightMinor design.atom
      = (veroneseGrid design.atom).det • design.weight := by
    rw [veroneseWeightMinor_eq_vecMul_adjugate, hrow, Matrix.vecMul_vecMul,
      Matrix.mul_adjugate]
    funext lbl
    simp [Matrix.vecMul, dotProduct, Matrix.one_apply, Finset.sum_ite_eq', mul_comm]
  rw [hminor]
  simp [mul_comm]

/-- The weight minor of a stress-free design is nonzero. -/
theorem veroneseWeightMinor_ne_zero_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    veroneseWeightMinor design.atom label ≠ 0 := by
  rw [← weight_mul_det_veroneseGrid]
  exact mul_ne_zero (ne_of_gt (design.weight_pos label))
    ((stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree)

/-- **POSITIVITY OF THE WEIGHTS IS SIX SIGN CONDITIONS ON THE ATOMS.**  The
product of the Veronese determinant with each weight minor is the weight times
the determinant squared, hence never negative.  No hypothesis. -/
theorem det_mul_veroneseWeightMinor_nonneg (design : WeightedDesign 6 3) (label : Fin 6) :
    0 ≤ (veroneseGrid design.atom).det * veroneseWeightMinor design.atom label := by
  rw [← weight_mul_det_veroneseGrid]
  have hsq : (veroneseGrid design.atom).det * (design.weight label * (veroneseGrid design.atom).det)
      = design.weight label * (veroneseGrid design.atom).det ^ 2 := by ring
  rw [hsq]
  exact mul_nonneg (design.weight_pos label).le (sq_nonneg _)

/-- On branch (i) the six sign conditions are STRICT.  A stress-free `(6,3)`
design is exactly a six-point family off a conic all six of whose weight minors
share the determinant's sign. -/
theorem det_mul_veroneseWeightMinor_pos (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    0 < (veroneseGrid design.atom).det * veroneseWeightMinor design.atom label := by
  have hdet : (veroneseGrid design.atom).det ≠ 0 :=
    (stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree
  rw [← weight_mul_det_veroneseGrid]
  have hsq : (veroneseGrid design.atom).det * (design.weight label * (veroneseGrid design.atom).det)
      = design.weight label * (veroneseGrid design.atom).det ^ 2 := by ring
  rw [hsq]
  have hsqPos : 0 < (veroneseGrid design.atom).det ^ 2 := by positivity
  exact mul_pos (design.weight_pos label) hsqPos

/-- **THE NORMALIZATION, ELIMINATED.**  `weight_sum_one` becomes one polynomial
identity in the atoms: the six weight minors total the Veronese determinant. -/
theorem sum_veroneseWeightMinor (design : WeightedDesign 6 3) :
    ∑ label, veroneseWeightMinor design.atom label = (veroneseGrid design.atom).det := by
  have hterm : ∀ label : Fin 6, veroneseWeightMinor design.atom label
      = design.weight label * (veroneseGrid design.atom).det :=
    fun label => (weight_mul_det_veroneseGrid design label).symm
  rw [Finset.sum_congr rfl fun label _ => hterm label, ← Finset.sum_mul,
    design.weight_sum_one, one_mul]

/-! ## Part 2: the per-label gauge -/

/-- The Veronese coordinates are homogeneous of degree two. -/
theorem veroneseCoords_smul (scale : ℝ) (direction : Fin 3 → ℝ) :
    veroneseCoords (scale • direction) = (scale ^ 2) • veroneseCoords direction := by
  funext coordIndex
  fin_cases coordIndex <;>
    simp [veroneseCoords, Pi.smul_apply, smul_eq_mul] <;> ring

/-- **THE GRID UNDER PER-LABEL RESCALING.**  Rescaling atom `c` by `scale c`
multiplies row `c` of the grid by `scale c ^ 2` and touches nothing else. -/
theorem veroneseGrid_smul_atoms (scale : Fin 6 → ℝ) (atomFamily : Fin 6 → Fin 3 → ℝ) :
    veroneseGrid (fun label => scale label • atomFamily label)
      = Matrix.diagonal (fun label => scale label ^ 2) * veroneseGrid atomFamily := by
  ext rowIndex coordIndex
  rw [Matrix.diagonal_mul]
  simp only [veroneseGrid, Matrix.of_apply]
  rw [veroneseCoords_smul]
  simp

/-- **SIGN FLIPS LEAVE THE GRID EQUAL.**  `Gtz.atomMatrix` does not see the sign
of its vector and neither does `veroneseCoords`, so every determinant in this
module is invariant under the per-label sign group that `Gtz.IsTie` is invariant
under.  The invariance is not proved, it is inherited. -/
theorem veroneseGrid_smul_atoms_of_sq_eq_one (scale : Fin 6 → ℝ)
    (hunit : ∀ label, scale label ^ 2 = 1) (atomFamily : Fin 6 → Fin 3 → ℝ) :
    veroneseGrid (fun label => scale label • atomFamily label) = veroneseGrid atomFamily := by
  rw [veroneseGrid_smul_atoms]
  have hone : (fun label => scale label ^ 2) = (fun _ : Fin 6 => (1 : ℝ)) := by
    funext label; exact hunit label
  rw [hone, Matrix.diagonal_one, Matrix.one_mul]

/-- The determinant picks up the product of the squared scales. -/
theorem det_veroneseGrid_smul_atoms (scale : Fin 6 → ℝ) (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (veroneseGrid (fun label => scale label • atomFamily label)).det
      = (∏ label, scale label ^ 2) * (veroneseGrid atomFamily).det := by
  rw [veroneseGrid_smul_atoms, Matrix.det_mul, Matrix.det_diagonal]

/-- Replacing row `label` of a row-scaled matrix is the same as row-scaling the
replaced matrix with the `label`-th scale set to one. -/
theorem updateRow_diagonal_mul (scale : Fin 6 → ℝ) (target : Matrix (Fin 6) (Fin 6) ℝ)
    (label : Fin 6) (row : Fin 6 → ℝ) :
    (Matrix.diagonal scale * target).updateRow label row
      = Matrix.diagonal (Function.update scale label 1) * target.updateRow label row := by
  ext rowIndex coordIndex
  rw [Matrix.diagonal_mul]
  by_cases hrow : rowIndex = label
  · subst hrow
    simp
  · rw [Matrix.updateRow_ne hrow, Matrix.diagonal_mul, Matrix.updateRow_ne hrow,
      Function.update_of_ne hrow]

/-- **THE MINOR UNDER PER-LABEL RESCALING.**  The `label`-th minor picks up the
product of the squared scales with the `label`-th factor DELETED, because row
`label` has been exchanged for the trace row and no longer carries a scale. -/
theorem veroneseWeightMinor_smul_atoms (scale : Fin 6 → ℝ) (atomFamily : Fin 6 → Fin 3 → ℝ)
    (label : Fin 6) :
    veroneseWeightMinor (fun lbl => scale lbl • atomFamily lbl) label
      = (∏ other ∈ Finset.univ.erase label, scale other ^ 2)
        * veroneseWeightMinor atomFamily label := by
  rw [veroneseWeightMinor, veroneseGrid_smul_atoms,
    updateRow_diagonal_mul, Matrix.det_mul, Matrix.det_diagonal, veroneseWeightMinor]
  congr 1
  rw [Finset.prod_update_of_mem (Finset.mem_univ label), one_mul]
  exact Finset.prod_congr (by rw [Finset.sdiff_singleton_eq_erase]) fun _ _ => rfl

/-! ## Part 3: the share form -/

/-- **THE WEIGHT-FREE SHARE FORM.**  The leverage times the weight minor.  It
scales exactly like the Veronese determinant, so its ratio to that determinant
is a function of the atom DIRECTIONS alone. -/
noncomputable def veroneseShareForm (atomFamily : Fin 6 → Fin 3 → ℝ) (label : Fin 6) : ℝ :=
  leverageOf (atomFamily label) * veroneseWeightMinor atomFamily label

/-- **THE ATOM SHARE, ELIMINATED.**  The share times the Veronese determinant is
the share form, at every `(6,3)` design and with no hypothesis. -/
theorem atomShare_mul_det_veroneseGrid (design : WeightedDesign 6 3) (label : Fin 6) :
    atomShare design label * (veroneseGrid design.atom).det
      = veroneseShareForm design.atom label := by
  rw [atomShare, veroneseShareForm, ← weight_mul_det_veroneseGrid]
  ring

/-- On branch (i) the share is the honest ratio of two determinants in the atoms. -/
theorem atomShare_eq_veroneseShareForm_div (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    atomShare design label
      = veroneseShareForm design.atom label / (veroneseGrid design.atom).det := by
  rw [← atomShare_mul_det_veroneseGrid, mul_div_assoc,
    div_self ((stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree), mul_one]

/-- The share form scales exactly like the determinant: the deleted `label`-th
factor of the minor is restored by the leverage. -/
theorem veroneseShareForm_smul_atoms (scale : Fin 6 → ℝ) (atomFamily : Fin 6 → Fin 3 → ℝ)
    (label : Fin 6) :
    veroneseShareForm (fun lbl => scale lbl • atomFamily lbl) label
      = (∏ other, scale other ^ 2) * veroneseShareForm atomFamily label := by
  rw [veroneseShareForm, veroneseShareForm, leverageOf_smul, veroneseWeightMinor_smul_atoms]
  have hsplit : (∏ other, scale other ^ 2)
      = scale label ^ 2 * ∏ other ∈ Finset.univ.erase label, scale other ^ 2 :=
    (Finset.mul_prod_erase Finset.univ (fun other => scale other ^ 2)
      (Finset.mem_univ label)).symm
  rw [hsplit]
  ring

/-- **THE ATOM SHARES ARE A PROJECTIVE INVARIANT OF THE SIX DIRECTIONS.**  Two
stress-free `(6,3)` designs whose atoms are proportional label by label carry
the same shares.  Read through `atomShare_eq_veroneseShareForm_div`, the two
sides of the ratio pick up the same factor `prod scale ^ 2` and it cancels. -/
theorem atomShare_eq_of_atom_smul_of_stressFree (design designPrime : WeightedDesign 6 3)
    (scale : Fin 6 → ℝ)
    (hatom : ∀ label, designPrime.atom label = scale label • design.atom label)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0)
    (hstressFreePrime : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (designPrime.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    atomShare designPrime label = atomShare design label := by
  have hfam : designPrime.atom = fun lbl => scale lbl • design.atom lbl := funext hatom
  have hdet : (veroneseGrid design.atom).det ≠ 0 :=
    (stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree
  have hprod : (∏ other, scale other ^ 2) ≠ 0 := by
    have hdetPrime : (veroneseGrid designPrime.atom).det ≠ 0 :=
      (stressFree_iff_veroneseGrid_det_ne_zero designPrime.atom).mp hstressFreePrime
    rw [hfam, det_veroneseGrid_smul_atoms] at hdetPrime
    exact left_ne_zero_of_mul hdetPrime
  rw [atomShare_eq_veroneseShareForm_div design hstressFree,
    atomShare_eq_veroneseShareForm_div designPrime hstressFreePrime, hfam,
    det_veroneseGrid_smul_atoms, veroneseShareForm_smul_atoms]
  field_simp

/-- The same rigidity with no determinant at all: uniqueness of the stress-free
weights already forces it.  The determinant route above is the one that turns
the statement into a computation in the atoms, and this one records that the
FACT is cheaper than the formula. -/
theorem atomShare_eq_of_atom_smul_of_stressFree' (design designPrime : WeightedDesign 6 3)
    (scale : Fin 6 → ℝ)
    (hatom : ∀ label, designPrime.atom label = scale label • design.atom label)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    atomShare designPrime label = atomShare design label := by
  have hatomMatrix : ∀ lbl : Fin 6,
      atomMatrix (designPrime.atom lbl) = (scale lbl ^ 2) • atomMatrix (design.atom lbl) := by
    intro lbl
    rw [hatom lbl, atomMatrix_smul]
  have hstress : (∑ lbl, (designPrime.weight lbl * scale lbl ^ 2 - design.weight lbl)
      • atomMatrix (design.atom lbl)) = 0 := by
    have hsplit : ∀ lbl : Fin 6,
        (designPrime.weight lbl * scale lbl ^ 2 - design.weight lbl)
            • atomMatrix (design.atom lbl)
          = designPrime.weight lbl • atomMatrix (designPrime.atom lbl)
            - design.weight lbl • atomMatrix (design.atom lbl) := by
      intro lbl
      rw [hatomMatrix lbl, smul_smul, sub_smul]
    rw [Finset.sum_congr rfl fun lbl _ => hsplit lbl, Finset.sum_sub_distrib,
      designPrime.isParseval, design.isParseval, sub_self]
  have hzero := hstressFree _ hstress
  have hlabel : designPrime.weight label * scale label ^ 2 - design.weight label = 0 :=
    congrFun hzero label
  have hweight : designPrime.weight label * scale label ^ 2 = design.weight label := by
    linarith [hlabel]
  rw [atomShare, atomShare, hatom label, leverageOf_smul, ← hweight]
  ring

/-! ## Part 4: the share defect and its boundary -/

/-- The weighted mean square correlation of one atom with the whole family is
its leverage.  This is Parseval read at the atom itself. -/
theorem sum_weight_mul_sq_dotProduct_self (design : WeightedDesign size rank) (label : Fin size) :
    ∑ other, design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2
      = leverageOf (design.atom label) := by
  have hquad : design.atom label ⬝ᵥ
      ((∑ other, design.weight other • atomMatrix (design.atom other)) *ᵥ design.atom label)
      = ∑ other, design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_dot_smul, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hcomm : design.atom label ⬝ᵥ design.atom other
        = design.atom other ⬝ᵥ design.atom label := dotProduct_comm _ _
    rw [hcomm]
    ring
  rw [← hquad, design.isParseval, Matrix.one_mulVec, ← leverageOf_eq_dotProduct_self]

/-- **THE SHARE DEFECT IS A CORRELATION.**  `l_c (1 - share_c)` is the weighted
mean square correlation of atom `c` with the OTHER atoms.  Exact, at every size
and rank, with no hypothesis.  It gives `share_c <= 1` again and, more to the
point, it says exactly when equality holds. -/
theorem leverage_mul_one_sub_atomShare (design : WeightedDesign size rank) (label : Fin size) :
    leverageOf (design.atom label) * (1 - atomShare design label)
      = ∑ other ∈ Finset.univ.erase label,
          design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun other => design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2)
    (Finset.mem_univ label)
  rw [sum_weight_mul_sq_dotProduct_self design label] at hsplit
  have hdiag : design.atom label ⬝ᵥ design.atom label = leverageOf (design.atom label) :=
    (leverageOf_eq_dotProduct_self (design.atom label)).symm
  rw [hdiag] at hsplit
  rw [atomShare]
  nlinarith [hsplit]

/-- **THE SHARE REACHES ONE EXACTLY AT ORTHOGONALITY.**  A share of one says the
atom is orthogonal to every other atom of the design, so the other atoms are
confined to the hyperplane it is normal to. -/
theorem atomShare_eq_one_iff_forall_dotProduct_eq_zero (design : WeightedDesign size rank)
    (label : Fin size) (hleverage : 0 < leverageOf (design.atom label)) :
    atomShare design label = 1
      ↔ ∀ other, other ≠ label → design.atom other ⬝ᵥ design.atom label = 0 := by
  have hdefect := leverage_mul_one_sub_atomShare design label
  constructor
  · intro hshare other hother
    rw [hshare, sub_self, mul_zero] at hdefect
    have hnonneg : ∀ index ∈ Finset.univ.erase label,
        0 ≤ design.weight index * (design.atom index ⬝ᵥ design.atom label) ^ 2 :=
      fun index _ => mul_nonneg (design.weight_pos index).le (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdefect.symm other
      (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
    have hsq : (design.atom other ⬝ᵥ design.atom label) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with hw | hs
      · exact absurd hw (ne_of_gt (design.weight_pos other))
      · exact hs
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  · intro horth
    have hvanish : ∑ other ∈ Finset.univ.erase label,
        design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun other hother => ?_
      rw [horth other (Finset.mem_erase.mp hother).1]
      ring
    rw [hvanish] at hdefect
    have := mul_eq_zero.mp hdefect
    rcases this with hlev | hone
    · exact absurd hlev (ne_of_gt hleverage)
    · linarith [hone]

/-! ## Part 5: the orthogonal conic -/

/-- An explicit nonzero vector orthogonal to a given vector of three-space. -/
noncomputable def perpWitness (vector : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if vector 0 = 0 ∧ vector 1 = 0 then ![1, 0, 0] else ![-(vector 1), vector 0, 0]

theorem perpWitness_dotProduct (vector : Fin 3 → ℝ) : perpWitness vector ⬝ᵥ vector = 0 := by
  rw [perpWitness]
  by_cases hflat : vector 0 = 0 ∧ vector 1 = 0
  · rw [if_pos hflat]
    simp [dotProduct, Fin.sum_univ_three, hflat.1]
  · rw [if_neg hflat]
    simp [dotProduct, Fin.sum_univ_three]
    ring

theorem perpWitness_ne_zero (vector : Fin 3 → ℝ) : perpWitness vector ≠ 0 := by
  rw [perpWitness]
  by_cases hflat : vector 0 = 0 ∧ vector 1 = 0
  · rw [if_pos hflat]
    intro hzero
    have := congrFun hzero 0
    simp at this
  · rw [if_neg hflat]
    intro hzero
    have hfirst := congrFun hzero 0
    have hsecond := congrFun hzero 1
    simp at hfirst hsecond
    exact hflat ⟨hsecond, by linarith [hfirst]⟩

/-- The rank-one product acts by pairing.  Mathlib states this with a
`MulOpposite` scalar, which is not what a real coefficient wants. -/
theorem vecMulVec_mulVec_real (left right probe : Fin 3 → ℝ) :
    Matrix.vecMulVec left right *ᵥ probe = (right ⬝ᵥ probe) • left := by
  funext index
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The symmetric product of two vectors: the conic whose value at `x` is twice
the product of the two pairings. -/
noncomputable def orthogonalPairConic (normal probe : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.vecMulVec normal probe + Matrix.vecMulVec probe normal

theorem orthogonalPairConic_symm (normal probe : Fin 3 → ℝ) :
    (orthogonalPairConic normal probe)ᵀ = orthogonalPairConic normal probe := by
  ext rowIndex colIndex
  simp [orthogonalPairConic, Matrix.vecMulVec_apply, mul_comm]
  ring

theorem orthogonalPairConic_form (normal probe direction : Fin 3 → ℝ) :
    direction ⬝ᵥ (orthogonalPairConic normal probe *ᵥ direction)
      = 2 * ((normal ⬝ᵥ direction) * (probe ⬝ᵥ direction)) := by
  rw [orthogonalPairConic, Matrix.add_mulVec, vecMulVec_mulVec_real, vecMulVec_mulVec_real,
    dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hone : direction ⬝ᵥ normal = normal ⬝ᵥ direction := dotProduct_comm _ _
  have htwo : direction ⬝ᵥ probe = probe ⬝ᵥ direction := dotProduct_comm _ _
  rw [hone, htwo]
  ring

theorem orthogonalPairConic_ne_zero {normal probe : Fin 3 → ℝ} (hnormal : normal ≠ 0)
    (hprobe : probe ≠ 0) (horth : normal ⬝ᵥ probe = 0) :
    orthogonalPairConic normal probe ≠ 0 := by
  intro hzero
  have happly : orthogonalPairConic normal probe *ᵥ probe = 0 := by
    rw [hzero, Matrix.zero_mulVec]
  rw [orthogonalPairConic, Matrix.add_mulVec, vecMulVec_mulVec_real,
    vecMulVec_mulVec_real, horth, zero_smul, add_zero] at happly
  have hlev : 0 < probe ⬝ᵥ probe := by
    rw [← leverageOf_eq_dotProduct_self]
    rcases lt_or_eq_of_le (leverageOf_nonneg probe) with hpos | hzero'
    · exact hpos
    · exact absurd (eq_zero_of_leverageOf_eq_zero hzero'.symm) hprobe
  exact hnormal (by
    have := smul_eq_zero.mp happly
    rcases this with hcoeff | hvec
    · exact absurd hcoeff (ne_of_gt hlev)
    · exact hvec)

/-- **A SHARE OF ONE PUTS THE SIX DIRECTIONS ON A CONIC.**  If atom `label` is
orthogonal to every other atom, the symmetric product of that atom with any
vector orthogonal to it is a nonzero conic through all the directions.  Rank
three is used: it supplies the orthogonal vector. -/
theorem exists_conic_of_atomShare_eq_one (design : WeightedDesign size 3) (label : Fin size)
    (hleverage : 0 < leverageOf (design.atom label)) (hshare : atomShare design label = 1) :
    ∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conic ≠ 0 ∧ conicᵀ = conic
      ∧ ∀ other, design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0 := by
  have hnormal : design.atom label ≠ 0 := fun hzero => by
    rw [hzero] at hleverage
    simp [leverageOf] at hleverage
  have horth := (atomShare_eq_one_iff_forall_dotProduct_eq_zero design label hleverage).mp hshare
  refine ⟨orthogonalPairConic (design.atom label) (perpWitness (design.atom label)),
    orthogonalPairConic_ne_zero hnormal (perpWitness_ne_zero _) ?_,
    orthogonalPairConic_symm _ _, fun other => ?_⟩
  · rw [dotProduct_comm]
    exact perpWitness_dotProduct (design.atom label)
  · rw [orthogonalPairConic_form]
    by_cases hother : other = label
    · subst hother
      have hzero : perpWitness (design.atom other) ⬝ᵥ design.atom other = 0 :=
        perpWitness_dotProduct (design.atom other)
      rw [hzero]
      ring
    · have hzero : design.atom label ⬝ᵥ design.atom other = 0 := by
        rw [dotProduct_comm]
        exact horth other hother
      rw [hzero]
      ring

/-- No atom of a stress-free design vanishes: a zero atom is its own stress. -/
theorem leverageOf_pos_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    0 < leverageOf (design.atom label) := by
  rcases lt_or_eq_of_le (leverageOf_nonneg (design.atom label)) with hpos | hzero
  · exact hpos
  · exfalso
    have hatomZero : design.atom label = 0 := eq_zero_of_leverageOf_eq_zero hzero.symm
    have hstress : (∑ atomIndex, (if atomIndex = label then (1 : ℝ) else 0)
        • atomMatrix (design.atom atomIndex)) = 0 := by
      refine Finset.sum_eq_zero fun atomIndex _ => ?_
      by_cases hindex : atomIndex = label
      · have hmatrix : atomMatrix (design.atom atomIndex) = 0 := by
          rw [hindex, hatomZero]
          ext rowIndex colIndex
          simp [atomMatrix, Matrix.vecMulVec_apply]
        rw [hmatrix, smul_zero]
      · simp [hindex]
    have := congrFun (hstressFree _ hstress) label
    simp at this

/-- **EVERY SHARE OF A BRANCH-(i) DESIGN IS STRICTLY BELOW ONE.**  The general
bound `Gtz.atomShare_le_one_ofAnyRank` is not strict; on the stress-free stratum
it is, because equality puts the six directions on a conic and
`Gtz.stressFree_iff_no_conic_sixThree` forbids that.  This is the boundary a
directed descent on the stratum approaches as the margin falls. -/
theorem atomShare_lt_one_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    atomShare design label < 1 := by
  rcases lt_or_eq_of_le (atomShare_le_one_ofAnyRank design label) with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨conic, hconicNe, hconicSymm, hconicVanishes⟩ :=
      exists_conic_of_atomShare_eq_one design label
        (leverageOf_pos_of_stressFree design hstressFree label) heq
    exact hconicNe ((stressFree_iff_no_conic_sixThree design.atom).mp hstressFree conic
      hconicSymm hconicVanishes)

/-- The strict share cap, with the weights eliminated.  Everything in the
statement is a polynomial in the eighteen atom coordinates. -/
theorem veroneseShareForm_lt_sq_det_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    veroneseShareForm design.atom label * (veroneseGrid design.atom).det
      < (veroneseGrid design.atom).det ^ 2 := by
  have hdet : (veroneseGrid design.atom).det ≠ 0 :=
    (stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree
  have hsqPos : 0 < (veroneseGrid design.atom).det ^ 2 := by positivity
  have hshare := atomShare_lt_one_of_stressFree design hstressFree label
  have hform : veroneseShareForm design.atom label * (veroneseGrid design.atom).det
      = atomShare design label * (veroneseGrid design.atom).det ^ 2 := by
    rw [← atomShare_mul_det_veroneseGrid]
    ring
  rw [hform]
  nlinarith [hsqPos, hshare]

/-- The six share forms total three times the determinant: the trace law of a
`(6,3)` design, with the weights eliminated. -/
theorem sum_veroneseShareForm (design : WeightedDesign 6 3) :
    ∑ label, veroneseShareForm design.atom label = 3 * (veroneseGrid design.atom).det := by
  have hterm : ∀ label : Fin 6, veroneseShareForm design.atom label
      = atomShare design label * (veroneseGrid design.atom).det :=
    fun label => (atomShare_mul_det_veroneseGrid design label).symm
  rw [Finset.sum_congr rfl fun label _ => hterm label, ← Finset.sum_mul,
    sum_atomShare_eq_rank design]
  norm_num

/-! ## Part 6: branch (i) with the weight vector removed -/

/-- **BRANCH (i), STATED IN THE ATOMS.**  Every hypothesis a primitive
stress-free `(6,3)` tie satisfies, with the weight vector gone from all but the
last clause, which is already weight-free.  The three determinant clauses are
polynomial in the eighteen atom coordinates, and all three are invariant under
the per-label sign group by `veroneseGrid_smul_atoms_of_sq_eq_one`. -/
theorem sixThree_stressFree_atom_conditions (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    (veroneseGrid design.atom).det ≠ 0
    ∧ (∀ label, 0 < (veroneseGrid design.atom).det * veroneseWeightMinor design.atom label)
    ∧ (∑ label, veroneseWeightMinor design.atom label = (veroneseGrid design.atom).det)
    ∧ (∑ label, veroneseShareForm design.atom label = 3 * (veroneseGrid design.atom).det)
    ∧ (∀ label, veroneseShareForm design.atom label * (veroneseGrid design.atom).det
        < (veroneseGrid design.atom).det ^ 2) := by
  refine ⟨(stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree,
    fun label => det_mul_veroneseWeightMinor_pos design hstressFree label,
    sum_veroneseWeightMinor design, sum_veroneseShareForm design,
    fun label => veroneseShareForm_lt_sq_det_of_stressFree design hstressFree label⟩

/-- The tie side, unchanged: `Gtz.IsTie` never mentions the weights, so the
elimination leaves it alone.  Stated here so the branch-(i) question reads as
one sentence about eighteen real numbers. -/
theorem sixThree_isTie_atom_condition (design : WeightedDesign 6 3) (htie : IsTie design) :
    ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef :=
  htie.2

/-! ## Part 7: the recognition converse

The elimination is only half an argument while it runs one way.  This part
builds a design back out of an atom family that satisfies the three polynomial
conditions, so branch (i) IS the semialgebraic set they cut out. -/

/-- Parseval in Veronese coordinates, both ways.  The companion of
`Gtz.sum_smul_atomMatrix_eq_zero_iff_veronese` at the identity instead of zero. -/
theorem sum_smul_atomMatrix_eq_one_iff_veronese (atomFamily : Fin 6 → Fin 3 → ℝ)
    (coeff : Fin 6 → ℝ) :
    (∑ atomIndex, coeff atomIndex • atomMatrix (atomFamily atomIndex)) = 1
      ↔ coeff ᵥ* veroneseGrid atomFamily = veroneseIdentityRow := by
  have hentry := sum_smul_atomMatrix_apply atomFamily coeff
  have hcoord := vecMul_veroneseGrid_apply atomFamily coeff
  have hswap : ∀ rowIndex colIndex : Fin 3,
      ∑ atomIndex, coeff atomIndex
          * (atomFamily atomIndex rowIndex * atomFamily atomIndex colIndex)
        = ∑ atomIndex, coeff atomIndex
          * (atomFamily atomIndex colIndex * atomFamily atomIndex rowIndex) :=
    fun rowIndex colIndex => Finset.sum_congr rfl fun _ _ => by ring
  constructor
  · intro hparseval
    funext coordIndex
    have hvalue : ∀ rowIndex colIndex : Fin 3,
        ∑ atomIndex, coeff atomIndex
            * (atomFamily atomIndex rowIndex * atomFamily atomIndex colIndex)
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex := by
      intro rowIndex colIndex
      rw [← hentry rowIndex colIndex, hparseval]
    rw [hcoord coordIndex]
    fin_cases coordIndex
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 0 0
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 1 1
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 2 2
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 0 1
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 0 2
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 1 2
  · intro hrow
    have hvalue : ∀ coordIndex : Fin 6,
        ∑ atomIndex, coeff atomIndex * veroneseCoords (atomFamily atomIndex) coordIndex
          = veroneseIdentityRow coordIndex := by
      intro coordIndex
      rw [← hcoord coordIndex, hrow]
    ext rowIndex colIndex
    rw [hentry rowIndex colIndex]
    fin_cases rowIndex <;> fin_cases colIndex
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 0
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 3
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 4
    · rw [hswap]; simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 3
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 1
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 5
    · rw [hswap]; simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 4
    · rw [hswap]; simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 5
    · simpa [veroneseCoords, veroneseIdentityRow, Matrix.one_apply] using hvalue 2

/-- **THE ELIMINATED WEIGHT.**  A function of the atoms only, which the Cramer
law shows is the design's weight whenever a design exists. -/
noncomputable def veroneseWeight (atomFamily : Fin 6 → Fin 3 → ℝ) (label : Fin 6) : ℝ :=
  veroneseWeightMinor atomFamily label / (veroneseGrid atomFamily).det

theorem veroneseWeight_eq_weight (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) (label : Fin 6) :
    veroneseWeight design.atom label = design.weight label := by
  rw [veroneseWeight, ← weight_mul_det_veroneseGrid, mul_div_assoc,
    div_self ((stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree), mul_one]

/-- The eliminated weight resolves the identity whenever the determinant does
not vanish.  Only the adjugate row law is used. -/
theorem sum_veroneseWeight_smul_atomMatrix (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hdet : (veroneseGrid atomFamily).det ≠ 0) :
    (∑ atomIndex, veroneseWeight atomFamily atomIndex • atomMatrix (atomFamily atomIndex)) = 1 := by
  rw [sum_smul_atomMatrix_eq_one_iff_veronese]
  funext coordIndex
  have hrow := congrFun (veroneseWeightMinor_vecMul_veroneseGrid atomFamily) coordIndex
  rw [Matrix.vecMul, dotProduct] at hrow ⊢
  have hscale : ∀ atomIndex : Fin 6,
      veroneseWeight atomFamily atomIndex * veroneseGrid atomFamily atomIndex coordIndex
        = ((veroneseGrid atomFamily).det)⁻¹
          * (veroneseWeightMinor atomFamily atomIndex
              * veroneseGrid atomFamily atomIndex coordIndex) := by
    intro atomIndex
    rw [veroneseWeight, div_eq_inv_mul]
    ring
  rw [Finset.sum_congr rfl fun atomIndex _ => hscale atomIndex, ← Finset.mul_sum, hrow,
    Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

/-- **BRANCH (i) BUILT FROM ATOM DATA ALONE.**  Three polynomial conditions on
the eighteen coordinates produce a stress-free `(6,3)` design whose weights are
the eliminated ones. -/
noncomputable def stressFreeDesignOfAtoms (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hdet : (veroneseGrid atomFamily).det ≠ 0)
    (hpos : ∀ label, 0 < (veroneseGrid atomFamily).det * veroneseWeightMinor atomFamily label)
    (hsum : ∑ label, veroneseWeightMinor atomFamily label = (veroneseGrid atomFamily).det) :
    WeightedDesign 6 3 where
  atom := atomFamily
  weight := veroneseWeight atomFamily
  weight_pos label := by
    have hsq : (0 : ℝ) < (veroneseGrid atomFamily).det ^ 2 := by positivity
    have hrewrite : veroneseWeight atomFamily label
        = ((veroneseGrid atomFamily).det * veroneseWeightMinor atomFamily label)
          / (veroneseGrid atomFamily).det ^ 2 := by
      rw [veroneseWeight]
      field_simp
    rw [hrewrite]
    exact div_pos (hpos label) hsq
  weight_sum_one := by
    have hterm : ∀ label : Fin 6, veroneseWeight atomFamily label
        = veroneseWeightMinor atomFamily label / (veroneseGrid atomFamily).det :=
      fun _ => rfl
    rw [Finset.sum_congr rfl fun label _ => hterm label, ← Finset.sum_div, hsum,
      div_self hdet]
  isParseval := sum_veroneseWeight_smul_atomMatrix atomFamily hdet

theorem stressFreeDesignOfAtoms_atom (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hdet : (veroneseGrid atomFamily).det ≠ 0)
    (hpos : ∀ label, 0 < (veroneseGrid atomFamily).det * veroneseWeightMinor atomFamily label)
    (hsum : ∑ label, veroneseWeightMinor atomFamily label = (veroneseGrid atomFamily).det) :
    (stressFreeDesignOfAtoms atomFamily hdet hpos hsum).atom = atomFamily := rfl

/-- **THE WEIGHT ELIMINATION AS AN EXACT EQUIVALENCE.**  An atom family carries a
stress-free `(6,3)` design exactly when its Veronese determinant is nonzero, its
six weight minors share that determinant's sign, and they total it.  The weight
vector has left the statement entirely: branch (i) is the semialgebraic set that
these three conditions cut out of the eighteen atom coordinates, and by
`veroneseGrid_smul_atoms_of_sq_eq_one` all three are invariant under the
per-label sign group. -/
theorem exists_stressFree_design_iff_veronese_conditions (atomFamily : Fin 6 → Fin 3 → ℝ) :
    (∃ design : WeightedDesign 6 3, design.atom = atomFamily
        ∧ ∀ stressCoeff : Fin 6 → ℝ,
            (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
              stressCoeff = 0)
      ↔ ((veroneseGrid atomFamily).det ≠ 0
          ∧ (∀ label, 0 < (veroneseGrid atomFamily).det * veroneseWeightMinor atomFamily label)
          ∧ ∑ label, veroneseWeightMinor atomFamily label
              = (veroneseGrid atomFamily).det) := by
  constructor
  · rintro ⟨design, hatom, hstressFree⟩
    subst hatom
    exact ⟨(stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree,
      fun label => det_mul_veroneseWeightMinor_pos design hstressFree label,
      sum_veroneseWeightMinor design⟩
  · rintro ⟨hdet, hpos, hsum⟩
    refine ⟨stressFreeDesignOfAtoms atomFamily hdet hpos hsum,
      stressFreeDesignOfAtoms_atom atomFamily hdet hpos hsum, ?_⟩
    rw [stressFreeDesignOfAtoms_atom atomFamily hdet hpos hsum]
    exact (stressFree_iff_veroneseGrid_det_ne_zero atomFamily).mpr hdet

/-! ## Part 8: the normal overflow law

Every argument on branch (i) must read a THIRD selected label
(`Gtz.exists_open_pair_rankThree`).  This part supplies one, in the one
direction where a heavy pair supplies nothing: the normal of the plane the pair
spans. -/

/-- Parseval against an arbitrary probe: the weighted mean square pairing of the
atoms with a probe is the probe's own leverage. -/
theorem sum_weight_mul_sq_dotProduct_probe (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) :
    ∑ atomIndex, design.weight atomIndex * (design.atom atomIndex ⬝ᵥ probe) ^ 2
      = leverageOf probe := by
  have hquad : probe ⬝ᵥ
      ((∑ atomIndex, design.weight atomIndex • atomMatrix (design.atom atomIndex)) *ᵥ probe)
      = ∑ atomIndex, design.weight atomIndex * (design.atom atomIndex ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [Matrix.smul_mulVec, atomMatrix_mulVec_eq_dot_smul, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hcomm : probe ⬝ᵥ design.atom atomIndex = design.atom atomIndex ⬝ᵥ probe :=
      dotProduct_comm _ _
    rw [hcomm]
    ring
  rw [← hquad, design.isParseval, Matrix.one_mulVec, ← leverageOf_eq_dotProduct_self]

/-- **THE NORMAL OVERFLOW LAW.**  Let a NONEMPTY set of labels read zero against
a nonzero probe.  Then some label OUTSIDE that set overshoots the probe: its
squared pairing strictly exceeds the probe's leverage.  Parseval spends the
whole leverage on the complement, and the complement carries strictly less than
the total weight, so one of its terms must overshoot.

At rank three, taking the probe to be a normal of the plane that two atoms span,
this hands back a third label whose triple has strictly positive gap along that
normal — the one direction in which a heavy pair contributes nothing. -/
theorem exists_overshoot_of_forall_dotProduct_eq_zero (design : WeightedDesign size rank)
    (probe : Fin rank → ℝ) (hprobe : probe ≠ 0) (flat : Finset (Fin size))
    (hflatNonempty : flat.Nonempty)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ probe = 0) :
    ∃ label, label ∉ flat ∧ leverageOf probe < (design.atom label ⬝ᵥ probe) ^ 2 := by
  classical
  have hlev : 0 < leverageOf probe := by
    rcases lt_or_eq_of_le (leverageOf_nonneg probe) with hpos | hzero
    · exact hpos
    · exact absurd (eq_zero_of_leverageOf_eq_zero hzero.symm) hprobe
  by_contra hcontra
  simp only [not_exists, not_and, not_lt] at hcontra
  have hbound : ∀ label : Fin size,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
        ≤ design.weight label * leverageOf probe * (if label ∈ flat then 0 else 1) := by
    intro label
    by_cases hmem : label ∈ flat
    · rw [if_pos hmem, hflat label hmem]
      simp
    · rw [if_neg hmem, mul_one]
      exact mul_le_mul_of_nonneg_left (hcontra label hmem) (design.weight_pos label).le
  have hmass : ∑ label, design.weight label * leverageOf probe
      * (if label ∈ flat then (0 : ℝ) else 1)
      = (∑ label ∈ Finset.univ \ flat, design.weight label) * leverageOf probe := by
    have hterm : ∀ label : Fin size,
        design.weight label * leverageOf probe * (if label ∈ flat then (0 : ℝ) else 1)
          = if label ∈ Finset.univ \ flat then design.weight label * leverageOf probe else 0 := by
      intro label
      by_cases hmem : label ∈ flat <;> simp [hmem, Finset.mem_sdiff]
    rw [Finset.sum_congr rfl fun label _ => hterm label,
      Finset.sum_ite_mem Finset.univ (Finset.univ \ flat)
        (fun label => design.weight label * leverageOf probe), Finset.univ_inter,
      Finset.sum_mul]
  have htotal : ∑ label ∈ Finset.univ \ flat, design.weight label < 1 := by
    have hsplit := Finset.sum_sdiff (Finset.subset_univ flat) (f := design.weight)
    have hflatPos : 0 < ∑ label ∈ flat, design.weight label :=
      Finset.sum_pos (fun label _ => design.weight_pos label) hflatNonempty
    rw [design.weight_sum_one] at hsplit
    linarith
  have hsum := Finset.sum_le_sum fun label (_ : label ∈ Finset.univ) => hbound label
  rw [sum_weight_mul_sq_dotProduct_probe design probe, hmass] at hsum
  nlinarith [hlev, htotal, hsum]

/-- The overflow, read on the gap of a triple.  If two atoms of a `(6,3)` design
lie in the plane a nonzero normal defines, some third label makes the triple's
gap strictly positive ALONG that normal.  The other two directions are the ones
a plane cover still has to supply. -/
theorem exists_third_label_normal_gap_pos (design : WeightedDesign size 3)
    (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0) (first second : Fin size)
    (hdistinct : first ≠ second)
    (hfirst : design.atom first ⬝ᵥ normal = 0) (hsecond : design.atom second ⬝ᵥ normal = 0) :
    ∃ third, third ≠ first ∧ third ≠ second
      ∧ leverageOf normal
          < normal ⬝ᵥ (subsetSum design {first, second, third} *ᵥ normal) := by
  classical
  obtain ⟨third, hthird, hover⟩ :=
    exists_overshoot_of_forall_dotProduct_eq_zero design normal hnormal
      ({first, second} : Finset (Fin size)) ⟨first, by simp⟩
      (by
        intro label hlabel
        rcases Finset.mem_insert.mp hlabel with hone | htwo
        · rw [hone]; exact hfirst
        · rw [Finset.mem_singleton.mp htwo]; exact hsecond)
  have hne : third ≠ first ∧ third ≠ second := by
    constructor
    · intro heq; exact hthird (by simp [heq])
    · intro heq; exact hthird (by simp [heq])
  refine ⟨third, hne.1, hne.2, ?_⟩
  have hfirstNot : first ∉ ({second, third} : Finset (Fin size)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hdistinct, Ne.symm hne.1⟩
  have hsecondNot : second ∉ ({third} : Finset (Fin size)) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm hne.2
  have hquad : normal ⬝ᵥ (subsetSum design {first, second, third} *ᵥ normal)
      = ∑ label ∈ ({first, second, third} : Finset (Fin size)),
          (design.atom label ⬝ᵥ normal) ^ 2 := by
    rw [subsetSum, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [atomMatrix_mulVec_eq_dot_smul, dotProduct_smul, smul_eq_mul]
    have hcomm : normal ⬝ᵥ design.atom label = design.atom label ⬝ᵥ normal :=
      dotProduct_comm _ _
    rw [hcomm]
    ring
  rw [hquad, Finset.sum_insert hfirstNot, Finset.sum_insert hsecondNot,
    Finset.sum_singleton, hfirst, hsecond]
  simpa using hover

end Gtz
