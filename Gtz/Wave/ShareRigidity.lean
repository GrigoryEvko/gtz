/-
# The dual conic of a label, and the share as a normalized trace

## What this module adds

The tree already reads the weight of a stress-free `(6,3)` design as an entry of
an inverse (`Gtz.gramSolvedWeight`), as a ratio of two Veronese determinants
(`Gtz.veroneseWeight`), and it already knows that the share is a projective
invariant of the six directions (`Gtz.atomShare_eq_of_atom_smul_of_stressFree`).
What it does NOT have is the geometric object those numbers come from.

This module names that object.  The six atom matrices of a stress-free `(6,3)`
design are a basis of the symmetric forms.  `Gtz.dualAtom` is the DUAL basis
under the trace pairing.  Four facts follow, and none is in the tree.

* `Gtz.trace_dualAtom_eq_weight` — the WEIGHT of a label is the TRACE of that
  label's dual form.  Every prior reading of a weight is a determinant ratio or
  an inverse entry.
* `Gtz.eq_smul_dualAtom_of_forall_ne` — that form is the ONLY conic through the
  other five directions, up to scale.
* `Gtz.trace_div_dotProduct_unitAtom_eq_atomShare` — the SHARE of a label is the
  trace of the conic through the other five directions, divided by that conic's
  value at the label's own unit direction.
* `Gtz.not_posSemidef_dualAtom` and its negative twin — that conic is never
  semidefinite.  It is always a real conic, never a point conic.

## Why the five-point statement is not vacuous

Five points of the projective plane never determine a conic.  The space of
conics has dimension six, five points impose five conditions, and a pencil
survives.  `Gtz/Design/TwoFamilyTightFrame.lean` records exactly that: at five
points the system is underdetermined and nothing normalizes the pencil.

The SIXTH direction normalizes it.  Stress-freeness says the six directions lie
on no conic (`Gtz.hasNoCommonQuadric_of_stressFree`).  Two conics through the
same five directions differ by a conic through all six, which must be zero.  So
uniqueness of the five-point conic is a theorem about the six-point
configuration, not about the five points, and it holds at every design of the
stress-free stratum.

## The engine

One unconditional linear system.  Pair the Parseval identity against the atom
`d` on both sides:

  `sum_c weight_c * (g_c . g_d)^2 = |g_d|^2`.

That is `Gtz.squaredPairingGrid_mulVec_weight`, and its matrix is the shipped
`Gtz.squaredPairingGrid`, the entrywise square of the atom Gram.  Off every
conic that matrix is invertible, so the rows of its inverse read the dual forms
and the weights at the same time.

## The gap ledger

Part six spends the dual basis on the object the campaign cares about.  Every
gap matrix `S_C - 1` of the design has coordinates `indicator - weight` in the
atom basis (`Gtz.subsetSum_sub_one_eq_sum_smul_atomMatrix`), and the dual forms
read those coordinates back off as traces
(`Gtz.trace_dualAtom_mul_subsetSum_sub_one`).  So at a FIXED stress-free design
the twenty triples are twenty translates of one weight vector, and not twenty
unrelated matrices.

The landed `Gtz.trace_gap_mul_normalizerForm` is the SUM of this ledger over the
six labels, because `Gtz.isNormalizerForm_sum_dualAtom` proves the normalizer
form is the sum of the six dual forms.  The per-label refinement is what is new.

## What is NOT new here, and where it lives

* The weight as an inverse entry: `Gtz.gramSolvedWeight`,
  `Gtz.weight_eq_veroneseGrid_inv_of_stressFree`.
* The share as a determinant ratio: `Gtz.atomShare_eq_veroneseShareForm_div`.
* The share as a projective invariant: `Gtz.atomShare_eq_of_atom_smul_of_stressFree`.
* The normalized row law: `Gtz.sum_atomShare_mul_sq_directionGram`.
* The normalizer form, its uniqueness and its trace: `Gtz.IsNormalizerForm`,
  `Gtz.isNormalizerForm_unique_of_noConic`, `Gtz.trace_eq_one_of_isNormalizerForm`,
  `Gtz.trace_gap_mul_normalizerForm`.
* Off-conicity as one Gram determinant:
  `Gtz.hasNoCommonQuadric_iff_det_squaredPairingGrid_ne_zero`.
* The rescaled design: `Gtz.UniformPositionBridge.rescaledDesign`.

## Honest scope

Nothing here decides the `(6,3)` hinge.  No statement in this module is an
equivalence with `Gtz.HingeHoldsAtSize 6 3`, with
`Gtz.StressFreeHingeHoldsSixThree`, or with tie-freeness of any stratum, so
nothing here joins the synonym class of `Gtz/Wave/WiringSynonymClass.lean`.  The
content is a normal form for the weight and the share, one uniqueness theorem in
the projective plane, and a coordinate system for the twenty gaps.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.ConicBinomialShadow
import Gtz.Design.FrameConservation
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.TwoFamilyTightFrame
import Gtz.Reduction.BranchTransferConstants
import Gtz.Uniform.RouteBProps
import Gtz.Wave.ShareOneForcingConic
import Gtz.Wave.VeroneseWeightElimination

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m k : ℕ}

/-! ## 1. Two rank-one facts the tree uses inline

Both hold at every size and rank with no design attached. -/

/-- A rank-one atom is symmetric. -/
theorem transpose_atomMatrix_self (vec : Fin k → ℝ) :
    (atomMatrix vec)ᵀ = atomMatrix vec := by
  rw [atomMatrix, Matrix.transpose_vecMulVec]

/-- A symmetric form moves between the two slots of the trace pairing.  Kept
private because two siblings carry the same statement at different index
shapes. -/
private theorem dotProduct_mulVec_swap {form : Matrix (Fin k) (Fin k) ℝ}
    (hsymmetric : formᵀ = form) (left right : Fin k → ℝ) :
    left ⬝ᵥ (form *ᵥ right) = right ⬝ᵥ (form *ᵥ left) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun leftCoord _ => Finset.sum_congr rfl fun rightCoord _ => ?_
  rw [show form rightCoord leftCoord = form leftCoord rightCoord from
    congrFun (congrFun hsymmetric leftCoord) rightCoord]
  ring

/-! ## 2. The weight system, unconditionally

Pairing the Parseval identity against an atom on both sides turns it into a
linear system in the weights whose matrix is the entrywise square of the atom
Gram. -/

/-- **THE WEIGHT SYSTEM.**  `sum_c weight_c * (g_c . g_d)^2 = |g_d|^2`, in
matrix form, at EVERY `(6,3)` design.  The diagonal split of one row is the
landed `Gtz.leverage_mul_one_sub_atomShare`, and the normalization of the whole
system by the leverages is the landed `Gtz.sum_atomShare_mul_sq_directionGram`.
What is new is the matrix reading, which is what makes the inverse available. -/
theorem squaredPairingGrid_mulVec_weight (design : WeightedDesign 6 3) :
    squaredPairingGrid design.atom *ᵥ design.weight
      = fun label => leverageOf (design.atom label) := by
  funext label
  have hleft : (squaredPairingGrid design.atom *ᵥ design.weight) label
      = ∑ other, design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
    show ∑ other, squaredPairingGrid design.atom label other * design.weight other = _
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [squaredPairingGrid, Matrix.of_apply, mul_comm, dotProduct_comm (design.atom other)]
  have hright : design.atom label
      ⬝ᵥ ((∑ other, design.weight other • atomMatrix (design.atom other))
          *ᵥ design.atom label)
      = ∑ other, design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  rw [hleft, ← hright, design.isParseval, Matrix.one_mulVec, leverageOf_eq_dotProduct_self]

/-- Off every conic the squared-pairing grid is invertible. -/
theorem det_squaredPairingGrid_ne_zero_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) :
    (squaredPairingGrid design.atom).det ≠ 0 :=
  (hasNoCommonQuadric_iff_det_squaredPairingGrid_ne_zero design.atom).mp
    (hasNoCommonQuadric_of_stressFree design hstressFree)

/-! ## 3. The dual atoms

The rows of the inverse squared-pairing grid, read back into the space of
symmetric forms.  These are the dual basis of the atom matrices under the trace
pairing, and geometrically they are the conics through five of the six
directions. -/

/-- **THE DUAL FORM OF A LABEL.**  The symmetric `3x3` form whose quadratic form
vanishes at the other five directions and equals one at this label's atom. -/
noncomputable def dualAtom (design : WeightedDesign 6 3) (label : Fin 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ other, (squaredPairingGrid design.atom)⁻¹ label other • atomMatrix (design.atom other)

/-- The dual form is symmetric.  No hypothesis. -/
theorem transpose_dualAtom (design : WeightedDesign 6 3) (label : Fin 6) :
    (dualAtom design label)ᵀ = dualAtom design label := by
  rw [dualAtom, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun other _ => by
    rw [Matrix.transpose_smul, transpose_atomMatrix_self]

/-- **THE DUAL BASIS LAW.**  The quadratic form of `Gtz.dualAtom design c` reads
one at the atom of `c` and zero at every other atom.  So it is a conic through
the five directions other than `c`, normalized at `c`. -/
theorem dotProduct_dualAtom_mulVec (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label other : Fin 6) :
    design.atom other ⬝ᵥ (dualAtom design label *ᵥ design.atom other)
      = if label = other then 1 else 0 := by
  have hunit : IsUnit (squaredPairingGrid design.atom).det :=
    (det_squaredPairingGrid_ne_zero_of_stressFree design hstressFree).isUnit
  have hentry := congrFun (congrFun
    (Matrix.nonsing_inv_mul (squaredPairingGrid design.atom) hunit) label) other
  rw [Matrix.mul_apply] at hentry
  rw [dualAtom, Matrix.sum_mulVec, dotProduct_sum]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
  calc ∑ third, (squaredPairingGrid design.atom)⁻¹ label third
          * (design.atom third ⬝ᵥ design.atom other) ^ 2
      = ∑ third, (squaredPairingGrid design.atom)⁻¹ label third
          * squaredPairingGrid design.atom third other :=
        Finset.sum_congr rfl fun third _ => by rw [squaredPairingGrid, Matrix.of_apply]
    _ = (1 : Matrix (Fin 6) (Fin 6) ℝ) label other := hentry
    _ = if label = other then 1 else 0 := by rw [Matrix.one_apply]

/-- **THE WEIGHT IS A TRACE.**  The weight of a label is the trace of that
label's dual form.  Every earlier reading of a weight in the tree is a
determinant ratio or an entry of an inverse matrix. -/
theorem trace_dualAtom_eq_weight (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    Matrix.trace (dualAtom design label) = design.weight label := by
  have hunit : IsUnit (squaredPairingGrid design.atom).det :=
    (det_squaredPairingGrid_ne_zero_of_stressFree design hstressFree).isUnit
  have hsolve : (squaredPairingGrid design.atom)⁻¹
      *ᵥ (fun other => leverageOf (design.atom other)) = design.weight := by
    rw [← squaredPairingGrid_mulVec_weight design, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have hrow := congrFun hsolve label
  rw [dualAtom, Matrix.trace_sum]
  simp only [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
  rw [← hrow]
  rfl

/-- The share of a label is its leverage times the trace of its dual form. -/
theorem leverage_mul_trace_dualAtom_eq_atomShare (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    leverageOf (design.atom label) * Matrix.trace (dualAtom design label)
      = atomShare design label := by
  rw [trace_dualAtom_eq_weight design hstressFree label, atomShare, mul_comm]

/-- The dual form is nonzero: its own quadratic form reads one. -/
theorem dualAtom_ne_zero (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    dualAtom design label ≠ 0 := by
  intro hzero
  have hvalue := dotProduct_dualAtom_mulVec design hstressFree label label
  rw [hzero, Matrix.zero_mulVec, dotProduct_zero, if_pos rfl] at hvalue
  exact zero_ne_one hvalue

/-! ## 4. The conic through five of the six directions

Five points of the projective plane leave a pencil of conics.  The sixth
direction of a stress-free design kills the pencil, because the difference of
two conics through the same five directions is a conic through all six. -/

/-- **THE FIVE-POINT CONIC IS UNIQUE ON THE STRESS-FREE STRATUM.**  Every
symmetric form that vanishes at the five directions other than `label` is a
scalar multiple of `Gtz.dualAtom design label`, and the scalar is the form's own
value at `label`. -/
theorem eq_smul_dualAtom_of_forall_ne (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6)
    {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : conicᵀ = conic)
    (hvanish : ∀ other, other ≠ label →
      design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0) :
    conic = (design.atom label ⬝ᵥ (conic *ᵥ design.atom label)) • dualAtom design label := by
  set value := design.atom label ⬝ᵥ (conic *ᵥ design.atom label) with hvalueDef
  have hdifference : conic - value • dualAtom design label = 0 := by
    refine hasNoCommonQuadric_of_stressFree design hstressFree _ ?_ ?_
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, hsymmetric,
        transpose_dualAtom design label]
    · intro other
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul, dotProduct_dualAtom_mulVec design hstressFree label other]
      by_cases hcase : label = other
      · subst hcase
        rw [if_pos rfl, mul_one, ← hvalueDef, sub_self]
      · rw [if_neg hcase, mul_zero, sub_zero]
        exact hvanish other fun heq => hcase heq.symm
  exact sub_eq_zero.mp hdifference

/-- A nonzero conic through the other five directions does not vanish at its own
label. -/
theorem dotProduct_mulVec_ne_zero_of_forall_ne (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6)
    {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : conicᵀ = conic) (hnonzero : conic ≠ 0)
    (hvanish : ∀ other, other ≠ label →
      design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0) :
    design.atom label ⬝ᵥ (conic *ᵥ design.atom label) ≠ 0 := fun hzero =>
  hnonzero (by
    rw [eq_smul_dualAtom_of_forall_ne design hstressFree label hsymmetric hvanish, hzero,
      zero_smul])

/-- **THE WEIGHT IS A NORMALIZED TRACE OF THE FIVE-POINT CONIC.**  Take any
nonzero symmetric form vanishing at the five directions other than `label`.  Its
trace, divided by its value at the atom of `label`, is that label's weight. -/
theorem trace_div_dotProduct_eq_weight (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6)
    {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : conicᵀ = conic) (hnonzero : conic ≠ 0)
    (hvanish : ∀ other, other ≠ label →
      design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0) :
    Matrix.trace conic / (design.atom label ⬝ᵥ (conic *ᵥ design.atom label))
      = design.weight label := by
  have hvalueNe := dotProduct_mulVec_ne_zero_of_forall_ne design hstressFree label
    hsymmetric hnonzero hvanish
  have htrace : Matrix.trace conic
      = (design.atom label ⬝ᵥ (conic *ᵥ design.atom label)) * design.weight label := by
    conv_lhs => rw [eq_smul_dualAtom_of_forall_ne design hstressFree label hsymmetric hvanish]
    rw [Matrix.trace_smul, smul_eq_mul, trace_dualAtom_eq_weight design hstressFree label]
  rw [htrace]
  exact mul_div_cancel_left₀ _ hvalueNe

/-- The quadratic form at the unit direction is the one at the atom, divided by
the leverage. -/
theorem dotProduct_unitAtom_mulVec (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6)
    (conic : Matrix (Fin 3) (Fin 3) ℝ) :
    unitAtom design label ⬝ᵥ (conic *ᵥ unitAtom design label)
      = (design.atom label ⬝ᵥ (conic *ᵥ design.atom label))
        / leverageOf (design.atom label) := by
  have hpos := leverageOf_pos_of_stressFree design (fun s hs => hstressFree s hs) label
  have hsq : (Real.sqrt (leverageOf (design.atom label)))⁻¹
      * (Real.sqrt (leverageOf (design.atom label)))⁻¹
      = (leverageOf (design.atom label))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hpos.le]
  simp only [unitAtom, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, hsq, inv_mul_eq_div]

/-- **THE SHARE IS THE NORMALIZED TRACE OF THE FIVE-POINT CONIC.**  Take any
nonzero symmetric form vanishing at the five directions other than `label`.  Its
trace, divided by its value at the UNIT direction of `label`, is that label's
share.

Every quantity on the left is a function of the six directions alone, so this is
the geometric explanation of `Gtz.atomShare_eq_of_atom_smul_of_stressFree`: the
diagonal of the projection form (`Gtz.projectionOfDesign_diagonal`) is read off
the projective configuration and nothing else. -/
theorem trace_div_dotProduct_unitAtom_eq_atomShare (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6)
    {conic : Matrix (Fin 3) (Fin 3) ℝ} (hsymmetric : conicᵀ = conic) (hnonzero : conic ≠ 0)
    (hvanish : ∀ other, other ≠ label →
      design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0) :
    Matrix.trace conic / (unitAtom design label ⬝ᵥ (conic *ᵥ unitAtom design label))
      = atomShare design label := by
  rw [dotProduct_unitAtom_mulVec design hstressFree label conic, div_div_eq_mul_div,
    mul_comm (Matrix.trace conic) (leverageOf (design.atom label)), mul_div_assoc,
    trace_div_dotProduct_eq_weight design hstressFree label hsymmetric hnonzero hvanish,
    atomShare, mul_comm]

/-- **THE FIVE-POINT CONIC EXISTS AND IS UNIQUE UP TO SCALE**, at every design of
the stress-free `(6,3)` stratum and every label. -/
theorem existsUnique_fivePointConic (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    (∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic ∧ conic ≠ 0
        ∧ ∀ other, other ≠ label →
          design.atom other ⬝ᵥ (conic *ᵥ design.atom other) = 0)
      ∧ ∀ first second : Matrix (Fin 3) (Fin 3) ℝ, firstᵀ = first → secondᵀ = second →
          (∀ other, other ≠ label →
            design.atom other ⬝ᵥ (first *ᵥ design.atom other) = 0) →
          (∀ other, other ≠ label →
            design.atom other ⬝ᵥ (second *ᵥ design.atom other) = 0) →
          (design.atom label ⬝ᵥ (second *ᵥ design.atom label)) • first
            = (design.atom label ⬝ᵥ (first *ᵥ design.atom label)) • second := by
  refine ⟨⟨dualAtom design label, transpose_dualAtom design label,
    dualAtom_ne_zero design hstressFree label, fun other hne => ?_⟩,
    fun first second hfirstSymm hsecondSymm hfirstVanish hsecondVanish => ?_⟩
  · rw [dotProduct_dualAtom_mulVec design hstressFree label other]
    exact if_neg fun heq => hne heq.symm
  · conv_lhs => rw [eq_smul_dualAtom_of_forall_ne design hstressFree label
      hfirstSymm hfirstVanish]
    conv_rhs => rw [eq_smul_dualAtom_of_forall_ne design hstressFree label
      hsecondSymm hsecondVanish]
    rw [smul_smul, smul_smul, mul_comm]

/-! ## 5. The normalizer form is the sum of the dual forms

`Gtz.IsNormalizerForm` names the conic through all six atom TIPS.  It is the sum
of the six dual forms.  This is the bridge that makes the landed normalizer
theory the SUM of the per-label ledger of part six. -/

/-- The sum of the dual forms is the design's normalizer form. -/
theorem isNormalizerForm_sum_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) :
    IsNormalizerForm design (∑ label, dualAtom design label) := by
  constructor
  · rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun label _ => transpose_dualAtom design label
  · intro other
    rw [Matrix.sum_mulVec, dotProduct_sum]
    simp only [dotProduct_dualAtom_mulVec design hstressFree]
    simp

/-- **THE NORMALIZER FORM IS THE SUM OF THE DUAL FORMS**, in the strong sense
that every normalizer form equals that sum.  Uniqueness off the conic locus
comes from `Gtz.isNormalizerForm_unique_of_noConic`. -/
theorem eq_sum_dualAtom_of_isNormalizerForm (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design)
    {normalizer : Matrix (Fin 3) (Fin 3) ℝ} (hnormalizer : IsNormalizerForm design normalizer) :
    normalizer = ∑ label, dualAtom design label :=
  isNormalizerForm_unique_of_noConic design
    (fun conic hsymmetric hquadric =>
      hasNoCommonQuadric_of_stressFree design hstressFree conic hsymmetric hquadric)
    hnormalizer (isNormalizerForm_sum_dualAtom design hstressFree)

/-! ## 6. The gap ledger

Every gap matrix of the design has coordinates `indicator - weight` in the atom
basis, and the dual forms read those coordinates back off as traces.  At a fixed
stress-free design the twenty triples are twenty translates of one weight
vector, and not twenty unrelated matrices. -/

/-- **EVERY GAP IN THE ATOM BASIS.**  Unconditional at every size and rank. -/
theorem subsetSum_sub_one_eq_sum_smul_atomMatrix (design : WeightedDesign m k)
    (selected : Finset (Fin m)) :
    subsetSum design selected - 1
      = ∑ label, ((if label ∈ selected then (1 : ℝ) else 0) - design.weight label)
          • atomMatrix (design.atom label) := by
  simp only [sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_mem, Finset.univ_inter, design.isParseval, subsetSum]

/-- **NO GAP OF A STRESS-FREE DESIGN VANISHES.**  Not for a triple, not for any
subset.  A vanishing gap would make the indicator equal the weight vector, and
weights are positive and total one.  The landed
`Gtz.subsetSum_sub_one_ne_zero_of_hasNoCommonQuadric` is the base-triple case. -/
theorem subsetSum_sub_one_ne_zero_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (selected : Finset (Fin 6)) :
    subsetSum design selected - 1 ≠ 0 := by
  intro hzero
  have hcoefficients := hstressFree
    (fun label => (if label ∈ selected then (1 : ℝ) else 0) - design.weight label)
    (by rw [← subsetSum_sub_one_eq_sum_smul_atomMatrix design selected]; exact hzero)
  have hzeroLabel : (if (0 : Fin 6) ∈ selected then (1 : ℝ) else 0) - design.weight 0 = 0 :=
    congrFun hcoefficients 0
  by_cases hmember : (0 : Fin 6) ∈ selected
  · rw [if_pos hmember] at hzeroLabel
    have hweight : design.weight 0 = 1 := by linarith
    have hsum : (1 : ℝ) < ∑ label, design.weight label := by
      rw [← hweight]
      exact Finset.single_lt_sum (i := 0) (j := 1) (by decide) (Finset.mem_univ 0)
        (Finset.mem_univ 1) (design.weight_pos 1) fun other _ _ => (design.weight_pos other).le
    rw [design.weight_sum_one] at hsum
    exact lt_irrefl 1 hsum
  · rw [if_neg hmember] at hzeroLabel
    exact absurd (by linarith : design.weight 0 = 0) (design.weight_pos 0).ne'

/-- **THE GAP LEDGER.**  The dual form of a label reads the gap of ANY subset as
that label's membership indicator minus its weight.  Twenty triples, six
coordinates each, every one in closed form and with no determinant.

Summing over the six labels through `Gtz.isNormalizerForm_sum_dualAtom` recovers
the landed `Gtz.trace_gap_mul_normalizerForm`, which sees only the cardinality.
This ledger sees which labels. -/
theorem trace_dualAtom_mul_subsetSum_sub_one (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) (selected : Finset (Fin 6)) :
    Matrix.trace (dualAtom design label * (subsetSum design selected - 1))
      = (if label ∈ selected then (1 : ℝ) else 0) - design.weight label := by
  have hterm : ∀ other : Fin 6,
      Matrix.trace (dualAtom design label * atomMatrix (design.atom other))
        = if label = other then (1 : ℝ) else 0 := fun other => by
    rw [trace_mul_atomMatrix, dotProduct_dualAtom_mulVec design hstressFree label other]
  rw [subsetSum, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Finset.mul_sum,
    Matrix.trace_sum]
  simp only [hterm]
  rw [Finset.sum_ite_eq, trace_dualAtom_eq_weight design hstressFree label]

/-- **THE SECOND MOMENT OF A GAP.**  The squared Frobenius norm of any gap is an
explicit quadratic form in the indicator-minus-weight vector, with the entrywise
square of the atom Gram as its matrix.  Unconditional at every size and rank. -/
theorem trace_sq_subsetSum_sub_one (design : WeightedDesign m k) (selected : Finset (Fin m)) :
    Matrix.trace ((subsetSum design selected - 1) * (subsetSum design selected - 1))
      = ∑ first, ((if first ∈ selected then (1 : ℝ) else 0) - design.weight first)
          * ∑ second, ((if second ∈ selected then (1 : ℝ) else 0) - design.weight second)
              * (design.atom first ⬝ᵥ design.atom second) ^ 2 := by
  conv_lhs => rw [subsetSum_sub_one_eq_sum_smul_atomMatrix design selected]
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun first _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun second _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_atomMatrix_mul_atomMatrix]

/-! ### The covering law and the dual certificate

Two necessary conditions for domination that read only the atom pairings.  Both
are unconditional at every size and rank. -/

/-- **THE COVERING LAW OF A DOMINATING SUBSET.**  If a subset dominates then it
covers every atom of the design in the squared-pairing sense: the squared
pairings of any atom against the members of the subset total at least that
atom's leverage.

Divided by the leverages this reads on the unit directions and says the selected
directions carry at least the whole of every direction of the design.  The
landed row law `Gtz.sum_atomShare_mul_sq_directionGram` says the SHARE-weighted
total of the same squared cosines is exactly one. -/
theorem leverage_le_sum_sq_dotProduct_of_dominates (design : WeightedDesign m k)
    {selected : Finset (Fin m)} (hdominates : Dominates design selected) (label : Fin m) :
    leverageOf (design.atom label)
      ≤ ∑ other ∈ selected, (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
  have hform := hdominates.dotProduct_mulVec_nonneg (design.atom label)
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset, ← leverageOf_eq_dotProduct_self] at hform
  linarith

/-- The refuter form: one undercovered label kills the subset. -/
theorem not_dominates_of_sum_sq_dotProduct_lt (design : WeightedDesign m k)
    (selected : Finset (Fin m)) (label : Fin m)
    (hshort : ∑ other ∈ selected, (design.atom other ⬝ᵥ design.atom label) ^ 2
      < leverageOf (design.atom label)) :
    ¬ Dominates design selected := fun hdominates =>
  absurd (leverage_le_sum_sq_dotProduct_of_dominates design hdominates label) (not_le.mpr hshort)

/-- **THE POSITIVE SEMIDEFINITE PROBE LAW.**  A dominating subset spends at
least the probe's whole trace on the probe, for every positive semidefinite
probe. -/
theorem trace_le_sum_dotProduct_mulVec_of_dominates (design : WeightedDesign m k)
    {selected : Finset (Fin m)} (hdominates : Dominates design selected)
    {probe : Matrix (Fin k) (Fin k) ℝ} (hprobe : probe.PosSemidef) :
    Matrix.trace probe
      ≤ ∑ other ∈ selected, design.atom other ⬝ᵥ (probe *ᵥ design.atom other) := by
  have hnonneg := trace_mul_nonneg_of_posSemidef hprobe hdominates
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, subsetSum, Finset.mul_sum,
    Matrix.trace_sum] at hnonneg
  simp only [trace_mul_atomMatrix] at hnonneg
  linarith

/-- The refuter form of the probe law. -/
theorem not_dominates_of_sum_dotProduct_mulVec_lt_trace (design : WeightedDesign m k)
    (selected : Finset (Fin m)) {probe : Matrix (Fin k) (Fin k) ℝ} (hprobe : probe.PosSemidef)
    (hshort : ∑ other ∈ selected, design.atom other ⬝ᵥ (probe *ᵥ design.atom other)
      < Matrix.trace probe) :
    ¬ Dominates design selected := fun hdominates =>
  absurd (trace_le_sum_dotProduct_mulVec_of_dominates design hdominates hprobe)
    (not_le.mpr hshort)

/-- **THE PROBE LAW IN THE DUAL COORDINATES.**  On the stress-free stratum the
symmetric form with prescribed values at the six atoms is the value-weighted sum
of the dual forms, so a probe is six numbers and not a matrix. -/
theorem dotProduct_sum_smul_dualAtom_mulVec (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (value : Fin 6 → ℝ) (other : Fin 6) :
    design.atom other ⬝ᵥ ((∑ label, value label • dualAtom design label) *ᵥ design.atom other)
      = value other := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_dualAtom_mulVec design hstressFree]
  simp

/-- The trace of that form is the value vector paired with the weights. -/
theorem trace_sum_smul_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (value : Fin 6 → ℝ) :
    Matrix.trace (∑ label, value label • dualAtom design label)
      = ∑ label, value label * design.weight label := by
  rw [Matrix.trace_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.trace_smul, smul_eq_mul, trace_dualAtom_eq_weight design hstressFree label]

/-! ### The dual forms are never semidefinite

A conic through five of the six directions of a stress-free design is a REAL
conic: it has a positive direction and a negative direction.  It is never a
point conic and never an imaginary one. -/

/-- **A SEMIDEFINITE FORM ANNIHILATES ITS OWN ZEROS.**  Polarize and read the
sign of the cross term. -/
theorem mulVec_eq_zero_of_posSemidef_of_dotProduct_eq_zero
    {form : Matrix (Fin k) (Fin k) ℝ} (hsymmetric : formᵀ = form) (hform : form.PosSemidef)
    {vec : Fin k → ℝ} (hzero : vec ⬝ᵥ (form *ᵥ vec) = 0) : form *ᵥ vec = 0 := by
  have hquadNonneg : ∀ probe : Fin k → ℝ, 0 ≤ probe ⬝ᵥ (form *ᵥ probe) := fun probe => by
    have := hform.dotProduct_mulVec_nonneg probe
    rwa [star_trivial] at this
  have hexpand : ∀ (probe : Fin k → ℝ) (step : ℝ),
      (vec + step • probe) ⬝ᵥ (form *ᵥ (vec + step • probe))
        = 2 * step * (vec ⬝ᵥ (form *ᵥ probe))
          + step ^ 2 * (probe ⬝ᵥ (form *ᵥ probe)) := by
    intro probe step
    have hcross : probe ⬝ᵥ (form *ᵥ vec) = vec ⬝ᵥ (form *ᵥ probe) :=
      dotProduct_mulVec_swap hsymmetric probe vec
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hzero, hcross]
    ring
  have hcrossZero : ∀ probe : Fin k → ℝ, vec ⬝ᵥ (form *ᵥ probe) = 0 := by
    intro probe
    set cross := vec ⬝ᵥ (form *ᵥ probe) with hcrossDef
    set quad := probe ⬝ᵥ (form *ᵥ probe) with hquadDef
    have hquad : 0 ≤ quad := hquadNonneg probe
    have hden : (0 : ℝ) < quad + 1 := by linarith
    by_contra hne
    have hsquare : 0 < cross ^ 2 := by
      rcases (sq_nonneg cross).lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd (sq_eq_zero_iff.mp heq.symm) hne
    have hkey := hquadNonneg (vec + (-cross / (quad + 1)) • probe)
    rw [hexpand probe (-cross / (quad + 1))] at hkey
    have hrewrite : 2 * (-cross / (quad + 1)) * cross
        + (-cross / (quad + 1)) ^ 2 * quad
        = cross ^ 2 * (-quad - 2) / (quad + 1) ^ 2 := by
      field_simp
      ring
    rw [hrewrite] at hkey
    have hnumerator : cross ^ 2 * (-quad - 2) < 0 := by nlinarith
    have hdenominator : (0 : ℝ) < (quad + 1) ^ 2 := by positivity
    exact absurd hkey (not_le.mpr (div_neg_of_neg_of_pos hnumerator hdenominator))
  have hself : (form *ᵥ vec) ⬝ᵥ (form *ᵥ vec) = 0 := by
    rw [← dotProduct_mulVec_swap hsymmetric vec (form *ᵥ vec)]
    exact hcrossZero _
  exact eq_zero_of_dotProduct_self_eq_zero hself

/-- **NO DUAL FORM IS NEGATIVE SEMIDEFINITE.**  Its trace is a positive
weight. -/
theorem not_posSemidef_neg_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    ¬ (-dualAtom design label).PosSemidef := by
  intro hpsd
  have htrace := hpsd.trace_nonneg
  rw [Matrix.trace_neg, trace_dualAtom_eq_weight design hstressFree label] at htrace
  have hpos := design.weight_pos label
  linarith

/-- **NO DUAL FORM IS POSITIVE SEMIDEFINITE.**  A semidefinite form vanishing at
five directions annihilates all five, so every vector in its image is a common
normal of those five.  On the stress-free stratum no five directions share a
normal (`Gtz.not_five_coplanar_of_stressFree`), so the form is zero — and the
dual forms are not zero. -/
theorem not_posSemidef_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    ¬ (dualAtom design label).PosSemidef := by
  intro hpsd
  have hsymmetric := transpose_dualAtom design label
  have hkernel : ∀ other : Fin 6, other ≠ label →
      dualAtom design label *ᵥ design.atom other = 0 := by
    intro other hne
    refine mulVec_eq_zero_of_posSemidef_of_dotProduct_eq_zero hsymmetric hpsd ?_
    rw [dotProduct_dualAtom_mulVec design hstressFree label other]
    exact if_neg fun heq => hne heq.symm
  obtain ⟨rowIndex, colIndex, hentry⟩ :
      ∃ rowIndex colIndex, dualAtom design label rowIndex colIndex ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact dualAtom_ne_zero design hstressFree label
      (by ext firstIndex secondIndex; exact hall firstIndex secondIndex)
  have hnormalNe : (fun coord => dualAtom design label rowIndex coord) ≠ 0 :=
    fun hzero => hentry (congrFun hzero colIndex)
  obtain ⟨other, hother, hpairing⟩ := not_five_coplanar_of_stressFree design.atom
    (fun stress hstress => hstressFree stress hstress) _ hnormalNe label
  refine hpairing ?_
  have hcolumn : (dualAtom design label *ᵥ design.atom other) rowIndex = 0 := by
    rw [hkernel other hother]
    rfl
  rw [Matrix.mulVec, dotProduct] at hcolumn
  rw [dotProduct]
  refine Eq.trans (Finset.sum_congr rfl fun coord _ => ?_) hcolumn
  exact mul_comm _ _

/-- **EVERY FIVE-POINT CONIC OF THE STRATUM IS A REAL CONIC.**  Neither
semidefinite sign is available to it. -/
theorem not_posSemidef_and_not_posSemidef_neg_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (label : Fin 6) :
    ¬ (dualAtom design label).PosSemidef ∧ ¬ (-dualAtom design label).PosSemidef :=
  ⟨not_posSemidef_dualAtom design hstressFree label,
    not_posSemidef_neg_dualAtom design hstressFree label⟩

/-! ## 7. Six directions off a conic interpolate every quadratic form

The dual forms are a basis, and the coordinates of a symmetric form in that
basis are its own six values at the six directions.  So a quadratic form on
three-space is determined by what it reads at the six atoms of a stress-free
design, and the reconstruction is explicit.

The consequence for the campaign is the last theorem of this part: the gap of a
subset is an explicit combination of the six dual conics whose coefficients
carry NO WEIGHT.  They are the covering defects of the subset, which are
polynomials in the eighteen atom coordinates. -/

/-- The dual forms are linearly independent: a combination reads its own
coefficient at each atom. -/
theorem sum_smul_dualAtom_eq_zero_iff (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (value : Fin 6 → ℝ) :
    (∑ label, value label • dualAtom design label) = 0 ↔ value = 0 := by
  constructor
  · intro hzero
    funext other
    have hvalue := dotProduct_sum_smul_dualAtom_mulVec design hstressFree value other
    rw [hzero, Matrix.zero_mulVec, dotProduct_zero] at hvalue
    exact hvalue.symm
  · intro hzero
    rw [hzero]
    simp

/-- **THE SIX-POINT INTERPOLATION OF A QUADRATIC FORM.**  Every symmetric `3x3`
form is the combination of the six dual conics whose coefficients are the form's
own values at the six atoms.  Six directions off a conic therefore determine a
quadratic form completely, and this is the formula.

Together with `Gtz.sum_smul_dualAtom_eq_zero_iff` it says the dual forms are a
basis of the symmetric forms, dual to the atom matrices. -/
theorem eq_sum_smul_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (form : Matrix (Fin 3) (Fin 3) ℝ)
    (hsymmetric : formᵀ = form) :
    form = ∑ label, (design.atom label ⬝ᵥ (form *ᵥ design.atom label))
        • dualAtom design label := by
  have hdifference : form
      - ∑ label, (design.atom label ⬝ᵥ (form *ᵥ design.atom label))
          • dualAtom design label = 0 := by
    refine hasNoCommonQuadric_of_stressFree design hstressFree _ ?_ ?_
    · rw [Matrix.transpose_sub, hsymmetric, Matrix.transpose_sum]
      congr 1
      exact Finset.sum_congr rfl fun label _ => by
        rw [Matrix.transpose_smul, transpose_dualAtom design label]
    · intro other
      rw [Matrix.sub_mulVec, dotProduct_sub,
        dotProduct_sum_smul_dualAtom_mulVec design hstressFree
          (fun label => design.atom label ⬝ᵥ (form *ᵥ design.atom label)) other,
        sub_self]
  exact sub_eq_zero.mp hdifference

/-- **THE WEIGHT-FREE NORMAL FORM OF EVERY GAP.**  The gap of a subset is the
combination of the six dual conics whose coefficients are that subset's covering
defects — the squared pairings of the subset against a label, minus that label's
leverage.  No weight occurs on either side.

`Gtz.leverage_le_sum_sq_dotProduct_of_dominates` says every coefficient of a
DOMINATING subset is nonnegative.  So domination forces the gap into the
nonnegative cone of this fixed basis, and the whole test is six polynomials in
the eighteen atom coordinates. -/
theorem subsetSum_sub_one_eq_sum_smul_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (selected : Finset (Fin 6)) :
    subsetSum design selected - 1
      = ∑ label, ((∑ other ∈ selected, (design.atom other ⬝ᵥ design.atom label) ^ 2)
          - leverageOf (design.atom label)) • dualAtom design label := by
  have hsymmetric : (subsetSum design selected - 1)ᵀ = subsetSum design selected - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
    congr 1
    exact Finset.sum_congr rfl fun other _ => transpose_atomMatrix_self _
  have hcoefficient : ∀ label : Fin 6,
      design.atom label ⬝ᵥ ((subsetSum design selected - 1) *ᵥ design.atom label)
        = (∑ other ∈ selected, (design.atom other ⬝ᵥ design.atom label) ^ 2)
          - leverageOf (design.atom label) := by
    intro label
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_subsetSum_mulVec_of_finset, ← leverageOf_eq_dotProduct_self]
  conv_lhs => rw [eq_sum_smul_dualAtom design hstressFree _ hsymmetric]
  exact Finset.sum_congr rfl fun label _ => by rw [hcoefficient label]

/-! ### The covering defect, named

The coefficients of the gap in the dual basis deserve a name, because they carry
no weight and the domination test reads them directly. -/

/-- **THE COVERING DEFECT** of a subset at a label: the squared pairings of the
subset's atoms against that label, minus that label's leverage.  It is the
coefficient of `Gtz.dualAtom` at that label in the gap of the subset, and it is
a polynomial in the atom coordinates with no weight in it. -/
def coveringDefect (design : WeightedDesign m k) (selected : Finset (Fin m))
    (label : Fin m) : ℝ :=
  (∑ other ∈ selected, (design.atom other ⬝ᵥ design.atom label) ^ 2)
    - leverageOf (design.atom label)

/-- The gap in the dual basis, with the coefficients named. -/
theorem subsetSum_sub_one_eq_sum_coveringDefect_smul_dualAtom (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (selected : Finset (Fin 6)) :
    subsetSum design selected - 1
      = ∑ label, coveringDefect design selected label • dualAtom design label :=
  subsetSum_sub_one_eq_sum_smul_dualAtom design hstressFree selected

/-- A dominating subset has nonnegative covering defect at every label. -/
theorem coveringDefect_nonneg_of_dominates (design : WeightedDesign m k)
    {selected : Finset (Fin m)} (hdominates : Dominates design selected) (label : Fin m) :
    0 ≤ coveringDefect design selected label :=
  sub_nonneg.mpr (leverage_le_sum_sq_dotProduct_of_dominates design hdominates label)

/-- **A DOMINATING SUBSET STRICTLY OVERCOVERS SOMEWHERE.**  On the stress-free
stratum the covering defects of a dominating subset are not all zero, because a
vanishing defect vector would make the gap vanish, and no gap of a stress-free
design vanishes.  With the covering law this promotes one of the six
inequalities to a STRICT one, at a label the theorem does not name.

This is the weight-free form of the fact that a dominating subset can never sit
exactly on the identity. -/
theorem exists_coveringDefect_pos_of_dominates (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) {selected : Finset (Fin 6)}
    (hdominates : Dominates design selected) :
    ∃ label, 0 < coveringDefect design selected label := by
  by_contra hall
  push_neg at hall
  refine subsetSum_sub_one_ne_zero_of_stressFree design hstressFree selected ?_
  rw [subsetSum_sub_one_eq_sum_coveringDefect_smul_dualAtom design hstressFree selected]
  refine Finset.sum_eq_zero fun label _ => ?_
  rw [le_antisymm (hall label) (coveringDefect_nonneg_of_dominates design hdominates label),
    zero_smul]

/-- **THE TRACE BRIDGE.**  The trace of a gap is the covering defect vector
paired with the weight vector, because the dual forms have the weights as their
traces.  This is the one place a weight re-enters the weight-free normal
form. -/
theorem trace_subsetSum_sub_one_eq_sum_coveringDefect_mul_weight (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) (selected : Finset (Fin 6)) :
    Matrix.trace (subsetSum design selected - 1)
      = ∑ label, coveringDefect design selected label * design.weight label := by
  rw [subsetSum_sub_one_eq_sum_coveringDefect_smul_dualAtom design hstressFree selected,
    Matrix.trace_sum]
  exact Finset.sum_congr rfl fun label _ => by
    rw [Matrix.trace_smul, smul_eq_mul, trace_dualAtom_eq_weight design hstressFree label]

/-! ## 8. The rescaling fiber

The GTZ question reads only the atoms, and the atoms carry two kinds of data:
the six points of the projective plane, and the six lengths.  This part measures
the length fiber exactly.  Both statements are unconditional at every size and
rank — no stress hypothesis appears. -/

/-- **THE SHARE IS CONSTANT ALONG THE RESCALING FIBER.**  Moving each atom along
its own ray, with the compensating weight change that
`Gtz.UniformPositionBridge.rescaledDesign` makes, leaves every share untouched.
The landed `Gtz.atomShare_eq_of_atom_smul_of_stressFree` compares two GIVEN
stress-free designs; this compares a design with a design it CONSTRUCTS, and
needs no stress hypothesis and no rank three. -/
theorem atomShare_rescaledDesign (design : WeightedDesign m k) (scaleSq : Fin m → ℝ)
    (hscalePos : ∀ label, 0 < scaleSq label)
    (hweightSum : ∑ label, design.weight label / scaleSq label = 1) (label : Fin m) :
    atomShare (UniformPositionBridge.rescaledDesign design scaleSq hscalePos hweightSum) label
      = atomShare design label := by
  have hweight : (UniformPositionBridge.rescaledDesign design scaleSq hscalePos hweightSum).weight
      label = design.weight label / scaleSq label := rfl
  rw [atomShare, atomShare, hweight, UniformPositionBridge.rescaledDesign_atom,
    leverageOf_smul, Real.sq_sqrt (hscalePos label).le, ← mul_assoc,
    div_mul_cancel₀ _ (hscalePos label).ne']

/-- Every design has at least one label. -/
theorem univ_nonempty_of_design (design : WeightedDesign m k) :
    (Finset.univ : Finset (Fin m)).Nonempty := by
  rcases Nat.eq_zero_or_pos m with hzero | hpos
  · subst hzero
    exact absurd design.weight_sum_one (by simp)
  · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hpos)

/-- **EVERY RAY OF ATOM SCALES CARRIES EXACTLY ONE DESIGN.**  Fix the six
directions and fix the RATIOS of the six lengths.  Then there is one and only
one global factor that restores the normalization of the weights.  So the fiber
of the projective configuration map through a design is the positive orthant of
scales modulo one global factor, and no smaller. -/
theorem existsUnique_normalizingFactor (design : WeightedDesign m k) (scaleSq : Fin m → ℝ)
    (hscalePos : ∀ label, 0 < scaleSq label) :
    ∃! factor : ℝ, 0 < factor
      ∧ ∑ label, design.weight label / (factor * scaleSq label) = 1 := by
  have htotalPos : 0 < ∑ label, design.weight label / scaleSq label :=
    Finset.sum_pos (fun label _ => div_pos (design.weight_pos label) (hscalePos label))
      (univ_nonempty_of_design design)
  have hrewrite : ∀ factor : ℝ, ∑ label, design.weight label / (factor * scaleSq label)
      = (∑ label, design.weight label / scaleSq label) / factor := by
    intro factor
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun label _ => by rw [mul_comm, ← div_div]
  refine ⟨∑ label, design.weight label / scaleSq label, ⟨htotalPos, ?_⟩, ?_⟩
  · rw [hrewrite]
    exact div_self htotalPos.ne'
  · rintro factor ⟨hfactorPos, hfactorSum⟩
    rw [hrewrite, div_eq_one_iff_eq hfactorPos.ne'] at hfactorSum
    exact hfactorSum.symm

end Gtz
