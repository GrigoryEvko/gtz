/-
# The conic Caratheodory kit and the rank-two circuit reduction

Module-generic conic Caratheodory with a monotone objective (no design content:
finite family of vectors, nonnegative coefficients, recession-flat objective), its
application discharging `RankTwoCircuitReduction` outright, the slide by-product
(`p ⊥ ker` of the projector-dependency map giving the symmetric trace-one shape
matrix on the equality locus of a rank-two tie), and the hinge one residual
lighter: `not_isTie_of_equalityStratum` carries `RankTwoEqualityStratum` as its
sole `Prop` hypothesis.
-/
import Mathlib
import Gtz.Ties.RankTwoMassCircuit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1: the module-generic conic reduction

No design, no matrices, no rank: a finite family of vectors in a finite-dimensional real
module, a nonnegative coefficient vector, and a linear objective that does not increase
along the recession cone. -/

section ConicReduction

variable {label : Type*} [Fintype label] [DecidableEq label]
variable {space : Type*} [AddCommGroup space] [Module ℝ space] [Module.Finite ℝ space]

/-- More vectors than dimensions carry a linear dependency, indexed by the labels rather
than by the vectors themselves -- the family may repeat a vector, so the finset-of-vectors
form of the pigeonhole would not apply. -/
theorem exists_relation_of_finrank_lt_card (vector : label → space) (support : Finset label)
    (hoversized : Module.finrank ℝ space < support.card) :
    ∃ relation : label → ℝ, (∀ index, index ∉ support → relation index = 0)
      ∧ (∑ index, relation index • vector index = 0)
      ∧ ∃ witness ∈ support, relation witness ≠ 0 := by
  classical
  have hdependent :
      ¬ LinearIndependent ℝ (fun index : { x // x ∈ support } => vector index.1) := by
    intro hindependent
    have hcardLe := hindependent.fintype_card_le_finrank
    rw [Fintype.card_coe] at hcardLe
    omega
  obtain ⟨relationOnSupport, hrelationSum, witness, hwitnessNe⟩ :=
    Fintype.not_linearIndependent_iff.mp hdependent
  refine ⟨fun index => if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0,
    fun index hout => dif_neg hout, ?_, witness.1, witness.2, ?_⟩
  · have hrestrict : ∑ index,
          (if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0) • vector index
        = ∑ index ∈ support,
          (if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0)
            • vector index := by
      refine (Finset.sum_subset (Finset.subset_univ support) ?_).symm
      intro index _ hout
      rw [dif_neg hout, zero_smul]
    rw [hrestrict, ← Finset.sum_attach support
      (fun index => (if hmem : index ∈ support then relationOnSupport ⟨index, hmem⟩ else 0)
        • vector index), ← hrelationSum, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun subtypeIndex _ => ?_
    simp only [dif_pos subtypeIndex.2, Subtype.coe_eta]
  · simpa only [dif_pos witness.2, Subtype.coe_eta] using hwitnessNe

omit [Fintype label] in
/-- Sliding a nonnegative coefficient vector along a direction that is negative somewhere
reaches the boundary of the nonnegative orthant: at some pivot label the coefficient hits
exactly zero, and no coefficient has gone negative on the way. -/
theorem exists_step_zeroing_one_label (coefficient direction : label → ℝ)
    (support : Finset label) (hcoefficientNonneg : ∀ index, 0 ≤ coefficient index)
    (hdirectionOffSupport : ∀ index, index ∉ support → direction index = 0)
    (hdirectionNegative : ∃ index ∈ support, direction index < 0) :
    ∃ (step : ℝ) (pivot : label), 0 ≤ step ∧ pivot ∈ support
      ∧ coefficient pivot + step * direction pivot = 0
      ∧ ∀ index, 0 ≤ coefficient index + step * direction index := by
  classical
  set negativeLabels := support.filter (fun index => direction index < 0) with hnegativeDef
  have hnegativeNonempty : negativeLabels.Nonempty := by
    obtain ⟨index, hmem, hneg⟩ := hdirectionNegative
    exact ⟨index, by rw [hnegativeDef, Finset.mem_filter]; exact ⟨hmem, hneg⟩⟩
  obtain ⟨pivot, hpivotMem, hpivotMin⟩ :=
    negativeLabels.exists_min_image
      (fun index => coefficient index / (- direction index)) hnegativeNonempty
  rw [hnegativeDef, Finset.mem_filter] at hpivotMem
  have hpivotNegative : direction pivot < 0 := hpivotMem.2
  have hpivotDenomPos : 0 < - direction pivot := by linarith
  refine ⟨coefficient pivot / (- direction pivot), pivot,
    div_nonneg (hcoefficientNonneg pivot) hpivotDenomPos.le, hpivotMem.1, ?_, ?_⟩
  · have hpivotNe : direction pivot ≠ 0 := ne_of_lt hpivotNegative
    field_simp
    ring
  · intro index
    by_cases hnegativeDirection : direction index < 0
    · have hindexSupport : index ∈ support := by
        by_contra hout
        rw [hdirectionOffSupport index hout] at hnegativeDirection
        exact lt_irrefl 0 hnegativeDirection
      have hindexMem : index ∈ negativeLabels := by
        rw [hnegativeDef, Finset.mem_filter]; exact ⟨hindexSupport, hnegativeDirection⟩
      have hindexDenomPos : 0 < - direction index := by linarith
      have hscaled : coefficient pivot / (- direction pivot) * (- direction index)
          ≤ coefficient index :=
        (le_div_iff₀ hindexDenomPos).mp (hpivotMin index hindexMem)
      nlinarith [hscaled]
    · push Not at hnegativeDirection
      have hproduct : 0 ≤ coefficient pivot / (- direction pivot) * direction index :=
        mul_nonneg (div_nonneg (hcoefficientNonneg pivot) hpivotDenomPos.le) hnegativeDirection
      linarith [hcoefficientNonneg index]

/-- The pivot loop, with the support cardinality as the termination measure. -/
private theorem exists_reduced_coefficient_aux (vector : label → space)
    (objective : label → ℝ) (dimensionBound : ℕ)
    (hdimension : Module.finrank ℝ space ≤ dimensionBound)
    (hrecessionObjective : ∀ ray : label → ℝ, (∀ index, 0 ≤ ray index) →
      (∑ index, ray index • vector index = 0) →
      ∑ index, ray index * objective index ≤ 0) :
    ∀ (fuel : ℕ) (coefficient : label → ℝ) (support : Finset label),
      support.card ≤ fuel → (∀ index, 0 ≤ coefficient index) →
      (∀ index, index ∉ support → coefficient index = 0) →
      ∃ (reduced : label → ℝ) (reducedSupport : Finset label),
        (∀ index, 0 ≤ reduced index)
        ∧ (∀ index, index ∉ reducedSupport → reduced index = 0)
        ∧ reducedSupport.card ≤ dimensionBound
        ∧ (∑ index, reduced index • vector index = ∑ index, coefficient index • vector index)
        ∧ (∑ index, coefficient index * objective index
            ≤ ∑ index, reduced index * objective index) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro coefficient support hcard hcoefficientNonneg hcoefficientOff
      exact ⟨coefficient, support, hcoefficientNonneg, hcoefficientOff,
        le_trans hcard (Nat.zero_le _), rfl, le_refl _⟩
  | succ previousFuel inductiveStep =>
      intro coefficient support hcard hcoefficientNonneg hcoefficientOff
      by_cases hsmall : support.card ≤ dimensionBound
      · exact ⟨coefficient, support, hcoefficientNonneg, hcoefficientOff, hsmall, rfl, le_refl _⟩
      push Not at hsmall
      obtain ⟨relation, hrelationOff, hrelationZero, witness, hwitnessMem, hwitnessNe⟩ :=
        exists_relation_of_finrank_lt_card vector support (lt_of_le_of_lt hdimension hsmall)
      -- Orient the dependency so that sliding along it cannot lower the objective, and so
      -- that it actually has a direction to slide in.
      have horiented : ∀ candidate : label → ℝ,
          (∀ index, index ∉ support → candidate index = 0) →
          (∑ index, candidate index • vector index = 0) →
          0 ≤ ∑ index, candidate index * objective index →
          candidate witness ≠ 0 →
          ∃ direction : label → ℝ,
            (∀ index, index ∉ support → direction index = 0)
            ∧ (∑ index, direction index • vector index = 0)
            ∧ (0 ≤ ∑ index, direction index * objective index)
            ∧ ∃ index ∈ support, direction index < 0 := by
        intro candidate hcandidateOff hcandidateZero hcandidateObjective hcandidateWitness
        by_cases hnegativeExists : ∃ index ∈ support, candidate index < 0
        · exact ⟨candidate, hcandidateOff, hcandidateZero, hcandidateObjective, hnegativeExists⟩
        push Not at hnegativeExists
        have hcandidateNonneg : ∀ index, 0 ≤ candidate index := by
          intro index
          by_cases hmem : index ∈ support
          · exact hnegativeExists index hmem
          · rw [hcandidateOff index hmem]
        have hcandidateObjectiveZero : ∑ index, candidate index * objective index = 0 :=
          le_antisymm (hrecessionObjective candidate hcandidateNonneg hcandidateZero)
            hcandidateObjective
        refine ⟨fun index => - candidate index, fun index hout => by
            simp only [hcandidateOff index hout, neg_zero], ?_, ?_,
          witness, hwitnessMem, ?_⟩
        · simp only [neg_smul, Finset.sum_neg_distrib, hcandidateZero, neg_zero]
        · simp only [neg_mul, Finset.sum_neg_distrib, hcandidateObjectiveZero, neg_zero,
            le_refl]
        · have hwitnessPos : 0 < candidate witness :=
            lt_of_le_of_ne (hcandidateNonneg witness) (Ne.symm hcandidateWitness)
          simpa using hwitnessPos
      have hdirectionExists : ∃ direction : label → ℝ,
          (∀ index, index ∉ support → direction index = 0)
          ∧ (∑ index, direction index • vector index = 0)
          ∧ (0 ≤ ∑ index, direction index * objective index)
          ∧ ∃ index ∈ support, direction index < 0 := by
        by_cases hobjective : 0 ≤ ∑ index, relation index * objective index
        · exact horiented relation hrelationOff hrelationZero hobjective hwitnessNe
        push Not at hobjective
        refine horiented (fun index => - relation index) (fun index hout => by
            simp only [hrelationOff index hout, neg_zero]) ?_ ?_ (by
              simpa using hwitnessNe)
        · simp only [neg_smul, Finset.sum_neg_distrib, hrelationZero, neg_zero]
        · simp only [neg_mul, Finset.sum_neg_distrib]
          linarith
      obtain ⟨direction, hdirectionOff, hdirectionZero, hdirectionObjective,
        hdirectionNegative⟩ := hdirectionExists
      obtain ⟨step, pivot, hstepNonneg, hpivotMem, hpivotZero, hshiftedNonneg⟩ :=
        exists_step_zeroing_one_label coefficient direction support hcoefficientNonneg
          hdirectionOff hdirectionNegative
      obtain ⟨shifted, hshiftedDef⟩ :
          ∃ shifted : label → ℝ, shifted = fun index => coefficient index + step * direction index :=
        ⟨_, rfl⟩
      have hshiftedNonnegAll : ∀ index, 0 ≤ shifted index := by
        intro index; rw [hshiftedDef]; exact hshiftedNonneg index
      have hshiftedOff : ∀ index, index ∉ support.erase pivot → shifted index = 0 := by
        intro index hout
        rw [Finset.mem_erase] at hout
        push Not at hout
        simp only [hshiftedDef]
        by_cases hindexPivot : index = pivot
        · rw [hindexPivot]; exact hpivotZero
        · have hindexOut : index ∉ support := hout hindexPivot
          rw [hcoefficientOff index hindexOut, hdirectionOff index hindexOut]; ring
      have hshiftedCard : (support.erase pivot).card ≤ previousFuel := by
        rw [Finset.card_erase_of_mem hpivotMem]
        have hpositive : 1 ≤ support.card := Finset.card_pos.mpr ⟨pivot, hpivotMem⟩
        omega
      have hshiftedVector : ∑ index, shifted index • vector index
          = ∑ index, coefficient index • vector index := by
        have hsplit : ∀ index : label, shifted index • vector index
            = coefficient index • vector index + step • (direction index • vector index) := by
          intro index
          rw [hshiftedDef]
          simp only [add_smul, smul_smul]
        rw [Finset.sum_congr rfl fun index _ => hsplit index, Finset.sum_add_distrib,
          ← Finset.smul_sum, hdirectionZero, smul_zero, add_zero]
      have hshiftedObjective : ∑ index, coefficient index * objective index
          ≤ ∑ index, shifted index * objective index := by
        have hsplit : ∀ index : label, shifted index * objective index
            = coefficient index * objective index
              + step * (direction index * objective index) := by
          intro index; rw [hshiftedDef]; ring
        rw [Finset.sum_congr rfl fun index _ => hsplit index, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        linarith [mul_nonneg hstepNonneg hdirectionObjective]
      obtain ⟨reduced, reducedSupport, hreducedNonneg, hreducedOff, hreducedCard,
        hreducedVector, hreducedObjective⟩ :=
        inductiveStep shifted (support.erase pivot) hshiftedCard hshiftedNonnegAll hshiftedOff
      exact ⟨reduced, reducedSupport, hreducedNonneg, hreducedOff, hreducedCard,
        hreducedVector.trans hshiftedVector, le_trans hshiftedObjective hreducedObjective⟩

omit [DecidableEq label] [Module.Finite ℝ space] in
/-- **THE STANDARD TRIGGER FOR THE RECESSION HYPOTHESIS.**  Suppose a linear functional is
nonnegative on every vector of the family.  Then a nonnegative combination that vanishes is
annihilated by that functional label by label, so any objective carrying the functional as a
factor is flat -- not merely non-increasing -- along the entire recession cone, whatever the
other factor does.

This is how a conic Caratheodory application normally discharges the hypothesis of
`exists_reduced_coefficient_of_recession`: the functional is the mass, the other factor is
whatever is being maximised per unit mass. -/
theorem recessionObjective_of_nonneg_functional (vector : label → space)
    (functional : space →ₗ[ℝ] ℝ) (factor : label → ℝ)
    (hfunctionalNonneg : ∀ index, 0 ≤ functional (vector index))
    (ray : label → ℝ) (hrayNonneg : ∀ index, 0 ≤ ray index)
    (hrayVanishes : ∑ index, ray index • vector index = 0) :
    ∑ index, ray index * (functional (vector index) * factor index) ≤ 0 := by
  have htotalVanishes : ∑ index, ray index * functional (vector index) = 0 := by
    have happlied : functional (∑ index, ray index • vector index) = 0 := by
      rw [hrayVanishes, map_zero]
    rw [map_sum] at happlied
    simpa only [map_smul, smul_eq_mul] using happlied
  have htermVanishes : ∀ index, ray index * functional (vector index) = 0 := fun index =>
    (Finset.sum_eq_zero_iff_of_nonneg fun other _ =>
        mul_nonneg (hrayNonneg other) (hfunctionalNonneg other)).mp htotalVanishes index
      (Finset.mem_univ index)
  refine le_of_eq (Finset.sum_eq_zero fun index _ => ?_)
  calc ray index * (functional (vector index) * factor index)
      = ray index * functional (vector index) * factor index := by ring
    _ = 0 := by rw [htermVanishes index, zero_mul]

/-- **CONIC CARATHEODORY, MONOTONE.**  A nonnegative coefficient vector realising a point
of the conic hull of finitely many vectors can be replaced by one supported on at most
`finrank` labels, realising the SAME point and scoring at least as high against a linear
objective -- provided the objective does not increase along the recession cone.

The recession hypothesis is not a technicality: without it the monotone conclusion is
false, since an unbounded objective direction can live entirely on labels the reduction
must discard.  It is exactly the boundedness condition of the underlying linear program,
and it holds automatically whenever a nonnegative linear functional separates the vectors
from zero -- which is how the rank-two application discharges it, by trace. -/
theorem exists_reduced_coefficient_of_recession (vector : label → space)
    (objective coefficient : label → ℝ) (dimensionBound : ℕ)
    (hdimension : Module.finrank ℝ space ≤ dimensionBound)
    (hcoefficientNonneg : ∀ index, 0 ≤ coefficient index)
    (hrecessionObjective : ∀ ray : label → ℝ, (∀ index, 0 ≤ ray index) →
      (∑ index, ray index • vector index = 0) →
      ∑ index, ray index * objective index ≤ 0) :
    ∃ (reduced : label → ℝ) (support : Finset label),
      (∀ index, 0 ≤ reduced index)
      ∧ (∀ index, index ∉ support → reduced index = 0)
      ∧ support.card ≤ dimensionBound
      ∧ (∑ index, reduced index • vector index = ∑ index, coefficient index • vector index)
      ∧ (∑ index, coefficient index * objective index
          ≤ ∑ index, reduced index * objective index) :=
  exists_reduced_coefficient_aux vector objective dimensionBound hdimension hrecessionObjective
    (Finset.univ : Finset label).card coefficient Finset.univ (le_refl _) hcoefficientNonneg
    fun index hout => absurd (Finset.mem_univ index) hout

end ConicReduction

/-! ## Part 2: monotone selection

The averaging step the convex-decomposition route would have needed.  It is not used
below -- the pivot loop above supersedes it -- but it is two lines and it is the reusable
form of "some summand of a convex decomposition beats the average". -/

/-- **Some member of a convex combination beats the average.** -/
theorem exists_index_ge_convex_combination {label : Type*} [Fintype label]
    (weight value : label → ℝ) (hweightNonneg : ∀ index, 0 ≤ weight index)
    (hweightTotal : ∑ index, weight index = 1) :
    ∃ index, ∑ other, weight other * value other ≤ value index := by
  classical
  by_contra hallBelow
  push Not at hallBelow
  obtain ⟨pivot, hpivotMem, hpivotPos⟩ :
      ∃ pivot ∈ (Finset.univ : Finset label), 0 < weight pivot := by
    by_contra hnonePositive
    push Not at hnonePositive
    have hvanishes : ∑ index, weight index = 0 :=
      Finset.sum_eq_zero fun index hmem =>
        le_antisymm (hnonePositive index hmem) (hweightNonneg index)
    rw [hweightTotal] at hvanishes
    exact one_ne_zero hvanishes
  have hstrict : ∑ index, weight index * value index
      < ∑ index, weight index * ∑ other, weight other * value other :=
    Finset.sum_lt_sum
      (fun index _ => mul_le_mul_of_nonneg_left (hallBelow index).le (hweightNonneg index))
      ⟨pivot, hpivotMem, mul_lt_mul_of_pos_left (hallBelow pivot) hpivotPos⟩
  rw [← Finset.sum_mul, hweightTotal, one_mul] at hstrict
  exact lt_irrefl _ hstrict

/-! ## Part 3: the rank-two specialisation -/

/-- The three independent coordinates of the symmetric rank-one atom `g g^T` in the plane.
A rank-two Parseval identity is a linear equation in exactly these, which is why three
atoms always suffice. -/
def symmetricCoordinates (atomVector : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![atomVector 0 * atomVector 0, atomVector 0 * atomVector 1, atomVector 1 * atomVector 1]

/-- Two coefficient vectors that agree on the three symmetric coordinates agree on the
whole atom sum: the `(1,0)` entry is the `(0,1)` entry because rank-one atoms are
symmetric, so the fourth matrix entry carries no extra information. -/
theorem sum_smul_atomMatrix_eq_of_symmetricCoordinates {size : ℕ}
    (atomVector : Fin size → (Fin 2 → ℝ)) (firstCoefficient secondCoefficient : Fin size → ℝ)
    (hcoordinates : ∑ label, firstCoefficient label • symmetricCoordinates (atomVector label)
      = ∑ label, secondCoefficient label • symmetricCoordinates (atomVector label)) :
    ∑ label, firstCoefficient label • atomMatrix (atomVector label)
      = ∑ label, secondCoefficient label • atomMatrix (atomVector label) := by
  have hcoordinateSum : ∀ (weightVector : Fin size → ℝ) (index : Fin 3),
      (∑ label, weightVector label • symmetricCoordinates (atomVector label)) index
        = ∑ label, weightVector label * symmetricCoordinates (atomVector label) index := by
    intro weightVector index
    simp [Finset.sum_apply]
  have hmatrixEntry : ∀ (weightVector : Fin size → ℝ) (row col : Fin 2),
      (∑ label, weightVector label • atomMatrix (atomVector label)) row col
        = ∑ label, weightVector label * (atomVector label row * atomVector label col) := by
    intro weightVector row col
    simp [Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply]
  have hfirstCoordinate := congrFun hcoordinates 0
  have hsecondCoordinate := congrFun hcoordinates 1
  have hthirdCoordinate := congrFun hcoordinates 2
  rw [hcoordinateSum, hcoordinateSum] at hfirstCoordinate hsecondCoordinate hthirdCoordinate
  simp only [symmetricCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hfirstCoordinate hsecondCoordinate hthirdCoordinate
  ext row col
  rw [hmatrixEntry, hmatrixEntry]
  fin_cases row <;> fin_cases col
  · exact hfirstCoordinate
  · exact hsecondCoordinate
  · calc ∑ label, firstCoefficient label * (atomVector label 1 * atomVector label 0)
        = ∑ label, firstCoefficient label * (atomVector label 0 * atomVector label 1) :=
          Finset.sum_congr rfl fun label _ => by ring
      _ = ∑ label, secondCoefficient label * (atomVector label 0 * atomVector label 1) :=
          hsecondCoordinate
      _ = ∑ label, secondCoefficient label * (atomVector label 1 * atomVector label 0) :=
          Finset.sum_congr rfl fun label _ => by ring
  · exact hthirdCoordinate

/-- **THE RANK-TWO REDUCTION.**  Every nonnegative coefficient vector on the atoms of a
rank-two design can be pushed onto at most THREE atoms, reproducing the same atom sum and
scoring at least as high against an ARBITRARY heaviness vector.  At the design's own weights
the atom sum is the identity, which is the circuit reduction residual below.

The heaviness vector is unconstrained, so this is pure convexity: the design's coefficient
vector solves three scalar equations in nonnegative unknowns, and a solution of three
equations can be squeezed onto three unknowns without losing ground against any linear
objective.  The one thing the squeeze needs is that the recession cone of the system is
objective-flat, and the trace supplies it -- a nonnegative combination of atom projectors
that vanishes has every leverage term zero, so it carries no heaviness at all. -/
theorem exists_threeAtomReduction_atLeastAsHeavy {size : ℕ} (D : WeightedDesign size 2)
    (heaviness coefficient : Fin size → ℝ) (hcoefficientNonneg : ∀ label, 0 ≤ coefficient label) :
    ∃ (subWeight : Fin size → ℝ) (support : Finset (Fin size)),
      (∀ label, 0 ≤ subWeight label)
      ∧ (∀ label, label ∉ support → subWeight label = 0)
      ∧ support.card ≤ 3
      ∧ (∑ label, subWeight label • atomMatrix (D.atom label)
          = ∑ label, coefficient label • atomMatrix (D.atom label))
      ∧ (∑ label, coefficient label * leverageOf (D.atom label) * heaviness label)
          ≤ ∑ label, subWeight label * leverageOf (D.atom label) * heaviness label := by
  classical
  obtain ⟨planarTrace, hplanarTraceDef⟩ :
      ∃ planarTrace : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
        ∀ coordinates : Fin 3 → ℝ, planarTrace coordinates = coordinates 0 + coordinates 2 :=
    ⟨{ toFun := fun coordinates => coordinates 0 + coordinates 2
       map_add' := fun first second => by simp only [Pi.add_apply]; ring
       map_smul' := fun scalar coordinates => by
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, fun _ => rfl⟩
  -- The trace of an atom projector, read off the three symmetric coordinates, is its
  -- leverage: this single identity carries both the recession hypothesis and the final
  -- translation back into design language.
  have hplanarTraceOfAtom : ∀ label : Fin size,
      planarTrace (symmetricCoordinates (D.atom label)) = leverageOf (D.atom label) := by
    intro label
    rw [hplanarTraceDef, leverageOf, Fin.sum_univ_two]
    simp only [symmetricCoordinates, Matrix.cons_val_zero, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    ring
  have hplanarTraceNonneg : ∀ label : Fin size,
      0 ≤ planarTrace (symmetricCoordinates (D.atom label)) := by
    intro label
    rw [hplanarTraceOfAtom, leverageOf]
    exact Finset.sum_nonneg fun coordinate _ => sq_nonneg _
  obtain ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard, hsubVector, hsubObjective⟩ :=
    exists_reduced_coefficient_of_recession
      (fun label => symmetricCoordinates (D.atom label))
      (fun label => planarTrace (symmetricCoordinates (D.atom label)) * heaviness label)
      coefficient 3 (by simp) hcoefficientNonneg
      fun ray hrayNonneg hrayVanishes =>
        recessionObjective_of_nonneg_functional _ planarTrace heaviness hplanarTraceNonneg
          ray hrayNonneg hrayVanishes
  refine ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard,
    sum_smul_atomMatrix_eq_of_symmetricCoordinates D.atom subWeight coefficient hsubVector, ?_⟩
  have hrestate : ∀ weightVector : Fin size → ℝ,
      ∑ label, weightVector label * leverageOf (D.atom label) * heaviness label
        = ∑ label, weightVector label
            * (planarTrace (symmetricCoordinates (D.atom label)) * heaviness label) :=
    fun weightVector => Finset.sum_congr rfl fun label _ => by
      rw [hplanarTraceOfAtom]; ring
  rw [hrestate coefficient, hrestate subWeight]
  exact hsubObjective

/-- **THE RANK-TWO CIRCUIT REDUCTION.**  The residual itself: the sub-collection reproduces
the identity, because the design's own coefficient vector does. -/
theorem exists_threeAtomSubdesign_atLeastAsHeavy (size : ℕ) (D : WeightedDesign size 2)
    (heaviness : Fin size → ℝ) :
    ∃ (subWeight : Fin size → ℝ) (support : Finset (Fin size)),
      (∀ label, 0 ≤ subWeight label)
      ∧ (∀ label, label ∉ support → subWeight label = 0)
      ∧ support.card ≤ 3
      ∧ (∑ label, subWeight label • atomMatrix (D.atom label) = 1)
      ∧ (∑ label, D.weight label * leverageOf (D.atom label) * heaviness label)
          ≤ ∑ label, subWeight label * leverageOf (D.atom label) * heaviness label := by
  obtain ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard, hsubVector, hsubHeavy⟩ :=
    exists_threeAtomReduction_atLeastAsHeavy D heaviness D.weight
      fun label => (D.weight_pos label).le
  exact ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard,
    hsubVector.trans D.isParseval, hsubHeavy⟩

/-! ## Part 4: the slide by-product -- the shape matrix of the heaviness vector

The reduction slides a coefficient vector along a dependency until a coefficient hits zero.
Run the same slide at a coefficient vector that is strictly positive everywhere and already
MAXIMAL: now it may be slid in either direction by a small step without leaving the feasible
set, so maximality forces the objective to annihilate every dependency.  A vector
annihilating every dependency is a linear functional read along the family; and in rank two
a linear functional on the three symmetric coordinates IS a symmetric two by two matrix.
The mass normalisation then pins its trace.  This is the `p_c = <g_c, R g_c> / l_c` input the
`nu != 1` band of the equality residual is blocked on. -/

section SlideByProduct

variable {label : Type*} [Fintype label] [DecidableEq label]
variable {space : Type*} [AddCommGroup space] [Module ℝ space]

omit [DecidableEq label] in
/-- **THE SLIDE, at a maximiser.**  A strictly positive feasible coefficient vector that
maximises a linear objective over the feasible set forces that objective to annihilate every
dependency of the family: both `+relation` and `-relation` are admissible small steps, so the
objective cannot move at all along either.

Strict positivity is what buys the two-sided step; it is free for a weighted design, whose
weights are positive by definition. -/
theorem sum_relation_mul_objective_eq_zero_of_maximal (vector : label → space)
    (objective coefficient : label → ℝ) (hcoefficientPos : ∀ index, 0 < coefficient index)
    (hmaximal : ∀ competitor : label → ℝ, (∀ index, 0 ≤ competitor index) →
      (∑ index, competitor index • vector index = ∑ index, coefficient index • vector index) →
      ∑ index, competitor index * objective index
        ≤ ∑ index, coefficient index * objective index)
    (relation : label → ℝ) (hrelation : ∑ index, relation index • vector index = 0) :
    ∑ index, relation index * objective index = 0 := by
  classical
  have honeSided : ∀ signedRelation : label → ℝ,
      (∑ index, signedRelation index • vector index = 0) →
      ∑ index, signedRelation index * objective index ≤ 0 := by
    intro signedRelation hsigned
    rcases isEmpty_or_nonempty label with hempty | hnonempty
    · haveI := hempty
      simp
    haveI := hnonempty
    obtain ⟨minimiser, _, hminimal⟩ :=
      Finset.univ.exists_min_image coefficient Finset.univ_nonempty
    obtain ⟨spread, hspreadDef⟩ :
        ∃ spread : ℝ, spread = ∑ index, |signedRelation index| := ⟨_, rfl⟩
    have hspreadNonneg : 0 ≤ spread := by
      rw [hspreadDef]; exact Finset.sum_nonneg fun index _ => abs_nonneg _
    have hdenomPos : (0 : ℝ) < 1 + spread := by linarith
    obtain ⟨stepSize, hstepDef⟩ :
        ∃ stepSize : ℝ, stepSize = coefficient minimiser / (1 + spread) := ⟨_, rfl⟩
    have hstepPos : 0 < stepSize := by
      rw [hstepDef]; exact div_pos (hcoefficientPos minimiser) hdenomPos
    have hshiftedNonneg : ∀ index, 0 ≤ coefficient index + stepSize * signedRelation index := by
      intro index
      have habsBound : |signedRelation index| ≤ spread := by
        rw [hspreadDef]
        exact Finset.single_le_sum (f := fun other => |signedRelation other|)
          (fun other _ => abs_nonneg _) (Finset.mem_univ index)
      have hminBound : coefficient minimiser ≤ coefficient index :=
        hminimal index (Finset.mem_univ index)
      have hscaled : stepSize * |signedRelation index| ≤ coefficient minimiser := by
        rw [hstepDef, div_mul_eq_mul_div, div_le_iff₀ hdenomPos]
        nlinarith [habsBound, (hcoefficientPos minimiser).le, abs_nonneg (signedRelation index)]
      nlinarith [hstepPos, hscaled, neg_abs_le (signedRelation index), hminBound]
    have hfeasible : ∑ index, (coefficient index + stepSize * signedRelation index) • vector index
        = ∑ index, coefficient index • vector index := by
      have hsplit : ∀ index : label,
          (coefficient index + stepSize * signedRelation index) • vector index
            = coefficient index • vector index
              + stepSize • (signedRelation index • vector index) := fun index => by
        simp only [add_smul, smul_smul]
      rw [Finset.sum_congr rfl fun index _ => hsplit index, Finset.sum_add_distrib,
        ← Finset.smul_sum, hsigned, smul_zero, add_zero]
    have hcompare := hmaximal _ hshiftedNonneg hfeasible
    have hexpand : ∑ index, (coefficient index + stepSize * signedRelation index)
          * objective index
        = ∑ index, coefficient index * objective index
          + stepSize * ∑ index, signedRelation index * objective index := by
      have hsplit : ∀ index : label,
          (coefficient index + stepSize * signedRelation index) * objective index
            = coefficient index * objective index
              + stepSize * (signedRelation index * objective index) := fun index => by ring
      rw [Finset.sum_congr rfl fun index _ => hsplit index, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    rw [hexpand] at hcompare
    by_contra hpositive
    push Not at hpositive
    nlinarith [hcompare, hstepPos, hpositive]
  have hforward := honeSided relation hrelation
  have hbackward := honeSided (fun index => - relation index) (by
    simp only [neg_smul, Finset.sum_neg_distrib, hrelation, neg_zero])
  simp only [neg_mul, Finset.sum_neg_distrib] at hbackward
  linarith

/-- **THE FACTORISATION.**  A scalar assignment that annihilates every dependency of a finite
family is the restriction of a single linear functional to that family.

This is the abstract content of "orthogonal to the kernel of the coefficient map lands in the
range of its transpose", proved by sectioning the coefficient map over its range and
extending the resulting functional to the whole space.  No finite-dimensionality is used. -/
theorem exists_functional_of_annihilates_relations (vector : label → space)
    (dualValue : label → ℝ)
    (hannihilates : ∀ relation : label → ℝ,
      (∑ index, relation index • vector index = 0) →
      ∑ index, relation index * dualValue index = 0) :
    ∃ functional : space →ₗ[ℝ] ℝ, ∀ index, functional (vector index) = dualValue index := by
  classical
  obtain ⟨combination, hcombination⟩ :
      ∃ combination : (label → ℝ) →ₗ[ℝ] space,
        ∀ weights : label → ℝ, combination weights = ∑ index, weights index • vector index :=
    ⟨Fintype.linearCombination ℝ vector, fun weights => Fintype.linearCombination_apply _ _ _⟩
  obtain ⟨pairing, hpairing⟩ :
      ∃ pairing : (label → ℝ) →ₗ[ℝ] ℝ,
        ∀ weights : label → ℝ, pairing weights = ∑ index, weights index * dualValue index :=
    ⟨Fintype.linearCombination ℝ dualValue, fun weights => by
      rw [Fintype.linearCombination_apply]
      exact Finset.sum_congr rfl fun index _ => smul_eq_mul _ _⟩
  have hunitCombination : ∀ index : label,
      combination (Pi.single index (1 : ℝ)) = vector index := by
    intro index
    rw [hcombination, Finset.sum_eq_single index]
    · simp
    · intro other _ hdistinct
      rw [Pi.single_eq_of_ne hdistinct, zero_smul]
    · intro hnotMem
      exact absurd (Finset.mem_univ index) hnotMem
  have hunitPairing : ∀ index : label,
      pairing (Pi.single index (1 : ℝ)) = dualValue index := by
    intro index
    rw [hpairing, Finset.sum_eq_single index]
    · simp
    · intro other _ hdistinct
      rw [Pi.single_eq_of_ne hdistinct, zero_mul]
    · intro hnotMem
      exact absurd (Finset.mem_univ index) hnotMem
  obtain ⟨sectionMap, hsectionMap⟩ :=
    combination.rangeRestrict.exists_rightInverse_of_surjective combination.range_rangeRestrict
  obtain ⟨functional, hfunctional⟩ := LinearMap.exists_extend (pairing.comp sectionMap)
  refine ⟨functional, fun index => ?_⟩
  obtain ⟨target, htarget⟩ :
      ∃ target : LinearMap.range combination,
        target = (⟨vector index, ⟨Pi.single index (1 : ℝ), hunitCombination index⟩⟩ :
          LinearMap.range combination) := ⟨_, rfl⟩
  have hpreimage : combination (sectionMap target) = vector index := by
    have hidentity := DFunLike.congr_fun hsectionMap target
    have hcoerced := congrArg (fun element : LinearMap.range combination => (element : space))
      hidentity
    simpa [htarget] using hcoerced
  obtain ⟨difference, hdifferenceDef⟩ :
      ∃ difference : label → ℝ, difference = sectionMap target - Pi.single index (1 : ℝ) :=
    ⟨_, rfl⟩
  have hdifferenceVanishes : ∑ other, difference other • vector other = 0 := by
    rw [← hcombination, hdifferenceDef, map_sub, hpreimage, hunitCombination index, sub_self]
  have hpairingDifference : pairing (sectionMap target) = dualValue index := by
    have hvanishes := hannihilates difference hdifferenceVanishes
    rw [← hpairing, hdifferenceDef, map_sub, hunitPairing index] at hvanishes
    linarith
  have hcoerceTarget : (target : space) = vector index := by rw [htarget]
  have hextended := DFunLike.congr_fun hfunctional target
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hextended
  rw [hcoerceTarget] at hextended
  rw [hextended]
  exact hpairingDifference

end SlideByProduct

/-! ### The rank-two packaging: the shape matrix -/

/-- The three symmetric coordinates of a coefficient-weighted atom sum are three of that
sum's matrix entries.  Read left to right this computes the coordinates; read right to left
it transports a matrix identity into coordinate form. -/
theorem sum_smul_symmetricCoordinates_eq {size : ℕ} (atomVector : Fin size → (Fin 2 → ℝ))
    (coefficient : Fin size → ℝ) :
    ∑ label, coefficient label • symmetricCoordinates (atomVector label)
      = ![(∑ label, coefficient label • atomMatrix (atomVector label)) 0 0,
          (∑ label, coefficient label • atomMatrix (atomVector label)) 0 1,
          (∑ label, coefficient label • atomMatrix (atomVector label)) 1 1] := by
  funext position
  fin_cases position <;>
    simp [Finset.sum_apply, Matrix.sum_apply, atomMatrix, Matrix.vecMulVec_apply,
      symmetricCoordinates]

/-- **THE SHAPE MATRIX.**  A heaviness vector whose mass-weighted form annihilates every
dependency among the atom projectors of a rank-two design is the quadratic form of a SINGLE
symmetric two by two matrix, evaluated at the atoms and normalised by leverage; and that
matrix's trace is exactly the design's mass-weighted heaviness, hence ONE on the equality
locus of the circuit bound.

Combined with `sum_relation_mul_objective_eq_zero_of_maximal` this is the whole `p_c =
<g_c, R g_c> / l_c` step: the hypothesis below is what maximality delivers. -/
theorem exists_isSymm_shapeMatrix_of_annihilates_relations {size : ℕ}
    (D : WeightedDesign size 2) (heaviness : Fin size → ℝ)
    (hannihilates : ∀ relation : Fin size → ℝ,
      (∑ label, relation label • atomMatrix (D.atom label) = 0) →
      ∑ label, relation label * (leverageOf (D.atom label) * heaviness label) = 0) :
    ∃ shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ, shapeMatrix.IsSymm
      ∧ (∀ label, leverageOf (D.atom label) * heaviness label
          = D.atom label ⬝ᵥ (shapeMatrix *ᵥ D.atom label))
      ∧ Matrix.trace shapeMatrix
          = ∑ label, D.weight label * leverageOf (D.atom label) * heaviness label := by
  classical
  obtain ⟨functional, hfunctional⟩ :=
    exists_functional_of_annihilates_relations (fun label => symmetricCoordinates (D.atom label))
      (fun label => leverageOf (D.atom label) * heaviness label)
      fun relation hrelation => hannihilates relation (by
        have hmatrix := sum_smul_atomMatrix_eq_of_symmetricCoordinates D.atom relation
          (fun _ => 0) (by rw [hrelation]; simp)
        rw [hmatrix]; simp)
  obtain ⟨alongFirst, alongCross, alongSecond, hcoefficientForm⟩ :
      ∃ alongFirst alongCross alongSecond : ℝ, ∀ coordinates : Fin 3 → ℝ,
        functional coordinates = alongFirst * coordinates 0 + alongCross * coordinates 1
          + alongSecond * coordinates 2 := by
    refine ⟨functional ![1, 0, 0], functional ![0, 1, 0], functional ![0, 0, 1],
      fun coordinates => ?_⟩
    have hdecompose : coordinates = coordinates 0 • ![1, 0, 0] + coordinates 1 • ![0, 1, 0]
        + coordinates 2 • (![0, 0, 1] : Fin 3 → ℝ) := by
      funext position
      fin_cases position <;> simp
    conv_lhs => rw [hdecompose]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hparsevalCoordinates :
      ∑ label, D.weight label • symmetricCoordinates (D.atom label) = ![1, 0, 1] := by
    rw [sum_smul_symmetricCoordinates_eq, D.isParseval]
    simp
  refine ⟨!![alongFirst, alongCross / 2; alongCross / 2, alongSecond], ?_, ?_, ?_⟩
  · show (!![alongFirst, alongCross / 2; alongCross / 2, alongSecond])ᵀ
        = !![alongFirst, alongCross / 2; alongCross / 2, alongSecond]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp
  · intro label
    rw [← hfunctional label, hcoefficientForm]
    simp [symmetricCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · have hthroughFunctional : functional (∑ label, D.weight label
        • symmetricCoordinates (D.atom label))
        = ∑ label, D.weight label * (leverageOf (D.atom label) * heaviness label) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun label _ => by
        rw [map_smul, smul_eq_mul, hfunctional label]
    rw [hparsevalCoordinates, hcoefficientForm] at hthroughFunctional
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.trace_fin_two_of] at hthroughFunctional ⊢
    have hreassociate : ∑ label, D.weight label * (leverageOf (D.atom label) * heaviness label)
        = ∑ label, D.weight label * leverageOf (D.atom label) * heaviness label :=
      Finset.sum_congr rfl fun label _ => by ring
    rw [← hreassociate, ← hthroughFunctional]
    ring

/-- **THE SHAPE MATRIX AT THE EQUALITY LOCUS -- the band lane's input.**  Suppose every
at-most-three-support coefficient vector reproducing the identity scores at most one against
the heaviness -- that is the circuit bound -- and suppose the design itself attains one.
Then the heaviness is the quadratic form of a symmetric two by two matrix of trace exactly
ONE, normalised by leverage.

The three-support bound upgrades to genuine maximality over ALL feasible competitors because
the reduction carries any competitor onto three atoms without losing ground; maximality then
licenses the two-sided slide, the slide annihilates every projector dependency, and a vector
annihilating every dependency is a single symmetric matrix read at the atoms. -/
theorem exists_isSymm_shapeMatrix_traceOne_of_threeSupportBound {size : ℕ}
    (D : WeightedDesign size 2) (heaviness : Fin size → ℝ)
    (hthreeSupportBound : ∀ (subWeight : Fin size → ℝ) (support : Finset (Fin size)),
      (∀ label, 0 ≤ subWeight label) → (∀ label, label ∉ support → subWeight label = 0) →
      support.card ≤ 3 → (∑ label, subWeight label • atomMatrix (D.atom label) = 1) →
      ∑ label, subWeight label * leverageOf (D.atom label) * heaviness label ≤ 1)
    (hdesignValue : ∑ label, D.weight label * leverageOf (D.atom label) * heaviness label = 1) :
    ∃ shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ, shapeMatrix.IsSymm
      ∧ (∀ label, leverageOf (D.atom label) * heaviness label
          = D.atom label ⬝ᵥ (shapeMatrix *ᵥ D.atom label))
      ∧ Matrix.trace shapeMatrix = 1 := by
  classical
  have hreassociate : ∀ weightVector : Fin size → ℝ,
      ∑ label, weightVector label * (leverageOf (D.atom label) * heaviness label)
        = ∑ label, weightVector label * leverageOf (D.atom label) * heaviness label :=
    fun weightVector => Finset.sum_congr rfl fun label _ => by ring
  have hmaximal : ∀ competitor : Fin size → ℝ, (∀ label, 0 ≤ competitor label) →
      (∑ label, competitor label • atomMatrix (D.atom label)
        = ∑ label, D.weight label • atomMatrix (D.atom label)) →
      ∑ label, competitor label * (leverageOf (D.atom label) * heaviness label)
        ≤ ∑ label, D.weight label * (leverageOf (D.atom label) * heaviness label) := by
    intro competitor hcompetitorNonneg hcompetitorFeasible
    obtain ⟨subWeight, support, hsubNonneg, hsubOff, hsubCard, hsubVector, hsubHeavy⟩ :=
      exists_threeAtomReduction_atLeastAsHeavy D heaviness competitor hcompetitorNonneg
    have hsubBound := hthreeSupportBound subWeight support hsubNonneg hsubOff hsubCard
      (hsubVector.trans (hcompetitorFeasible.trans D.isParseval))
    rw [hreassociate, hreassociate, hdesignValue]
    linarith [hsubHeavy, hsubBound]
  obtain ⟨shapeMatrix, hsymmetric, hquadratic, htrace⟩ :=
    exists_isSymm_shapeMatrix_of_annihilates_relations D heaviness
      fun relation hrelation =>
        sum_relation_mul_objective_eq_zero_of_maximal (fun label => atomMatrix (D.atom label))
          (fun label => leverageOf (D.atom label) * heaviness label) D.weight D.weight_pos
          hmaximal relation hrelation
  exact ⟨shapeMatrix, hsymmetric, hquadratic, htrace.trans hdesignValue⟩


/-! ## MERGE TEST: both residual inputs, discharged against the live hinge file -/

theorem rankTwoCircuitReduction_holds : RankTwoCircuitReduction :=
  exists_threeAtomSubdesign_atLeastAsHeavy

/-- **THE HINGE, one residual lighter.** -/
theorem not_isTie_of_equalityStratum (hequality : RankTwoEqualityStratum)
    (D : WeightedDesign m 2)
    (firstLabel secondLabel thirdLabel fourthLabel : Fin m)
    (hone : firstLabel ≠ secondLabel) (htwo : firstLabel ≠ thirdLabel)
    (hthree : firstLabel ≠ fourthLabel) (hfour : secondLabel ≠ thirdLabel)
    (hfive : secondLabel ≠ fourthLabel) (hsix : thirdLabel ≠ fourthLabel)
    (hgramOne : unitPairGram D firstLabel secondLabel ≠ 1)
    (hgramTwo : unitPairGram D firstLabel thirdLabel ≠ 1)
    (hgramThree : unitPairGram D firstLabel fourthLabel ≠ 1)
    (hgramFour : unitPairGram D secondLabel thirdLabel ≠ 1)
    (hgramFive : unitPairGram D secondLabel fourthLabel ≠ 1)
    (hgramSix : unitPairGram D thirdLabel fourthLabel ≠ 1) :
    ¬ IsTie D :=
  not_isTie_of_circuitReduction_of_equalityStratum rankTwoCircuitReduction_holds hequality D
    firstLabel secondLabel thirdLabel fourthLabel hone htwo hthree hfour hfive hsix
    hgramOne hgramTwo hgramThree hgramFour hgramFive hgramSix

/-- **THE BAND LANE'S INPUT, ASSEMBLED.**  On the equality locus of a rank-two tie the
heaviness vector is the quadratic form of a symmetric trace-one matrix at the atoms.  The
three-support cap is the shipped circuit bound; nothing else is used. -/
theorem exists_isSymm_shapeMatrix_traceOne_of_isTie (D : WeightedDesign m 2) (htie : IsTie D)
    (hdesignValue : ∑ label, atomMass D label * atomHeaviness D label = 1) :
    ∃ shapeMatrix : Matrix (Fin 2) (Fin 2) ℝ, shapeMatrix.IsSymm
      ∧ (∀ label, leverageOf (D.atom label) * atomHeaviness D label
          = D.atom label ⬝ᵥ (shapeMatrix *ᵥ D.atom label))
      ∧ Matrix.trace shapeMatrix = 1 := by
  classical
  refine exists_isSymm_shapeMatrix_traceOne_of_threeSupportBound D (atomHeaviness D)
    ?_ hdesignValue
  intro subWeight support hsubNonneg hsubOff hsubCard hsubParseval
  have hpairCap : ∀ pivot partner : Fin m, pivot ≠ partner →
      atomHeaviness D pivot * atomHeaviness D partner ≤ unitPairGram D pivot partner :=
    fun pivot partner hdistinct =>
      atomHeaviness_mul_le_unitPairGram_of_isTie D htie pivot partner hdistinct
  set reducedMass := fun label => subWeight label * leverageOf (D.atom label) with hreducedDef
  set liveSupport := support.filter (fun label => D.atom label ≠ 0) with hliveDef
  have hmassNonneg : ∀ label, 0 ≤ reducedMass label := fun label =>
    mul_nonneg (hsubNonneg label) (leverageOf_nonneg _)
  have hmassOff : ∀ label, label ∉ liveSupport → reducedMass label = 0 := by
    intro label hout
    rw [hliveDef, Finset.mem_filter] at hout
    push Not at hout
    rw [hreducedDef]
    by_cases hinSupport : label ∈ support
    · have hatomZero : D.atom label = 0 := by
        by_contra hnonzero
        exact hnonzero (hout hinSupport)
      simp [hatomZero, leverageOf]
    · simp [hsubOff label hinSupport]
  have hmassTotal : ∑ label, reducedMass label = 2 := by
    have hrank := sum_coefficient_mul_leverage D subWeight hsubParseval
    norm_num at hrank
    exact hrank
  have hliveNonzero : ∀ pivot ∈ liveSupport, D.atom pivot ≠ 0 := by
    intro pivot hpivotMem
    rw [hliveDef, Finset.mem_filter] at hpivotMem
    exact hpivotMem.2
  have hbound : ∑ label, reducedMass label * atomHeaviness D label ≤ 1 :=
    sum_mass_mul_heaviness_le_one_of_support_card_le_three
      reducedMass (atomHeaviness D) (unitPairGram D) liveSupport hmassNonneg hmassOff hmassTotal
      (fun pivot hpivotMem => sum_coefficientMass_mul_unitPairGram_eq_one D subWeight
        hsubParseval (hliveNonzero pivot hpivotMem))
      (fun pivot hpivotMem => unitPairGram_self D (hliveNonzero pivot hpivotMem))
      (atomHeaviness_nonneg D) (atomHeaviness_le_one D) hpairCap
      (by
        have hsubset : liveSupport.card ≤ support.card :=
          Finset.card_le_card (by rw [hliveDef]; exact Finset.filter_subset _ _)
        exact_mod_cast le_trans hsubset hsubCard)
  exact hbound


end Gtz
