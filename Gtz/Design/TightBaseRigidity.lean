import Gtz.Design.UniversalNeedle
import Gtz.Design.ComplementFrame
import Gtz.Design.UThreeSixDisjunction
import Gtz.Quantitative.ChartSecondOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tight base triple: kernel rigidity and the exact energy transfer

The A1 residual `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` hands a
weakly dominating base triple `{0, 1, 2}` together with a direction on which its
gap form reads zero.  This module extracts what that pair of hypotheses forces.

Two readings, one weak and one strong.

The weak reading is scalar.  A tight direction makes the base triple's UNWEIGHTED
squared readings equal the probe energy.  Parseval then transfers the remainder
to the complement, and `tight_complement_energy_eq` states the transfer as an
EXACT identity: the complement's weighted energy equals the selection's
`(1 - weight)`-weighted energy.  No inequality, no cap, no eigenvalue.

The strong reading is a vector equation.  The residual also carries weak
domination, so the base gap is positive semidefinite.  A positive semidefinite
matrix that reads zero at a direction annihilates it, so the tight direction
lies in the kernel.  `tightBase_mulVec_eq_zero` upgrades one scalar equation to
three, and `subsetSum_mulVec_eq_self_of_tight` states the eigenvector form.

The identity then prices the residual's separation hypothesis.  The residual
demands that the base residual beat the complement cap at the tight direction.
`exists_mem_lt_one_sub_of_tight_separated` converts that demand into a named
base label whose weight, added to the cap, stays below one, and which reads
nonzero at the tight direction.
-/

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ## The scalar reading of a tight direction -/

/-- **A tight direction equalizes the unweighted readings with the energy.**
The gap form of a selection reads zero at a direction exactly when the
selection's unweighted squared readings there sum to the probe energy. -/
theorem sum_sq_eq_dotProduct_self_of_tight (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0) :
    ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec] at htight
  linarith

/-! ## The exact energy transfer -/

/-- **THE TIGHT ENERGY IDENTITY.**  At a direction where a selection holds its
gap form tight, the complement's WEIGHTED energy equals the selection's
`(1 - weight)`-weighted energy.

This is an equality, not a bound.  Parseval supplies the total, the tight
equation supplies the selection's unweighted total, and the difference of the
two readings is exactly the complement's weighted energy.  Division-free, and
no positivity of any gap is used. -/
theorem tight_complement_energy_eq (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (probe : Fin rank → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0) :
    ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = ∑ label ∈ selected,
          (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hparseval : (∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
      = probe ⬝ᵥ probe := sum_weight_mul_sq_dotProduct design probe
  have hsplit : (∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2)
        + ∑ label ∈ selectedᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = ∑ label, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 :=
    Finset.sum_add_sum_compl selected _
  have hunweighted : ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe :=
    sum_sq_eq_dotProduct_self_of_tight design selected probe htight
  have hexpand : ∑ label ∈ selected,
        (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2
      = (∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2)
        - ∑ label ∈ selected, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun label _ => by ring
  rw [hexpand, hunweighted]
  linarith [hsplit, hparseval]

/-- The A1 instance: the base triple `{0, 1, 2}` against its complement
`{3, 4, 5}`. -/
theorem tight_baseTriple_complement_energy_eq (design : WeightedDesign 6 3)
    (probe : Fin 3 → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe) = 0) :
    ∑ label ∈ ({3, 4, 5} : Finset (Fin 6)),
        design.weight label * (design.atom label ⬝ᵥ probe) ^ 2
      = ∑ label ∈ ({0, 1, 2} : Finset (Fin 6)),
          (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2 := by
  have hcompl : ({0, 1, 2} : Finset (Fin 6))ᶜ = ({3, 4, 5} : Finset (Fin 6)) := by decide
  have := tight_complement_energy_eq design ({0, 1, 2} : Finset (Fin 6)) probe htight
  rwa [hcompl] at this

/-! ## The kernel reading of a tight direction -/

/-- **A WEAKLY DOMINATING SELECTION ANNIHILATES ITS TIGHT DIRECTIONS.**  Weak
domination makes the gap form positive semidefinite, and a positive semidefinite
matrix that reads zero at a direction sends it to zero.

This upgrades the residual's single scalar equation to a vector equation, so a
prover receives `rank` equations rather than one. -/
theorem tight_mulVec_eq_zero (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {probe : Fin rank → ℝ}
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0) :
    (subsetSum design selected - 1) *ᵥ probe = 0 :=
  mulVec_eq_zero_of_posSemidef_of_dotProduct_zero hdominates htight

/-- **The eigenvector form.**  A tight direction of a weakly dominating
selection is an eigenvector of the selection's unweighted atom sum, with
eigenvalue exactly one. -/
theorem subsetSum_mulVec_eq_self_of_tight (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {probe : Fin rank → ℝ}
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0) :
    subsetSum design selected *ᵥ probe = probe := by
  have hker := tight_mulVec_eq_zero design hdominates htight
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
  exact hker

/-- The A1 instance of the kernel reading, at the pinned base triple. -/
theorem tightBase_mulVec_eq_zero (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6)))
    {probe : Fin 3 → ℝ}
    (htight : probe ⬝ᵥ ((subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe) = 0) :
    (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1) *ᵥ probe = 0 :=
  tight_mulVec_eq_zero design hdominates htight

/-! ## The identity prices the separation hypothesis -/

/-- The base residual reads the complement's weighted energy at any probe. -/
theorem dotProduct_baseResidual_eq_complement_energy (design : WeightedDesign size rank)
    (baseSet : Finset (Fin size)) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ (baseResidual design baseSet *ᵥ probe)
      = ∑ label ∈ baseSetᶜ, design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 := by
  rw [baseResidual_eq_complementSum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun label _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_atomMatrix_mulVec_self]

/-- **THE SEPARATION NAMES A LIGHT BASE LABEL.**  The A1 residual demands that
the base residual beat the complement cap at the tight direction.  Through the
tight energy identity this forces a base label that reads nonzero at that
direction and whose weight, added to the cap, stays strictly below one.

A prover receives a named label rather than a global inequality. -/
theorem exists_mem_lt_one_sub_of_tight_separated (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) {cap : ℝ} (probe : Fin rank → ℝ)
    (htight : probe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probe) = 0)
    (hseparated : cap * (probe ⬝ᵥ probe)
      < probe ⬝ᵥ (baseResidual design selected *ᵥ probe)) :
    ∃ label ∈ selected, design.weight label + cap < 1
      ∧ (design.atom label ⬝ᵥ probe) ^ 2 ≠ 0 := by
  have hidentity := tight_complement_energy_eq design selected probe htight
  have hread := dotProduct_baseResidual_eq_complement_energy design selected probe
  have hunweighted : ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe :=
    sum_sq_eq_dotProduct_self_of_tight design selected probe htight
  have hsum : 0 < ∑ label ∈ selected,
      (1 - design.weight label - cap) * (design.atom label ⬝ᵥ probe) ^ 2 := by
    have hrewrite : ∑ label ∈ selected,
          (1 - design.weight label - cap) * (design.atom label ⬝ᵥ probe) ^ 2
        = (∑ label ∈ selected,
            (1 - design.weight label) * (design.atom label ⬝ᵥ probe) ^ 2)
          - cap * ∑ label ∈ selected, (design.atom label ⬝ᵥ probe) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by ring
    rw [hrewrite, hunweighted, ← hidentity, ← hread]
    linarith
  by_contra hnone
  push Not at hnone
  have hterm : ∀ label ∈ selected,
      (1 - design.weight label - cap) * (design.atom label ⬝ᵥ probe) ^ 2 ≤ 0 := by
    intro label hmem
    rcases eq_or_ne ((design.atom label ⬝ᵥ probe) ^ 2) 0 with hzero | hne
    · rw [hzero, mul_zero]
    · have hweight : 1 ≤ design.weight label + cap := by
        by_contra hlt
        exact hne (hnone label hmem (by linarith))
      have hsq : 0 ≤ (design.atom label ⬝ᵥ probe) ^ 2 := sq_nonneg _
      nlinarith
  exact absurd (Finset.sum_nonpos hterm) (not_le.mpr hsum)

end Gtz
