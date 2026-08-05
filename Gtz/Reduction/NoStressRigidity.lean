/-
# Branch (i) of the stress trichotomy: the no-stress stratum is weight-rigid

`sixThree_stress_trichotomy` splits every (6,3) design by its stress structure;
its first branch is the STRESS-FREE stratum, phrased as kernel triviality of
the atom-matrix combination map.  This file proves that on that stratum the
weights are a FUNCTION OF THE DIRECTIONS: Parseval `sum_c t_c * A_c = 1` has at
most one solution, so the stratum is parametrized by the six directions alone
and admits no weight perturbation at fixed atoms.  K4 lives entirely in this
stratum (its stress determinant is -1 at every weighting), so these are the
rigidity facts every branch-(i) domination argument starts from.

Everything is stated at general size and rank; the (6,3) capstone instantiates
the phrasing of the trichotomy's first disjunct verbatim.
-/
import Mathlib
import Gtz.Reduction.HingeFunnel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **The dual-basis uniqueness lemma.**  If the atom matrices carry no stress
(the combination map has trivial kernel — branch (i)'s hypothesis verbatim),
then Parseval has at most one coefficient vector: any two resolutions of the
identity along the same atoms coincide. -/
theorem parsevalWeights_unique_of_stressFree
    {atomFamily : Fin m → Fin k → ℝ}
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ c, stressCoeff c • atomMatrix (atomFamily c)) = 0 → stressCoeff = 0)
    {firstWeights secondWeights : Fin m → ℝ}
    (hfirst : ∑ c, firstWeights c • atomMatrix (atomFamily c) = 1)
    (hsecond : ∑ c, secondWeights c • atomMatrix (atomFamily c) = 1) :
    firstWeights = secondWeights := by
  have hdifference :
      ∑ c, (firstWeights c - secondWeights c) • atomMatrix (atomFamily c) = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, hfirst, hsecond, sub_self]
  have hkernel :=
    hstressFree (fun c => firstWeights c - secondWeights c) hdifference
  funext label
  have hcoordinate := congrFun hkernel label
  simpa [sub_eq_zero] using hcoordinate

/-- **Weight rigidity of a stress-free design**: any coefficient vector solving
Parseval along the design's atoms IS the design's weight vector. -/
theorem weight_eq_of_stressFree_of_parseval (design : WeightedDesign m k)
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0)
    {candidateWeights : Fin m → ℝ}
    (hcandidate : ∑ c, candidateWeights c • atomMatrix (design.atom c) = 1) :
    candidateWeights = design.weight :=
  parsevalWeights_unique_of_stressFree hstressFree hcandidate design.isParseval

/-- **No second design on the same atoms**: two designs sharing a stress-free
atom family share the weights — the stress-free stratum is parametrized by
directions alone. -/
theorem weight_eq_of_atom_eq_of_stressFree
    (designOne designTwo : WeightedDesign m k)
    (hatoms : designTwo.atom = designOne.atom)
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ c, stressCoeff c • atomMatrix (designOne.atom c)) = 0 → stressCoeff = 0) :
    designTwo.weight = designOne.weight := by
  refine weight_eq_of_stressFree_of_parseval designOne hstressFree ?_
  rw [← hatoms]
  exact designTwo.isParseval

/-- The kernel-triviality phrasing of branch (i) is exactly linear independence
of the atom matrices — the bridge between the trichotomy's vocabulary and
Mathlib's. -/
theorem stressFree_iff_linearIndependent_atomMatrix
    (atomFamily : Fin m → Fin k → ℝ) :
    (∀ stressCoeff : Fin m → ℝ,
      (∑ c, stressCoeff c • atomMatrix (atomFamily c)) = 0 → stressCoeff = 0)
    ↔ LinearIndependent ℝ (fun c => atomMatrix (atomFamily c)) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hstressFree stressCoeff hcombination label
    exact congrFun (hstressFree stressCoeff hcombination) label
  · intro hindependent stressCoeff hcombination
    funext label
    exact hindependent stressCoeff hcombination label

/-- **The (6,3) branch-(i) structure theorem**, in the trichotomy's own words:
a stress-free (6,3) design admits no reweighting — any other design on the same
six atoms is the same design up to the weight component being EQUAL.  With
`sixThree_stress_trichotomy` this says the first branch of the trichotomy is
weight-rigid: its designs are points of a directions-only moduli. -/
theorem sixThree_noStress_weights_determined (design : WeightedDesign 6 3)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0)
    (other : WeightedDesign 6 3) (hatoms : other.atom = design.atom) :
    other.weight = design.weight :=
  weight_eq_of_atom_eq_of_stressFree design other hatoms hstressFree

end Gtz
