/-
# The A10 residue interface + the deep-cycle dissolution

Two landings from the gtz3-a10-confinement workflow (both audits SOUND),
converging with `Gtz.TriangleClosure` from the independent Poncelet round.

INTERFACE: A10 (zero-set confinement, `{Φ = 1} ∩ K ⊆ closure(𝒯)`) is
mechanized as a consumer theorem over the kernel's real vocabulary — the
classification through ≤ 11 atoms, the structural dichotomy, and the
deep-cycle residue Prop are isolated hypotheses, never smuggled. The
CyclicStress layer pins the residue onto the Cayley-torsion locus.

DISSOLUTION: on the focal conic `ν = 1/2 + ρc` (which every equality-design
atom satisfies via the frame form), an atom's two tight partners are ALWAYS
mutually tight — the P3-closure gap times the chord norm is EXACTLY
`(ρ² − 1/4)(c₁² + s₁² − 1)/4`, zero on the unit circle, with NO
design-compatibility hypothesis. Combined with max-degree-2, every tight
component is a triangle: the deep-cycle residue predicate is empty on the
planar shadow, and the residue Prop holds vacuously. The honest remainder
is the planar→3D frame bridge (the flagged B5 Gordan/IFT step), NOT the
cycles.
-/
import Mathlib
import Gtz.Basic
import Gtz.CyclicStress
import Gtz.LawEquivalence

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- **Φ = 1, in the kernel's real vocabulary** (an exact tie). The best
k-subset dominates weakly (`Dominates`) but NO k-subset dominates strictly:
`max_C λ_min(S_C) = 1`, the boundary of the `GtzWeighted` feasible interior. -/
def IsTie (D : WeightedDesign m k) : Prop :=
  (∃ C : Finset (Fin m), C.card = k ∧ Dominates D C) ∧
  (∀ C : Finset (Fin m), C.card = k → ¬ (subsetSum D C - 1).PosDef)

/-- **Zero-set confinement on the collared class** (the A10 target): every
tied design in the class lies on the closure of the tie variety —
`distToTieVariety D = 0`, with the distance kernel-abstract. -/
def ZeroSetConfinement (distToTieVariety : WeightedDesign m k → ℝ)
    (isInClass : WeightedDesign m k → Prop) : Prop :=
  ∀ D : WeightedDesign m k, isInClass D → IsTie D → distToTieVariety D = 0

/-- **The classification through ≤ 11 atoms** (kernel-backed: max-degree +
leaf-tangency + the P4/C5/leaf-corner exclusions + C3 = family): every tied
design in the class with at most 11 atoms is confined. -/
def ClassificationLeEleven (distToTieVariety : WeightedDesign m k → ℝ)
    (isInClass : WeightedDesign m k → Prop) : Prop :=
  ∀ D : WeightedDesign m k, isInClass D → IsTie D → m ≤ 11
    → distToTieVariety D = 0

/-- **The structural dichotomy**: every tied design in the class either
merges to ≤ 11 atoms or carries a deep full-stress cycle. -/
def TieDichotomy (isInClass : WeightedDesign m k → Prop)
    (carriesDeepCycle : WeightedDesign m k → Prop) : Prop :=
  ∀ D : WeightedDesign m k, isInClass D → IsTie D
    → m ≤ 11 ∨ carriesDeepCycle D

/-- **The residue Prop** (the former Poncelet-torsion wall, stated exactly):
every tied design carrying a deep full-stress cycle is confined. The
dissolution below makes its antecedent empty on the planar shadow. -/
def ResidueConfinement (distToTieVariety : WeightedDesign m k → ℝ)
    (isInClass : WeightedDesign m k → Prop)
    (carriesDeepCycle : WeightedDesign m k → Prop) : Prop :=
  ∀ D : WeightedDesign m k, isInClass D → IsTie D → carriesDeepCycle D
    → distToTieVariety D = 0

/-- **The consumer theorem — the A10 reduction, mechanized**: classification
through ≤ 11 atoms + the structural dichotomy + the residue Prop imply
zero-set confinement. Pure logical assembly; the open pieces are the
isolated hypotheses. -/
theorem zeroSetConfinement_of_classification_and_residue
    (distToTieVariety : WeightedDesign m k → ℝ)
    (isInClass : WeightedDesign m k → Prop)
    (carriesDeepCycle : WeightedDesign m k → Prop)
    (hclassified : ClassificationLeEleven distToTieVariety isInClass)
    (hdichotomy : TieDichotomy isInClass carriesDeepCycle)
    (hresidue : ResidueConfinement distToTieVariety isInClass carriesDeepCycle) :
    ZeroSetConfinement distToTieVariety isInClass := by
  intro D hisInClass hisTie
  rcases hdichotomy D hisInClass hisTie with hsmall | hcycle
  · exact hclassified D hisInClass hisTie hsmall
  · exact hresidue D hisInClass hisTie hcycle

/-- **The dichotomy with the deep-cycle branch dissolved**: when the residue
predicate is provably empty (delivered by `focal_conic_p3_closes` /
`triangle_closure_biquadratic` at the geometry level), every tie lives at
≤ 11 atoms — the whole classification is the small regime. -/
theorem dichotomy_collapses_of_no_residue
    (isInClass : WeightedDesign m k → Prop)
    (carriesDeepCycle : WeightedDesign m k → Prop)
    (hnoResidue : ∀ D, ¬ carriesDeepCycle D)
    (hdichotomy : TieDichotomy isInClass carriesDeepCycle) :
    ∀ D, isInClass D → IsTie D → m ≤ 11 := by
  intro D hisInClass hisTie
  rcases hdichotomy D hisInClass hisTie with hsmall | hcycle
  · exact hsmall
  · exact absurd hcycle (hnoResidue D)

section CyclicResidue
variable {cycleLen : ℕ} [NeZero cycleLen]

/-- **The residue is confined to the Cayley-torsion locus** (the A10
interface reading of `cyclic_stress_closure`): a deep FULL-stress cycle
forces the closure equation `∏ leafG = (−1)^cycleLen · ∏ leafH`. -/
theorem deepCycle_forces_closure
    (stress leafG leafH : ZMod cycleLen → ℝ)
    (hnonzero : ∀ i, stress i ≠ 0)
    (hties : ∀ i, stress i * leafG i = -(stress (i + 1) * leafH i)) :
    (∏ i, leafG i) = (-1) ^ cycleLen * (∏ i, leafH i) :=
  cyclic_stress_closure stress leafG leafH hties hnonzero

/-- **Nothing lives off the torsion locus** (`cyclic_stress_vanishes_of_open`
read at the interface): when the closure equation fails, no stress can have
full support — leaf-tangency finishes the partially-stressed cycle. -/
theorem no_deepCycle_off_torsionLocus
    (stress leafG leafH : ZMod cycleLen → ℝ)
    (hties : ∀ i, stress i * leafG i = -(stress (i + 1) * leafH i))
    (hopen : (∏ i, leafG i) ≠ (-1) ^ cycleLen * (∏ i, leafH i)) :
    ¬ (∀ i, stress i ≠ 0) := by
  intro hfull
  obtain ⟨i, hi⟩ := cyclic_stress_vanishes_of_open stress leafG leafH hties hopen
  exact hfull i hi

end CyclicResidue

/-- **Two routes agree at the zero set**: if the funneling law held on the
class (`margin ≥ lawConst · dist^alpha`), confinement would be immediate —
at a tie the margin vanishes, so the distance does. A10's point is that the
law is NOT known; this certifies the classification route and the law route
target the same statement. -/
theorem zeroSetConfinement_of_funnelingLaw
    (distToTieVariety margin : WeightedDesign m k → ℝ)
    (isInClass : WeightedDesign m k → Prop)
    (lawConst : ℝ) (alpha : ℕ)
    (hlawConstPos : 0 < lawConst) (halphaNonzero : alpha ≠ 0)
    (hdistNonneg : ∀ D, 0 ≤ distToTieVariety D)
    (hmarginAtTie : ∀ D, isInClass D → IsTie D → margin D = 0)
    (hlaw : ∀ D, isInClass D
      → lawConst * distToTieVariety D ^ alpha ≤ margin D) :
    ZeroSetConfinement distToTieVariety isInClass := by
  intro D hisInClass hisTie
  exact law_confines_zero_set (hlaw D hisInClass) hlawConstPos
    (hdistNonneg D) halphaNonzero (hmarginAtTie D hisInClass hisTie)

/-- **The P3-closure numerator factors** (the dissolution certificate): the
conic-tightness gap of an atom's two partners, reduced via Vieta, is exactly
`(ρ² − 1/4)(c₁² + s₁² − 1)` — zero on the unit circle. Pure `ring`. -/
theorem p3_closure_numerator_factors (c1 s1 rho : ℝ) :
    c1^2*rho^2 - c1^2/4 + rho^2*s1^2 - rho^2 - s1^2/4 + 1/4
      = (rho^2 - 1/4) * (c1^2 + s1^2 - 1) := by
  ring

/-- **Focal-conic P3-closure** (the residue dissolution, unconditional):
atom 1 is a unit vector `(c1, s1)` on the focal conic `ν = 1/2 + ρc`; its
two tight partners are the intersections of its polar chord with the unit
circle, encoded by the Vieta data. Then the partners are TIGHT to each
other — the conic tightness gap vanishes — with NO design-compatibility
hypothesis. With max-degree-2 this closes every tight walk into a triangle:
the deep-cycle residue is empty on the planar shadow. -/
theorem focal_conic_p3_closes
    (c1 s1 rho c0c2 s0s2 c0plusc2 P Q R chordNorm : ℝ)
    (hp1 : c1^2 + s1^2 = 1)
    (hP : P = c1/2 - (1/2 + rho*c1)*rho)
    (hQ : Q = s1/2)
    (hR : R = ((1/2 + rho*c1) - 1)/2)
    (hCN : chordNorm = P^2 + Q^2)
    (hchord : chordNorm ≠ 0)
    (hsum : c0plusc2 * chordNorm = 2*P*R)
    (hcc : c0c2 * chordNorm = R^2 - Q^2)
    (hss : s0s2 * chordNorm = R^2 - P^2) :
    (1 + (c0c2 + s0s2))/2 - (1/4 + rho*c0plusc2/2 + rho^2*c0c2) = 0 := by
  have key : chordNorm *
      ((1 + (c0c2 + s0s2))/2 - (1/4 + rho*c0plusc2/2 + rho^2*c0c2))
      = (rho^2 - 1/4) * (c1^2 + s1^2 - 1) / 4 := by
    subst hP hQ hR hCN
    linear_combination (1/2 - rho^2) * hcc + (1/2) * hss - (rho/2) * hsum
  have hzero : chordNorm *
      ((1 + (c0c2 + s0s2))/2 - (1/4 + rho*c0plusc2/2 + rho^2*c0c2)) = 0 := by
    rw [key, hp1]; ring
  rcases mul_eq_zero.mp hzero with hcn0 | hgap
  · exact absurd hcn0 hchord
  · exact hgap

/-- **No chordless tight four-cycle** (atom-level residue emptiness, abstract
and axiom-free): with symmetric tightness and P3-closure at one vertex, four
distinct atoms cannot form a chordless tight 4-cycle — the closure at `b`
makes `a, c` tight, contradicting chordlessness. -/
theorem no_chordless_tight_four_cycle
    {Atom : Type*} (isTightPair : Atom → Atom → Prop)
    (a b c d : Atom)
    (hab : isTightPair a b) (hbc : isTightPair b c)
    (_hcd : isTightPair c d) (_hda : isTightPair d a)
    (hnac : ¬ isTightPair a c)
    (hp3ClosesAtB : isTightPair a b → isTightPair b c → a ≠ c
      → isTightPair a c)
    (hac_ne : a ≠ c) : False :=
  hnac (hp3ClosesAtB hab hbc hac_ne)

end Gtz
