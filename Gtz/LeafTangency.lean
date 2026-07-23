/-
# The leaf-tangency theorem: a stress-leaf's neighbour has no second partner

The analytic engine of the zero-set classification (verified workflow landing,
SS96): at any stress-leaf of a planar equality design, the leaf equation is the
angular criticality of its edge's silence form, and together with tightness it
forces the NEIGHBOUR's polar line to be tangent to the circle at the leaf — a
tangent line meets the circle once, so the neighbour has no second distinct
tight partner. Consequence (with the corpus kills): every path component and
every partially-stressed cycle of an equality design is dead; the zero-set
residue collapses to full-stress cycles.

The kernel decomposition, sqrt-free, riding TightGraph's polar-chord kit
(`polarNormal`, `tight_iff_polar`):

* the planar basis expansion along a unit vector and its quarter-turn;
* a double zero (value + angular derivative) of the affine polar form with
  nonzero offset pins the normal to `n = −e·w` — the tangency — and every
  other unit zero of the form coincides with `w`;
* two unit vectors at Gram value one coincide.
-/
import Mathlib
import Gtz.TightGraph
import Gtz.SplittingRule
import Gtz.ResolventPerturbation

namespace Gtz

open Matrix

/-! ### The planar double-zero geometry -/

/-- **The planar basis expansion**: any vector decomposes along a unit vector
and its quarter-turn. -/
theorem basis_expansion {unitDir : Fin 2 → ℝ}
    (hunit : unitDir ⬝ᵥ unitDir = 1) (anyVec : Fin 2 → ℝ) :
    anyVec = (anyVec ⬝ᵥ unitDir) • unitDir
      + (anyVec ⬝ᵥ rotateQuarter unitDir) • rotateQuarter unitDir := by
  have hnormSq : unitDir 0 * unitDir 0 + unitDir 1 * unitDir 1 = 1 := by
    have hexpand := hunit
    simp only [dotProduct, Fin.sum_univ_two] at hexpand
    exact hexpand
  funext index
  fin_cases index
  · simp [rotateQuarter, dotProduct, Fin.sum_univ_two]
    linear_combination (-anyVec 0) * hnormSq
  · simp [rotateQuarter, dotProduct, Fin.sum_univ_two]
    linear_combination (-anyVec 1) * hnormSq

/-- **Two unit vectors at Gram value one coincide**: the squared difference
vanishes. -/
theorem eq_of_unit_dot_eq_one {firstDir secondDir : Fin 2 → ℝ}
    (hfirst : firstDir ⬝ᵥ firstDir = 1) (hsecond : secondDir ⬝ᵥ secondDir = 1)
    (hgram : firstDir ⬝ᵥ secondDir = 1) : firstDir = secondDir := by
  have hdiff : (firstDir - secondDir) ⬝ᵥ (firstDir - secondDir) = 0 := by
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, hfirst, hsecond,
      dotProduct_comm secondDir firstDir, hgram]
    ring
  have hzero := eq_zero_of_dotProduct_self_eq_zero hdiff
  funext index
  have hcomponent := congrFun hzero index
  simpa [sub_eq_zero] using hcomponent

/-- **The tangency lemma**: an affine form on the circle with a double zero
(value and angular derivative both vanish) at a unit direction, with nonzero
offset, has its normal pinned to `n = −e·w` — the polar line is tangent at
`w`, and every other unit zero of the form coincides with `w`. -/
theorem affine_double_zero_unique {normal leafDir otherDir : Fin 2 → ℝ}
    {offset : ℝ}
    (hleafUnit : leafDir ⬝ᵥ leafDir = 1)
    (hotherUnit : otherDir ⬝ᵥ otherDir = 1)
    (hoffset : offset ≠ 0)
    (hvalue : normal ⬝ᵥ leafDir + offset = 0)
    (hcritical : normal ⬝ᵥ rotateQuarter leafDir = 0)
    (hother : normal ⬝ᵥ otherDir + offset = 0) :
    otherDir = leafDir := by
  -- the double zero pins the normal: n = −offset • w
  have hpinned : normal = (-offset) • leafDir := by
    have hexpand := basis_expansion hleafUnit normal
    rw [hcritical, zero_smul, add_zero] at hexpand
    have hcoeff : normal ⬝ᵥ leafDir = -offset := by linarith
    rw [hcoeff] at hexpand
    exact hexpand
  -- on the tangent line, the second zero has Gram value one against the leaf
  have hgram : leafDir ⬝ᵥ otherDir = 1 := by
    rw [hpinned, smul_dotProduct, smul_eq_mul] at hother
    have hfactor : offset * (leafDir ⬝ᵥ otherDir - 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with hbad | hgood
    · exact absurd hbad hoffset
    · linarith
  exact (eq_of_unit_dot_eq_one hleafUnit hotherUnit hgram).symm

/-! ### The leaf-tangency theorem -/

/-- **The leaf-tangency theorem**: on the focal conic, let `leafDir` be a
stress-leaf with stressed neighbour `unitJ` of conic value `ν_j ≠ 1` (finite
neighbour leverage). If the leaf's edge is tight, the leaf equation holds
(angular criticality of the edge's polar form — the stress-leaf's single
stress equation), and some direction `otherDir` is also tight against the
neighbour, then `otherDir` IS the leaf: the neighbour's polar line is tangent
to the circle at the leaf, so the neighbour has no second distinct tight
partner. Kills every path component and every partially-stressed cycle. -/
theorem leaf_tangency {moment leafDir unitJ otherDir : Fin 2 → ℝ}
    {conicJ : ℝ}
    (hleafUnit : leafDir ⬝ᵥ leafDir = 1)
    (hotherUnit : otherDir ⬝ᵥ otherDir = 1)
    (hfiniteLev : conicJ ≠ 1)
    -- tightness of the leaf's edge against the neighbour, conic form
    (htightLeaf : (1 + unitJ ⬝ᵥ leafDir) / 2
      = conicJ * (1 / 2 + moment ⬝ᵥ leafDir))
    -- the leaf equation: angular criticality of the edge's polar form
    (hleafEq : polarNormal moment unitJ conicJ
      ⬝ᵥ rotateQuarter leafDir = 0)
    -- a second tight partner of the neighbour
    (htightOther : (1 + unitJ ⬝ᵥ otherDir) / 2
      = conicJ * (1 / 2 + moment ⬝ᵥ otherDir)) :
    otherDir = leafDir := by
  have hoffset : (1 - conicJ) / 2 ≠ 0 := by
    intro hzero
    exact hfiniteLev (by linarith)
  have hvalueLeaf : polarNormal moment unitJ conicJ ⬝ᵥ leafDir
      + (1 - conicJ) / 2 = 0 := by
    have hpolar := (tight_iff_polar moment unitJ leafDir conicJ
      (1 / 2 + moment ⬝ᵥ leafDir) rfl).mp htightLeaf
    linarith [hpolar]
  have hvalueOther : polarNormal moment unitJ conicJ ⬝ᵥ otherDir
      + (1 - conicJ) / 2 = 0 := by
    have hpolar := (tight_iff_polar moment unitJ otherDir conicJ
      (1 / 2 + moment ⬝ᵥ otherDir) rfl).mp htightOther
    linarith [hpolar]
  exact affine_double_zero_unique hleafUnit hotherUnit hoffset hvalueLeaf
    hleafEq hvalueOther

end Gtz
