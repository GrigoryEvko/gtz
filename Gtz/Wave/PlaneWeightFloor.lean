/-
# The plane weight floor: a sub-frame of the plane cannot be light

A PLANE SUB-FRAME is finitely many plane vectors `g_a` with strictly positive
weights `t_a` whose weighted atoms resolve the plane identity,

    `sum_a t_a g_a g_a^T = 1` ,

with the total weight `sigma := sum_a t_a` LEFT FREE.  A rank-two design is the
case `sigma = 1`.  Sub-frames of smaller total weight are what a plane SHADOW of a
higher-rank design produces once the atoms that read only the normal are dropped,
and the campaign's coplanar strata all have that shape.

**THEOREM (`Gtz.one_le_sum_weight_of_planeFrame`).**  If NO pair of the sub-frame
strictly dominates the identity on the plane it spans, that is

    `(l_a - 1) (l_b - 1) <= <g_a, g_b>^2`   at every pair,

which is `det(g_a g_a^T + g_b g_b^T - 1) <= 0`, and every leverage exceeds one,
then `sigma >= 1`.  Equivalently (`Gtz.weighted_mean_leverage_le_two`) the
weight-average leverage `2 / sigma` is at most TWO.

The floor is ATTAINED, on a two-parameter family, so no quantitative margin is
available and none is claimed.  The contrapositive is the usable form
(`Gtz.exists_planeStrictPair_of_sum_weight_lt_one`): a plane sub-frame of total
weight BELOW one carries a strictly dominating pair.

## The mechanism, in three moves

**Move 1, the arithmetic core** (`Gtz.sum_le_one_of_pairCap`).  Let `u_a >= 0`
total ONE, and let `A_a <= 1 - u_a` obey `A_a A_b <= u_a u_b` at every pair.  Then
`sum_a A_a <= 1`.  At most one index carries `A_k > u_k`, because a second would
break its own pair cap.  If none does, add the caps.  If `k` does, multiply the
other caps by `A_k` and add:

    `A_k * sum_a A_a <= A_k^2 + u_k (1 - u_k) <= A_k` ,

the last step being `(A_k - u_k)(A_k - (1 - u_k)) <= 0`, and `A_k > u_k >= 0`
cancels.  Both endpoints of that quadratic are equalities, which is exactly why
the floor is attained on a family and not at a point.

**Move 2, corank one** (`Gtz.coShare_planeTriple`).  At THREE atoms the sub-frame
has corank one and the core's hypotheses become identities.  Write
`u_a := 1 - t_a l_a` for the co-share and `J` for the wedge.  The two-term
determinant of Parseval read against one atom,
`det(1 - t_x G_x) = det(t_y G_y + t_z G_z)`, gives

    `u_x = t_y t_z J_yz^2` ,

so the co-shares are nonnegative and total `3 - 2 = 1`.  Their pair products are
then forced,

    `u_x u_y = t_x t_y <g_x, g_y>^2` ,

the SATURATED pairing cap.  For `(k+1, k)` DESIGNS the tree already lands that
equality as `Gtz.weight_mul_sq_dotProduct_eq_coShare_mul`, through the rank-one
outer square of `Gtz.coProjection`.  Here it is proved in the raw, unnormalised
plane vocabulary, where there is no design to hang a projection on, and it falls
out of the co-share law and Lagrange with no case analysis at all.

**Move 3, the exchange** (`Gtz.exists_smaller_planeFrame`).  Four plane atoms
carry a linear dependency, because the symmetric two by two matrices form a
THREE-dimensional space.  Sliding the weights along that dependency keeps
Parseval, keeps every leverage and every pairing, and moves the excess total
`sum_a t_a (l_a - 1)` linearly.  Push in the direction that does not decrease it
until a weight reaches zero: the support drops by at least one and the excess
total does not fall.  So the excess total is largest at three atoms, where Move 2
caps it by one, and `sum_a t_a l_a = 2` turns that cap into `sigma >= 1`.

No compactness, no eigenvalue, no spectral theorem.

## What else is here

* `Gtz.rank_le_two_of_noPlaneStrictPair` and
  `Gtz.exists_planeStrictPair_of_three_le_rank` -- the same core run at corank one
  in EVERY rank: a `(k+1, k)` design with `k >= 3` always carries a pair that
  strictly dominates the identity on the plane that pair spans.  At `k = 2` it does
  not, and the three-atom rank-two ties are exactly the equality case.
* `Gtz.exists_planeStrictPair_of_shadowFlat` -- the rank-three reading.  Fix an
  orthonormal plane frame of a rank-three design and a set `A` carrying every atom
  whose shadow is nonzero.  If the shadows in `A` are heavy and `A` misses weight,
  some pair of `A` strictly dominates the identity ON THAT PLANE.  The
  five-coplanar `(6,3)` configuration is the instance where `A` is the five planar
  atoms and the sixth atom is the spike.
* `Gtz.lightTrineFrame` -- the explicit witness that REFUTES the campaign brief's
  triple cap conjecture `kappa_ab + kappa_bc + kappa_ca <= 2 pi`.  Three plane
  atoms of leverage `11/10` at sixty degrees form a plane sub-frame with no
  strictly dominating pair whose three caps total `6 arccos(1/11) > 2 pi`
  (`Gtz.two_pi_lt_sum_planeCap_lightTrine`).  The conjecture is false on realisable
  data.  What is true is the floor above, and the floor is what empties the
  stratum, because the stratum asks for `sigma < 1`.

[MEASURED before proving, outside Lean, 384 threads.  The chart dictionary at
200000 random whitened plane sub-frames of three to six atoms: Parseval residual
`3.8e-12`, the two circle readings `2.5e-12` and `3.1e-12`, the deficit law
`2.5e-12`, the cap identities `2.8e-14`.  The floor by direct minimisation of
`sigma` over cap-feasible sub-frames, 20000 restarts per size: `1.000071` at three
atoms, `1.000954` at four, `1.004262` at five, `1.007370` at six, `1.013740` at
seven, every minimiser drifting onto the three-class family.  The arithmetic core
at 4000000 random draws, 306352 of them feasible, maximum total `0.99777`.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.InPlaneRestriction
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.CorankOneRigidity
import Gtz.Wave.PlaneCapTripleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

/-! ## Part 1: the arithmetic core

One inequality about two families of reals.  It knows nothing about designs, and
every application below is an instance of it. -/

/-- **THE PAIR-CAP CORE.**  Nonnegative `u` totalling one, and `A` below `1 - u`
whose pair products are below the pair products of `u`, total at most one. -/
theorem sum_le_one_of_pairCap {index : Type*} [DecidableEq index] (support : Finset index)
    (coSquare excess : index → ℝ)
    (hnonneg : ∀ label ∈ support, 0 ≤ coSquare label)
    (htotal : ∑ label ∈ support, coSquare label = 1)
    (hceiling : ∀ label ∈ support, excess label ≤ 1 - coSquare label)
    (hpair : ∀ label ∈ support, ∀ other ∈ support, label ≠ other →
      excess label * excess other ≤ coSquare label * coSquare other) :
    ∑ label ∈ support, excess label ≤ 1 := by
  classical
  by_cases hsmall : ∀ label ∈ support, excess label ≤ coSquare label
  · calc ∑ label ∈ support, excess label
        ≤ ∑ label ∈ support, coSquare label := Finset.sum_le_sum hsmall
      _ = 1 := htotal
  · push_neg at hsmall
    obtain ⟨pivot, hpivotMem, hpivotLarge⟩ := hsmall
    have hpivotPos : 0 < excess pivot := lt_of_le_of_lt (hnonneg pivot hpivotMem) hpivotLarge
    have hrest : excess pivot * ∑ label ∈ support.erase pivot, excess label
        ≤ coSquare pivot * ∑ label ∈ support.erase pivot, coSquare label := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun label hlabel => ?_
      exact hpair pivot hpivotMem label (Finset.mem_of_mem_erase hlabel)
        (Ne.symm (Finset.ne_of_mem_erase hlabel))
    have hsplitCo : coSquare pivot + ∑ label ∈ support.erase pivot, coSquare label = 1 := by
      rw [Finset.add_sum_erase _ _ hpivotMem]; exact htotal
    have hsplitEx : excess pivot + ∑ label ∈ support.erase pivot, excess label
        = ∑ label ∈ support, excess label := Finset.add_sum_erase _ _ hpivotMem
    have hceil := hceiling pivot hpivotMem
    have hbound : excess pivot * ∑ label ∈ support.erase pivot, excess label
        ≤ coSquare pivot * (1 - coSquare pivot) := by
      have hco : ∑ label ∈ support.erase pivot, coSquare label = 1 - coSquare pivot := by
        linarith
      rw [← hco]; exact hrest
    have hquadratic :
        excess pivot ^ 2 + coSquare pivot * (1 - coSquare pivot) ≤ excess pivot := by
      nlinarith [hpivotLarge, hceil]
    have hkey : excess pivot * (∑ label ∈ support, excess label) ≤ excess pivot * 1 := by
      rw [← hsplitEx, mul_one, mul_add]
      nlinarith [hbound, hquadratic]
    exact le_of_mul_le_mul_left hkey hpivotPos

/-! ## Part 2: corank one at every rank

The complementary projection of a `(k+1, k)` design is a rank-one outer square, so
its co-shares are nonnegative, total one, and saturate the pairing cap.  Those are
exactly the three hypotheses of the core. -/

/-- No pair of the design strictly dominates the identity on the plane it spans:
`det(S_{c,d} - 1) <= 0` read as a Gram inequality, at every rank. -/
def NoPlaneStrictPair {size rank : ℕ} (D : WeightedDesign size rank) : Prop :=
  ∀ atomFirst atomSecond : Fin size, atomFirst ≠ atomSecond →
    (leverageOf (D.atom atomFirst) - 1) * (leverageOf (D.atom atomSecond) - 1)
      ≤ (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2

/-- The excess total of any design is `rank - 1`: the trace identity, shifted by
the weight normalisation. -/
theorem sum_weight_mul_leverage_sub_one_eq {size rank : ℕ} (D : WeightedDesign size rank) :
    ∑ atomIndex, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) = (rank : ℝ) - 1 := by
  have hsplit : ∀ atomIndex : Fin size,
      D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1)
        = D.weight atomIndex * leverageOf (D.atom atomIndex) - D.weight atomIndex :=
    fun _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hsplit atomIndex,
    Finset.sum_sub_distrib, sum_weight_mul_leverage D, D.weight_sum_one]

/-- **THE EXCESS TOTAL OF A CORANK-ONE DESIGN IS CAPPED BY ONE.**  The core run on
the co-shares of `Gtz.coProjection`: they are nonnegative
(`Gtz.designCoShare_nonneg`), they total one (`Gtz.sum_designCoShare`), and the
pairing cap is saturated (`Gtz.weight_mul_sq_dotProduct_eq_coShare_mul`). -/
theorem sum_weight_mul_leverage_sub_one_le_one_of_corankOne {rank : ℕ}
    (D : WeightedDesign (rank + 1) rank) (hcap : NoPlaneStrictPair D) :
    ∑ atomIndex, D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1) ≤ 1 := by
  classical
  refine sum_le_one_of_pairCap Finset.univ (designCoShare D)
    (fun atomIndex => D.weight atomIndex * (leverageOf (D.atom atomIndex) - 1))
    (fun atomIndex _ => designCoShare_nonneg D atomIndex) ?_ ?_ ?_
  · rw [sum_designCoShare D]; push_cast; ring
  · intro atomIndex _
    rw [designCoShare_apply]
    have hweight := D.weight_pos atomIndex
    nlinarith
  · intro atomFirst _ atomSecond _ hdistinct
    have hsaturated := weight_mul_sq_dotProduct_eq_coShare_mul D hdistinct
    have hweights : (0 : ℝ) ≤ D.weight atomFirst * D.weight atomSecond :=
      (mul_pos (D.weight_pos atomFirst) (D.weight_pos atomSecond)).le
    calc D.weight atomFirst * (leverageOf (D.atom atomFirst) - 1)
            * (D.weight atomSecond * (leverageOf (D.atom atomSecond) - 1))
        = D.weight atomFirst * D.weight atomSecond
            * ((leverageOf (D.atom atomFirst) - 1)
              * (leverageOf (D.atom atomSecond) - 1)) := by ring
      _ ≤ D.weight atomFirst * D.weight atomSecond
            * (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2 :=
          mul_le_mul_of_nonneg_left (hcap atomFirst atomSecond hdistinct) hweights
      _ = designCoShare D atomFirst * designCoShare D atomSecond := hsaturated

/-- **A CORANK-ONE DESIGN WITH NO PLANE-STRICT PAIR HAS RANK AT MOST TWO.** -/
theorem rank_le_two_of_noPlaneStrictPair {rank : ℕ} (D : WeightedDesign (rank + 1) rank)
    (hcap : NoPlaneStrictPair D) : rank ≤ 2 := by
  have hbound := sum_weight_mul_leverage_sub_one_le_one_of_corankOne D hcap
  rw [sum_weight_mul_leverage_sub_one_eq D] at hbound
  have hcast : (rank : ℝ) ≤ 2 := by linarith
  exact_mod_cast hcast

/-- **EVERY `(k+1, k)` DESIGN WITH `k >= 3` CARRIES A PLANE-STRICT PAIR.**  Two of
its atoms strictly dominate the identity on the plane they span.  At `k = 2` this
fails, and the three-atom rank-two ties are exactly the equality case. -/
theorem exists_planeStrictPair_of_three_le_rank {rank : ℕ} (hrank : 3 ≤ rank)
    (D : WeightedDesign (rank + 1) rank) :
    ∃ atomFirst atomSecond : Fin (rank + 1), atomFirst ≠ atomSecond ∧
      (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2
        < (leverageOf (D.atom atomFirst) - 1) * (leverageOf (D.atom atomSecond) - 1) := by
  by_contra hcontra
  push_neg at hcontra
  have hcap : NoPlaneStrictPair D := fun atomFirst atomSecond hdistinct =>
    hcontra atomFirst atomSecond hdistinct
  have := rank_le_two_of_noPlaneStrictPair D hcap
  omega

/-! ## Part 3: plane sub-frames and their readings

From here the data is RAW: plane vectors, positive weights on a finite support,
and Parseval with the total weight free. -/

/-- **THE DIAGONAL READING OF PLANE PARSEVAL.**  Each coordinate carries mass one. -/
theorem planeFrame_diagReading {index : Type*} (atomOf : index → Fin 2 → ℝ)
    (weightOf : index → ℝ) (support : Finset index)
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) (row : Fin 2) :
    ∑ label ∈ support, weightOf label * (atomOf label row * atomOf label row) = 1 := by
  have hentry := congrFun (congrFun hframe row) row
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at hentry
  rw [← hentry]
  exact Finset.sum_congr rfl fun label _ => by
    simp [atomMatrix, Matrix.vecMulVec_apply]

/-- **THE CROSS READING OF PLANE PARSEVAL.**  The two coordinates are uncorrelated. -/
theorem planeFrame_crossReading {index : Type*} (atomOf : index → Fin 2 → ℝ)
    (weightOf : index → ℝ) (support : Finset index)
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∑ label ∈ support, weightOf label * (atomOf label 0 * atomOf label 1) = 0 := by
  have hentry := congrFun (congrFun hframe 0) 1
  rw [Matrix.sum_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at hentry
  rw [← hentry]
  exact Finset.sum_congr rfl fun label _ => by
    simp [atomMatrix, Matrix.vecMulVec_apply]

/-- The leverage total of a plane sub-frame is TWO, whatever its weight total. -/
theorem planeFrame_trace {index : Type*} (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ)
    (support : Finset index)
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∑ label ∈ support, weightOf label * leverageOf (atomOf label) = 2 := by
  have hzero := planeFrame_diagReading atomOf weightOf support hframe 0
  have hone := planeFrame_diagReading atomOf weightOf support hframe 1
  have hsplit : ∀ label : index, weightOf label * leverageOf (atomOf label)
      = weightOf label * (atomOf label 0 * atomOf label 0)
        + weightOf label * (atomOf label 1 * atomOf label 1) := by
    intro label
    simp only [leverageOf, Fin.sum_univ_two]
    ring
  rw [Finset.sum_congr rfl fun label (_ : label ∈ support) => hsplit label,
    Finset.sum_add_distrib, hzero, hone]
  norm_num

/-- The leverage as a plain sum of two squares. -/
theorem leverageOf_planeMul (vec : Fin 2 → ℝ) : leverageOf vec = vec 0 * vec 0 + vec 1 * vec 1 := by
  simp only [leverageOf, Fin.sum_univ_two]; ring

/-- The pairing of two plane vectors, written out. -/
theorem dotProduct_planeMul (vecFirst vecSecond : Fin 2 → ℝ) :
    vecFirst ⬝ᵥ vecSecond = vecFirst 0 * vecSecond 0 + vecFirst 1 * vecSecond 1 := by
  simp only [dotProduct, Fin.sum_univ_two]

/-- **LAGRANGE IN LEVERAGE VOCABULARY.**  The tree's `Gtz.planeWedge_sq_add_dot_sq`
states the same identity with self-pairings on the right. -/
theorem planeLagrange_leverage (vecFirst vecSecond : Fin 2 → ℝ) :
    planeWedge vecFirst vecSecond ^ 2 + (vecFirst ⬝ᵥ vecSecond) ^ 2
      = leverageOf vecFirst * leverageOf vecSecond := by
  rw [← dotProduct_self_eq_leverageOf, ← dotProduct_self_eq_leverageOf]
  exact planeWedge_sq_add_dot_sq vecFirst vecSecond

/-! ### The three-atom sub-frame: corank one in raw coordinates -/

/-- **THE CO-SHARE LAW, IN COORDINATES.**  The two-term determinant of Parseval
read against one atom.  Both determinants are `ring` identities, so the whole
proof is three readings and one rearrangement. -/
theorem coShare_planeTriple_aux
    {weightX weightY weightZ firstX secondX firstY secondY firstZ secondZ : ℝ}
    (hzero : weightX * (firstX * firstX) + weightY * (firstY * firstY)
      + weightZ * (firstZ * firstZ) = 1)
    (hcross : weightX * (firstX * secondX) + weightY * (firstY * secondY)
      + weightZ * (firstZ * secondZ) = 0)
    (hone : weightX * (secondX * secondX) + weightY * (secondY * secondY)
      + weightZ * (secondZ * secondZ) = 1) :
    1 - weightX * (firstX * firstX + secondX * secondX)
      = weightY * weightZ * (firstY * secondZ - secondY * firstZ) ^ 2 := by
  have hcol : weightY * (firstY * firstY) + weightZ * (firstZ * firstZ)
      = 1 - weightX * (firstX * firstX) := by linarith
  have hrow : weightY * (secondY * secondY) + weightZ * (secondZ * secondZ)
      = 1 - weightX * (secondX * secondX) := by linarith
  have hmix : weightY * (firstY * secondY) + weightZ * (firstZ * secondZ)
      = -(weightX * (firstX * secondX)) := by linarith
  have hkey : (weightY * (firstY * firstY) + weightZ * (firstZ * firstZ))
        * (weightY * (secondY * secondY) + weightZ * (secondZ * secondZ))
      - (weightY * (firstY * secondY) + weightZ * (firstZ * secondZ)) ^ 2
      = weightY * weightZ * (firstY * secondZ - secondY * firstZ) ^ 2 := by ring
  rw [hcol, hrow, hmix] at hkey
  linear_combination hkey

/-- **THE SATURATED PAIRING CAP, IN COORDINATES.**  The trace, the co-share law at
the THIRD atom, and Lagrange.  No case analysis. -/
theorem coShare_mul_planeTriple_aux
    {weightX weightY weightZ leverageX leverageY leverageZ pairing wedge : ℝ}
    (htrace : weightX * leverageX + weightY * leverageY + weightZ * leverageZ = 2)
    (hthird : 1 - weightZ * leverageZ = weightX * weightY * wedge ^ 2)
    (hlagrange : wedge ^ 2 + pairing ^ 2 = leverageX * leverageY) :
    (1 - weightX * leverageX) * (1 - weightY * leverageY)
      = weightX * weightY * pairing ^ 2 := by
  linear_combination -htrace - hthird - (weightX * weightY) * hlagrange

/-- The diagonal reading, unrolled at a three-element support. -/
theorem planeTriple_diagReading {index : Type*} [DecidableEq index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ)
    {first second third : index} (hab : first ≠ second) (hac : first ≠ third)
    (hbc : second ≠ third)
    (hframe : ∑ label ∈ ({first, second, third} : Finset index),
        weightOf label • atomMatrix (atomOf label) = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (row : Fin 2) :
    weightOf first * (atomOf first row * atomOf first row)
        + weightOf second * (atomOf second row * atomOf second row)
        + weightOf third * (atomOf third row * atomOf third row) = 1 := by
  have hsum := planeFrame_diagReading atomOf weightOf _ hframe row
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at hsum
  linarith [hsum]

/-- The cross reading, unrolled at a three-element support. -/
theorem planeTriple_crossReading {index : Type*} [DecidableEq index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ)
    {first second third : index} (hab : first ≠ second) (hac : first ≠ third)
    (hbc : second ≠ third)
    (hframe : ∑ label ∈ ({first, second, third} : Finset index),
        weightOf label • atomMatrix (atomOf label) = (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    weightOf first * (atomOf first 0 * atomOf first 1)
        + weightOf second * (atomOf second 0 * atomOf second 1)
        + weightOf third * (atomOf third 0 * atomOf third 1) = 0 := by
  have hsum := planeFrame_crossReading atomOf weightOf _ hframe
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at hsum
  linarith [hsum]

/-- **THE EXCESS CAP AT THREE ATOMS.**  A three-atom plane sub-frame with no
plane-strict pair has excess total at most one.  This is the corank-one instance of
the core, and it is where the whole theorem is decided. -/
theorem sum_excess_le_one_of_planeTriple {index : Type*} [DecidableEq index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ)
    {first second third : index} (hab : first ≠ second) (hac : first ≠ third)
    (hbc : second ≠ third)
    (hpos : ∀ label ∈ ({first, second, third} : Finset index), 0 < weightOf label)
    (hframe : ∑ label ∈ ({first, second, third} : Finset index),
        weightOf label • atomMatrix (atomOf label) = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hcap : ∀ label ∈ ({first, second, third} : Finset index),
      ∀ other ∈ ({first, second, third} : Finset index), label ≠ other →
        (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
          ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2) :
    ∑ label ∈ ({first, second, third} : Finset index),
      weightOf label * (leverageOf (atomOf label) - 1) ≤ 1 := by
  classical
  have hzero := planeTriple_diagReading atomOf weightOf hab hac hbc hframe 0
  have hcross := planeTriple_crossReading atomOf weightOf hab hac hbc hframe
  have hone := planeTriple_diagReading atomOf weightOf hab hac hbc hframe 1
  -- The three co-share laws, one per atom, from the same three readings.
  have hcoFirst : 1 - weightOf first * leverageOf (atomOf first)
      = weightOf second * weightOf third
        * planeWedge (atomOf second) (atomOf third) ^ 2 := by
    rw [leverageOf_planeMul, planeWedge]
    exact coShare_planeTriple_aux hzero hcross hone
  have hcoSecond : 1 - weightOf second * leverageOf (atomOf second)
      = weightOf first * weightOf third
        * planeWedge (atomOf first) (atomOf third) ^ 2 := by
    rw [leverageOf_planeMul, planeWedge]
    exact coShare_planeTriple_aux (by linarith [hzero]) (by linarith [hcross])
      (by linarith [hone])
  have hcoThird : 1 - weightOf third * leverageOf (atomOf third)
      = weightOf first * weightOf second
        * planeWedge (atomOf first) (atomOf second) ^ 2 := by
    rw [leverageOf_planeMul, planeWedge]
    exact coShare_planeTriple_aux (by linarith [hzero]) (by linarith [hcross])
      (by linarith [hone])
  have htrace : weightOf first * leverageOf (atomOf first)
      + weightOf second * leverageOf (atomOf second)
      + weightOf third * leverageOf (atomOf third) = 2 := by
    have hsum := planeFrame_trace atomOf weightOf _ hframe
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton] at hsum
    linarith [hsum]
  -- The saturated pairing cap at each of the three pairs.
  have hsatFS : (1 - weightOf first * leverageOf (atomOf first))
      * (1 - weightOf second * leverageOf (atomOf second))
      = weightOf first * weightOf second * (atomOf first ⬝ᵥ atomOf second) ^ 2 :=
    coShare_mul_planeTriple_aux htrace hcoThird
      (planeLagrange_leverage (atomOf first) (atomOf second))
  have hsatST : (1 - weightOf second * leverageOf (atomOf second))
      * (1 - weightOf third * leverageOf (atomOf third))
      = weightOf second * weightOf third * (atomOf second ⬝ᵥ atomOf third) ^ 2 :=
    coShare_mul_planeTriple_aux (by linarith [htrace]) hcoFirst
      (planeLagrange_leverage (atomOf second) (atomOf third))
  have hsatFT : (1 - weightOf first * leverageOf (atomOf first))
      * (1 - weightOf third * leverageOf (atomOf third))
      = weightOf first * weightOf third * (atomOf first ⬝ᵥ atomOf third) ^ 2 :=
    coShare_mul_planeTriple_aux (by linarith [htrace]) hcoSecond
      (planeLagrange_leverage (atomOf first) (atomOf third))
  have hmemFirst : first ∈ ({first, second, third} : Finset index) := by simp
  have hmemSecond : second ∈ ({first, second, third} : Finset index) := by simp
  have hmemThird : third ∈ ({first, second, third} : Finset index) := by simp
  have hposFirst := hpos first hmemFirst
  have hposSecond := hpos second hmemSecond
  have hposThird := hpos third hmemThird
  -- The core.
  refine sum_le_one_of_pairCap ({first, second, third} : Finset index)
    (fun label => 1 - weightOf label * leverageOf (atomOf label))
    (fun label => weightOf label * (leverageOf (atomOf label) - 1)) ?_ ?_ ?_ ?_
  · intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · rw [hcoFirst]; positivity
    · rw [hcoSecond]; positivity
    · rw [hcoThird]; positivity
  · rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    linarith [htrace]
  · intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · nlinarith [hposFirst]
    · nlinarith [hposSecond]
    · nlinarith [hposThird]
  · intro label hlabel other hother hdistinct
    have hcapLO := hcap label hlabel other hother hdistinct
    have hprodPos : (0 : ℝ) ≤ weightOf label * weightOf other :=
      (mul_pos (hpos label hlabel) (hpos other hother)).le
    have hstep : weightOf label * (leverageOf (atomOf label) - 1)
          * (weightOf other * (leverageOf (atomOf other) - 1))
        ≤ weightOf label * weightOf other * (atomOf label ⬝ᵥ atomOf other) ^ 2 := by
      calc weightOf label * (leverageOf (atomOf label) - 1)
            * (weightOf other * (leverageOf (atomOf other) - 1))
          = weightOf label * weightOf other
              * ((leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)) := by ring
        _ ≤ weightOf label * weightOf other * (atomOf label ⬝ᵥ atomOf other) ^ 2 :=
            mul_le_mul_of_nonneg_left hcapLO hprodPos
    refine hstep.trans (le_of_eq ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel hother
    rcases hlabel with rfl | rfl | rfl <;> rcases hother with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hdistinct
        | exact hsatFS.symm
        | exact hsatST.symm
        | exact hsatFT.symm
        | (rw [dotProduct_comm]; linear_combination -hsatFS)
        | (rw [dotProduct_comm]; linear_combination -hsatST)
        | (rw [dotProduct_comm]; linear_combination -hsatFT)


/-! ## Part 4: supports of one and two atoms are impossible -/

/-- A one-atom plane sub-frame does not exist: a rank-one matrix is not the
identity. -/
theorem not_planeFrame_singleton {index : Type*} [DecidableEq index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (only : index)
    (hframe : ∑ label ∈ ({only} : Finset index), weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) : False := by
  have hzero := planeFrame_diagReading atomOf weightOf _ hframe 0
  have hcross := planeFrame_crossReading atomOf weightOf _ hframe
  have hone := planeFrame_diagReading atomOf weightOf _ hframe 1
  rw [Finset.sum_singleton] at hzero hcross hone
  nlinarith [hzero, hcross, hone]

/-- A two-atom plane sub-frame has an orthogonal pair, so heaviness makes that pair
strictly dominate.  Hence no two-atom sub-frame satisfies the cap. -/
theorem not_planeFrame_pair {index : Type*} [DecidableEq index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) {first second : index}
    (hne : first ≠ second) (hposFirst : 0 < weightOf first) (hposSecond : 0 < weightOf second)
    (hframe : ∑ label ∈ ({first, second} : Finset index),
        weightOf label • atomMatrix (atomOf label) = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hheavyFirst : 1 < leverageOf (atomOf first)) (hheavySecond : 1 < leverageOf (atomOf second))
    (hcap : (leverageOf (atomOf first) - 1) * (leverageOf (atomOf second) - 1)
      ≤ (atomOf first ⬝ᵥ atomOf second) ^ 2) : False := by
  have hzero := planeFrame_diagReading atomOf weightOf _ hframe 0
  have hcross := planeFrame_crossReading atomOf weightOf _ hframe
  have hone := planeFrame_diagReading atomOf weightOf _ hframe 1
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton] at hzero hcross hone
  -- `1 - t_first l_first = det(t_second G_second) = 0`, and the same at the second atom:
  -- the co-share law with a third weight of zero.
  have hcoFirst : weightOf first * leverageOf (atomOf first) = 1 := by
    have haux := coShare_planeTriple_aux (weightX := weightOf first)
      (weightY := weightOf second) (weightZ := 0) (firstX := atomOf first 0)
      (secondX := atomOf first 1) (firstY := atomOf second 0) (secondY := atomOf second 1)
      (firstZ := 0) (secondZ := 0) (by linarith [hzero]) (by linarith [hcross])
      (by linarith [hone])
    simp only [mul_zero, zero_mul] at haux
    rw [leverageOf_planeMul]
    linarith [haux]
  have hcoSecond : weightOf second * leverageOf (atomOf second) = 1 := by
    have haux := coShare_planeTriple_aux (weightX := weightOf second)
      (weightY := weightOf first) (weightZ := 0) (firstX := atomOf second 0)
      (secondX := atomOf second 1) (firstY := atomOf first 0) (secondY := atomOf first 1)
      (firstZ := 0) (secondZ := 0) (by linarith [hzero]) (by linarith [hcross])
      (by linarith [hone])
    simp only [mul_zero, zero_mul] at haux
    rw [leverageOf_planeMul]
    linarith [haux]
  have hwedge : weightOf first * weightOf second
      * planeWedge (atomOf first) (atomOf second) ^ 2 = 1 := by
    have hkey : (weightOf first * (atomOf first 0 * atomOf first 0)
          + weightOf second * (atomOf second 0 * atomOf second 0))
        * (weightOf first * (atomOf first 1 * atomOf first 1)
          + weightOf second * (atomOf second 1 * atomOf second 1))
        - (weightOf first * (atomOf first 0 * atomOf first 1)
          + weightOf second * (atomOf second 0 * atomOf second 1)) ^ 2
        = weightOf first * weightOf second
          * (atomOf first 0 * atomOf second 1 - atomOf first 1 * atomOf second 0) ^ 2 := by
      ring
    rw [hzero, hcross, hone] at hkey
    rw [planeWedge]
    linarith [hkey]
  have hlagrange := planeLagrange_leverage (atomOf first) (atomOf second)
  have hprod : weightOf first * weightOf second
      * (leverageOf (atomOf first) * leverageOf (atomOf second)) = 1 := by
    calc weightOf first * weightOf second
          * (leverageOf (atomOf first) * leverageOf (atomOf second))
        = (weightOf first * leverageOf (atomOf first))
            * (weightOf second * leverageOf (atomOf second)) := by ring
      _ = 1 := by rw [hcoFirst, hcoSecond]; norm_num
  have hvanish : weightOf first * weightOf second
      * (atomOf first ⬝ᵥ atomOf second) ^ 2 = 0 := by
    linear_combination hprod - hwedge + (weightOf first * weightOf second) * hlagrange
  have hpairingZero : (atomOf first ⬝ᵥ atomOf second) ^ 2 = 0 := by
    have hweights : (0 : ℝ) < weightOf first * weightOf second := mul_pos hposFirst hposSecond
    rcases mul_eq_zero.mp hvanish with hbad | hgood
    · exact absurd hbad (ne_of_gt hweights)
    · exact hgood
  nlinarith [hcap, hpairingZero, hheavyFirst, hheavySecond]

/-! ## Part 5: the exchange, and the floor at every size

Four plane atoms carry a linear dependency, because the symmetric two by two
matrices form a THREE-dimensional space.  Sliding the weights along it keeps
Parseval and moves the excess total linearly, so the excess total is largest at
three atoms. -/

/-- **FOUR PLANE ATOMS CARRY A DEPENDENCY.**  Produced from a four by four matrix
whose last row is zero: a vanishing determinant supplies a kernel vector, so no
rank theory is needed. -/
theorem exists_planeDependency {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (support : Finset index) (hcard : 4 ≤ support.card) :
    ∃ dep : index → ℝ, (∃ label ∈ support, dep label ≠ 0) ∧
      ∀ row col : Fin 2,
        ∑ label ∈ support, dep label * (atomOf label row * atomOf label col) = 0 := by
  classical
  obtain ⟨quad, hquadSub, hquadCard⟩ := Finset.exists_subset_card_eq hcard
  set emb : Fin 4 ↪o index := quad.orderEmbOfFin hquadCard with hemb
  have hmemEmb : ∀ i : Fin 4, emb i ∈ support := fun i =>
    hquadSub (quad.orderEmbOfFin_mem hquadCard i)
  set veronese : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun row col =>
    (![atomOf (emb col) 0 * atomOf (emb col) 0,
       atomOf (emb col) 0 * atomOf (emb col) 1,
       atomOf (emb col) 1 * atomOf (emb col) 1, 0] : Fin 4 → ℝ) row with hveronese
  have hdet : veronese.det = 0 := by
    refine Matrix.det_eq_zero_of_row_eq_zero (i := 3) fun col => ?_
    simp [hveronese]
  obtain ⟨coef, hcoefNe, hcoefKer⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsqZero : ∑ i : Fin 4, coef i * (atomOf (emb i) 0 * atomOf (emb i) 0) = 0 := by
    have hentry := congrFun hcoefKer 0
    simp only [Matrix.mulVec, dotProduct, hveronese, Matrix.of_apply, Matrix.cons_val_zero,
      Pi.zero_apply, Fin.sum_univ_four] at hentry
    simp only [Fin.sum_univ_four]
    linear_combination hentry
  have hmixZero : ∑ i : Fin 4, coef i * (atomOf (emb i) 0 * atomOf (emb i) 1) = 0 := by
    have hentry := congrFun hcoefKer 1
    simp [Matrix.mulVec, dotProduct, hveronese, Fin.sum_univ_four] at hentry
    simp only [Fin.sum_univ_four]
    linear_combination hentry
  have hsqOne : ∑ i : Fin 4, coef i * (atomOf (emb i) 1 * atomOf (emb i) 1) = 0 := by
    have hentry := congrFun hcoefKer 2
    simp only [Matrix.mulVec, dotProduct, hveronese, Matrix.of_apply, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply, Fin.sum_univ_four] at hentry
    simp only [Fin.sum_univ_four]
    linear_combination hentry
  refine ⟨fun label => ∑ i : Fin 4, if label = emb i then coef i else 0, ?_, ?_⟩
  · obtain ⟨pivot, hpivot⟩ : ∃ i : Fin 4, coef i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hcoefNe (funext hcon)
    refine ⟨emb pivot, hmemEmb pivot, ?_⟩
    have hcond : ∀ j : Fin 4,
        (if emb pivot = emb j then coef j else 0) = (if pivot = j then coef j else 0) := by
      intro j
      by_cases hmatch : pivot = j
      · simp [hmatch]
      · have hembNe : ¬ (emb pivot = emb j) := fun hbad => hmatch (emb.injective hbad)
        simp [hmatch, hembNe]
    have hval : (∑ j : Fin 4, if emb pivot = emb j then coef j else 0) = coef pivot := by
      calc (∑ j : Fin 4, if emb pivot = emb j then coef j else 0)
          = ∑ j : Fin 4, (if pivot = j then coef j else 0) :=
            Finset.sum_congr rfl fun j _ => hcond j
        _ = coef pivot := by
            rw [Finset.sum_ite_eq Finset.univ pivot coef, if_pos (Finset.mem_univ pivot)]
    show (∑ j : Fin 4, if emb pivot = emb j then coef j else 0) ≠ 0
    rw [hval]
    exact hpivot
  · have htransport : ∀ f : index → ℝ,
        ∑ label ∈ support, (∑ i : Fin 4, if label = emb i then coef i else 0) * f label
          = ∑ i : Fin 4, coef i * f (emb i) := by
      intro f
      have hstep : ∀ label ∈ support,
          (∑ i : Fin 4, if label = emb i then coef i else 0) * f label
            = ∑ i : Fin 4, (if label = emb i then coef i * f label else 0) := by
        intro label _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      calc ∑ label ∈ support, (∑ i : Fin 4, if label = emb i then coef i else 0) * f label
          = ∑ label ∈ support, ∑ i : Fin 4, (if label = emb i then coef i * f label else 0) :=
            Finset.sum_congr rfl hstep
        _ = ∑ i : Fin 4, ∑ label ∈ support, (if label = emb i then coef i * f label else 0) :=
            Finset.sum_comm
        _ = ∑ i : Fin 4, coef i * f (emb i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_ite_eq' support (emb i) (fun label => coef i * f label),
              if_pos (hmemEmb i)]
    intro row col
    rw [htransport (fun label => atomOf label row * atomOf label col)]
    fin_cases row <;> fin_cases col <;> simp only [Fin.zero_eta, Fin.mk_one]
    · exact hsqZero
    · exact hmixZero
    · rw [show (∑ i : Fin 4, coef i * (atomOf (emb i) 1 * atomOf (emb i) 0))
          = ∑ i : Fin 4, coef i * (atomOf (emb i) 0 * atomOf (emb i) 1) from
        Finset.sum_congr rfl fun i _ => by ring]
      exact hmixZero
    · exact hsqOne

/-- **ONE EXCHANGE STEP**, with the direction of the dependency already chosen so
that the excess total does not fall. -/
theorem exists_smaller_planeFrame_of_dependency {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (dep : index → ℝ)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 0 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hdepZero : ∀ row col : Fin 2,
      ∑ label ∈ support, dep label * (atomOf label row * atomOf label col) = 0)
    (hdepNe : ∃ label ∈ support, dep label ≠ 0)
    (hgamma : 0 ≤ ∑ label ∈ support, dep label * (leverageOf (atomOf label) - 1)) :
    ∃ (newWeight : index → ℝ) (newSupport : Finset index), newSupport ⊂ support ∧
      (∀ label ∈ newSupport, 0 < newWeight label) ∧
      (∑ label ∈ newSupport, newWeight label • atomMatrix (atomOf label)
        = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1)
        ≤ ∑ label ∈ newSupport, newWeight label * (leverageOf (atomOf label) - 1) := by
  classical
  have hdepTrace : ∑ label ∈ support, dep label * leverageOf (atomOf label) = 0 := by
    have hzero := hdepZero 0 0
    have hone := hdepZero 1 1
    have hsplit : ∀ label ∈ support, dep label * leverageOf (atomOf label)
        = dep label * (atomOf label 0 * atomOf label 0)
          + dep label * (atomOf label 1 * atomOf label 1) := by
      intro label _
      rw [leverageOf_planeMul]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hzero, hone]
    norm_num
  obtain ⟨witness, hwitnessMem, hwitnessNe⟩ := hdepNe
  have hnegNonempty : (support.filter fun label => dep label < 0).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hallNonneg : ∀ label ∈ support, 0 ≤ dep label := by
      intro label hlabel
      by_contra hbad
      push_neg at hbad
      have hmem : label ∈ support.filter fun l => dep l < 0 :=
        Finset.mem_filter.mpr ⟨hlabel, hbad⟩
      rw [hcon] at hmem
      exact absurd hmem (Finset.notMem_empty label)
    have hwitnessPos : 0 < dep witness :=
      lt_of_le_of_ne (hallNonneg witness hwitnessMem) (Ne.symm hwitnessNe)
    have hstrict : 0 < ∑ label ∈ support, dep label * leverageOf (atomOf label) :=
      Finset.sum_pos' (fun label hlabel =>
        mul_nonneg (hallNonneg label hlabel) (hheavy label hlabel).le)
        ⟨witness, hwitnessMem, mul_pos hwitnessPos (hheavy witness hwitnessMem)⟩
    rw [hdepTrace] at hstrict
    exact lt_irrefl 0 hstrict
  obtain ⟨pivot, hpivotMem, hpivotMin⟩ := Finset.exists_min_image
    (support.filter fun label => dep label < 0)
    (fun label => weightOf label / (-dep label)) hnegNonempty
  obtain ⟨hpivotSupport, hpivotNeg⟩ := Finset.mem_filter.mp hpivotMem
  have hpivotNegPos : (0 : ℝ) < -dep pivot := by linarith
  obtain ⟨step, hstepDef⟩ : ∃ scale : ℝ, scale = weightOf pivot / (-dep pivot) := ⟨_, rfl⟩
  have hstepPos : 0 < step := by
    rw [hstepDef]; exact div_pos (hpos pivot hpivotSupport) hpivotNegPos
  obtain ⟨newWeight, hnewDef⟩ :
      ∃ nw : index → ℝ, nw = fun label => weightOf label + step * dep label := ⟨_, rfl⟩
  have hnewApply : ∀ label : index, newWeight label = weightOf label + step * dep label := by
    intro label; rw [hnewDef]
  have hnewNonneg : ∀ label ∈ support, 0 ≤ newWeight label := by
    intro label hlabel
    rw [hnewApply]
    by_cases hsign : 0 ≤ dep label
    · have hterm : 0 ≤ step * dep label := mul_nonneg hstepPos.le hsign
      linarith [hpos label hlabel]
    · push_neg at hsign
      have hmem : label ∈ support.filter fun other => dep other < 0 :=
        Finset.mem_filter.mpr ⟨hlabel, hsign⟩
      have hnegPos : (0 : ℝ) < -dep label := by linarith
      have hratio : step ≤ weightOf label / (-dep label) := by
        rw [hstepDef]; exact hpivotMin label hmem
      have hkey : step * (-dep label) ≤ weightOf label := (le_div_iff₀ hnegPos).mp hratio
      linarith [hkey]
  have hpivotZero : newWeight pivot = 0 := by
    have hcancel : step * dep pivot = -weightOf pivot := by
      rw [hstepDef, div_mul_eq_mul_div, eq_comm, eq_div_iff (ne_of_gt hpivotNegPos)]
      ring
    rw [hnewApply, hcancel]
    ring
  obtain ⟨newSupport, hnewSupportDef⟩ :
      ∃ ns : Finset index, ns = support.filter fun label => 0 < newWeight label := ⟨_, rfl⟩
  have hmemNew : ∀ label : index,
      label ∈ newSupport ↔ (label ∈ support ∧ 0 < newWeight label) := by
    intro label
    rw [hnewSupportDef, Finset.mem_filter]
  have hsub : newSupport ⊆ support := fun label hlabel => ((hmemNew label).mp hlabel).1
  have hdropped : ∀ label ∈ support, label ∉ newSupport → newWeight label = 0 := by
    intro label hlabel hnot
    have hnotpos : ¬ (0 < newWeight label) := fun hbad => hnot ((hmemNew label).mpr ⟨hlabel, hbad⟩)
    push_neg at hnotpos
    exact le_antisymm hnotpos (hnewNonneg label hlabel)
  have hdepMat : ∑ label ∈ support, dep label • atomMatrix (atomOf label)
      = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext row col
    rw [Matrix.sum_apply, Matrix.zero_apply, ← hdepZero row col]
    exact Finset.sum_congr rfl fun label _ => by
      simp [atomMatrix, Matrix.vecMulVec_apply]
  have hfullFrame : ∑ label ∈ support, newWeight label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have hsplit : ∀ label ∈ support, newWeight label • atomMatrix (atomOf label)
        = weightOf label • atomMatrix (atomOf label)
          + step • (dep label • atomMatrix (atomOf label)) := by
      intro label _
      rw [hnewApply, add_smul, smul_smul]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum, hdepMat,
      smul_zero, add_zero, hframe]
  refine ⟨newWeight, newSupport, ?_,
    fun label hlabel => ((hmemNew label).mp hlabel).2, ?_, ?_⟩
  · refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨pivot, hpivotSupport, ?_⟩
    intro hbad
    have := ((hmemNew pivot).mp hbad).2
    rw [hpivotZero] at this
    exact lt_irrefl 0 this
  · rw [← hfullFrame]
    refine Finset.sum_subset (f := fun label => newWeight label • atomMatrix (atomOf label))
      hsub fun label hlabel hnot => ?_
    rw [hdropped label hlabel hnot, zero_smul]
  · have hexcess : ∑ label ∈ newSupport, newWeight label * (leverageOf (atomOf label) - 1)
        = ∑ label ∈ support, newWeight label * (leverageOf (atomOf label) - 1) := by
      refine Finset.sum_subset
        (f := fun label => newWeight label * (leverageOf (atomOf label) - 1))
        hsub fun label hlabel hnot => ?_
      rw [hdropped label hlabel hnot, zero_mul]
    rw [hexcess]
    have hlinear : ∑ label ∈ support, newWeight label * (leverageOf (atomOf label) - 1)
        = (∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1))
          + step * ∑ label ∈ support, dep label * (leverageOf (atomOf label) - 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun label _ => by rw [hnewApply]; ring
    rw [hlinear]
    nlinarith [hstepPos, hgamma]

/-- **THE EXCHANGE STEP.**  Above three atoms the support can always be cut without
lowering the excess total. -/
theorem exists_smaller_planeFrame {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (hcard : 4 ≤ support.card)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 0 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ (newWeight : index → ℝ) (newSupport : Finset index), newSupport ⊂ support ∧
      (∀ label ∈ newSupport, 0 < newWeight label) ∧
      (∑ label ∈ newSupport, newWeight label • atomMatrix (atomOf label)
        = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1)
        ≤ ∑ label ∈ newSupport, newWeight label * (leverageOf (atomOf label) - 1) := by
  classical
  obtain ⟨dep, hdepNe, hdepZero⟩ := exists_planeDependency atomOf support hcard
  by_cases hgamma : 0 ≤ ∑ label ∈ support, dep label * (leverageOf (atomOf label) - 1)
  · exact exists_smaller_planeFrame_of_dependency atomOf weightOf support dep hpos hheavy
      hframe hdepZero hdepNe hgamma
  · push_neg at hgamma
    refine exists_smaller_planeFrame_of_dependency atomOf weightOf support
      (fun label => -dep label) hpos hheavy hframe (fun row col => ?_) ?_ ?_
    · have hneg : ∀ label ∈ support, -dep label * (atomOf label row * atomOf label col)
          = -(dep label * (atomOf label row * atomOf label col)) := fun _ _ => by ring
      rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, hdepZero row col, neg_zero]
    · obtain ⟨label, hlabel, hne⟩ := hdepNe
      exact ⟨label, hlabel, by simpa using hne⟩
    · have hneg : ∀ label ∈ support, -dep label * (leverageOf (atomOf label) - 1)
          = -(dep label * (leverageOf (atomOf label) - 1)) := fun _ _ => by ring
      rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
      linarith [hgamma]

/-! ## Part 6: the floor

The exchange cuts the support until three atoms remain, and there the corank-one
core caps the excess total.  Supports of one and two atoms cannot occur. -/

private theorem sum_excess_le_one_aux {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) :
    ∀ (bound : ℕ) (weightOf : index → ℝ) (support : Finset index), support.card ≤ bound →
      (∀ label ∈ support, 0 < weightOf label) →
      (∀ label ∈ support, 1 < leverageOf (atomOf label)) →
      (∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
        = (1 : Matrix (Fin 2) (Fin 2) ℝ)) →
      (∀ label ∈ support, ∀ other ∈ support, label ≠ other →
        (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
          ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2) →
      ∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1) ≤ 1 := by
  intro bound
  induction bound with
  | zero =>
    intro weightOf support hcard hpos hheavy hframe hcap
    have hempty : support = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    rw [Finset.sum_empty] at hframe
    have hbad := congrFun (congrFun hframe 0) 0
    simp [Matrix.one_apply] at hbad
  | succ shorter ih =>
    intro weightOf support hcard hpos hheavy hframe hcap
    by_cases hbig : 4 ≤ support.card
    · obtain ⟨newWeight, newSupport, hproper, hnewPos, hnewFrame, hmono⟩ :=
        exists_smaller_planeFrame atomOf weightOf support hbig hpos
          (fun label hlabel => lt_trans one_pos (hheavy label hlabel)) hframe
      have hsubset : newSupport ⊆ support := hproper.subset
      have hshrink : newSupport.card ≤ shorter := by
        have hlt := Finset.card_lt_card hproper
        omega
      exact le_trans hmono (ih newWeight newSupport hshrink hnewPos
        (fun label hlabel => hheavy label (hsubset hlabel)) hnewFrame
        (fun label hlabel other hother hne =>
          hcap label (hsubset hlabel) other (hsubset hother) hne))
    · push_neg at hbig
      have hsplit : support.card = 0 ∨ support.card = 1 ∨ support.card = 2
          ∨ support.card = 3 := by omega
      rcases hsplit with hnum | hnum | hnum | hnum
      · have hempty : support = ∅ := Finset.card_eq_zero.mp hnum
        subst hempty
        rw [Finset.sum_empty] at hframe
        have hbad := congrFun (congrFun hframe 0) 0
        simp [Matrix.one_apply] at hbad
      · obtain ⟨only, hsingle⟩ := Finset.card_eq_one.mp hnum
        subst hsingle
        exact (not_planeFrame_singleton atomOf weightOf only hframe).elim
      · obtain ⟨left, right, hne, hpairEq⟩ := Finset.card_eq_two.mp hnum
        subst hpairEq
        have hmemLeft : left ∈ ({left, right} : Finset index) := by simp
        have hmemRight : right ∈ ({left, right} : Finset index) := by simp
        exact (not_planeFrame_pair atomOf weightOf hne (hpos left hmemLeft)
          (hpos right hmemRight) hframe (hheavy left hmemLeft) (hheavy right hmemRight)
          (hcap left hmemLeft right hmemRight hne)).elim
      · obtain ⟨one, two, three, hab, hac, hbc, htripleEq⟩ := Finset.card_eq_three.mp hnum
        subst htripleEq
        exact sum_excess_le_one_of_planeTriple atomOf weightOf hab hac hbc hpos hframe hcap

/-- **THE EXCESS CAP OF A PLANE SUB-FRAME.**  At every size, with the total weight
unnormalised: `sum_a t_a (l_a - 1) <= 1`. -/
theorem sum_excess_le_one_of_planeFrame {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 1 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hcap : ∀ label ∈ support, ∀ other ∈ support, label ≠ other →
      (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
        ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2) :
    ∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1) ≤ 1 :=
  sum_excess_le_one_aux atomOf support.card weightOf support le_rfl hpos hheavy hframe hcap

/-- **THE PLANE WEIGHT FLOOR.**  A plane sub-frame whose leverages exceed one and
none of whose pairs strictly dominates the identity on the plane it spans has total
weight at least ONE.

The floor is attained, on the two-parameter family of three-class rank-two ties,
so there is no margin here and none is claimed. -/
theorem one_le_sum_weight_of_planeFrame {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 1 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hcap : ∀ label ∈ support, ∀ other ∈ support, label ≠ other →
      (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
        ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2) :
    1 ≤ ∑ label ∈ support, weightOf label := by
  have htrace := planeFrame_trace atomOf weightOf support hframe
  have hexcess := sum_excess_le_one_of_planeFrame atomOf weightOf support hpos hheavy hframe hcap
  have hsplit : ∑ label ∈ support, weightOf label * (leverageOf (atomOf label) - 1)
      = (∑ label ∈ support, weightOf label * leverageOf (atomOf label))
        - ∑ label ∈ support, weightOf label := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsplit, htrace] at hexcess
  linarith

/-- **THE MEAN LEVERAGE OF A PLANE SUB-FRAME IS AT MOST TWO.**  The same statement,
read as an average: `sum_a t_a l_a = 2` always, so the floor says the weighted mean
leverage `2 / sigma` never exceeds two.  The Mercedes trine attains it. -/
theorem weighted_mean_leverage_le_two {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 1 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hcap : ∀ label ∈ support, ∀ other ∈ support, label ≠ other →
      (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
        ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2) :
    ∑ label ∈ support, weightOf label * leverageOf (atomOf label)
      ≤ 2 * ∑ label ∈ support, weightOf label := by
  have htrace := planeFrame_trace atomOf weightOf support hframe
  have hfloor := one_le_sum_weight_of_planeFrame atomOf weightOf support hpos hheavy hframe hcap
  rw [htrace]
  linarith

/-- **A LIGHT PLANE SUB-FRAME CARRIES A STRICTLY DOMINATING PAIR.**  The
contrapositive of the floor, and the form the campaign spends: total weight below
one buys a pair `{a,b}` with `det(g_a g_a^T + g_b g_b^T - 1) > 0`. -/
theorem exists_planeStrictPair_of_sum_weight_lt_one {index : Type*} [LinearOrder index]
    (atomOf : index → Fin 2 → ℝ) (weightOf : index → ℝ) (support : Finset index)
    (hpos : ∀ label ∈ support, 0 < weightOf label)
    (hheavy : ∀ label ∈ support, 1 < leverageOf (atomOf label))
    (hframe : ∑ label ∈ support, weightOf label • atomMatrix (atomOf label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hlight : ∑ label ∈ support, weightOf label < 1) :
    ∃ label ∈ support, ∃ other ∈ support, label ≠ other ∧
      (atomOf label ⬝ᵥ atomOf other) ^ 2
        < (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1) := by
  by_contra hcontra
  push_neg at hcontra
  have hcap : ∀ label ∈ support, ∀ other ∈ support, label ≠ other →
      (leverageOf (atomOf label) - 1) * (leverageOf (atomOf other) - 1)
        ≤ (atomOf label ⬝ᵥ atomOf other) ^ 2 := by
    intro label hlabel other hother hne
    exact hcontra label hlabel other hother hne
  have := one_le_sum_weight_of_planeFrame atomOf weightOf support hpos hheavy hframe hcap
  linarith

/-! ## Part 7: the triple cap conjecture is FALSE

The campaign brief conjectures `kappa_ab + kappa_bc + kappa_ca <= 2 pi` for the caps
of a coplanar stratum, with equality only at the Mercedes.  Three plane atoms of
leverage `11/10` at sixty degrees refute it: they form a plane sub-frame, no pair
of them strictly dominates, and their three caps total `6 arccos(1/11)`, which
exceeds `2 pi`.  What is true is the floor of Part 6, and the floor is what empties
the stratum, because the stratum asks for total weight below one. -/

/-- The non-strict cap of a pair, as the brief defines it:
`cos(kappa/2) = sin(beta_a) sin(beta_b)` with `sin^2 beta_a = 1 - 1/l_a`. -/
noncomputable def nonStrictCapAngle (leverageFirst leverageSecond : ℝ) : ℝ :=
  2 * Real.arccos (Real.sqrt ((1 - 1 / leverageFirst) * (1 - 1 / leverageSecond)))

/-- The LIGHT TRINE: three plane atoms of leverage `11/10` at sixty degrees. -/
noncomputable def lightTrineAtom : Fin 3 → Fin 2 → ℝ :=
  ![![Real.sqrt (11 / 10), 0],
    ![Real.sqrt (11 / 10) / 2, Real.sqrt (11 / 10) * Real.sqrt 3 / 2],
    ![-(Real.sqrt (11 / 10) / 2), Real.sqrt (11 / 10) * Real.sqrt 3 / 2]]

/-- The uniform weight that makes the light trine resolve the plane identity. -/
noncomputable def lightTrineWeight : Fin 3 → ℝ := fun _ => 20 / 33

private theorem lightTrine_rootSq :
    Real.sqrt (11 / 10) * Real.sqrt (11 / 10) = 11 / 10 := Real.mul_self_sqrt (by norm_num)

private theorem lightTrine_threeSq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private theorem lightTrine_crossSq :
    (Real.sqrt (11 / 10) * Real.sqrt 3) * (Real.sqrt (11 / 10) * Real.sqrt 3) = 33 / 10 := by
  calc (Real.sqrt (11 / 10) * Real.sqrt 3) * (Real.sqrt (11 / 10) * Real.sqrt 3)
      = (Real.sqrt (11 / 10) * Real.sqrt (11 / 10)) * (Real.sqrt 3 * Real.sqrt 3) := by ring
    _ = (11 / 10) * 3 := by rw [lightTrine_rootSq, lightTrine_threeSq]
    _ = 33 / 10 := by norm_num

theorem lightTrineAtom_leverage (label : Fin 3) :
    leverageOf (lightTrineAtom label) = 11 / 10 := by
  have hzero : leverageOf (lightTrineAtom 0) = 11 / 10 := by
    rw [leverageOf_planeMul]
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have hone : leverageOf (lightTrineAtom 1) = 11 / 10 := by
    rw [leverageOf_planeMul]
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have htwo : leverageOf (lightTrineAtom 2) = 11 / 10 := by
    rw [leverageOf_planeMul]
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  fin_cases label
  · exact hzero
  · exact hone
  · exact htwo

/-- **THE LIGHT TRINE IS A PLANE SUB-FRAME.** -/
theorem lightTrineFrame :
    ∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hentry : ∀ row col : Fin 2,
      (∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label)) row col
        = lightTrineWeight 0 * (lightTrineAtom 0 row * lightTrineAtom 0 col)
          + lightTrineWeight 1 * (lightTrineAtom 1 row * lightTrineAtom 1 col)
          + lightTrineWeight 2 * (lightTrineAtom 2 row * lightTrineAtom 2 col) := by
    intro row col
    rw [Matrix.sum_apply, Fin.sum_univ_three]
    simp [atomMatrix, Matrix.vecMulVec_apply]
  have hdiagZero : (∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label))
      0 0 = 1 := by
    rw [hentry]
    simp only [lightTrineWeight, lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have hdiagOne : (∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label))
      1 1 = 1 := by
    rw [hentry]
    simp only [lightTrineWeight, lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have hoffOne : (∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label))
      0 1 = 0 := by
    rw [hentry]
    simp only [lightTrineWeight, lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have hoffTwo : (∑ label : Fin 3, lightTrineWeight label • atomMatrix (lightTrineAtom label))
      1 0 = 0 := by
    rw [hentry]
    simp only [lightTrineWeight, lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  ext row col
  fin_cases row <;> fin_cases col
  · exact hdiagZero.trans (Matrix.one_apply_eq (0 : Fin 2)).symm
  · exact hoffOne.trans (Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)).symm
  · exact hoffTwo.trans (Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)).symm
  · exact hdiagOne.trans (Matrix.one_apply_eq (1 : Fin 2)).symm

/-- The total weight of the light trine is `20/11`, comfortably above the floor. -/
theorem lightTrine_sum_weight : ∑ label : Fin 3, lightTrineWeight label = 20 / 11 := by
  simp only [lightTrineWeight, Fin.sum_univ_three]
  norm_num

/-- **NO PAIR OF THE LIGHT TRINE STRICTLY DOMINATES.**  Every squared pairing is
`121/400`, and the excess product is `1/100`. -/
theorem lightTrine_noStrictPair {labelFirst labelSecond : Fin 3}
    (hne : labelFirst ≠ labelSecond) :
    (leverageOf (lightTrineAtom labelFirst) - 1) * (leverageOf (lightTrineAtom labelSecond) - 1)
      ≤ (lightTrineAtom labelFirst ⬝ᵥ lightTrineAtom labelSecond) ^ 2 := by
  have hdot : ∀ leftIndex rightIndex : Fin 3,
      lightTrineAtom leftIndex ⬝ᵥ lightTrineAtom rightIndex
        = lightTrineAtom leftIndex 0 * lightTrineAtom rightIndex 0
          + lightTrineAtom leftIndex 1 * lightTrineAtom rightIndex 1 := by
    intro leftIndex rightIndex
    rw [dotProduct_planeMul]
  rw [lightTrineAtom_leverage, lightTrineAtom_leverage]
  have entry01 : (lightTrineAtom 0 0 * lightTrineAtom 1 0
      + lightTrineAtom 0 1 * lightTrineAtom 1 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have entry02 : (lightTrineAtom 0 0 * lightTrineAtom 2 0
      + lightTrineAtom 0 1 * lightTrineAtom 2 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have entry10 : (lightTrineAtom 1 0 * lightTrineAtom 0 0
      + lightTrineAtom 1 1 * lightTrineAtom 0 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have entry12 : (lightTrineAtom 1 0 * lightTrineAtom 2 0
      + lightTrineAtom 1 1 * lightTrineAtom 2 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have entry20 : (lightTrineAtom 2 0 * lightTrineAtom 0 0
      + lightTrineAtom 2 1 * lightTrineAtom 0 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have entry21 : (lightTrineAtom 2 0 * lightTrineAtom 1 0
      + lightTrineAtom 2 1 * lightTrineAtom 1 1) ^ 2 = 121 / 400 := by
    simp only [lightTrineAtom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    nlinarith [lightTrine_rootSq, lightTrine_threeSq, lightTrine_crossSq]
  have hpairing : (lightTrineAtom labelFirst ⬝ᵥ lightTrineAtom labelSecond) ^ 2 = 121 / 400 := by
    rw [hdot]
    fin_cases labelFirst <;> fin_cases labelSecond <;>
      first
        | exact absurd rfl hne
        | exact entry01
        | exact entry02
        | exact entry10
        | exact entry12
        | exact entry20
        | exact entry21
  rw [hpairing]
  norm_num

theorem nonStrictCapAngle_lightTrine :
    nonStrictCapAngle (11 / 10) (11 / 10) = 2 * Real.arccos (1 / 11) := by
  have hval : ((1 : ℝ) - 1 / (11 / 10)) * (1 - 1 / (11 / 10)) = (1 / 11) ^ 2 := by norm_num
  rw [nonStrictCapAngle, hval, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 11)]

theorem pi_div_three_lt_arccos_inv_eleven : Real.pi / 3 < Real.arccos (1 / 11) := by
  have hhalf : Real.arccos (1 / 2) = Real.pi / 3 := by
    rw [show (1 : ℝ) / 2 = Real.cos (Real.pi / 3) by rw [Real.cos_pi_div_three]]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  rw [← hhalf]
  by_contra hcontra
  push_neg at hcontra
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
    (Real.arccos_le_pi _) hcontra
  rw [Real.cos_arccos (by norm_num) (by norm_num),
    Real.cos_arccos (by norm_num) (by norm_num)] at hmono
  norm_num at hmono

/-- **THE TRIPLE CAP CONJECTURE IS FALSE.**  The three caps of the light trine total
more than `2 pi`, on a genuine plane sub-frame with no strictly dominating pair. -/
theorem two_pi_lt_sum_nonStrictCapAngle_lightTrine :
    2 * Real.pi < nonStrictCapAngle (11 / 10) (11 / 10)
      + nonStrictCapAngle (11 / 10) (11 / 10) + nonStrictCapAngle (11 / 10) (11 / 10) := by
  rw [nonStrictCapAngle_lightTrine]
  linarith [pi_div_three_lt_arccos_inv_eleven]
