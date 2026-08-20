import Gtz.Wave.CorankOneGramMirror
import Gtz.Wave.CorankOneAssembly
import Gtz.Wave.InvariantTaxTeeth
import Gtz.Wave.InvariantBudgets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The one-zero stratum: the anchored pair and its determinant law

The readings `beta_c = g_c . w` of a corank-one weak dominator along its unit
null direction stratify the arm by their zero pattern: `K2` (two zeros, one
inside atom IS `+-w`), `K1` (exactly one zero), `K0` (none).  This module
builds `K1`, which had no map.

THE STRUCTURE.  A zero reading at one inside atom moves the whole null
direction onto the OTHER TWO: `beta_x = 0` and the resolve identity give
`w = beta_y . g_y + beta_z . g_z`, so

  `(g_y g_y' + g_z g_z') w = w`   (`Gtz.kOne_pairAnchor`)

-- THE PAIR ALONE FIXES THE NULL DIRECTION.  Everything else follows from
that single anchor equation, at general vectors, with no design and no tie:

* `Gtz.pairAnchor_wedge_eq` — the anchored pair has a SINGULAR gap:
  `(l_y - 1)(l_z - 1) = <g_y,g_z>^2`, equivalently the pair wedge is
  `w_{yz} = l_y + l_z - 1`.  The pair sits exactly on the discriminant.
* `Gtz.det_pairSum_add_atom_sub_one` — the unconditional expansion of
  `det(g_yg_y' + g_zg_z' + gg' - 1)` in the six scalars of the three vectors.
* `Gtz.pairAnchor_det_update` — THE ANCHORED DETERMINANT LAW: at an anchored
  pair, for EVERY probe atom `g`,

    `det(g_yg_y' + g_zg_z' + gg' - 1) = -(l_y + l_z - 2)(g . w)^2` .

  The determinant of the enlarged gap is a PURE SQUARE in the reading of the
  new atom, scaled by the pair's leverage excess.  No inverse, no spectrum.
* `Gtz.not_posDef_of_pairAnchor_add_atom` — hence a sign law: once the pair
  carries leverage two, NO atom can make the triple strictly dominate.

THE `K1` CONSEQUENCES.  At a `K1` corank-one dominator the zero-reading atom
has leverage strictly above one (`Gtz.kOne_leverage_gt_one`: leverage one
would make it `+-w`, whose reading is `+-1`), the second invariant of the gap
prices the stratum

  `e2(S_C - 1) = (l_y + l_z - 2)(l_x - 1) - (<g_x,g_y>^2 + <g_x,g_z>^2)`
  (`Gtz.kOne_e2_price`),

and positive semidefiniteness turns that into the leverage floor
`2 <= l_y + l_z` (`Gtz.kOne_two_le_leverageSum`).  Feeding the floor back into
the sign law gives THE FREE REFUSAL BUDGET OF `K1`
(`Gtz.kOne_not_posDef_pairTriple`): every triple built from the two live atoms
and ANY sixth atom fails to dominate strictly, with no tie hypothesis at all.
At `(6,3)` that is four of the twenty triples discharged for free, the `K1`
analogue of the `Z1` and `K2` refusal budgets.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The unconditional pair-sum determinant expansion -/

/-- **THE PAIR-SUM EXPANSION.**  For any three vectors the determinant of the
gap of the three rank-one sums is a polynomial in their six scalar
invariants.  The coefficient of the probe leverage is the pair
DISCRIMINANT `D = (l_y - 1)(l_z - 1) - p^2`, and the constant term is `-D`. -/
theorem det_pairSum_add_atom_sub_one (gy gz g : Fin 3 → ℝ) :
    (atomMatrix gy + atomMatrix gz + atomMatrix g - 1).det
      = -((leverageOf gy - 1) * (leverageOf gz - 1) - (gy ⬝ᵥ gz) ^ 2)
        + (1 - leverageOf gz) * (g ⬝ᵥ gy) ^ 2
        + (1 - leverageOf gy) * (g ⬝ᵥ gz) ^ 2
        + 2 * (gy ⬝ᵥ gz) * ((g ⬝ᵥ gy) * (g ⬝ᵥ gz))
        + ((leverageOf gy - 1) * (leverageOf gz - 1) - (gy ⬝ᵥ gz) ^ 2)
            * leverageOf g := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf_eq_dotProduct, dotProduct, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-! ## 2. The anchored pair -/

/-- The anchor equation resolves the null direction inside the pair. -/
theorem pairAnchor_resolve {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w) :
    (gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz = w := by
  have h : (atomMatrix gy + atomMatrix gz) *ᵥ w
      = (gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz := by
    rw [Matrix.add_mulVec,
      show atomMatrix gy *ᵥ w = (gy ⬝ᵥ w) • gy from vecMulVec_mulVec_eq _ _ _,
      show atomMatrix gz *ᵥ w = (gz ⬝ᵥ w) • gz from vecMulVec_mulVec_eq _ _ _]
  rw [← h]
  exact hanchor

/-- The first reading relation of an anchored pair. -/
theorem pairAnchor_relation_left {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w) :
    leverageOf gy * (gy ⬝ᵥ w) + (gy ⬝ᵥ gz) * (gz ⬝ᵥ w) = gy ⬝ᵥ w := by
  have h : gy ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = gy ⬝ᵥ w := by
    rw [pairAnchor_resolve hanchor]
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul] at h
  rw [leverageOf_eq_dotProduct]
  linear_combination h

/-- The second reading relation of an anchored pair. -/
theorem pairAnchor_relation_right {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w) :
    (gy ⬝ᵥ gz) * (gy ⬝ᵥ w) + leverageOf gz * (gz ⬝ᵥ w) = gz ⬝ᵥ w := by
  have h : gz ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = gz ⬝ᵥ w := by
    rw [pairAnchor_resolve hanchor]
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm gz gy] at h
  rw [leverageOf_eq_dotProduct]
  linear_combination h

/-- The readings of an anchored unit direction have unit square sum. -/
theorem pairAnchor_readings_sq_sum {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (gy ⬝ᵥ w) ^ 2 + (gz ⬝ᵥ w) ^ 2 = 1 := by
  have h : w ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = w ⬝ᵥ w := by
    rw [pairAnchor_resolve hanchor]
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm w gy, dotProduct_comm w gz, hunit] at h
  linear_combination h

/-- **THE ANCHORED PAIR IS SINGULAR.**  A pair that fixes a unit direction
sits exactly on the discriminant: `(l_y - 1)(l_z - 1) = <g_y,g_z>^2`.
Equivalently its wedge is `l_y + l_z - 1`: the pair gap `S_{yz} - 1` is a
singular matrix, and one of its eigenvalues is pinned at zero. -/
theorem pairAnchor_wedge_eq {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (leverageOf gy - 1) * (leverageOf gz - 1) - (gy ⬝ᵥ gz) ^ 2 = 0 := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  linear_combination
    ((gy ⬝ᵥ w) * (leverageOf gz - 1) - (gz ⬝ᵥ w) * (gy ⬝ᵥ gz)) * h1
    + ((gz ⬝ᵥ w) * (leverageOf gy - 1) - (gy ⬝ᵥ w) * (gy ⬝ᵥ gz)) * h2
    - ((leverageOf gy - 1) * (leverageOf gz - 1) - (gy ⬝ᵥ gz) ^ 2) * h3

/-- **THE ANCHORED DETERMINANT LAW.**  At a pair that fixes the unit
direction `w`, the gap determinant of the pair enlarged by ANY atom is a pure
square in that atom's reading:

  `det(g_yg_y' + g_zg_z' + gg' - 1) = -(l_y + l_z - 2)·(g . w)^2` .

The pair's leverage excess is the whole price, and the probe enters only
through its null reading.  Inverse-free, spectrum-free, every rank three. -/
theorem pairAnchor_det_update (gy gz g w : Fin 3 → ℝ)
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (atomMatrix gy + atomMatrix gz + atomMatrix g - 1).det
      = -(leverageOf gy + leverageOf gz - 2) * (g ⬝ᵥ w) ^ 2 := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  have hD := pairAnchor_wedge_eq hanchor hunit
  have hgw : g ⬝ᵥ w = (gy ⬝ᵥ w) * (g ⬝ᵥ gy) + (gz ⬝ᵥ w) * (g ⬝ᵥ gz) := by
    have h : g ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = g ⬝ᵥ w := by
      rw [pairAnchor_resolve hanchor]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul] at h
    linear_combination -h
  rw [det_pairSum_add_atom_sub_one, hgw]
  linear_combination
    (leverageOf g - 1) * hD
    + ((g ⬝ᵥ gy) ^ 2 * (gy ⬝ᵥ w) - (g ⬝ᵥ gz) ^ 2 * (gy ⬝ᵥ w)
        + 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gz ⬝ᵥ w)) * h1
    + (-((g ⬝ᵥ gy) ^ 2 * (gz ⬝ᵥ w)) + (g ⬝ᵥ gz) ^ 2 * (gz ⬝ᵥ w)
        + 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gy ⬝ᵥ w)) * h2
    + ((g ⬝ᵥ gy) ^ 2 * (leverageOf gz - 1) + (g ⬝ᵥ gz) ^ 2 * (leverageOf gy - 1)
        - 2 * (g ⬝ᵥ gy) * (g ⬝ᵥ gz) * (gy ⬝ᵥ gz)) * h3

/-- **THE SIGN LAW.**  Once an anchored pair carries leverage two, no atom
can complete it to a strict dominator: the enlarged gap has nonpositive
determinant, and a positive definite matrix has positive determinant. -/
theorem not_posDef_of_pairAnchor_add_atom (gy gz g w : Fin 3 → ℝ)
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1)
    (hlev : 2 ≤ leverageOf gy + leverageOf gz) :
    ¬ (atomMatrix gy + atomMatrix gz + atomMatrix g - 1).PosDef := by
  intro hpd
  have hpos := hpd.det_pos
  rw [pairAnchor_det_update gy gz g w hanchor hunit] at hpos
  nlinarith [sq_nonneg (g ⬝ᵥ w), hlev]

/-! ## 3. The second invariant of the anchored triple -/

/-- The unconditional second-invariant expansion of a three-atom gap. -/
theorem e2_tripleSum_sub_one (gx gy gz : Fin 3 → ℝ) :
    (((Matrix.trace (atomMatrix gy + atomMatrix gz + atomMatrix gx - 1)) ^ 2
        - Matrix.trace ((atomMatrix gy + atomMatrix gz + atomMatrix gx - 1)
          * (atomMatrix gy + atomMatrix gz + atomMatrix gx - 1))) / 2)
      = (leverageOf gy + leverageOf gz - 2) * (leverageOf gx - 1)
        - ((gx ⬝ᵥ gy) ^ 2 + (gx ⬝ᵥ gz) ^ 2)
        + ((leverageOf gy - 1) * (leverageOf gz - 1) - (gy ⬝ᵥ gz) ^ 2) := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.one_apply, atomMatrix, Matrix.vecMulVec_apply,
    leverageOf_eq_dotProduct, dotProduct, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- **THE `K1` PRICE.**  At an anchored pair the second invariant of the
enlarged gap is the leverage excess of the pair times the leverage excess of
the third atom, minus the two cross pairings. -/
theorem pairAnchor_e2_price {gx gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (((Matrix.trace (atomMatrix gy + atomMatrix gz + atomMatrix gx - 1)) ^ 2
        - Matrix.trace ((atomMatrix gy + atomMatrix gz + atomMatrix gx - 1)
          * (atomMatrix gy + atomMatrix gz + atomMatrix gx - 1))) / 2)
      = (leverageOf gy + leverageOf gz - 2) * (leverageOf gx - 1)
        - ((gx ⬝ᵥ gy) ^ 2 + (gx ⬝ᵥ gz) ^ 2) := by
  rw [e2_tripleSum_sub_one, pairAnchor_wedge_eq hanchor hunit, add_zero]

/-- **THE LEVERAGE FLOOR OF AN ANCHORED PAIR.**  If the enlarged gap is
positive semidefinite and the third atom carries leverage above one, the pair
carries leverage two.  Positive semidefiniteness enters once, through the
nonnegativity of the second invariant. -/
theorem two_le_leverageSum_of_pairAnchor {gx gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1)
    (hpsd : (atomMatrix gy + atomMatrix gz + atomMatrix gx - 1).PosSemidef)
    (hlx : 1 < leverageOf gx) :
    2 ≤ leverageOf gy + leverageOf gz := by
  have he2 := e2_nonneg_of_posSemidef hpsd
  rw [pairAnchor_e2_price hanchor hunit] at he2
  nlinarith [sq_nonneg (gx ⬝ᵥ gy), sq_nonneg (gx ⬝ᵥ gz), he2, hlx]

/-! ## 4. The stratum at a corank-one dominator -/

variable {m : ℕ}

/-- **THE `K1` ANCHOR.**  At a weak dominator whose gap kills `w`, a zero
reading at one inside atom hands the null direction to the other two: the
PAIR fixes `w` on its own. -/
theorem kOne_pairAnchor (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w) = 0)
    (hax : D.atom x ⬝ᵥ w = 0) :
    (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w := by
  classical
  have hres := dominator_resolves_nullDir D hdominates hnull
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton, hax, zero_smul, zero_add] at hres
  rw [Matrix.add_mulVec,
    show atomMatrix (D.atom y) *ᵥ w = (D.atom y ⬝ᵥ w) • D.atom y from
      vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom z) *ᵥ w = (D.atom z ⬝ᵥ w) • D.atom z from
      vecMulVec_mulVec_eq _ _ _]
  exact hres

/-- **THE ZERO-READING ATOM IS STRICTLY HEAVY.**  In `K1` the atom whose
reading vanishes carries leverage strictly above one: leverage one would make
it the null direction itself, whose reading is one. -/
theorem kOne_leverage_gt_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    1 < leverageOf (D.atom x) := by
  rcases lt_or_eq_of_le
    (one_le_leverage_of_mem_dominating_triple D hxy hxz hyz hdominates) with h | h
  · exact h
  · exfalso
    rcases eq_nullDir_of_leverage_eq_one D hxy hxz hyz hdominates hline hunit h.symm
      with hpos | hneg
    · rw [hpos, hunit] at hax; exact one_ne_zero hax
    · rw [hneg, neg_dotProduct, hunit] at hax
      exact one_ne_zero (neg_eq_zero.mp hax)

/-- **THE `K1` LEVERAGE FLOOR.**  The two live atoms of a `K1` dominator
carry leverage two between them. -/
theorem kOne_two_le_leverageSum (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    2 ≤ leverageOf (D.atom y) + leverageOf (D.atom z) := by
  classical
  have hanchor := kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom y) + atomMatrix (D.atom z) + atomMatrix (D.atom x) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  refine two_le_leverageSum_of_pairAnchor hanchor hunit ?_
    (kOne_leverage_gt_one D hxy hxz hyz hdominates hline hunit hax)
  rw [← hsum]
  exact hdominates

/-- **THE FREE REFUSAL BUDGET OF `K1`.**  At a `K1` corank-one dominator the
two live atoms together with ANY sixth atom fail to dominate strictly.  No
tie hypothesis: the pair anchor and its leverage floor do all the work, so
every triple through the live pair is discharged before the fight starts. -/
theorem kOne_not_posDef_pairTriple (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (d : Fin m) (hdy : d ≠ y) (hdz : d ≠ z) :
    ¬ (subsetSum D ({y, z, d} : Finset (Fin m)) - 1).PosDef := by
  classical
  have hsum : subsetSum D ({y, z, d} : Finset (Fin m))
      = atomMatrix (D.atom y) + atomMatrix (D.atom z) + atomMatrix (D.atom d) := by
    rw [subsetSum, Finset.sum_insert (by simp [hyz, hdy.symm]),
      Finset.sum_insert (by simp [hdz.symm]), Finset.sum_singleton]
    abel
  rw [hsum]
  exact not_posDef_of_pairAnchor_add_atom _ _ _ w
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) hunit
    (kOne_two_le_leverageSum D hxy hxz hyz hdominates hline hunit hax)

/-- **THE `K1` GAP DETERMINANT, EXPLICIT.**  Every triple through the live
pair reads its gap determinant off the sixth atom's null reading alone. -/
theorem kOne_pairTriple_det (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ}
    (hnull : w ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w) = 0)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (d : Fin m) (hdy : d ≠ y) (hdz : d ≠ z) :
    (subsetSum D ({y, z, d} : Finset (Fin m)) - 1).det
      = -(leverageOf (D.atom y) + leverageOf (D.atom z) - 2)
          * (D.atom d ⬝ᵥ w) ^ 2 := by
  classical
  have hsum : subsetSum D ({y, z, d} : Finset (Fin m))
      = atomMatrix (D.atom y) + atomMatrix (D.atom z) + atomMatrix (D.atom d) := by
    rw [subsetSum, Finset.sum_insert (by simp [hyz, hdy.symm]),
      Finset.sum_insert (by simp [hdz.symm]), Finset.sum_singleton]
    abel
  rw [hsum]
  exact pairAnchor_det_update _ _ _ w
    (kOne_pairAnchor D hxy hxz hyz hdominates hnull hax) hunit

/-! ## 5. The live pair in the tax currencies -/

/-- **THE ANCHORED WEDGE.**  The squared area of an anchored pair is its
leverage sum minus one.  The pair wedge is one of the two currencies the
wedge-bracket tax prices, and at an anchor it is pinned by the leverages
alone: no angle survives. -/
theorem pairAnchor_wedge_value {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    leverageOf gy * leverageOf gz - (gy ⬝ᵥ gz) ^ 2
      = leverageOf gy + leverageOf gz - 1 := by
  linear_combination pairAnchor_wedge_eq hanchor hunit

/-- **THE LIVE PAIR OF A `K1` DOMINATOR CARRIES WEDGE AT LEAST ONE.**  The
leverage floor turns the anchored wedge into a hard floor in the currency of
`Gtz.wedge_mass_budget`, whose total over all fifteen pairs is fixed.  A `K1`
dominator therefore spends a definite share of the design's whole wedge
budget on its own live pair. -/
theorem kOne_one_le_pairWedge (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    1 ≤ leverageOf (D.atom y) * leverageOf (D.atom z)
        - (D.atom y ⬝ᵥ D.atom z) ^ 2 := by
  have hanchor := kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax
  rw [pairAnchor_wedge_value hanchor hunit]
  have := kOne_two_le_leverageSum D hxy hxz hyz hdominates hline hunit hax
  linarith

/-! ## 6. The refusal budget of the stratum -/

/-- **THE `K1` REFUSAL BUDGET.**  At a `K1` corank-one dominator a tie is
exactly the refusal of the triples that MISS the live pair.  Every triple
through both live atoms is discharged by the sign law before the fight
starts, so at `(6,3)` sixteen of the twenty conditions carry the whole
stratum.  This is the `K1` analogue of the `Z1` erase-anchor equivalence and
of the two-zero budget, and it loses nothing: the reverse direction is the
definition. -/
theorem kOne_isTie_iff_avoidingRefusals (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    IsTie D ↔ ∀ T : Finset (Fin m), T.card = 3 → ¬ (y ∈ T ∧ z ∈ T) →
      ¬ (subsetSum D T - 1).PosDef := by
  classical
  constructor
  · intro htie T hT _
    exact htie.2 T hT
  · intro href
    have hcardC : ({x, y, z} : Finset (Fin m)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    refine ⟨⟨({x, y, z} : Finset (Fin m)), hcardC, hdominates⟩, fun T hT => ?_⟩
    by_cases hyzT : y ∈ T ∧ z ∈ T
    · obtain ⟨hyT, hzT⟩ := hyzT
      have hzmem : z ∈ T.erase y := Finset.mem_erase.mpr ⟨hyz.symm, hzT⟩
      have hcard1 : ((T.erase y).erase z).card = 1 := by
        rw [Finset.card_erase_of_mem hzmem, Finset.card_erase_of_mem hyT, hT]
      obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hcard1
      have hdmem : d ∈ (T.erase y).erase z := by rw [hd]; exact Finset.mem_singleton_self d
      have hdz : d ≠ z := (Finset.mem_erase.mp hdmem).1
      have hdy : d ≠ y := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hdmem)).1
      have hTeq : T = ({y, z, d} : Finset (Fin m)) := by
        rw [← Finset.insert_erase hyT, ← Finset.insert_erase hzmem, hd]
      rw [hTeq]
      exact kOne_not_posDef_pairTriple D hxy hxz hyz hdominates hline hunit hax
        d hdy hdz
    · exact href T hT hyzT

/-! ## 7. The transverse energy and the weight cap -/

/-- Parseval read at a probe: the weighted squared readings total the probe's
own square. -/
theorem parseval_probe_form (D : WeightedDesign m 3) (probe : Fin 3 → ℝ) :
    ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 = probe ⬝ᵥ probe := by
  have hstep : ∀ c : Fin m,
      D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
        = probe ⬝ᵥ ((D.weight c • atomMatrix (D.atom c)) *ᵥ probe) := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      show atomMatrix (D.atom c) *ᵥ probe = (D.atom c ⬝ᵥ probe) • D.atom c from
        vecMulVec_mulVec_eq _ _ _, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probe (D.atom c)]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hstep c), ← dotProduct_sum,
    ← Matrix.sum_mulVec, D.isParseval, Matrix.one_mulVec]

/-- **THE TRANSVERSE ENERGY OF AN ANCHORED PAIR.**  Strip the null direction
off the first live atom.  The pair reads the surviving transverse probe with
energy exactly its leverage excess times the probe's own square: the pair
acts on the plane it spans as one eigenvalue, and that eigenvalue is
`l_y + l_z - 1`.  The anchored spectral content, carried without any
spectral decomposition. -/
theorem pairAnchor_transverse_energy {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    (leverageOf gy - (gy ⬝ᵥ w) ^ 2) ^ 2
        + ((gy ⬝ᵥ gz) - (gy ⬝ᵥ w) * (gz ⬝ᵥ w)) ^ 2
      = (leverageOf gy + leverageOf gz - 1)
          * (leverageOf gy - (gy ⬝ᵥ w) ^ 2) := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  linear_combination
    (-(gy ⬝ᵥ w) * leverageOf gz + (gz ⬝ᵥ w) * (gy ⬝ᵥ gz)) * h1
    + ((gy ⬝ᵥ w) * (gy ⬝ᵥ gz) - (gz ⬝ᵥ w) * leverageOf gy) * h2
    + ((gy ⬝ᵥ w) ^ 2 + leverageOf gy * leverageOf gz - leverageOf gy
        - (gy ⬝ᵥ gz) ^ 2) * h3

/-- **THE WEIGHT CAP OF THE LIVE PAIR.**  Parseval, read at the transverse
probe of the live pair, caps the pair's leverage excess by the reciprocal of
the smaller live weight:

  `min(t_y, t_z)·(l_y + l_z - 1) <= 1` .

The pair carries a definite transverse energy, and the design has only one
unit of Parseval mass in that direction to pay with.  A weight-carrying law
of the stratum: the leverage floor `2 <= l_y + l_z` pushes up, this pushes
down, and the two meet on the weights. -/
theorem kOne_pair_weight_cap (D : WeightedDesign m 3)
    {y z : Fin m} (hyz : y ≠ z)
    {w : Fin 3 → ℝ}
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1)
    (hP : 0 < leverageOf (D.atom y) - (D.atom y ⬝ᵥ w) ^ 2) :
    min (D.weight y) (D.weight z)
        * (leverageOf (D.atom y) + leverageOf (D.atom z) - 1) ≤ 1 := by
  classical
  set P : ℝ := leverageOf (D.atom y) - (D.atom y ⬝ᵥ w) ^ 2 with hPdef
  set probe : Fin 3 → ℝ := D.atom y - (D.atom y ⬝ᵥ w) • w with hprobe
  have hyp : D.atom y ⬝ᵥ probe = P := by
    rw [hprobe, dotProduct_sub, dotProduct_smul, smul_eq_mul, hPdef,
      leverageOf_eq_dotProduct]
    ring
  have hzp : D.atom z ⬝ᵥ probe = (D.atom y ⬝ᵥ D.atom z)
      - (D.atom y ⬝ᵥ w) * (D.atom z ⬝ᵥ w) := by
    rw [hprobe, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (D.atom z) (D.atom y)]
  have hpp : probe ⬝ᵥ probe = P := by
    rw [hprobe, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      hunit, smul_eq_mul, smul_eq_mul, smul_eq_mul, hPdef,
      leverageOf_eq_dotProduct, dotProduct_comm w (D.atom y)]
    ring
  have hpar := parseval_probe_form D probe
  rw [hpp] at hpar
  have hpair : D.weight y * (D.atom y ⬝ᵥ probe) ^ 2
      + D.weight z * (D.atom z ⬝ᵥ probe) ^ 2 ≤ P := by
    rw [← hpar]
    have hstep : ∑ c ∈ ({y, z} : Finset (Fin m)),
          D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
        ≤ ∑ c, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c _ _ => mul_nonneg (D.weight_pos c).le (sq_nonneg _))
    rwa [Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hstep
  have hten := pairAnchor_transverse_energy hanchor hunit
  rw [hyp, hzp] at hpair
  have hmy : min (D.weight y) (D.weight z) ≤ D.weight y := min_le_left _ _
  have hmz : min (D.weight y) (D.weight z) ≤ D.weight z := min_le_right _ _
  have hkey : min (D.weight y) (D.weight z)
      * ((leverageOf (D.atom y) + leverageOf (D.atom z) - 1) * P) ≤ P := by
    calc min (D.weight y) (D.weight z)
          * ((leverageOf (D.atom y) + leverageOf (D.atom z) - 1) * P)
        = min (D.weight y) (D.weight z)
            * (P ^ 2 + ((D.atom y ⬝ᵥ D.atom z)
              - (D.atom y ⬝ᵥ w) * (D.atom z ⬝ᵥ w)) ^ 2) := by
          rw [← hten]
      _ ≤ D.weight y * P ^ 2
            + D.weight z * ((D.atom y ⬝ᵥ D.atom z)
              - (D.atom y ⬝ᵥ w) * (D.atom z ⬝ᵥ w)) ^ 2 := by
          nlinarith [sq_nonneg P, sq_nonneg ((D.atom y ⬝ᵥ D.atom z)
            - (D.atom y ⬝ᵥ w) * (D.atom z ⬝ᵥ w)), hmy, hmz]
      _ ≤ P := hpair
  nlinarith [hkey, hP]

end Gtz
