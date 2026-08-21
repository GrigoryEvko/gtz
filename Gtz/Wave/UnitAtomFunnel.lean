/-
# The unit atom funnel: the boundary of the leverage floor is rigid

`Gtz.leverage_one_le_of_isTie` proves every atom of a tie is heavy, and the
ledger names its boundary honestly: at leverage exactly one the deflated
complement is singular, the transport yields weak domination, and "the residue
it names is a BOUNDARY, not an oversight".  This module crosses that boundary.
The same deflated gap bound that proves the floor also pins the boundary
completely:

  **a tie with a unit atom carries a weak dominator that avoids the atom and
  REPRODUCES it** (`Gtz.unitAtom_exists_dominator_fixing`):

  `S_T *ᵥ g_a = g_a` ,  so  `Σ_{c ∈ T} (g_c·g_a)·g_c = g_a`  and
  `Σ_{c ∈ T} (g_c·g_a)² = 1` .

The unit atom is an exact unit eigenvector of a dominating triple it does not
belong to, and the triple's readings of the atom resolve its full length.

## The mechanism

At `ℓ_a = 1` the complement `1 − g_ag_aᵀ` is the orthogonal projection off the
atom, so the landed bound `(1−t_a)(S_T − 1) ⪰ t_a(1 − g_ag_aᵀ)` says the gap of
the selected triple dominates a projection.  Domination of `1` follows at once.
A tie then forbids strictness, so the gap has a null direction; the bound
forces every null direction onto the atom's line, and the null equation IS the
reproduction.

## What the reproduction buys

The null probe of this dominator is not an abstract direction — it is an atom
of the design, of unit length, outside the dominator.  The corank strata of
this probe collapse early:

* **Two zero readings give a parallel pair outright**
  (`Gtz.unitAtom_parallel_of_two_readings_zero`): the reproduction collapses to
  `(g_c·g_a)·g_c = g_a`, a hinge witness with no chart, no corner, and no
  certificate.  The K2 pattern of this probe is not a fight.
* The readings cannot all vanish: they resolve one
  (`Gtz.unitAtom_readings_resolve`).

Combined with the landed dichotomy, every `(6,3)` tie is all-heavy or funnels
(`Gtz.isTie_sixThree_allHeavy_or_funnel`), unconditionally: the third branch of
the trichotomy now carries an exact eigen-structure instead of a bare boundary
equation.
-/
import Gtz.Design.StratumEmptinessLedger
import Gtz.Wave.PairMinorBudget
import Gtz.Wave.CorankOneExchange
import Gtz.Design.PrimitiveTightClassification
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Reduction.SplitTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. The unit complement is a projection -/

/-- At unit leverage the atom's complement is positive semidefinite: the form is
the squared distance to the atom's line. -/
theorem posSemidef_one_sub_atomMatrix_of_unit {a : Fin 3 → ℝ}
    (hunit : leverageOf a = 1) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix a).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun v => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.one_apply,
      atomMatrix, Matrix.vecMulVec_apply, star_trivial]
    rcases eq_or_ne i j with h | h
    · subst h; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  · have hform : v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix a) *ᵥ v)
        = v ⬝ᵥ v - (a ⬝ᵥ v) ^ 2 := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
        vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
        dotProduct_comm v a]
      ring
    have hcs : (a ⬝ᵥ v) ^ 2 ≤ v ⬝ᵥ v := by
      have hlag := bracketNormal_lagrange a v v
      have hnn : 0 ≤ bracketNormal a v ⬝ᵥ bracketNormal a v :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hself : a ⬝ᵥ a = 1 := by
        rw [dotProduct_self_eq_leverage, hunit]
      rw [hlag, hself, one_mul] at hnn
      nlinarith [hnn]
    rw [star_trivial, hform]
    linarith

/-- A vanishing complement form at unit leverage puts the vector on the atom's
line: the Cauchy–Schwarz equality case, through the Lagrange identity. -/
theorem eq_smul_of_unit_complement_form_zero {a v : Fin 3 → ℝ}
    (hunit : leverageOf a = 1)
    (hzero : v ⬝ᵥ v - (a ⬝ᵥ v) ^ 2 = 0) :
    v = (a ⬝ᵥ v) • a := by
  have hself : a ⬝ᵥ a = 1 := by
    rw [dotProduct_self_eq_leverage, hunit]
  have hlag := bracketNormal_lagrange a v v
  rw [hself, one_mul] at hlag
  have hnormal : bracketNormal a v ⬝ᵥ bracketNormal a v = 0 := by
    rw [hlag]; nlinarith [hzero]
  have hzero' : bracketNormal a v = 0 := dotProduct_self_eq_zero.mp hnormal
  have hkey := smul_dotProduct_self_eq_of_bracketNormal_eq_zero a v hzero'
  rw [hself, one_smul] at hkey
  exact hkey

/-! ## 2. The funnel -/

/-- **THE UNIT ATOM FUNNEL.**  A tie with a unit atom has a weak dominator that
avoids the atom and reproduces it: the deflated gap bound dominates the atom's
orthogonal projection, so the selected triple dominates, and the tie's refusal
of strictness forces the atom itself into the gap's kernel. -/
theorem unitAtom_exists_dominator_fixing (D : WeightedDesign (m + 1) 3)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m 3) (htie : IsTie D)
    (a : Fin (m + 1)) (hunit : leverageOf (D.atom a) = 1) :
    ∃ T : Finset (Fin (m + 1)), T.card = 3 ∧ a ∉ T ∧ Dominates D T ∧
      subsetSum D T *ᵥ D.atom a = D.atom a := by
  have hweightPos := D.weight_pos a
  have hweightLtOne : D.weight a < 1 := weight_lt_one D (by omega) a
  have hmass : (0 : ℝ) < 1 - D.weight a := by linarith
  have hshare : D.weight a * leverageOf (D.atom a) < 1 := by
    rw [hunit]; linarith
  obtain ⟨T, hcard, havoid, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller a hshare
  have hproj := posSemidef_one_sub_atomMatrix_of_unit hunit
  -- domination: the scaled gap is the bound plus a PSD complement
  have hgapScaled : (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)).PosSemidef := by
    have hsplit : ((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
        = (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
            - D.weight a • (1 - atomMatrix (D.atom a)))
          + D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix (D.atom a)) := by
      module
    rw [hsplit]
    exact hbound.add (hproj.smul hweightPos.le)
  have hgap : (subsetSum D T - 1).PosSemidef := by
    have hunscale : subsetSum D T - 1
        = (((1 : ℝ) - D.weight a)⁻¹) • (((1 : ℝ) - D.weight a) • (subsetSum D T - 1)) := by
      rw [smul_smul, inv_mul_cancel₀ hmass.ne', one_smul]
    rw [hunscale]
    exact hgapScaled.smul (inv_pos.mpr hmass).le
  refine ⟨T, hcard, havoid, hgap, ?_⟩
  -- the tie forbids strictness: extract a null form direction
  have hnotPD : ¬ (subsetSum D T - 1).PosDef := htie.2 T hcard
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hnotPD
  push Not at hnotPD
  obtain ⟨v, hvne, hvle⟩ := hnotPD hgap.1
  rw [star_trivial] at hvle
  have hvge : 0 ≤ v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgap).2 v
    rwa [star_trivial] at h
  have hvzero : v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v) = 0 := le_antisymm hvle hvge
  -- the bound splits the zero form; the complement part must vanish
  have hboundForm : 0 ≤ v ⬝ᵥ ((((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
      - D.weight a • (1 - atomMatrix (D.atom a))) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 v
    rwa [star_trivial] at h
  have hprojForm : 0 ≤ v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - atomMatrix (D.atom a)) *ᵥ v) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hproj).2 v
    rwa [star_trivial] at h
  have hsplitForm : v ⬝ᵥ ((((1 : ℝ) - D.weight a) • (subsetSum D T - 1)
        - D.weight a • (1 - atomMatrix (D.atom a))) *ᵥ v)
      = ((1 : ℝ) - D.weight a) * (v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v))
        - D.weight a * (v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix (D.atom a)) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hsplitForm, hvzero, mul_zero, zero_sub] at hboundForm
  have hcompZero : v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - atomMatrix (D.atom a)) *ᵥ v) = 0 := by
    nlinarith [hboundForm, hprojForm, hweightPos]
  -- the vanishing complement puts v on the atom's line
  have hcompForm : v ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ)
        - atomMatrix (D.atom a)) *ᵥ v)
      = v ⬝ᵥ v - (D.atom a ⬝ᵥ v) ^ 2 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm v (D.atom a)]
    ring
  have honline : v = (D.atom a ⬝ᵥ v) • D.atom a :=
    eq_smul_of_unit_complement_form_zero hunit (by rw [← hcompForm]; exact hcompZero)
  have hread : D.atom a ⬝ᵥ v ≠ 0 := by
    intro hzero
    apply hvne
    rw [honline, hzero, zero_smul]
  -- the atom's own form vanishes, so the gap annihilates the atom
  have hatomForm : D.atom a ⬝ᵥ ((subsetSum D T - 1) *ᵥ D.atom a) = 0 := by
    have hexpand : v ⬝ᵥ ((subsetSum D T - 1) *ᵥ v)
        = (D.atom a ⬝ᵥ v) ^ 2
          * (D.atom a ⬝ᵥ ((subsetSum D T - 1) *ᵥ D.atom a)) := by
      conv_lhs => rw [honline]
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      ring
    have := hvzero
    rw [hexpand] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hread
    · exact h
  have hsym : (subsetSum D T - 1)ᵀ = subsetSum D T - 1 := hgap.1
  have hkill := mulVec_eq_zero_of_form_eq_zero hgap hsym hatomForm
  have hfinal : subsetSum D T *ᵥ D.atom a - D.atom a = 0 := by
    have h : (subsetSum D T - 1) *ᵥ D.atom a
        = subsetSum D T *ᵥ D.atom a - D.atom a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [← h]; exact hkill
  funext i
  have := congrFun hfinal i
  simp only [Pi.sub_apply, Pi.zero_apply] at this
  linarith

/-! ## 3. The reproduction and the readings -/

/-- **THE REPRODUCTION.**  The dominator's atoms rebuild the unit atom with its
own readings as the coefficients. -/
theorem unitAtom_reproduction (D : WeightedDesign (m + 1) 3)
    {T : Finset (Fin (m + 1))} {a : Fin (m + 1)}
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a) :
    ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) • D.atom c = D.atom a := by
  have hexpand : subsetSum D T *ᵥ D.atom a
      = ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) • D.atom c := by
    rw [subsetSum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun c _ => by
      rw [atomMatrix, vecMulVec_mulVec_eq]
  rw [← hexpand]; exact hfix

/-- **THE READINGS RESOLVE ONE.**  The dominator's squared readings of the unit
atom total the atom's own length. -/
theorem unitAtom_readings_resolve (D : WeightedDesign (m + 1) 3)
    {T : Finset (Fin (m + 1))} {a : Fin (m + 1)}
    (hunit : leverageOf (D.atom a) = 1)
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a) :
    ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) ^ 2 = 1 := by
  have hrep := unitAtom_reproduction D hfix
  have hread := congrArg (fun w => D.atom a ⬝ᵥ w) hrep
  simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul] at hread
  rw [dotProduct_self_eq_leverage, hunit] at hread
  rw [← hread]
  exact Finset.sum_congr rfl fun c _ => by
    rw [dotProduct_comm (D.atom c) (D.atom a)]; ring

/-! ## 4. The K2 pattern of this probe is a hinge witness -/

/-- **TWO ZERO READINGS GIVE A PARALLEL PAIR.**  If the unit atom reads only one
member of its dominator, the reproduction collapses to a single term and the
atom is a multiple of that member — a hinge witness, with no chart and no
certificate.  The K2 stratum of this null probe is not a fight. -/
theorem unitAtom_parallel_of_two_readings_zero (D : WeightedDesign (m + 1) 3)
    {T : Finset (Fin (m + 1))} {a c₀ : Fin (m + 1)}
    (havoid : a ∉ T) (hmem : c₀ ∈ T)
    (hfix : subsetSum D T *ᵥ D.atom a = D.atom a)
    (hzeros : ∀ c ∈ T, c ≠ c₀ → D.atom c ⬝ᵥ D.atom a = 0) :
    HasParallelPair D := by
  have hrep := unitAtom_reproduction D hfix
  have hcollapse : ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) • D.atom c
      = (D.atom c₀ ⬝ᵥ D.atom a) • D.atom c₀ := by
    refine Finset.sum_eq_single_of_mem c₀ hmem fun c hc hne => ?_
    rw [hzeros c hc hne, zero_smul]
  rw [hcollapse] at hrep
  refine ⟨c₀, a, D.atom c₀ ⬝ᵥ D.atom a, ?_, hrep.symm⟩
  intro heq
  exact havoid (heq ▸ hmem)

/-! ## 5. The funnel at six points, unconditionally -/

/-- **THE FUNNEL AT `(6,3)`.**  The smaller-size input is the landed
`GtzWeighted 5 3`, so no open instance is assumed. -/
theorem isTie_sixThree_unitAtom_funnel (D : WeightedDesign 6 3) (htie : IsTie D)
    (a : Fin 6) (hunit : leverageOf (D.atom a) = 1) :
    ∃ T : Finset (Fin 6), T.card = 3 ∧ a ∉ T ∧ Dominates D T ∧
      subsetSum D T *ᵥ D.atom a = D.atom a :=
  unitAtom_exists_dominator_fixing (m := 5) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie a hunit

/-- **EVERY `(6,3)` TIE IS ALL-HEAVY OR FUNNELS.**  The landed dichotomy's
boundary branch upgraded: the unit atom comes with a dominator avoiding it,
reproducing it, and reading its full length. -/
theorem isTie_sixThree_allHeavy_or_funnel (D : WeightedDesign 6 3)
    (htie : IsTie D) :
    AllHeavy D ∨ ∃ (a : Fin 6) (T : Finset (Fin 6)),
      leverageOf (D.atom a) = 1 ∧ T.card = 3 ∧ a ∉ T ∧ Dominates D T ∧
      subsetSum D T *ᵥ D.atom a = D.atom a ∧
      ∑ c ∈ T, (D.atom c ⬝ᵥ D.atom a) ^ 2 = 1 := by
  rcases allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree D htie with hheavy | ⟨a, hunit⟩
  · exact Or.inl hheavy
  · obtain ⟨T, hcard, havoid, hdom, hfix⟩ := isTie_sixThree_unitAtom_funnel D htie a hunit
    exact Or.inr ⟨a, T, hunit, hcard, havoid, hdom, hfix,
      unitAtom_readings_resolve D hunit hfix⟩

end Gtz
