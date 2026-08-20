/-
# The corank-one Gram mirror: the reading calculus, the leverage ladder, and
# the null census

A weak dominator `C` of a corank-one gap owns a null direction `w`, and the
landed resolve identity (`Gtz.dominator_resolves_nullDir`) reproduces `w`
through the inside readings `β_c = g_c ⬝ᵥ w`.  This module lands the mirror of
that identity on the Gram side and the case structure it induces on the arm.

## The reading calculus

`Gtz.nullDir_resolve_reading` reads the resolve identity at an arbitrary probe:

  `Σ_{c∈C} (g_c·w)(g_c·p) = w·p`  for every `p`.

At `p = g_e` this is the Gram eigenvector law
(`Gtz.insideGram_fixes_nullReadings`): the reading vector `β` is fixed by the
inside Gram, the corank-one sibling of the corner's
`Gtz.insideGram_of_rankOneGap`.  At unit `w` the landed
`Gtz.gapForm_eq_zero_iff_sum_sq` closes the circle: `Σ_C β_c² = 1`.

## The leverage ladder — where the two-zero stratum lives

* `Gtz.one_le_leverage_of_mem_dominating_triple` — every atom of a weakly
  dominating TRIPLE has leverage at least one.  No tie, no smaller-size GTZ
  input: the landed `Gtz.leverage_one_le_of_isTie_sixThree` prices all six
  atoms of a tie through `GtzWeighted 5 3`; this floor prices the three
  selected atoms of one dominator through nothing.  The probe is the common
  orthogonal of the other two atoms.
* `Gtz.inside_pair_orthogonal_of_leverage_eq_one` — at leverage exactly one
  the equality case rigidifies: the atom is orthogonal to its two partners.
* `Gtz.eq_nullDir_of_leverage_eq_one` — with a corank-one gap
  (`Gtz.GapNullLine`, unit null direction) a leverage-one inside atom IS the
  null direction up to sign.
* `Gtz.leverage_eq_one_of_nullReadings_zero` — the converse: two vanishing
  inside readings force the third atom onto the null line at leverage one.
* `Gtz.one_lt_leverage_of_nullReading_ne_zero` — off the two-zero stratum the
  floor is strict.

So the zero pattern of `β` stratifies the arm: the two-zero stratum is EXACTLY
"one inside atom is `±w`", which reproduces the `Z1` hypotheses (unit
leverage, orthogonal to its partners) with the null direction in the role of
the gap axis.  `Gtz.isTie_iff_avoidingRefusals_of_leverage_le_one` is the
transferred budget: the tie of a design with a leverage-one atom is exactly
the refusals of the triples that avoid it.

## The null census

At a null direction of `C` every one-atom exchange has an exact `w`-form
(`Gtz.swapGapForm_at_nullDir`):

  `wᵀ(S_{C−e+d} − 1)w = (g_d·w)² − (g_e·w)²` ,

so a swap whose incoming null reading does not beat the outgoing one is
refused with no tie hypothesis (`Gtz.not_posDef_swap_of_nullReading_sq_le`) —
the corank-one sibling of the corner's `Gtz.not_posDef_swap_of_rankOneGap`,
which is unconditional where this one bifurcates.  The complement carries the
same calculus (`Gtz.complGapForm_at_nullDir`): its `w`-form is the TOTAL
unweighted null mass minus twice the null norm, so a design whose null mass
stays at or below `2|w|²` refuses the complement for free
(`Gtz.not_posDef_compl_of_nullMass_le`).

## Calibration [MEASURED, scratchpad/corank1/fix.jl, exact rationals]

At the `(5,3)` diamond, dominator `{0,1,2}`: `β² = (3/4, 1/8, 1/8)`, all
nonzero, so the diamond sits in the ALL-NONZERO stratum and every kill of the
two-zero stratum is diamond-safe.  Outside null masses `(2, 2)`: every swap
has `(g_d·w)² = 2 > β_e²`, so the census refuses NOTHING there — the diamond's
refusals are all plane refusals, as they must be.  At the `(6,3)` split
diamond the same table extends by the copy at `β² = 3/4`; the copy-for-spine
swap has `w`-form `0` (it IS another weak dominator) and the complement has
`w`-form `15/4`.  The census is empty at both fixtures: its content is the
stratification, not the fixtures' refusals.
-/
import Gtz.Wave.CorankOneExchange
import Gtz.Wave.CorankOneAssembly
import Gtz.Design.SelectorEquivalences
import Gtz.Design.TightAntecedentMining
import Gtz.Design.LeverageBound
import Gtz.Reduction.ExchangeInvariant
import Gtz.LinAlg.PsdKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The reading calculus -/

/-- **The resolve identity, read at a probe.**  The null readings of the
dominator couple every probe's inside readings to the probe's null component. -/
theorem nullDir_resolve_reading (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    (probe : Fin 3 → ℝ) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ nullDir) * (D.atom c ⬝ᵥ probe) = nullDir ⬝ᵥ probe := by
  have hdot := congrArg (fun v => v ⬝ᵥ probe)
    (dominator_resolves_nullDir D hdominates hnull)
  simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul] using hdot

/-- **The inside Gram fixes the null readings.**  Read at an atom, the resolve
identity is the eigenvector law `H β = β` of the label Gram at eigenvalue one —
the corank-one mirror of the corner's `Gtz.insideGram_of_rankOneGap`. -/
theorem insideGram_fixes_nullReadings (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hdominates : Dominates D C) {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) (e : Fin m) :
    ∑ c ∈ C, (D.atom c ⬝ᵥ nullDir) * (D.atom c ⬝ᵥ D.atom e)
      = D.atom e ⬝ᵥ nullDir := by
  rw [nullDir_resolve_reading D hdominates hnull (D.atom e), dotProduct_comm]

/-! ## 2. The leverage ladder -/

/-- **The inside leverage floor.**  Every atom of a weakly dominating triple has
leverage at least one.  The probe is the common orthogonal of the other two
atoms: the gap form there reads `(g_x·p)² − |p|² ≥ 0`, and the square expansion
of `(g_x·p)·g_x − p` converts that excess into the leverage floor.  No tie and
no lower-size input — contrast `Gtz.leverage_one_le_of_isTie_sixThree`, which
prices all atoms of a tie through `GtzWeighted 5 3`. -/
theorem one_le_leverage_of_mem_dominating_triple (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m))) :
    1 ≤ leverageOf (D.atom x) := by
  obtain ⟨probe, hne, hy0, hz0⟩ :=
    exists_commonOrthogonal_of_pair (D.atom y) (D.atom z)
  have hpsd : 0 ≤ probe ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at h
  rw [dominationGap_form,
    sum_over_triple (fun c => (D.atom c ⬝ᵥ probe) ^ 2) hxy hxz hyz, hy0, hz0] at hpsd
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  have hqq : 0 ≤ ((D.atom x ⬝ᵥ probe) • D.atom x - probe) ⬝ᵥ
      ((D.atom x ⬝ᵥ probe) • D.atom x - probe) := dotProduct_self_nonneg _
  have hexp : ((D.atom x ⬝ᵥ probe) • D.atom x - probe) ⬝ᵥ
      ((D.atom x ⬝ᵥ probe) • D.atom x - probe)
      = (D.atom x ⬝ᵥ probe) ^ 2 * leverageOf (D.atom x)
        - 2 * (D.atom x ⬝ᵥ probe) ^ 2 + probe ⬝ᵥ probe := by
    rw [leverageOf_eq_dotProduct]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, dotProduct_comm probe (D.atom x)]
    ring
  rw [hexp] at hqq
  by_contra hlt
  push Not at hlt
  nlinarith [hqq, hpsd, hpp]

/-- **The equality case rigidifies.**  A leverage-one atom of a weakly
dominating triple is orthogonal to its two partners: the floor's probe
collapses onto the atom's own line. -/
theorem inside_pair_orthogonal_of_leverage_eq_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    (hlev : leverageOf (D.atom x) = 1) :
    D.atom x ⬝ᵥ D.atom y = 0 ∧ D.atom x ⬝ᵥ D.atom z = 0 := by
  obtain ⟨probe, hne, hy0, hz0⟩ :=
    exists_commonOrthogonal_of_pair (D.atom y) (D.atom z)
  have hpsd : 0 ≤ probe ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ probe) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at h
  rw [dominationGap_form,
    sum_over_triple (fun c => (D.atom c ⬝ᵥ probe) ^ 2) hxy hxz hyz, hy0, hz0] at hpsd
  have hexp : ((D.atom x ⬝ᵥ probe) • D.atom x - probe) ⬝ᵥ
      ((D.atom x ⬝ᵥ probe) • D.atom x - probe)
      = (D.atom x ⬝ᵥ probe) ^ 2 * leverageOf (D.atom x)
        - 2 * (D.atom x ⬝ᵥ probe) ^ 2 + probe ⬝ᵥ probe := by
    rw [leverageOf_eq_dotProduct]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, dotProduct_comm probe (D.atom x)]
    ring
  rw [hlev, mul_one] at hexp
  have hqzero : (D.atom x ⬝ᵥ probe) • D.atom x - probe = 0 := by
    apply eq_zero_of_dotProduct_self_eq_zero
    have hqq := dotProduct_self_nonneg ((D.atom x ⬝ᵥ probe) • D.atom x - probe)
    have hle : ((D.atom x ⬝ᵥ probe) • D.atom x - probe) ⬝ᵥ
        ((D.atom x ⬝ᵥ probe) • D.atom x - probe) ≤ 0 := by
      rw [hexp]
      nlinarith [hpsd]
    linarith
  have hprobe_eq : probe = (D.atom x ⬝ᵥ probe) • D.atom x := (sub_eq_zero.mp hqzero).symm
  have hrne : D.atom x ⬝ᵥ probe ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hprobe_eq
    exact hne hprobe_eq
  constructor
  · have hyx : D.atom y ⬝ᵥ ((D.atom x ⬝ᵥ probe) • D.atom x) = 0 := by
      rw [← hprobe_eq]; exact hy0
    rw [dotProduct_smul, smul_eq_mul] at hyx
    rcases mul_eq_zero.mp hyx with h | h
    · exact absurd h hrne
    · rwa [dotProduct_comm] at h
  · have hzx : D.atom z ⬝ᵥ ((D.atom x ⬝ᵥ probe) • D.atom x) = 0 := by
      rw [← hprobe_eq]; exact hz0
    rw [dotProduct_smul, smul_eq_mul] at hzx
    rcases mul_eq_zero.mp hzx with h | h
    · exact absurd h hrne
    · rwa [dotProduct_comm] at h

/-- **A leverage-one inside atom is form-null.**  Its own gap form vanishes:
the atom sits on the soft locus of its own dominator. -/
theorem gapForm_null_at_leverage_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    (hlev : leverageOf (D.atom x) = 1) :
    D.atom x ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ D.atom x) = 0 := by
  obtain ⟨horthy, horthz⟩ :=
    inside_pair_orthogonal_of_leverage_eq_one D hxy hxz hyz hdominates hlev
  have hyx : D.atom y ⬝ᵥ D.atom x = 0 := by rwa [dotProduct_comm] at horthy
  have hzx : D.atom z ⬝ᵥ D.atom x = 0 := by rwa [dotProduct_comm] at horthz
  have hxx : D.atom x ⬝ᵥ D.atom x = 1 := by
    rw [← leverageOf_eq_dotProduct]; exact hlev
  rw [dominationGap_form,
    sum_over_triple (fun c => (D.atom c ⬝ᵥ D.atom x) ^ 2) hxy hxz hyz,
    hyx, hzx, hxx]
  norm_num

/-- **THE TWO-ZERO DETECTOR.**  At a corank-one weak dominator with unit null
direction, a leverage-one inside atom IS the null direction up to sign. -/
theorem eq_nullDir_of_leverage_eq_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hlev : leverageOf (D.atom x) = 1) :
    D.atom x = nullDir ∨ D.atom x = -nullDir := by
  obtain ⟨s, hs⟩ := hline.2.2 (D.atom x)
    (gapForm_null_at_leverage_one D hxy hxz hyz hdominates hlev)
  have hxx : D.atom x ⬝ᵥ D.atom x = 1 := by
    rw [← leverageOf_eq_dotProduct]; exact hlev
  rw [hs, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, hunit,
    mul_one] at hxx
  have hcases : (s - 1) * (s + 1) = 0 := by nlinarith [hxx]
  rcases mul_eq_zero.mp hcases with h1 | h2
  · left
    rw [hs, show s = 1 by linarith, one_smul]
  · right
    rw [hs, show s = -1 by linarith, neg_smul, one_smul]

/-- **The two-zero readings, forward.**  A leverage-one inside atom silences
its partners' null readings: the reading vector is a signed coordinate
vector. -/
theorem nullReadings_zero_of_leverage_eq_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hlev : leverageOf (D.atom x) = 1) :
    D.atom y ⬝ᵥ nullDir = 0 ∧ D.atom z ⬝ᵥ nullDir = 0 := by
  obtain ⟨horthy, horthz⟩ :=
    inside_pair_orthogonal_of_leverage_eq_one D hxy hxz hyz hdominates hlev
  have hyx : D.atom y ⬝ᵥ D.atom x = 0 := by rwa [dotProduct_comm] at horthy
  have hzx : D.atom z ⬝ᵥ D.atom x = 0 := by rwa [dotProduct_comm] at horthz
  rcases eq_nullDir_of_leverage_eq_one D hxy hxz hyz hdominates hline hunit hlev
    with hx | hx
  · exact ⟨by rw [← hx]; exact hyx, by rw [← hx]; exact hzx⟩
  · have hy : D.atom y ⬝ᵥ nullDir = 0 := by
      have := hyx
      rw [hx] at this
      simpa [dotProduct_neg] using this
    have hz : D.atom z ⬝ᵥ nullDir = 0 := by
      have := hzx
      rw [hx] at this
      simpa [dotProduct_neg] using this
    exact ⟨hy, hz⟩

/-- **The two-zero readings, backward.**  Two vanishing inside null readings
force the third atom onto the null line at leverage exactly one.  Only the
form-null hypothesis is consumed — the full null LINE is not needed for this
direction. -/
theorem leverage_eq_one_of_nullReadings_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    leverageOf (D.atom x) = 1 ∧ (D.atom x = nullDir ∨ D.atom x = -nullDir) := by
  have hres := dominator_resolves_nullDir D hdominates hnull
  rw [sum_over_triple (fun c => (D.atom c ⬝ᵥ nullDir) • D.atom c) hxy hxz hyz,
    hy, hz, zero_smul, zero_smul, add_zero, add_zero] at hres
  have hr2 : (D.atom x ⬝ᵥ nullDir) * (D.atom x ⬝ᵥ nullDir) = 1 := by
    have h1 := congrArg (fun v => v ⬝ᵥ nullDir) hres
    simpa only [smul_dotProduct, smul_eq_mul, hunit] using h1
  have hrne : D.atom x ⬝ᵥ nullDir ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hr2
    norm_num at hr2
  have hlev : leverageOf (D.atom x) = 1 := by
    have h2 := congrArg (fun v => v ⬝ᵥ D.atom x) hres
    simp only [smul_dotProduct, smul_eq_mul] at h2
    rw [leverageOf_eq_dotProduct]
    have hcomm : nullDir ⬝ᵥ D.atom x = D.atom x ⬝ᵥ nullDir := dotProduct_comm _ _
    rw [hcomm] at h2
    have h2' : D.atom x ⬝ᵥ nullDir * (D.atom x ⬝ᵥ D.atom x)
        = D.atom x ⬝ᵥ nullDir * 1 := by rw [mul_one]; exact h2
    exact mul_left_cancel₀ hrne h2'
  refine ⟨hlev, ?_⟩
  have hcases : (D.atom x ⬝ᵥ nullDir - 1) * (D.atom x ⬝ᵥ nullDir + 1) = 0 := by
    nlinarith [hr2]
  rcases mul_eq_zero.mp hcases with h1 | h2
  · left
    have hone : D.atom x ⬝ᵥ nullDir = 1 := by linarith
    rw [hone, one_smul] at hres
    exact hres
  · right
    have hneg : D.atom x ⬝ᵥ nullDir = -1 := by linarith
    rw [hneg, neg_smul, one_smul] at hres
    rw [← hres, neg_neg]

/-- **The strict floor off the two-zero stratum.**  An inside atom whose two
partners do not both silence the null direction has leverage strictly above
one. -/
theorem one_lt_leverage_of_nullReading_ne_zero (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) nullDir)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hread : ¬ (D.atom y ⬝ᵥ nullDir = 0 ∧ D.atom z ⬝ᵥ nullDir = 0)) :
    1 < leverageOf (D.atom x) := by
  rcases lt_or_eq_of_le
    (one_le_leverage_of_mem_dominating_triple D hxy hxz hyz hdominates) with h | h
  · exact h
  · exact absurd
      (nullReadings_zero_of_leverage_eq_one D hxy hxz hyz hdominates hline hunit h.symm)
      hread

/-! ## 3. The null census -/

/-- **The swap `w`-form.**  At a null direction of the dominator, every one-atom
exchange reads the difference of the two squared null readings. -/
theorem swapGapForm_at_nullDir (D : WeightedDesign m 3) (C : Finset (Fin m))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C) :
    nullDir ⬝ᵥ ((subsetSum D (insert d (C.erase e)) - 1) *ᵥ nullDir)
      = (D.atom d ⬝ᵥ nullDir) ^ 2 - (D.atom e ⬝ᵥ nullDir) ^ 2 := by
  rw [subsetSum_swap_sub_one D C he hd, Matrix.sub_mulVec, dotProduct_sub,
    exchangeAnchor_form, hnull, zero_add]
  congr 1
  rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
    dotProduct_comm nullDir (D.atom e), pow_two]

/-- **The free half of the census.**  A swap whose incoming squared null reading
does not beat the outgoing one is refused by the null direction itself — no tie
hypothesis.  The corank-two corner refuses ALL its swaps this way
(`Gtz.not_posDef_swap_of_rankOneGap`); at corank one the census bifurcates on
the reading comparison, and the swaps it misses are the informative ones. -/
theorem not_posDef_swap_of_nullReading_sq_le (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {nullDir : Fin 3 → ℝ} (hwne : nullDir ≠ 0)
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    {e d : Fin m} (he : e ∈ C) (hd : d ∉ C)
    (hle : (D.atom d ⬝ᵥ nullDir) ^ 2 ≤ (D.atom e ⬝ᵥ nullDir) ^ 2) :
    ¬ (subsetSum D (insert d (C.erase e)) - 1).PosDef := by
  intro hpd
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hwne
  rw [star_trivial, swapGapForm_at_nullDir D C hnull he hd] at hform
  linarith

/-- **The complement `w`-form.**  Against a null direction of `C`, the
complement's gap form is the TOTAL unweighted null mass minus twice the null
norm: the inside mass is exactly `|w|²`, so only the outside excess remains. -/
theorem complGapForm_at_nullDir (D : WeightedDesign m 3) (C : Finset (Fin m))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0) :
    nullDir ⬝ᵥ ((subsetSum D Cᶜ - 1) *ᵥ nullDir)
      = (∑ c, (D.atom c ⬝ᵥ nullDir) ^ 2) - 2 * (nullDir ⬝ᵥ nullDir) := by
  have hmass := (gapForm_eq_zero_iff_sum_sq D C nullDir).mp hnull
  have hsplit := Finset.sum_add_sum_compl C (fun c => (D.atom c ⬝ᵥ nullDir) ^ 2)
  rw [dominationGap_form]
  linarith

/-- **The complement census.**  A design whose total unweighted null mass stays
at or below twice the null norm refuses the complement of the dominator for
free.  At `(6,3)` this is the `σ ≤ 1` half of the complement bifurcation. -/
theorem not_posDef_compl_of_nullMass_le (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {nullDir : Fin 3 → ℝ} (hwne : nullDir ≠ 0)
    (hnull : nullDir ⬝ᵥ ((subsetSum D C - 1) *ᵥ nullDir) = 0)
    (hle : (∑ c, (D.atom c ⬝ᵥ nullDir) ^ 2) ≤ 2 * (nullDir ⬝ᵥ nullDir)) :
    ¬ (subsetSum D Cᶜ - 1).PosDef := by
  intro hpd
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hwne
  rw [star_trivial, complGapForm_at_nullDir D C hnull] at hform
  linarith

/-! ## 4. The transferred budget of the two-zero stratum -/

/-- **The avoiding-refusal budget.**  A design with a weakly dominating triple
and an atom of leverage at most one ties exactly when every triple that avoids
that atom is refused: the triples through it are free
(`Gtz.notPosDef_of_mem_leverage_le_one`).  This transfers the `Z1` refusal
budget to the corank-one arm, where the two-zero stratum supplies the
leverage-one atom in the form `g = ±w`. -/
theorem isTie_iff_avoidingRefusals_of_leverage_le_one (D : WeightedDesign m 3)
    {C : Finset (Fin m)} (hcard : C.card = 3) (hdominates : Dominates D C)
    {x : Fin m} (hlev : leverageOf (D.atom x) ≤ 1) :
    IsTie D ↔ ∀ T : Finset (Fin m), T.card = 3 → x ∉ T →
      ¬ (subsetSum D T - 1).PosDef := by
  constructor
  · intro htie T hT _
    exact htie.2 T hT
  · intro href
    refine ⟨⟨C, hcard, hdominates⟩, fun T hT => ?_⟩
    by_cases hxT : x ∈ T
    · obtain ⟨a, b, hab, hTerase⟩ := Finset.card_eq_two.mp
        (by rw [Finset.card_erase_of_mem hxT, hT])
      have hTeq : T = ({x, a, b} : Finset (Fin m)) := by
        rw [← Finset.insert_erase hxT, hTerase]
      rw [hTeq]
      exact notPosDef_of_mem_leverage_le_one D x a b hlev
    · exact href T hT hxT

/-- **THE TWO-ZERO OUTSIDE EXCESS.**  In the two-zero stratum some atom outside
the dominator reads the null direction STRICTLY above one in square.  Weighted
Parseval at `w` puts outside null mass `1 - t_x` on outside weight
`1 - t_x - t_y - t_z`, and the two silenced weights are positive, so the
average outside squared reading exceeds one.  This is the `B_T > 1` half of a
`u`-split kill of the stratum: the witness atom hands every triple through it
a null mass above one, and the remaining fight is the plane discriminant.
[MEASURED, scratchpad/corank1/mega2.jl: the stratum carries NO tie at `(6,3)`
across a 10^9-evaluation search, min obstruction `1.2e-2`; the kill is true.] -/
theorem exists_outside_nullReading_sq_gt_one_of_twoZeroReadings
    (D : WeightedDesign m 3) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    ∃ d ∈ ({x, y, z} : Finset (Fin m))ᶜ, 1 < (D.atom d ⬝ᵥ nullDir) ^ 2 := by
  classical
  obtain ⟨-, hxw⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hnull hunit hy hz
  have hx2 : (D.atom x ⬝ᵥ nullDir) ^ 2 = 1 := by
    rcases hxw with hxw | hxw <;> rw [hxw] <;>
      simp only [dotProduct_neg, neg_dotProduct, neg_neg, hunit] <;> norm_num
  by_contra hcon
  push Not at hcon
  have hparseval := sum_weight_mul_dotProduct_sq D nullDir
  rw [hunit] at hparseval
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun c => D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2)
  have hinside : ∑ c ∈ ({x, y, z} : Finset (Fin m)),
      D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 = D.weight x := by
    rw [sum_over_triple (fun c => D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2) hxy hxz hyz,
      hx2, hy, hz]
    ring
  have houtside_mass : ∑ c ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2 = 1 - D.weight x := by
    have := hsplit.trans hparseval
    rw [hinside] at this
    linarith
  have hbound : ∑ c ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight c * (D.atom c ⬝ᵥ nullDir) ^ 2
      ≤ ∑ c ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight c := by
    refine Finset.sum_le_sum fun c hc => ?_
    have hle := hcon c hc
    have hw := (D.weight_pos c).le
    nlinarith [hle, hw]
  have hweights : ∑ c ∈ (({x, y, z} : Finset (Fin m))ᶜ), D.weight c
      = 1 - (D.weight x + D.weight y + D.weight z) := by
    have hsum := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m)) D.weight
    rw [D.weight_sum_one] at hsum
    rw [sum_over_triple D.weight hxy hxz hyz] at hsum
    linarith
  rw [houtside_mass, hweights] at hbound
  have hy_pos := D.weight_pos y
  have hz_pos := D.weight_pos z
  linarith

/-- **THE TWO-ZERO BUDGET.**  At a corank-one weak dominator whose null
direction two inside atoms silence, the tie collapses to the refusals of the
triples avoiding the third inside atom — that atom is `±w` at leverage one, and
every triple through it is free.  The `(5,3)` diamond and the `(6,3)` split
diamond both sit OFF this stratum (all three readings nonzero, measured
exactly), so a kill of this budget's refusal system is fixture-safe. -/
theorem isTie_iff_avoidingRefusals_of_twoZeroReadings (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {nullDir : Fin 3 → ℝ}
    (hnull : nullDir ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ nullDir) = 0)
    (hunit : nullDir ⬝ᵥ nullDir = 1)
    (hy : D.atom y ⬝ᵥ nullDir = 0) (hz : D.atom z ⬝ᵥ nullDir = 0) :
    IsTie D ↔ ∀ T : Finset (Fin m), T.card = 3 → x ∉ T →
      ¬ (subsetSum D T - 1).PosDef := by
  obtain ⟨hlev, _⟩ :=
    leverage_eq_one_of_nullReadings_zero D hxy hxz hyz hdominates hnull hunit hy hz
  have hcard : ({x, y, z} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  exact isTie_iff_avoidingRefusals_of_leverage_le_one D hcard hdominates hlev.le

end Gtz
