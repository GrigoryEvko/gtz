/-
# The deflation cone, the covering law, and the corner selector census

`Gtz.exists_deflatedGapBound_of_isTie` hands every label `c` of a `(6,3)` tie a
triple `T` that AVOIDS `c` and carries the Loewner bound

  `(1 - t_c)·(S_T - 1)  ⪰  t_c·(1 - g_c g_cᵀ)` .

The campaign spends that bound only at a UNIT atom
(`Gtz/Wave/FunnelSecondInvariantFloor.lean`), where the projection on the right
has a clean second invariant.  This module spends it at EVERY atom, by reading
it at a probe instead of at an invariant, and then spends the reading at a
corank-two corner — the composition the corner lane never made.

## 1. The cone

Read the bound at a probe `z`:

  `t_c·(|z|² - ⟨g_c,z⟩²)  ≤  (1 - t_c)·(Σ_{e ∈ T} ⟨g_e,z⟩² - |z|²)`

(`Gtz.deflatedBound_quadForm`).  Two readings, in opposite directions.

* **The cone** (`Gtz.deflatedBound_cone`).  If `T` FAILS at `z` — that is
  `Σ_{e ∈ T} ⟨g_e,z⟩² ≤ |z|²` — then `|z|² ≤ ⟨g_c,z⟩²`.  Every failure direction
  of the selected triple lies inside the double cone of the DELETED atom, of
  half-angle `arccos(1/√ℓ_c)`.  The selected triple is blind only where its own
  deleted atom is long.
* **The cover** (`Gtz.deflatedBound_reads_above`).  Contrapositive: at every
  probe the deleted atom reads SHORT, the selected triple reads STRICTLY above.

## 2. The covering law at `(6,3)`

`Gtz.exists_triple_reads_above_of_isTie_sixThree`: at a `(6,3)` tie EVERY
nonzero probe is read strictly above its own square by SOME triple.  The proof
is a two-line dichotomy.  If some atom reads the probe short, its own selector
reads the probe above by part 1.  If every one of the six atoms reads the probe
at least as long as the probe itself, then any three of them already total three
times the probe's square.

This is a genuine covering statement and it is NOT implied by domination: a
dominating triple reads every probe at least `|z|²`, and at a corner it reads
the whole axis-orthogonal plane at EXACTLY `|z|²`.  The law says some OTHER
triple beats that plane strictly.

## 3. The corner selector census

At a corank-two corner `S_C - 1 = lam·u uᵀ` the plane `u^⊥` carries the inside
triple as an UNWEIGHTED tight frame (`Gtz.planeMass_of_rankOneGap`), so the
plane reading of the bound is computable in closed form.  Two selectors are then
excluded outright, each by one probe of the plane:

* **`Gtz.corner_deflatedSelector_not_twoInside`** — delete an INSIDE atom `a`.
  The selector cannot keep the other two inside atoms.  Probe the plane
  orthogonally to the selector's third atom: the two kept inside atoms total
  `|y|² - ⟨g_a,y⟩²` by tightness, the third atom reads zero, and the bound
  collapses to `t_a·|y|² ≤ (2t_a - 1)·⟨g_a,y⟩²`.  The corner's own plane
  leverage law (`Gtz.corner_inside_planeLeverage_lt_one`) makes
  `⟨g_a,y⟩² < |y|²`, and `0 < t_a < 1` closes both signs of `2t_a - 1`.
* **`Gtz.corner_deflatedSelector_ne_corner`** — delete an OUTSIDE atom `d`.
  The selector is never the corner itself.  The same probe, now orthogonal to
  `g_d` as well, makes the corner's plane reading exactly `|y|²`, so the bound
  reads `t_d·|y|² ≤ 0`.

Packaged: `Gtz.corner_sixThree_selector_census`.  At a `(6,3)` tie with a corner,
the selector of every INSIDE atom meets the corner in AT MOST ONE atom, hence
meets the complement in at least two, and the selector of every OUTSIDE atom is
some triple other than the corner.

Both statements are strictly finer than the landed refusal census
`Gtz.strictDominator_inter_card_le_one`, which speaks about STRICT DOMINATORS of
the design.  A selector need not dominate the design at all: it dominates the
DEFLATED design, and the Loewner bound is what survives the pullback.

## 4. The trace floor off the unit atom

`Gtz.trace_floor_of_deflatedGapBound` needs `ℓ_a = 1`.  The trace of a positive
semidefinite matrix is nonnegative whatever the atom, so the same one-line
argument gives `Gtz.deflatedBound_leverage_floor`:

  `Σ_{e ∈ T} ℓ_e  ≥  3 + t_a·(3 - ℓ_a)/(1 - t_a)` ,

which is the landed floor at `ℓ_a = 1` and a genuine floor at every `ℓ_a < 3`.

[MEASURED, double precision, on the exact corank-two corner chart of
`scratchpad/corner` (eleven parameters: `lam`, the axis multipliers `v` on the
unit sphere, five weights, and a rotation of the outside frame; Parseval and
`S_C - 1 = lam·u uᵀ` both hold by construction to `1e-14`).  The cone reading of
part 1 was checked at every label of every sampled design against the selector
returned by an explicit search over the ten admissible triples: no violation.
The two census exclusions of part 3 were checked by enumerating, for each label,
every triple that carries the Loewner bound: at no sampled corner did a
two-inside triple carry the bound at an inside atom, and at no sampled corner
did the corner itself carry the bound at an outside atom.]
-/
import Gtz.Wave.CorankStratumCollapse
import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Wave.CorankTwoOneShared
import Gtz.Design.StratumTieFreeClasses
import Gtz.Reduction.PolarPlaneTurn
import Gtz.Reduction.PolarCrossWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## Part 1 — the deflated bound, read at a probe

The bound is a Loewner inequality between two explicit matrices.  Every scalar
consequence in this module is one reading of it. -/

/-- The identity form reads a probe against an atom. -/
theorem dotProduct_one_sub_atomMatrix_mulVec (atomVec probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (((1 : Matrix (Fin 3) (Fin 3) ℝ) - atomMatrix atomVec) *ᵥ probe)
      = probe ⬝ᵥ probe - (atomVec ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, atomMatrix,
    vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm probe atomVec]
  ring

/-- The gap of a subset reads a probe as the total of squared readings, less the
probe's own square. -/
theorem quadForm_subsetSum_gap (D : WeightedDesign m 3) (C : Finset (Fin m))
    (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum D C - 1) *ᵥ probe)
      = (∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_subsetSum_mulVec_sq D C probe]

/-- **THE DEFLATED BOUND AT A PROBE.**  The whole scalar content of the Loewner
bound, at one probe.  No design hypothesis beyond the bound itself. -/
theorem deflatedBound_quadForm (D : WeightedDesign m 3) (selected : Finset (Fin m))
    (dropLabel : Fin m)
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom dropLabel))).PosSemidef)
    (probe : Fin 3 → ℝ) :
    D.weight dropLabel * (probe ⬝ᵥ probe - (D.atom dropLabel ⬝ᵥ probe) ^ 2)
      ≤ (1 - D.weight dropLabel)
        * ((∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe) := by
  have hquad := (posSemidef_iff_quadForm_nonneg _
    (transpose_eq_of_isHermitian hbound.1)).mp hbound probe
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    quadForm_subsetSum_gap D selected probe,
    dotProduct_one_sub_atomMatrix_mulVec (D.atom dropLabel) probe] at hquad
  linarith

/-- **THE CONE.**  Every failure direction of a selected triple lies inside the
double cone of the DELETED atom: if the triple reads the probe at most the
probe's own square, the deleted atom reads it at least that square.

The deleted atom's weight is strictly positive and strictly below one, so both
factors of the bound carry their sign. -/
theorem deflatedBound_cone (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    (selected : Finset (Fin m)) (dropLabel : Fin m)
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom dropLabel))).PosSemidef)
    {probe : Fin 3 → ℝ}
    (hfail : (∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2) ≤ probe ⬝ᵥ probe) :
    probe ⬝ᵥ probe ≤ (D.atom dropLabel ⬝ᵥ probe) ^ 2 := by
  have hread := deflatedBound_quadForm D selected dropLabel hbound probe
  have hpos := D.weight_pos dropLabel
  have hlt := weight_lt_one D hsize dropLabel
  nlinarith [hread, hpos, hlt, hfail]

/-- **THE COVER.**  Contrapositive of the cone: at every probe the deleted atom
reads SHORT, the selected triple reads STRICTLY above. -/
theorem deflatedBound_reads_above (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    (selected : Finset (Fin m)) (dropLabel : Fin m)
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom dropLabel))).PosSemidef)
    {probe : Fin 3 → ℝ}
    (hshort : (D.atom dropLabel ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe) :
    probe ⬝ᵥ probe < ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 := by
  by_contra hcon
  push Not at hcon
  exact absurd (deflatedBound_cone D hsize selected dropLabel hbound hcon) (not_le.mpr hshort)

/-- **THE LEVERAGE FLOOR, OFF THE UNIT ATOM.**  The trace of the bound's slack is
nonnegative whatever the deleted atom's leverage, so the selected triple's
leverage total clears `3` by the deflation ratio times the atom's trace deficit.

At `ℓ_a = 1` this is the landed `Gtz.trace_floor_of_deflatedGapBound`; at every
`ℓ_a < 3` it is a genuine floor, and at `ℓ_a ≥ 3` it degenerates to the trivial
statement that the trace is at least the deficit. -/
theorem deflatedBound_leverage_floor (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (dropLabel : Fin m)
    (hbound : (((1 : ℝ) - D.weight dropLabel)
        • (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
        - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom dropLabel))).PosSemidef) :
    (1 - D.weight dropLabel)
        * (leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 3)
      ≥ D.weight dropLabel * (3 - leverageOf (D.atom dropLabel)) := by
  have hgapTrace : Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin m)) - 1)
      = leverageOf (D.atom x) + leverageOf (D.atom y) + leverageOf (D.atom z) - 3 := by
    have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
        = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
      rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
        Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
      abel
    rw [hsum, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, atomMatrix, atomMatrix,
      atomMatrix, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
      ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct, ← leverageOf_eq_dotProduct]
    simp
  have hprojTrace : Matrix.trace ((1 : Matrix (Fin 3) (Fin 3) ℝ)
      - atomMatrix (D.atom dropLabel)) = 3 - leverageOf (D.atom dropLabel) := by
    rw [Matrix.trace_sub, atomMatrix, Matrix.trace_vecMulVec, ← leverageOf_eq_dotProduct]
    simp
  have htrace := hbound.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    hgapTrace, hprojTrace] at htrace
  linarith

/-! ## Part 2 — the selector at `(6,3)`, and the covering law

`Gtz.gtzWeighted_of_le_five` is shipped, so the deflated bound fires at every
label of a `(6,3)` tie with no extra hypothesis. -/

/-- **THE SELECTOR OF A LABEL.**  At a `(6,3)` tie every label owns a triple that
avoids it, carries the Loewner bound, and therefore reads STRICTLY above every
probe the label itself reads short. -/
theorem exists_deflatedSelector_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (dropLabel : Fin 6) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ dropLabel ∉ selected
      ∧ (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
          - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
            - atomMatrix (D.atom dropLabel))).PosSemidef
      ∧ ∀ probe : Fin 3 → ℝ, (D.atom dropLabel ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe →
          probe ⬝ᵥ probe < ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 := by
  obtain ⟨selected, hcard, havoid, hbound⟩ :=
    exists_deflatedGapBound_of_isTie (m := 5) D (by norm_num)
      (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie dropLabel
  exact ⟨selected, hcard, havoid, hbound,
    fun probe hshort => deflatedBound_reads_above D (by norm_num) selected dropLabel
      hbound hshort⟩

/-- **THE COVERING LAW.**  At a `(6,3)` tie EVERY nonzero probe is read strictly
above its own square by some triple.

This is not domination.  A dominating triple reads every probe at least `|z|²`,
and at a corank-two corner it reads the whole plane `u^⊥` at EXACTLY `|z|²`, so
domination alone gives nothing strict there.  The law says the strict cover is
carried by SOME triple at EVERY direction, and the proof names it: either a
short atom's own selector, or — if every atom reads the probe long — any three
atoms at once. -/
theorem exists_triple_reads_above_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {probe : Fin 3 → ℝ} (hne : probe ≠ 0) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ probe ⬝ᵥ probe < ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 := by
  classical
  have hprobePos : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with hpos | hzero
    · exact hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hne
  by_cases hall : ∀ label : Fin 6, probe ⬝ᵥ probe ≤ (D.atom label ⬝ᵥ probe) ^ 2
  · refine ⟨({0, 1, 2} : Finset (Fin 6)), by decide, ?_⟩
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    linarith [hall 0, hall 1, hall 2]
  · push Not at hall
    obtain ⟨label, hshort⟩ := hall
    obtain ⟨selected, hcard, -, -, hcover⟩ := exists_deflatedSelector_sixThree D htie label
    exact ⟨selected, hcard, hcover probe hshort⟩

/-- **NO DIRECTION IS UNIFORMLY TIGHT.**  Contrapositive packaging: a design in
which some nonzero probe is read at most its own square by EVERY triple is not a
tie.  This is a producer — it refutes the tie from ONE direction. -/
theorem not_isTie_sixThree_of_uniformlyTight (D : WeightedDesign 6 3)
    {probe : Fin 3 → ℝ} (hne : probe ≠ 0)
    (htight : ∀ selected : Finset (Fin 6), selected.card = 3 →
      (∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2) ≤ probe ⬝ᵥ probe) :
    ¬ IsTie D := by
  intro htie
  obtain ⟨selected, hcard, hstrict⟩ :=
    exists_triple_reads_above_of_isTie_sixThree D htie hne
  exact absurd (htight selected hcard) (not_le.mpr hstrict)

/-! ## Part 3 — the corner's plane geometry

Two facts about the axis-orthogonal plane of a corank-two corner.  The first is
the strict positivity of the inside plane leverage, which the landed
`Gtz.corner_inside_planeLeverage_lt_one` caps from above and nothing caps from
below.  The second is the probe the census consumes. -/

/-- The plane component of a vector reads a plane probe by Cauchy-Schwarz, with
the axis mass removed. -/
theorem sq_dotProduct_le_planeLeverage {u atomVec probe : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hperp : u ⬝ᵥ probe = 0) :
    (atomVec ⬝ᵥ probe) ^ 2
      ≤ (leverageOf atomVec - (atomVec ⬝ᵥ u) ^ 2) * (probe ⬝ᵥ probe) := by
  have hcs := dotProduct_sq_le_mul (atomVec - (atomVec ⬝ᵥ u) • u) probe
  have hread : (atomVec - (atomVec ⬝ᵥ u) • u) ⬝ᵥ probe = atomVec ⬝ᵥ probe := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hperp, mul_zero, sub_zero]
  have hself : (atomVec - (atomVec ⬝ᵥ u) • u) ⬝ᵥ (atomVec - (atomVec ⬝ᵥ u) • u)
      = leverageOf atomVec - (atomVec ⬝ᵥ u) ^ 2 := by
    have hcomm : u ⬝ᵥ atomVec = atomVec ⬝ᵥ u := dotProduct_comm _ _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hunit, hcomm, leverageOf_eq_dotProduct]
    ring
  rwa [hread, hself] at hcs

/-- **THE INSIDE PLANE LEVERAGE IS STRICTLY POSITIVE.**  At an all-heavy corner
no inside atom lies on the axis: the corner trace law caps each inside leverage
strictly below `1 + lam`, and the plane leverage law turns that into a strictly
positive plane mass. -/
theorem corner_inside_planeLeverage_pos (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e)) {a : Fin m} (ha : a ∈ C) :
    0 < leverageOf (D.atom a) - (D.atom a ⬝ᵥ u) ^ 2 := by
  classical
  have htotal := sum_inside_leverage_sub_one_eq_lam D C hcard hunit hgap
  have hsplit : ∑ e ∈ C.erase a, (leverageOf (D.atom e) - 1)
      + (leverageOf (D.atom a) - 1) = lam := by
    rw [Finset.sum_erase_add _ _ ha]; exact htotal
  have hrest : 0 < ∑ e ∈ C.erase a, (leverageOf (D.atom e) - 1) := by
    refine Finset.sum_pos (fun e he => ?_) ?_
    · have := hheavy e (Finset.mem_of_mem_erase he); linarith
    · rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hcard]
      norm_num
  have hcap : leverageOf (D.atom a) < 1 + lam := by linarith
  have hplane := corner_inside_planeLeverage D C hcard hlam.le hunit hgap ha
  nlinarith [hplane, hlam, hcap]

/-- **NO INSIDE ATOM IS PARALLEL TO THE AXIS.**  The normal of the axis and an
inside atom is nonzero at an all-heavy corner, so it is a legitimate plane
probe. -/
theorem corner_inside_bracketNormal_ne_zero (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e)) {a : Fin m} (ha : a ∈ C) :
    bracketNormal u (D.atom a) ≠ 0 := by
  have hplanePos := corner_inside_planeLeverage_pos D C hcard hlam hunit hgap hheavy ha
  have hune : u ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp only [dotProduct_zero] at hunit
    exact absurd hunit (by norm_num)
  refine bracketNormal_ne_zero_of_not_parallel u (D.atom a) hune fun ratio hpar => ?_
  have hlev : leverageOf (D.atom a) = ratio ^ 2 := by
    rw [leverageOf_eq_dotProduct, hpar, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hunit]
    ring
  have haxis : D.atom a ⬝ᵥ u = ratio := by
    rw [hpar, smul_dotProduct, smul_eq_mul, hunit, mul_one]
  rw [hlev, haxis] at hplanePos
  simp only [sub_self] at hplanePos
  exact absurd hplanePos (by norm_num)

/-- **THE PLANE PROBE.**  A nonzero probe orthogonal both to the axis and to a
chosen target.  In three dimensions the two constraints leave a line, and when
the target happens to lie ON the axis the witness supplies the line instead. -/
theorem exists_axisPerp_probe {u target witness : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hwitness : bracketNormal u witness ≠ 0) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧ probe ⬝ᵥ u = 0 ∧ target ⬝ᵥ probe = 0 := by
  classical
  have hune : u ≠ 0 := by
    intro hzero
    rw [hzero] at hunit
    simp only [dotProduct_zero] at hunit
    exact absurd hunit (by norm_num)
  by_cases hnormal : bracketNormal u target = 0
  · refine ⟨bracketNormal u witness, hwitness, bracketNormal_dotProduct_left u witness, ?_⟩
    have hpar := eq_smul_of_bracketNormal_eq_zero u target hune hnormal
    rw [hpar, smul_dotProduct, smul_eq_mul,
      dotProduct_comm u (bracketNormal u witness),
      bracketNormal_dotProduct_left u witness, mul_zero]
  · refine ⟨bracketNormal u target, hnormal, bracketNormal_dotProduct_left u target, ?_⟩
    rw [dotProduct_comm target (bracketNormal u target),
      bracketNormal_dotProduct_right u target]

/-! ## Part 4 — the corner selector census

Two exclusions, each one probe of the plane.  Both consume the corner's
unweighted plane tightness `Gtz.planeMass_of_rankOneGap` and nothing else about
the design. -/

/-- **A SELECTOR AT AN INSIDE ATOM KEEPS AT MOST ONE INSIDE ATOM.**  Core form:
the Loewner bound at an inside atom `a` is inconsistent with a selected triple
made of the other two inside atoms and one further label.

Probe the plane orthogonally to that further label.  Plane tightness makes the
two kept inside atoms total `|y|² - ⟨g_a,y⟩²`, the further label reads zero, and
the bound becomes `t_a·|y|² ≤ (2t_a - 1)·⟨g_a,y⟩²`.  The corner caps
`⟨g_a,y⟩² < |y|²`, and `0 < t_a < 1` refutes both signs of `2t_a - 1`. -/
theorem corner_deflatedSelector_not_twoInside (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e))
    {a b c third : Fin m} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbthird : b ≠ third) (hcthird : c ≠ third)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D ({b, c, third} : Finset (Fin m)) - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    False := by
  classical
  -- the corner is exactly the three named inside atoms
  have hCeq : C = ({a, b, c} : Finset (Fin m)) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro label hlabel
      rcases Finset.mem_insert.mp hlabel with h | h
      · exact h ▸ ha
      · rcases Finset.mem_insert.mp h with h' | h'
        · exact h' ▸ hb
        · exact (Finset.mem_singleton.mp h') ▸ hc
    · rw [hcard, Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  -- the plane probe orthogonal to the selector's further label
  obtain ⟨probe, hprobeNe, hprobePerp, hthirdRead⟩ :=
    exists_axisPerp_probe (u := u) (target := D.atom third) (witness := D.atom a) hunit
      (corner_inside_bracketNormal_ne_zero D C hcard hlam hunit hgap hheavy ha)
  have hprobePos : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with hpos | hzero
    · exact hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hprobeNe
  -- plane tightness of the corner
  have htight := planeMass_of_rankOneGap D C hprobePerp hgap
  rw [hCeq, sum_over_triple (fun label => (D.atom label ⬝ᵥ probe) ^ 2) hab hac hbc] at htight
  -- the selector's plane reading
  have hselector : (∑ label ∈ ({b, c, third} : Finset (Fin m)),
      (D.atom label ⬝ᵥ probe) ^ 2)
      = probe ⬝ᵥ probe - (D.atom a ⬝ᵥ probe) ^ 2 := by
    rw [sum_over_triple (fun label => (D.atom label ⬝ᵥ probe) ^ 2) hbc hbthird hcthird,
      hthirdRead]
    linarith [htight]
  -- the bound, collapsed
  have hread := deflatedBound_quadForm D ({b, c, third} : Finset (Fin m)) a hbound probe
  rw [hselector] at hread
  -- the corner's plane cap on the deleted atom
  have hcap := corner_inside_planeLeverage_lt_one D C hcard hlam hunit hgap ha (hheavy a ha)
  have hcs := sq_dotProduct_le_planeLeverage (u := u) (atomVec := D.atom a) (probe := probe)
    hunit (by rw [dotProduct_comm]; exact hprobePerp)
  have hshort : (D.atom a ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := by nlinarith [hcs, hcap, hprobePos]
  have hweightPos := D.weight_pos a
  have hweightLt := weight_lt_one D hsize a
  nlinarith [hread, hshort, hprobePos, hweightPos, hweightLt, sq_nonneg (D.atom a ⬝ᵥ probe)]

/-- **A SELECTOR AT AN OUTSIDE ATOM IS NEVER THE CORNER.**  Core form: the
Loewner bound at a label outside the corner is inconsistent with the corner
itself as the selected triple.

The same probe, now orthogonal to the outside atom too.  The corner's plane
reading is exactly `|y|²`, so the bound reads `t_d·|y|² ≤ 0`. -/
theorem corner_deflatedSelector_ne_corner (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e))
    {a outLabel : Fin m} (ha : a ∈ C)
    (hbound : (((1 : ℝ) - D.weight outLabel) • (subsetSum D C - 1)
        - D.weight outLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom outLabel))).PosSemidef) :
    False := by
  classical
  obtain ⟨probe, hprobeNe, hprobePerp, houtRead⟩ :=
    exists_axisPerp_probe (u := u) (target := D.atom outLabel) (witness := D.atom a) hunit
      (corner_inside_bracketNormal_ne_zero D C hcard hlam hunit hgap hheavy ha)
  have hprobePos : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with hpos | hzero
    · exact hpos
    · exact absurd (dotProduct_self_eq_zero.mp hzero.symm) hprobeNe
  have htight := planeMass_of_rankOneGap D C hprobePerp hgap
  have hread := deflatedBound_quadForm D C outLabel hbound probe
  rw [htight, houtRead] at hread
  have hweightPos := D.weight_pos outLabel
  nlinarith [hread, hprobePos, hweightPos]

/-! ### The census at `(6,3)` -/

/-- **THE INSIDE SELECTOR MEETS THE CORNER AT MOST ONCE.**  Any triple carrying
the Loewner bound at an inside atom `a` shares at most one atom with the corner.
`a` itself is excluded by the bound's own membership clause, and the other two
inside atoms cannot both survive. -/
theorem corner_deflatedSelector_inter_card_le_one (D : WeightedDesign m 3) (hsize : 2 ≤ m)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e))
    {a : Fin m} (ha : a ∈ C) {selected : Finset (Fin m)} (hselCard : selected.card = 3)
    (havoid : a ∉ selected)
    (hbound : (((1 : ℝ) - D.weight a) • (subsetSum D selected - 1)
        - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom a))).PosSemidef) :
    (selected ∩ C).card ≤ 1 := by
  classical
  by_contra hbig
  push Not at hbig
  -- two inside atoms survive the selection
  obtain ⟨b, hbmem, c, hcmem, hbc⟩ := Finset.one_lt_card.mp hbig
  have hbSel : b ∈ selected := (Finset.mem_inter.mp hbmem).1
  have hbC : b ∈ C := (Finset.mem_inter.mp hbmem).2
  have hcSel : c ∈ selected := (Finset.mem_inter.mp hcmem).1
  have hcC : c ∈ C := (Finset.mem_inter.mp hcmem).2
  have hab : a ≠ b := fun heq => havoid (heq ▸ hbSel)
  have hac : a ≠ c := fun heq => havoid (heq ▸ hcSel)
  -- the selector is exactly those two and one further label
  have hpairSub : ({b, c} : Finset (Fin m)) ⊆ selected := by
    intro label hlabel
    rcases Finset.mem_insert.mp hlabel with h | h
    · exact h ▸ hbSel
    · exact (Finset.mem_singleton.mp h) ▸ hcSel
  have hpairCard : ({b, c} : Finset (Fin m)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  have hdiffCard : (selected \ ({b, c} : Finset (Fin m))).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hpairSub, hselCard, hpairCard]
  obtain ⟨third, hthird⟩ := Finset.card_eq_one.mp hdiffCard
  have hthirdMem : third ∈ selected \ ({b, c} : Finset (Fin m)) := by
    rw [hthird]; exact Finset.mem_singleton_self third
  have hthirdSel : third ∈ selected := (Finset.mem_sdiff.mp hthirdMem).1
  have hthirdOut : third ∉ ({b, c} : Finset (Fin m)) := (Finset.mem_sdiff.mp hthirdMem).2
  have hbthird : b ≠ third := fun heq => hthirdOut (heq ▸ Finset.mem_insert_self b {c})
  have hcthird : c ≠ third := fun heq =>
    hthirdOut (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
  have hselEq : selected = ({b, c, third} : Finset (Fin m)) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro label hlabel
      rcases Finset.mem_insert.mp hlabel with h | h
      · exact h ▸ hbSel
      · rcases Finset.mem_insert.mp h with h' | h'
        · exact h' ▸ hcSel
        · exact (Finset.mem_singleton.mp h') ▸ hthirdSel
    · rw [hselCard, Finset.card_insert_of_notMem (by simp [hbc, hbthird]),
        Finset.card_insert_of_notMem (by simp [hcthird]), Finset.card_singleton]
  rw [hselEq] at hbound
  exact corner_deflatedSelector_not_twoInside D hsize C hcard hlam hunit hgap hheavy ha hbC hcC
    hab hac hbc hbthird hcthird hbound

/-- **THE `(6,3)` CORNER SELECTOR CENSUS.**  At a `(6,3)` tie carrying a
corank-two corner with all three inside atoms strictly heavy:

* the selector of every INSIDE atom shares at most one atom with the corner,
  hence at least two of its three atoms lie in the complement;
* the selector of every OUTSIDE atom is a triple other than the corner.

Both clauses come with the Loewner bound attached, so a successor may keep
spending it. -/
theorem corner_sixThree_selector_census (D : WeightedDesign 6 3) (htie : IsTie D)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e)) :
    (∀ a ∈ C, ∃ selected : Finset (Fin 6), selected.card = 3 ∧ a ∉ selected
        ∧ (selected ∩ C).card ≤ 1 ∧ 2 ≤ (selected ∩ Cᶜ).card
        ∧ (((1 : ℝ) - D.weight a) • (subsetSum D selected - 1)
            - D.weight a • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
              - atomMatrix (D.atom a))).PosSemidef)
      ∧ (∀ d ∈ (Cᶜ : Finset (Fin 6)), ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ d ∉ selected ∧ selected ≠ C
          ∧ (((1 : ℝ) - D.weight d) • (subsetSum D selected - 1)
              - D.weight d • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
                - atomMatrix (D.atom d))).PosSemidef) := by
  classical
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨anchor, hanchor⟩ := hCne
  constructor
  · intro a ha
    obtain ⟨selected, hselCard, havoid, hbound, -⟩ := exists_deflatedSelector_sixThree D htie a
    have hinter := corner_deflatedSelector_inter_card_le_one D (by norm_num) C hcard hlam
      hunit hgap hheavy ha hselCard havoid hbound
    refine ⟨selected, hselCard, havoid, hinter, ?_, hbound⟩
    have hdisj : Disjoint (selected ∩ C) (selected ∩ Cᶜ) :=
      Finset.disjoint_left.mpr fun label hleft hright =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hright).2) (Finset.mem_inter.mp hleft).2
    have hunion : (selected ∩ C) ∪ (selected ∩ Cᶜ) = selected := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have hsplit : (selected ∩ C).card + (selected ∩ Cᶜ).card = selected.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    omega
  · intro d hd
    obtain ⟨selected, hselCard, havoid, hbound, -⟩ := exists_deflatedSelector_sixThree D htie d
    refine ⟨selected, hselCard, havoid, ?_, hbound⟩
    intro hselEq
    rw [hselEq] at hbound
    exact corner_deflatedSelector_ne_corner D C hcard hlam hunit hgap hheavy hanchor hbound

/-- **THE COMPLEMENT IS NEVER A SELECTOR EITHER, AT A CORNER WITH A HEAVY
COMPLEMENT.**  Read the census at an inside atom: its selector meets the corner
at most once, so it is not the corner; read it at an outside atom: its selector
is not the corner.  Together, at a `(6,3)` tie with a corner NO label selects the
corner, so the corner is a weak dominator that the deflation never reproduces. -/
theorem corner_sixThree_not_selected (D : WeightedDesign 6 3)
    (C : Finset (Fin 6)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hheavy : ∀ e ∈ C, 1 < leverageOf (D.atom e)) (dropLabel : Fin 6) :
    ¬ (((1 : ℝ) - D.weight dropLabel) • (subsetSum D C - 1)
        - D.weight dropLabel • ((1 : Matrix (Fin 3) (Fin 3) ℝ)
          - atomMatrix (D.atom dropLabel))).PosSemidef := by
  classical
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨anchor, hanchor⟩ := hCne
  intro hbound
  exact corner_deflatedSelector_ne_corner D C hcard hlam hunit hgap hheavy hanchor hbound

end Gtz
