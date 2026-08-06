/-
# The rigidity bridge: from a chart theorem to the tree's stratum obligation

`Gtz.StressFreeStratumIsTieFree pattern` quantifies over ARBITRARY stress-free
`(6,3)` designs whose dependent triples are the ones the pattern names.  The
campaign's certificates do not live there.  They live on a CHART: the six
directions are FIXED rational vectors and the only free numbers are the masses
`m` and the weights `w`.  This file is the missing conversion.

## The two halves

* `Gtz.directionChartGap` is the chart's gap matrix

  `G_C(m, w) = Sigma_{c in C} (m_c / w_c) v_c v_c^T  -  Sigma_c m_c v_c v_c^T`,

  and `Gtz.DirectionChartIsTieFree` is the chart-level obligation stated on it: if some
  triple makes `G_C` positive semidefinite then some triple makes it positive
  definite.  No design, no whitener and no square root occurs in that statement.

* `Gtz.DirectionChartCoversPrimitiveStratum` is the RIGIDITY half: every primitive design
  realizing the pattern has atoms `g_c = t_c . (P v_{relabel c})` for one common
  invertible `P` and nonzero scalars `t_c`.

`Gtz.stressFreeStratumIsTieFree_of_directionChart` composes them.  The composition is
bookkeeping: Parseval turns `(t, P, w)` into the chart point `m_c = w_c t_c^2`,
and `Gtz.subsetSum_sub_one_eq_congr_directionChartGap` says the design's gap is the
chart's gap conjugated by `P`, so weak domination transports by
`Gtz.posSemidef_congr_right` and strict domination by `Gtz.posDef_congr_right`.

## The invariance group, named exactly

The obligation is invariant under

* `GL(3, R)` acting on atoms by `g |-> P g`.  This is not an isometry action:
  `P` moves Parseval to `P M(m) P^T = I`, which is exactly the whitening
  condition, and it moves the gap by a CONGRUENCE, `S_C - I = P G_C P^T`, so
  both `PosSemidef` and `PosDef` transport.  On directions only the class of `P`
  in `PGL(3)` matters, since a scalar is absorbed by the per-atom scale.
* the per-atom scaling group `(R^*)^size`, `g_c |-> t_c g_c`.  Domination is NOT
  invariant under it — `Gtz.subsetSum` is weight-free, so rescaling an atom
  really changes `S_C`.  What is free is the PAIR `(t, w)`, and the invariant
  combination is the mass `m_c = w_c t_c^2`.  That is why the chart carries
  eleven numbers at `size = 6` (six masses, five independent weights) and not
  six.
* the relabelling group `S_size`, already quantified inside
  `Gtz.StressFreeStratumIsTieFree`.

No orthogonal group and no choice of whitener appears: the bridge never builds a
design out of chart data, it only reads chart data off a design.

## The M(K4) instance

`Gtz.directionChartCoversPrimitiveStratum_kFourDirection` is the first complete instance.
Its hypotheses are `Gtz.IsPrimitiveDesign` and the K4 line pattern — STRESS-
FREENESS IS NOT USED.  The tree derives primitivity from stress-freeness
(`Gtz.isPrimitiveDesign_of_stressFree`) and the covering needs no more.

The proof is the classical "`PGL(3)` is simply transitive on four general lines"
made rational.  `{3,4,5}` is not a line of the pattern and `Gtz.HasLinePattern`
is an IFF, so those three atoms are a basis.  Expand `0, 1, 2` in it; each
expansion misses one basis vector because its own line says so, giving six
coefficients `A, B, C, D, E, F`.  Five of them are nonzero because a vanishing
one is literally a parallel pair.  The FOURTH line `{0,1,2}` then reads as the
single scalar relation `A D E + B C F = 0`, and that relation is exactly what
makes ONE rescaling of the basis — the columns `AC v_3`, `-BC v_4`, `-AD v_5` —
carry all six directions at once.

Degenerate sub-cases: a repeated or vanishing direction is excluded by
`Gtz.IsPrimitiveDesign` (at `ratio = 0` it says no atom is zero), and a
degenerate `{3,4,5}` is excluded by the pattern being an IFF.  There is no third
case: the six coefficients enumerate the ways an atom can collapse onto a basis
vector, and each collapse is a parallel pair.
-/
import Mathlib
import Gtz.Design.StressFreeMatroidStratification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

open Matrix

/-! ## Symmetry and scaling of the rank-one atoms -/

/-- The three coordinates of `Fin 3`, as literals a `rcases ... with rfl` can
substitute — `fin_cases` leaves anonymous-constructor indices that `ring` reads
as atoms distinct from the literals. -/
theorem fin_three_cases (coord : Fin 3) : coord = 0 ∨ coord = 1 ∨ coord = 2 := by
  revert coord
  decide

/-- The six labels of `Fin 6`, in the same substitutable form. -/
theorem fin_six_cases (index : Fin 6) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
  revert index
  decide

/-- A rank-one atom is a symmetric matrix. -/
theorem atomMatrix_transpose {rank : ℕ} (vec : Fin rank → ℝ) :
    (atomMatrix vec)ᵀ = atomMatrix vec := by
  ext rowIndex colIndex
  simp only [Matrix.transpose_apply, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- Scaling all three slots of a bracket multiplies it by the product. -/
theorem tripleBracket_smul_slots (leftScale midScale rightScale : ℝ)
    (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket (leftScale • leftVec) (midScale • midVec) (rightScale • rightVec)
      = leftScale * midScale * rightScale * tripleBracket leftVec midVec rightVec := by
  simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]
  ring

/-- A cyclic rotation of the slots leaves the bracket alone. -/
theorem tripleBracket_rotate (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec = tripleBracket midVec rightVec leftVec := by
  simp only [tripleBracket_eq]
  ring

/-! ## The chart

A chart is a family of FIXED direction vectors.  Its points are the masses and
the weights; the gap below carries all of domination once the design's change of
basis has been divided out. -/

/-- The chart gap `G_C(m, w) = Sigma_{c in C} (m_c / w_c) v_c v_c^T - Sigma_c m_c v_c v_c^T`. -/
noncomputable def directionChartGap {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (∑ label ∈ selected, (mass label / weight label) • atomMatrix (direction label))
    - ∑ label, mass label • atomMatrix (direction label)

/-- The chart gap is symmetric: it is a combination of rank-one atoms. -/
theorem directionChartGap_transpose {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) :
    (directionChartGap direction mass weight selected)ᵀ = directionChartGap direction mass weight selected := by
  ext rowIndex colIndex
  simp only [directionChartGap, Matrix.transpose_apply, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul]
  congr 1
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => by ring

/-- A point of the chart: the masses and the weights.  Eleven numbers at
`size = 6` — six masses and five independent weights. -/
structure DirectionChartPoint (size : ℕ) where
  /-- The mass of each direction, `m_c = w_c t_c^2`. -/
  mass : Fin size → ℝ
  /-- The design weight of each direction. -/
  weight : Fin size → ℝ
  /-- Masses are positive. -/
  mass_pos : ∀ label, 0 < mass label
  /-- Weights are positive. -/
  weight_pos : ∀ label, 0 < weight label
  /-- The weights are a probability vector. -/
  weight_sum_one : ∑ label, weight label = 1

/-- **The chart-level obligation.**  At every chart point, a weakly dominating
triple forces a strictly dominating one.  This is `¬ Gtz.IsTie` with the design
divided out. -/
def DirectionChartIsTieFree {size : ℕ} (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint size,
    (∃ selected : Finset (Fin size), selected.card = 3 ∧
        (directionChartGap direction point.mass point.weight selected).PosSemidef) →
      ∃ selected : Finset (Fin size), selected.card = 3 ∧
        (directionChartGap direction point.mass point.weight selected).PosDef

/-- The stronger form the certificate corpus actually measures: SOME triple is
strictly dominating at every chart point, with no antecedent. -/
def DirectionChartHasStrictTriple {size : ℕ} (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint size, ∃ selected : Finset (Fin size), selected.card = 3 ∧
    (directionChartGap direction point.mass point.weight selected).PosDef

/-- The strict form implies the obligation. -/
theorem directionChartIsTieFree_of_hasStrictTriple {size : ℕ}
    {direction : Fin size → (Fin 3 → ℝ)} (hstrict : DirectionChartHasStrictTriple direction) :
    DirectionChartIsTieFree direction :=
  fun point _ => hstrict point

/-! ## The rigidity half -/

/-- **The design sits on the chart.**  Its atoms are the chart directions,
relabelled, moved by ONE invertible change of basis and scaled one at a time. -/
def IsDirectionChartRealization {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size)) : Prop :=
  ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin size → ℝ,
    IsUnit basisChange.det ∧ (∀ label, scale label ≠ 0) ∧
      ∀ label, design.atom label = scale label • (basisChange *ᵥ direction (relabel label))

/-- **The covering statement.**  Every primitive design realizing the pattern,
under any relabelling, sits on the chart.  This is the mathematical content of
the bridge; everything else is bookkeeping. -/
def DirectionChartCoversPrimitiveStratum {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (pattern : LinePattern size) : Prop :=
  ∀ (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size)),
    IsPrimitiveDesign design →
      HasLinePattern design (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) →
        IsDirectionChartRealization direction design relabel

/-! ## The bookkeeping: a realization turns the design's gap into the chart's -/

/-- Congruence commutes with a weighted sum of atoms. -/
theorem congr_sum_smul_atomMatrix {size : ℕ} (basisChange : Matrix (Fin 3) (Fin 3) ℝ)
    (coefficient : Fin size → ℝ) (direction : Fin size → (Fin 3 → ℝ))
    (selected : Finset (Fin size)) :
    basisChange * (∑ label ∈ selected, coefficient label • atomMatrix (direction label))
        * basisChangeᵀ
      = ∑ label ∈ selected, coefficient label •
          (basisChange * atomMatrix (direction label) * basisChangeᵀ) := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The atom matrix of a realized atom, with the scale squared out in front. -/
theorem atomMatrix_of_realization {size : ℕ} {direction : Fin size → (Fin 3 → ℝ)}
    {design : WeightedDesign size 3} {relabel : Equiv.Perm (Fin size)}
    {basisChange : Matrix (Fin 3) (Fin 3) ℝ} {scale : Fin size → ℝ}
    (hrealize : ∀ label,
      design.atom label = scale label • (basisChange *ᵥ direction (relabel label)))
    (label : Fin size) :
    atomMatrix (design.atom label)
      = (scale label ^ 2) •
        (basisChange * atomMatrix (direction (relabel label)) * basisChangeᵀ) := by
  rw [hrealize label, atomMatrix_smul, atomMatrix_conj]

/-- The chart point a realization reads off the design: at direction index `i`
the mass is `m_i = w_i t_i^2` and the weight is the design's own. -/
noncomputable def realizationDirectionChartPoint {size : ℕ} (design : WeightedDesign size 3)
    (relabel : Equiv.Perm (Fin size)) {scale : Fin size → ℝ}
    (hscaleNe : ∀ label, scale label ≠ 0) : DirectionChartPoint size where
  mass := fun index =>
    design.weight (relabel.symm index) * scale (relabel.symm index) ^ 2
  weight := fun index => design.weight (relabel.symm index)
  mass_pos := fun index =>
    mul_pos (design.weight_pos _) (pow_pos (abs_pos.mpr (hscaleNe (relabel.symm index))) 2
      |>.trans_le (le_of_eq (by rw [← abs_pow, abs_of_nonneg (sq_nonneg _)])))
  weight_pos := fun index => design.weight_pos _
  weight_sum_one := by
    rw [Equiv.sum_comp relabel.symm design.weight]
    exact design.weight_sum_one

/-- **The gap dictionary.**  A realized design's gap on a subset is the chart's
gap on the relabelled subset, conjugated by the change of basis.  Parseval is
spent exactly here, to identify the subtracted term. -/
theorem subsetSum_sub_one_eq_congr_directionChartGap {size : ℕ} {direction : Fin size → (Fin 3 → ℝ)}
    (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size))
    {basisChange : Matrix (Fin 3) (Fin 3) ℝ} {scale : Fin size → ℝ}
    (hscaleNe : ∀ label, scale label ≠ 0)
    (hrealize : ∀ label,
      design.atom label = scale label • (basisChange *ᵥ direction (relabel label)))
    (selected : Finset (Fin size)) :
    subsetSum design selected - 1
      = basisChange * directionChartGap direction
          (realizationDirectionChartPoint design relabel hscaleNe).mass
          (realizationDirectionChartPoint design relabel hscaleNe).weight
          (selected.map relabel.toEmbedding) * basisChangeᵀ := by
  have hmassValue : ∀ index : Fin size,
      (realizationDirectionChartPoint design relabel hscaleNe).mass index
        = design.weight (relabel.symm index) * scale (relabel.symm index) ^ 2 := fun _ => rfl
  have hweightValue : ∀ index : Fin size,
      (realizationDirectionChartPoint design relabel hscaleNe).weight index
        = design.weight (relabel.symm index) := fun _ => rfl
  have hratio : ∀ index : Fin size,
      (realizationDirectionChartPoint design relabel hscaleNe).mass index
          / (realizationDirectionChartPoint design relabel hscaleNe).weight index
        = scale (relabel.symm index) ^ 2 := by
    intro index
    rw [hmassValue, hweightValue, mul_comm, mul_div_assoc,
      div_self (design.weight_pos (relabel.symm index)).ne', mul_one]
  have hselected : basisChange *
        (∑ index ∈ selected.map relabel.toEmbedding,
          ((realizationDirectionChartPoint design relabel hscaleNe).mass index
            / (realizationDirectionChartPoint design relabel hscaleNe).weight index)
              • atomMatrix (direction index)) * basisChangeᵀ
      = subsetSum design selected := by
    rw [congr_sum_smul_atomMatrix, subsetSum, Finset.sum_map selected relabel.toEmbedding]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [atomMatrix_of_realization hrealize label]
    have hcoefficient : (realizationDirectionChartPoint design relabel hscaleNe).mass
        (relabel.toEmbedding label)
          / (realizationDirectionChartPoint design relabel hscaleNe).weight (relabel.toEmbedding label)
        = scale label ^ 2 := by
      rw [hratio]
      congr 1
      exact congrArg scale (Equiv.symm_apply_apply relabel label)
    rw [hcoefficient]
    congr 2
  have htotal : basisChange *
        (∑ index, (realizationDirectionChartPoint design relabel hscaleNe).mass index
            • atomMatrix (direction index)) * basisChangeᵀ
      = 1 := by
    rw [congr_sum_smul_atomMatrix, ← design.isParseval,
      ← Equiv.sum_comp relabel
        (fun index => (realizationDirectionChartPoint design relabel hscaleNe).mass index
          • (basisChange * atomMatrix (direction index) * basisChangeᵀ))]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [atomMatrix_of_realization hrealize label, hmassValue,
      Equiv.symm_apply_apply, smul_smul]
  rw [directionChartGap, Matrix.mul_sub, Matrix.sub_mul, hselected, htotal]

/-- Weak domination transports to the chart. -/
theorem dominates_iff_posSemidef_directionChartGap {size : ℕ} {direction : Fin size → (Fin 3 → ℝ)}
    (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size))
    {basisChange : Matrix (Fin 3) (Fin 3) ℝ} {scale : Fin size → ℝ}
    (hunit : IsUnit basisChange.det) (hscaleNe : ∀ label, scale label ≠ 0)
    (hrealize : ∀ label,
      design.atom label = scale label • (basisChange *ᵥ direction (relabel label)))
    (selected : Finset (Fin size)) :
    Dominates design selected
      ↔ (directionChartGap direction (realizationDirectionChartPoint design relabel hscaleNe).mass
          (realizationDirectionChartPoint design relabel hscaleNe).weight
          (selected.map relabel.toEmbedding)).PosSemidef := by
  have hcongruence := posSemidef_congr_right (P := basisChangeᵀ)
    (directionChartGap_transpose direction (realizationDirectionChartPoint design relabel hscaleNe).mass
      (realizationDirectionChartPoint design relabel hscaleNe).weight
      (selected.map relabel.toEmbedding))
    (by rwa [Matrix.det_transpose])
  rw [Matrix.transpose_transpose] at hcongruence
  rw [Dominates, subsetSum_sub_one_eq_congr_directionChartGap design relabel hscaleNe hrealize selected]
  exact hcongruence.symm

/-- Strict domination transports to the chart. -/
theorem posDef_gap_iff_posDef_directionChartGap {size : ℕ} {direction : Fin size → (Fin 3 → ℝ)}
    (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size))
    {basisChange : Matrix (Fin 3) (Fin 3) ℝ} {scale : Fin size → ℝ}
    (hunit : IsUnit basisChange.det) (hscaleNe : ∀ label, scale label ≠ 0)
    (hrealize : ∀ label,
      design.atom label = scale label • (basisChange *ᵥ direction (relabel label)))
    (selected : Finset (Fin size)) :
    (subsetSum design selected - 1).PosDef
      ↔ (directionChartGap direction (realizationDirectionChartPoint design relabel hscaleNe).mass
          (realizationDirectionChartPoint design relabel hscaleNe).weight
          (selected.map relabel.toEmbedding)).PosDef := by
  have hcongruence := posDef_congr_right (P := basisChangeᵀ)
    (directionChartGap_transpose direction (realizationDirectionChartPoint design relabel hscaleNe).mass
      (realizationDirectionChartPoint design relabel hscaleNe).weight
      (selected.map relabel.toEmbedding))
    (by rwa [Matrix.det_transpose])
  rw [Matrix.transpose_transpose] at hcongruence
  rw [subsetSum_sub_one_eq_congr_directionChartGap design relabel hscaleNe hrealize selected]
  exact hcongruence.symm

/-- Mapping a subset forward and back along a permutation is the identity. -/
theorem map_symm_toEmbedding_map {size : ℕ} (relabel : Equiv.Perm (Fin size))
    (selected : Finset (Fin size)) :
    (selected.map relabel.symm.toEmbedding).map relabel.toEmbedding = selected := by
  ext label
  simp

/-! ## The bridge -/

/-- **THE BRIDGE, POINTWISE.**  A design that sits on a tie-free chart is not a
tie.  Both bridges below are this statement plus a covering. -/
theorem not_isTie_of_isDirectionChartRealization {size : ℕ}
    {direction : Fin size → (Fin 3 → ℝ)} (design : WeightedDesign size 3)
    (relabel : Equiv.Perm (Fin size))
    (hchart : DirectionChartIsTieFree direction)
    (hrealization : IsDirectionChartRealization direction design relabel) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨basisChange, scale, hunit, hscaleNe, hrealize⟩ := hrealization
  obtain ⟨weakSubset, hweakCard, hweakDominates⟩ := htie.1
  have hweakChart := (dominates_iff_posSemidef_directionChartGap design relabel hunit hscaleNe hrealize
    weakSubset).mp hweakDominates
  obtain ⟨strictSubset, hstrictCard, hstrictPosDef⟩ :=
    hchart (realizationDirectionChartPoint design relabel hscaleNe)
      ⟨weakSubset.map relabel.toEmbedding, by rwa [Finset.card_map], hweakChart⟩
  refine htie.2 (strictSubset.map relabel.symm.toEmbedding) (by rwa [Finset.card_map]) ?_
  rw [posDef_gap_iff_posDef_directionChartGap design relabel hunit hscaleNe hrealize,
    map_symm_toEmbedding_map]
  exact hstrictPosDef

/-- **THE RIGIDITY BRIDGE.**  A chart-level tie-freeness theorem plus a covering
statement give the tree's per-pattern obligation.  Stress-freeness is spent only
to produce primitivity, which is all the covering needs. -/
theorem stressFreeStratumIsTieFree_of_directionChart {direction : Fin 6 → (Fin 3 → ℝ)}
    {pattern : LinePattern 6}
    (hchart : DirectionChartIsTieFree direction)
    (hcover : DirectionChartCoversPrimitiveStratum direction pattern) :
    StressFreeStratumIsTieFree pattern :=
  fun design relabel hstressFree hpattern =>
    not_isTie_of_isDirectionChartRealization design relabel hchart
      (hcover design relabel (isPrimitiveDesign_of_stressFree design hstressFree) hpattern)

/-! ## The parameterized bridge

`M(K4)` is rigid — its chart has no moduli.  The other four surviving classes do
have moduli (`#4` one parameter, `#3` two, `#1` three, `#0` the whole general
position stratum), so their charts are FAMILIES of direction assignments and
their obligation is tie-freeness at every admissible parameter. -/

/-- **The covering statement for a parameterized chart.**  Every primitive design
realizing the pattern sits on the chart at SOME admissible parameter. -/
def ParameterizedChartCovers {size : ℕ} {Parameter : Type}
    (direction : Parameter → Fin size → (Fin 3 → ℝ)) (isAdmissible : Parameter → Prop)
    (pattern : LinePattern size) : Prop :=
  ∀ (design : WeightedDesign size 3) (relabel : Equiv.Perm (Fin size)),
    IsPrimitiveDesign design →
      HasLinePattern design (fun leftLabel midLabel rightLabel =>
        pattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) →
        ∃ parameter : Parameter, isAdmissible parameter ∧
          IsDirectionChartRealization (direction parameter) design relabel

/-- **THE RIGIDITY BRIDGE, PARAMETERIZED.**  Tie-freeness of the chart at every
admissible parameter, plus a covering statement, give the tree's per-pattern
obligation.  The rigid case is this one at a one-point parameter space. -/
theorem stressFreeStratumIsTieFree_of_parameterizedChart {Parameter : Type}
    {direction : Parameter → Fin 6 → (Fin 3 → ℝ)} {isAdmissible : Parameter → Prop}
    {pattern : LinePattern 6}
    (hchart : ∀ parameter : Parameter, isAdmissible parameter →
      DirectionChartIsTieFree (direction parameter))
    (hcover : ParameterizedChartCovers direction isAdmissible pattern) :
    StressFreeStratumIsTieFree pattern := by
  intro design relabel hstressFree hpattern
  obtain ⟨parameter, hadmissible, hrealization⟩ :=
    hcover design relabel (isPrimitiveDesign_of_stressFree design hstressFree) hpattern
  exact not_isTie_of_isDirectionChartRealization design relabel (hchart parameter hadmissible)
    hrealization

/-! ## Linear algebra for the covering proofs -/

/-- **The Cramer expansion in a bracket basis**, cleared of denominators: a
polynomial identity in twelve real variables. -/
theorem tripleBracket_smul_eq_cramer (baseFirst baseMid baseLast probe : Fin 3 → ℝ) :
    tripleBracket baseFirst baseMid baseLast • probe
      = tripleBracket probe baseMid baseLast • baseFirst
        + tripleBracket baseFirst probe baseLast • baseMid
        + tripleBracket baseFirst baseMid probe • baseLast := by
  funext coord
  rcases fin_three_cases coord with rfl | rfl | rfl <;>
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, tripleBracket_eq] <;> ring

/-- The two-term expansion: a probe dependent with the first two basis vectors
has a vanishing last coefficient, so it lies in their span. -/
theorem smul_eq_two_term_expansion (baseFirst baseMid baseLast probe : Fin 3 → ℝ)
    (hdependent : tripleBracket baseFirst baseMid probe = 0) :
    tripleBracket baseFirst baseMid baseLast • probe
      = tripleBracket probe baseMid baseLast • baseFirst
        + tripleBracket baseFirst probe baseLast • baseMid := by
  rw [tripleBracket_smul_eq_cramer baseFirst baseMid baseLast probe, hdependent, zero_smul,
    add_zero]

/-- Divide a scalar equation between vectors by a nonzero scalar. -/
theorem eq_div_smul_of_smul_eq_smul {leftCoef rightCoef : ℝ} {leftVec rightVec : Fin 3 → ℝ}
    (hleftNe : leftCoef ≠ 0) (heq : leftCoef • leftVec = rightCoef • rightVec) :
    leftVec = (rightCoef / leftCoef) • rightVec := by
  have hscaled := congrArg (fun vec : Fin 3 → ℝ => leftCoef⁻¹ • vec) heq
  simp only [smul_smul, inv_mul_cancel₀ hleftNe, one_smul] at hscaled
  rw [hscaled, div_eq_inv_mul]

/-- The matrix carrying the three given vectors as its COLUMNS. -/
def columnMatrix (colFirst colMid colLast : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (Matrix.of ![colFirst, colMid, colLast])ᵀ

/-- A column matrix applied to a coordinate vector is the column combination. -/
theorem columnMatrix_mulVec (colFirst colMid colLast coord : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ coord
      = coord 0 • colFirst + coord 1 • colMid + coord 2 • colLast := by
  funext row
  simp only [columnMatrix, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Its determinant is the bracket of the columns. -/
theorem det_columnMatrix (colFirst colMid colLast : Fin 3 → ℝ) :
    (columnMatrix colFirst colMid colLast).det = tripleBracket colFirst colMid colLast := by
  rw [columnMatrix, Matrix.det_transpose, tripleBracket]

/-- **The fourth-line relation.**  Three vectors expanded pairwise in a basis,
each missing one basis vector, have a bracket that is a single scalar multiple of
the basis bracket.  This is where the complete quadrilateral's last line becomes
one equation. -/
theorem tripleBracket_of_two_term_expansions (baseFirst baseMid baseLast : Fin 3 → ℝ)
    (coefA coefB coefC coefD coefE coefF : ℝ) (probeFirst probeMid probeLast : Fin 3 → ℝ)
    (hFirst : probeFirst = coefA • baseFirst + coefB • baseMid)
    (hMid : probeMid = coefC • baseFirst + coefD • baseLast)
    (hLast : probeLast = coefE • baseMid + coefF • baseLast) :
    tripleBracket probeFirst probeMid probeLast
      = -((coefA * coefD * coefE + coefB * coefC * coefF)
          * tripleBracket baseFirst baseMid baseLast) := by
  subst hFirst
  subst hMid
  subst hLast
  simp only [tripleBracket_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The M(K4) chart

The six edge vectors of `K4`, labelled so that the four triangles are exactly the
four lines of `Gtz.graphicKFourFamily = [[0,1,2],[0,3,4],[1,3,5],[2,4,5]]`.
Reading labels as edges of `K4` on vertices `a b c d`, `0 = ab`, `1 = ac`,
`2 = bc`, `3 = ad`, `4 = bd`, `5 = cd`, line `{0,1,2}` is the triangle `abc`,
`{0,3,4}` is `abd`, `{1,3,5}` is `acd`, `{2,4,5}` is `bcd`. -/

/-- The K4 edge vectors, in the labelling of `Gtz.graphicKFourFamily`. -/
def kFourDirection : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, -1, 0]
  | 1 => ![1, 0, -1]
  | 2 => ![0, 1, -1]
  | 3 => ![1, 0, 0]
  | 4 => ![0, 1, 0]
  | 5 => ![0, 0, 1]

theorem kFourDirection_zero : kFourDirection 0 = ![1, -1, 0] := rfl
theorem kFourDirection_one : kFourDirection 1 = ![1, 0, -1] := rfl
theorem kFourDirection_two : kFourDirection 2 = ![0, 1, -1] := rfl
theorem kFourDirection_three : kFourDirection 3 = ![1, 0, 0] := rfl
theorem kFourDirection_four : kFourDirection 4 = ![0, 1, 0] := rfl
theorem kFourDirection_five : kFourDirection 5 = ![0, 0, 1] := rfl

/-- **The chart is on the right stratum.**  The K4 edge vectors have dependent
triples EXACTLY the four triangles, so the chart obligation
`Gtz.DirectionChartIsTieFree kFourDirection` is a statement about the `M(K4)` stratum and
not about a degeneration of it. -/
theorem tripleBracket_kFourDirection_eq_zero_iff (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (kFourDirection leftLabel) (kFourDirection midLabel)
        (kFourDirection rightLabel) = 0
      ↔ lineFamilyPattern graphicKFourFamily leftLabel midLabel rightLabel := by
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [kFourDirection, tripleBracket_eq, lineFamilyPattern, graphicKFourFamily]

/-! ### The six column readings -/

theorem columnMatrix_mulVec_kFourZero (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 0 = colFirst - colMid := by
  rw [columnMatrix_mulVec, kFourDirection_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

theorem columnMatrix_mulVec_kFourOne (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 1 = colFirst - colLast := by
  rw [columnMatrix_mulVec, kFourDirection_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

theorem columnMatrix_mulVec_kFourTwo (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 2 = colMid - colLast := by
  rw [columnMatrix_mulVec, kFourDirection_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

theorem columnMatrix_mulVec_kFourThree (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 3 = colFirst := by
  rw [columnMatrix_mulVec, kFourDirection_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

theorem columnMatrix_mulVec_kFourFour (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 4 = colMid := by
  rw [columnMatrix_mulVec, kFourDirection_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

theorem columnMatrix_mulVec_kFourFive (colFirst colMid colLast : Fin 3 → ℝ) :
    columnMatrix colFirst colMid colLast *ᵥ kFourDirection 5 = colLast := by
  rw [columnMatrix_mulVec, kFourDirection_five]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  module

/-- The per-atom scales of the M(K4) realization. -/
noncomputable def kFourScale (coefA coefB coefC coefD coefE bigDelta : ℝ) : Fin 6 → ℝ
  | 0 => 1 / (coefC * bigDelta)
  | 1 => 1 / (coefA * bigDelta)
  | 2 => coefE / (-(coefB * coefC) * bigDelta)
  | 3 => 1 / (coefA * coefC)
  | 4 => 1 / (-(coefB * coefC))
  | 5 => 1 / (-(coefA * coefD))

/-- The per-atom scales of the `#4` realization. -/
noncomputable def threeLinesScale (coefA coefB coefC coefD coefE bigDelta : ℝ) : Fin 6 → ℝ
  | 0 => 1 / (coefA * coefC)
  | 1 => 1 / (coefB * coefC)
  | 2 => 1 / (coefC * bigDelta)
  | 3 => 1 / (coefA * coefD)
  | 4 => 1 / (coefA * bigDelta)
  | 5 => coefE / (coefB * coefC * bigDelta)

/-! ### The construction, from coordinates to the change of basis -/

/-- **The rescaling that fits all six directions at once.**  Given the six
expansion coefficients of a complete quadrilateral in the basis `{3,4,5}`, with
the fourth line's relation `A D E + B C F = 0`, the columns `AC v_3`, `-BC v_4`,
`-AD v_5` realize every direction. -/
theorem exists_realization_of_kFourCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (bigDelta coefA coefB coefC coefD coefE coefF : ℝ)
    (hbracketNe : tripleBracket (vec 3) (vec 4) (vec 5) ≠ 0)
    (hbigDeltaNe : bigDelta ≠ 0)
    (hcoefANe : coefA ≠ 0) (hcoefBNe : coefB ≠ 0) (hcoefCNe : coefC ≠ 0)
    (hcoefDNe : coefD ≠ 0) (hcoefENe : coefE ≠ 0)
    (hexpandZero : bigDelta • vec 0 = coefA • vec 3 + coefB • vec 4)
    (hexpandOne : bigDelta • vec 1 = coefC • vec 3 + coefD • vec 5)
    (hexpandTwo : bigDelta • vec 2 = coefE • vec 4 + coefF • vec 5)
    (hrelation : coefA * coefD * coefE + coefB * coefC * coefF = 0) :
    ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
      IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
        ∀ index, vec index = scale index • (basisChange *ᵥ kFourDirection index) := by
  have hcolFirstNe : coefA * coefC ≠ 0 := mul_ne_zero hcoefANe hcoefCNe
  have hcolMidNe : -(coefB * coefC) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hcoefBNe hcoefCNe)
  have hcolLastNe : -(coefA * coefD) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hcoefANe hcoefDNe)
  refine ⟨columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
      ((-(coefA * coefD)) • vec 5),
    kFourScale coefA coefB coefC coefD coefE bigDelta, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, det_columnMatrix, tripleBracket_smul_slots]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcolFirstNe hcolMidNe) hcolLastNe) hbracketNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_div_ne_zero (mul_ne_zero hcoefCNe hbigDeltaNe)
    · exact one_div_ne_zero (mul_ne_zero hcoefANe hbigDeltaNe)
    · exact div_ne_zero hcoefENe (mul_ne_zero hcolMidNe hbigDeltaNe)
    · exact one_div_ne_zero hcolFirstNe
    · exact one_div_ne_zero hcolMidNe
    · exact one_div_ne_zero hcolLastNe
  · have hzero : vec 0 = kFourScale coefA coefB coefC coefD coefE bigDelta 0 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 0) := by
      refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefCNe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec_kFourZero, mul_smul, hexpandZero]
      module
    have hone : vec 1 = kFourScale coefA coefB coefC coefD coefE bigDelta 1 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 1) := by
      refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefANe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec_kFourOne, mul_smul, hexpandOne]
      module
    have htwo : vec 2 = kFourScale coefA coefB coefC coefD coefE bigDelta 2 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 2) := by
      refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcolMidNe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec_kFourTwo, mul_smul, hexpandTwo]
      match_scalars
      · ring
      · linear_combination -hrelation
    have hthree : vec 3 = kFourScale coefA coefB coefC coefD coefE bigDelta 3 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 3) := by
      refine eq_div_smul_of_smul_eq_smul hcolFirstNe ?_
      rw [columnMatrix_mulVec_kFourThree]
      module
    have hfour : vec 4 = kFourScale coefA coefB coefC coefD coefE bigDelta 4 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 4) := by
      refine eq_div_smul_of_smul_eq_smul hcolMidNe ?_
      rw [columnMatrix_mulVec_kFourFour]
      module
    have hfive : vec 5 = kFourScale coefA coefB coefC coefD coefE bigDelta 5 •
        (columnMatrix ((coefA * coefC) • vec 3) ((-(coefB * coefC)) • vec 4)
          ((-(coefA * coefD)) • vec 5) *ᵥ kFourDirection 5) := by
      refine eq_div_smul_of_smul_eq_smul hcolLastNe ?_
      rw [columnMatrix_mulVec_kFourFive]
      module
    intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hzero
    · exact hone
    · exact htwo
    · exact hthree
    · exact hfour
    · exact hfive

/-- **The coordinates of a complete quadrilateral.**  Six vectors whose dependent
triples are the four K4 triangles, no two parallel, have the six expansion
coefficients above, all five load-bearing ones nonzero, satisfying the
fourth-line relation. -/
theorem exists_kFourCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (hnonparallel : ∀ keptIndex dropIndex : Fin 6, keptIndex ≠ dropIndex →
      ∀ ratio : ℝ, vec dropIndex ≠ ratio • vec keptIndex)
    (hbracketNe : tripleBracket (vec 3) (vec 4) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 3) (vec 4) (vec 0) = 0)
    (hlineThird : tripleBracket (vec 3) (vec 5) (vec 1) = 0)
    (hlineFourth : tripleBracket (vec 4) (vec 5) (vec 2) = 0) :
    ∃ bigDelta coefA coefB coefC coefD coefE coefF : ℝ,
      bigDelta ≠ 0 ∧ coefA ≠ 0 ∧ coefB ≠ 0 ∧ coefC ≠ 0 ∧ coefD ≠ 0 ∧ coefE ≠ 0 ∧
        bigDelta • vec 0 = coefA • vec 3 + coefB • vec 4 ∧
        bigDelta • vec 1 = coefC • vec 3 + coefD • vec 5 ∧
        bigDelta • vec 2 = coefE • vec 4 + coefF • vec 5 ∧
        coefA * coefD * coefE + coefB * coefC * coefF = 0 := by
  have hexpandZero : tripleBracket (vec 3) (vec 4) (vec 5) • vec 0
      = tripleBracket (vec 0) (vec 4) (vec 5) • vec 3
        + tripleBracket (vec 3) (vec 0) (vec 5) • vec 4 :=
    smul_eq_two_term_expansion (vec 3) (vec 4) (vec 5) (vec 0) hlineSecond
  have hexpandOne : tripleBracket (vec 3) (vec 4) (vec 5) • vec 1
      = tripleBracket (vec 1) (vec 4) (vec 5) • vec 3
        + tripleBracket (vec 3) (vec 4) (vec 1) • vec 5 := by
    have hstep := smul_eq_two_term_expansion (vec 3) (vec 5) (vec 4) (vec 1) hlineThird
    rw [show tripleBracket (vec 3) (vec 5) (vec 4)
        = -tripleBracket (vec 3) (vec 4) (vec 5) from tripleBracket_swapRight _ _ _,
      show tripleBracket (vec 1) (vec 5) (vec 4)
        = -tripleBracket (vec 1) (vec 4) (vec 5) from tripleBracket_swapRight _ _ _,
      show tripleBracket (vec 3) (vec 1) (vec 4)
        = -tripleBracket (vec 3) (vec 4) (vec 1) from tripleBracket_swapRight _ _ _] at hstep
    have hnegated := congrArg (fun target : Fin 3 → ℝ => (-1 : ℝ) • target) hstep
    simpa only [smul_add, smul_smul, neg_mul, one_mul, neg_neg] using hnegated
  have hexpandTwo : tripleBracket (vec 3) (vec 4) (vec 5) • vec 2
      = tripleBracket (vec 3) (vec 2) (vec 5) • vec 4
        + tripleBracket (vec 3) (vec 4) (vec 2) • vec 5 := by
    have hstep := smul_eq_two_term_expansion (vec 4) (vec 5) (vec 3) (vec 2) hlineFourth
    rw [show tripleBracket (vec 4) (vec 5) (vec 3)
        = tripleBracket (vec 3) (vec 4) (vec 5) from
      ((tripleBracket_rotate (vec 3) (vec 4) (vec 5)).symm),
      show tripleBracket (vec 2) (vec 5) (vec 3)
        = tripleBracket (vec 3) (vec 2) (vec 5) from by
          rw [tripleBracket_rotate (vec 3) (vec 2) (vec 5),
            tripleBracket_rotate (vec 2) (vec 5) (vec 3)],
      show tripleBracket (vec 4) (vec 2) (vec 3)
        = tripleBracket (vec 3) (vec 4) (vec 2) from by
          rw [tripleBracket_rotate (vec 3) (vec 4) (vec 2),
            tripleBracket_rotate (vec 4) (vec 2) (vec 3)]] at hstep
    exact hstep
  have hcollapse : ∀ (dropIndex keptIndex : Fin 6) (coefficient : ℝ), dropIndex ≠ keptIndex →
      tripleBracket (vec 3) (vec 4) (vec 5) • vec dropIndex = coefficient • vec keptIndex →
      False := by
    intro dropIndex keptIndex coefficient hne hcollapsed
    exact hnonparallel keptIndex dropIndex (Ne.symm hne)
      (coefficient / tripleBracket (vec 3) (vec 4) (vec 5))
      (eq_div_smul_of_smul_eq_smul hbracketNe hcollapsed)
  have hcoefANe : tripleBracket (vec 0) (vec 4) (vec 5) ≠ 0 := by
    intro hzero
    exact hcollapse 0 4 (tripleBracket (vec 3) (vec 0) (vec 5)) (by decide)
      (by rw [hexpandZero, hzero, zero_smul, zero_add])
  have hcoefBNe : tripleBracket (vec 3) (vec 0) (vec 5) ≠ 0 := by
    intro hzero
    exact hcollapse 0 3 (tripleBracket (vec 0) (vec 4) (vec 5)) (by decide)
      (by rw [hexpandZero, hzero, zero_smul, add_zero])
  have hcoefCNe : tripleBracket (vec 1) (vec 4) (vec 5) ≠ 0 := by
    intro hzero
    exact hcollapse 1 5 (tripleBracket (vec 3) (vec 4) (vec 1)) (by decide)
      (by rw [hexpandOne, hzero, zero_smul, zero_add])
  have hcoefDNe : tripleBracket (vec 3) (vec 4) (vec 1) ≠ 0 := by
    intro hzero
    exact hcollapse 1 3 (tripleBracket (vec 1) (vec 4) (vec 5)) (by decide)
      (by rw [hexpandOne, hzero, zero_smul, add_zero])
  have hcoefENe : tripleBracket (vec 3) (vec 2) (vec 5) ≠ 0 := by
    intro hzero
    exact hcollapse 2 5 (tripleBracket (vec 3) (vec 4) (vec 2)) (by decide)
      (by rw [hexpandTwo, hzero, zero_smul, zero_add])
  refine ⟨tripleBracket (vec 3) (vec 4) (vec 5), tripleBracket (vec 0) (vec 4) (vec 5),
    tripleBracket (vec 3) (vec 0) (vec 5), tripleBracket (vec 1) (vec 4) (vec 5),
    tripleBracket (vec 3) (vec 4) (vec 1), tripleBracket (vec 3) (vec 2) (vec 5),
    tripleBracket (vec 3) (vec 4) (vec 2),
    hbracketNe, hcoefANe, hcoefBNe, hcoefCNe, hcoefDNe, hcoefENe,
    hexpandZero, hexpandOne, hexpandTwo, ?_⟩
  have hcubed : tripleBracket (tripleBracket (vec 3) (vec 4) (vec 5) • vec 0)
      (tripleBracket (vec 3) (vec 4) (vec 5) • vec 1)
      (tripleBracket (vec 3) (vec 4) (vec 5) • vec 2) = 0 := by
    rw [tripleBracket_smul_slots, hlineFirst, mul_zero]
  rw [tripleBracket_of_two_term_expansions (vec 3) (vec 4) (vec 5)
    (tripleBracket (vec 0) (vec 4) (vec 5)) (tripleBracket (vec 3) (vec 0) (vec 5))
    (tripleBracket (vec 1) (vec 4) (vec 5)) (tripleBracket (vec 3) (vec 4) (vec 1))
    (tripleBracket (vec 3) (vec 2) (vec 5)) (tripleBracket (vec 3) (vec 4) (vec 2))
    _ _ _ hexpandZero hexpandOne hexpandTwo] at hcubed
  rcases mul_eq_zero.mp (neg_eq_zero.mp hcubed) with hleft | hright
  · exact hleft
  · exact absurd hright hbracketNe

/-! ## The M(K4) covering -/

/-- **THE M(K4) RIGIDITY THEOREM, on bare vectors.**  Six pairwise non-parallel
vectors whose dependent triples are the four triangles of `K4` are the K4 edge
vectors up to one invertible change of basis and one scalar each. -/
theorem exists_kFourRealization_of_brackets (vec : Fin 6 → (Fin 3 → ℝ))
    (hnonparallel : ∀ keptIndex dropIndex : Fin 6, keptIndex ≠ dropIndex →
      ∀ ratio : ℝ, vec dropIndex ≠ ratio • vec keptIndex)
    (hbracketNe : tripleBracket (vec 3) (vec 4) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 3) (vec 4) (vec 0) = 0)
    (hlineThird : tripleBracket (vec 3) (vec 5) (vec 1) = 0)
    (hlineFourth : tripleBracket (vec 4) (vec 5) (vec 2) = 0) :
    ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
      IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
        ∀ index, vec index = scale index • (basisChange *ᵥ kFourDirection index) := by
  obtain ⟨bigDelta, coefA, coefB, coefC, coefD, coefE, coefF, hbigDeltaNe, hcoefANe,
    hcoefBNe, hcoefCNe, hcoefDNe, hcoefENe, hexpandZero, hexpandOne, hexpandTwo, hrelation⟩ :=
    exists_kFourCoordinates vec hnonparallel hbracketNe hlineFirst hlineSecond hlineThird
      hlineFourth
  exact exists_realization_of_kFourCoordinates vec bigDelta coefA coefB coefC coefD coefE coefF
    hbracketNe hbigDeltaNe hcoefANe hcoefBNe hcoefCNe hcoefDNe hcoefENe hexpandZero hexpandOne
    hexpandTwo hrelation

/-- **THE M(K4) COVERING.**  Every primitive `(6,3)` design realizing the `M(K4)`
line pattern, under any relabelling, sits on the K4 chart.  Stress-freeness is
not used. -/
theorem directionChartCoversPrimitiveStratum_kFourDirection :
    DirectionChartCoversPrimitiveStratum kFourDirection (lineFamilyPattern graphicKFourFamily) := by
  intro design relabel hprimitive hpattern
  have hsymmNe : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      relabel.symm leftIndex ≠ relabel.symm rightIndex := by
    intro leftIndex rightIndex hne heq
    exact hne (by simpa using congrArg relabel heq)
  have hbracket : ∀ leftIndex midIndex rightIndex : Fin 6,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
      (tripleBracket (design.atom (relabel.symm leftIndex))
          (design.atom (relabel.symm midIndex)) (design.atom (relabel.symm rightIndex)) = 0
        ↔ lineFamilyPattern graphicKFourFamily leftIndex midIndex rightIndex) := by
    intro leftIndex midIndex rightIndex hleftMid hleftRight hmidRight
    have hraw := hpattern (relabel.symm leftIndex) (relabel.symm midIndex)
      (relabel.symm rightIndex) (hsymmNe _ _ hleftMid) (hsymmNe _ _ hleftRight)
      (hsymmNe _ _ hmidRight)
    simpa only [atomBracket, Equiv.apply_symm_apply] using hraw
  obtain ⟨basisChange, scale, hunit, hscaleNe, hrealize⟩ :=
    exists_kFourRealization_of_brackets (fun index => design.atom (relabel.symm index))
      (fun keptIndex dropIndex hne ratio =>
        hprimitive (relabel.symm keptIndex) (relabel.symm dropIndex) ratio (hsymmNe _ _ hne))
      (fun hzero => (by decide : ¬ lineFamilyPattern graphicKFourFamily 3 4 5)
        ((hbracket 3 4 5 (by decide) (by decide) (by decide)).mp hzero))
      ((hbracket 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 3 4 0 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 3 5 1 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 4 5 2 (by decide) (by decide) (by decide)).mpr (by decide))
  refine ⟨basisChange, fun label => scale (relabel label), hunit,
    fun label => hscaleNe (relabel label), fun label => ?_⟩
  have hstep := hrealize (relabel label)
  rwa [Equiv.symm_apply_apply] at hstep

/-! ## The assembled instance -/

/-- **THE M(K4) STRATUM OBLIGATION FROM THE CHART.**  Tie-freeness of the K4
chart — a statement about eleven positive numbers against six fixed rational
direction vectors — gives the tree's residual obligation for entry `#5` of
`Gtz.stressFreeResidualFamiliesSix`. -/
theorem stressFreeStratumIsTieFree_graphicKFour_of_chart
    (hchart : DirectionChartIsTieFree kFourDirection) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  stressFreeStratumIsTieFree_of_directionChart hchart directionChartCoversPrimitiveStratum_kFourDirection

/-- The same, from the stronger strict-triple form the certificates measure. -/
theorem stressFreeStratumIsTieFree_graphicKFour_of_strictTriple
    (hstrict : DirectionChartHasStrictTriple kFourDirection) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  stressFreeStratumIsTieFree_graphicKFour_of_chart
    (directionChartIsTieFree_of_hasStrictTriple hstrict)

/-! ## The `#4` chart: three three-point lines, moduli dimension one

Entry `#4` of `Gtz.stressFreeResidualFamiliesSix` is
`[[0,1,2],[0,3,4],[1,3,5]]` — three three-point lines, pairwise meeting.  Its
realization space is ONE parameter wide: the triangle `0, 1, 3` can be normalized
to the coordinate frame, the inserted atoms `2` and `4` to `(1,1,0)` and
`(1,0,1)`, and the last freedom is where `5` sits on the line through `1` and `3`.

The two excluded parameter values are the two ways the stratum degenerates:
`s = 0` makes atom `5` parallel to atom `1` (a parallel pair, forbidden by
primitivity), and `s = -1` makes `{2,4,5}` collinear, which is the `M(K4)`
interface — a DIFFERENT pattern, forbidden because `Gtz.HasLinePattern` is an
iff.  Both exclusions are PROVED below, not assumed: they come out of the
covering as `Gtz.IsAdmissibleThreeLinesParameter`. -/

/-- The `#4` directions: the triangle `0, 1, 3` in the coordinate frame, the
inserted atoms `2` and `4` fixed, and atom `5` sliding along the line `1 3`. -/
def threeLinesDirection (slide : ℝ) : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, 1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, 1]
  | 5 => ![0, 1, slide]

theorem threeLinesDirection_zero (slide : ℝ) : threeLinesDirection slide 0 = ![1, 0, 0] := rfl
theorem threeLinesDirection_one (slide : ℝ) : threeLinesDirection slide 1 = ![0, 1, 0] := rfl
theorem threeLinesDirection_two (slide : ℝ) : threeLinesDirection slide 2 = ![1, 1, 0] := rfl
theorem threeLinesDirection_three (slide : ℝ) : threeLinesDirection slide 3 = ![0, 0, 1] := rfl
theorem threeLinesDirection_four (slide : ℝ) : threeLinesDirection slide 4 = ![1, 0, 1] := rfl
theorem threeLinesDirection_five (slide : ℝ) :
    threeLinesDirection slide 5 = ![0, 1, slide] := rfl

/-- The two forbidden slides: `0` collapses atom `5` onto atom `1`, `-1` makes
`{2,4,5}` a fourth line and lands on `M(K4)`. -/
def IsAdmissibleThreeLinesParameter (slide : ℝ) : Prop := slide ≠ 0 ∧ slide ≠ -1

/-- The three-line family of entry `#4`. -/
def threeLinesFamily : List (List (Fin 6)) := [[0, 1, 2], [0, 3, 4], [1, 3, 5]]

set_option maxHeartbeats 1000000 in
/-- **The `#4` chart is on the right stratum**, for every admissible slide: the
dependent triples are exactly the three listed lines.  The degenerate label
triples are dispatched first, so only the one hundred and twenty genuinely
distinct ones reach the arithmetic. -/
theorem tripleBracket_threeLinesDirection_eq_zero_iff (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (leftLabel midLabel rightLabel : Fin 6)
    (hleftMid : leftLabel ≠ midLabel) (hleftRight : leftLabel ≠ rightLabel)
    (hmidRight : midLabel ≠ rightLabel) :
    tripleBracket (threeLinesDirection slide leftLabel) (threeLinesDirection slide midLabel)
        (threeLinesDirection slide rightLabel) = 0
      ↔ lineFamilyPattern threeLinesFamily leftLabel midLabel rightLabel := by
  obtain ⟨hslideNe, hslideNeNegOne⟩ := hadmissible
  have hsuccNe : slide + 1 ≠ 0 := fun hzero => hslideNeNegOne (by linarith)
  rcases fin_six_cases leftLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin_six_cases midLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases fin_six_cases rightLabel with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | (simp [threeLinesDirection, tripleBracket_eq, lineFamilyPattern, threeLinesFamily,
              hslideNe, hsuccNe] <;>
              (intro hslideZero; exact hslideNeNegOne (by linarith)))

/-- **The coordinates of a three-line configuration.**  Six pairwise non-parallel
vectors whose dependent triples are the three lines of entry `#4` have six
expansion coefficients in the basis `{0,1,3}`, all nonzero, whose combination
`A D E + B C F` is nonzero because `{2,4,5}` is NOT a line. -/
theorem exists_threeLinesCoordinates (vec : Fin 6 → (Fin 3 → ℝ))
    (hnonparallel : ∀ keptIndex dropIndex : Fin 6, keptIndex ≠ dropIndex →
      ∀ ratio : ℝ, vec dropIndex ≠ ratio • vec keptIndex)
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hoffLineNe : tripleBracket (vec 2) (vec 4) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 0) (vec 3) (vec 4) = 0)
    (hlineThird : tripleBracket (vec 1) (vec 3) (vec 5) = 0) :
    ∃ bigDelta coefA coefB coefC coefD coefE coefF : ℝ,
      bigDelta ≠ 0 ∧ coefA ≠ 0 ∧ coefB ≠ 0 ∧ coefC ≠ 0 ∧ coefD ≠ 0 ∧ coefE ≠ 0 ∧
        coefF ≠ 0 ∧ coefA * coefD * coefE + coefB * coefC * coefF ≠ 0 ∧
        bigDelta • vec 2 = coefA • vec 0 + coefB • vec 1 ∧
        bigDelta • vec 4 = coefC • vec 0 + coefD • vec 3 ∧
        bigDelta • vec 5 = coefE • vec 1 + coefF • vec 3 := by
  have hexpandTwo : tripleBracket (vec 0) (vec 1) (vec 3) • vec 2
      = tripleBracket (vec 2) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 2) (vec 3) • vec 1 :=
    smul_eq_two_term_expansion (vec 0) (vec 1) (vec 3) (vec 2) hlineFirst
  have hexpandFour : tripleBracket (vec 0) (vec 1) (vec 3) • vec 4
      = tripleBracket (vec 4) (vec 1) (vec 3) • vec 0
        + tripleBracket (vec 0) (vec 1) (vec 4) • vec 3 := by
    have hstep := smul_eq_two_term_expansion (vec 0) (vec 3) (vec 1) (vec 4) hlineSecond
    rw [show tripleBracket (vec 0) (vec 3) (vec 1)
        = -tripleBracket (vec 0) (vec 1) (vec 3) from tripleBracket_swapRight _ _ _,
      show tripleBracket (vec 4) (vec 3) (vec 1)
        = -tripleBracket (vec 4) (vec 1) (vec 3) from tripleBracket_swapRight _ _ _,
      show tripleBracket (vec 0) (vec 4) (vec 1)
        = -tripleBracket (vec 0) (vec 1) (vec 4) from tripleBracket_swapRight _ _ _] at hstep
    have hnegated := congrArg (fun target : Fin 3 → ℝ => (-1 : ℝ) • target) hstep
    simpa only [smul_add, smul_smul, neg_mul, one_mul, neg_neg] using hnegated
  have hexpandFive : tripleBracket (vec 0) (vec 1) (vec 3) • vec 5
      = tripleBracket (vec 0) (vec 5) (vec 3) • vec 1
        + tripleBracket (vec 0) (vec 1) (vec 5) • vec 3 := by
    have hstep := smul_eq_two_term_expansion (vec 1) (vec 3) (vec 0) (vec 5) hlineThird
    rw [show tripleBracket (vec 1) (vec 3) (vec 0)
        = tripleBracket (vec 0) (vec 1) (vec 3) from
      (tripleBracket_rotate (vec 0) (vec 1) (vec 3)).symm,
      show tripleBracket (vec 5) (vec 3) (vec 0)
        = tripleBracket (vec 0) (vec 5) (vec 3) from
      (tripleBracket_rotate (vec 0) (vec 5) (vec 3)).symm,
      show tripleBracket (vec 1) (vec 5) (vec 0)
        = tripleBracket (vec 0) (vec 1) (vec 5) from
      (tripleBracket_rotate (vec 0) (vec 1) (vec 5)).symm] at hstep
    exact hstep
  have hcollapse : ∀ (dropIndex keptIndex : Fin 6) (coefficient : ℝ), dropIndex ≠ keptIndex →
      tripleBracket (vec 0) (vec 1) (vec 3) • vec dropIndex = coefficient • vec keptIndex →
      False := by
    intro dropIndex keptIndex coefficient hne hcollapsed
    exact hnonparallel keptIndex dropIndex (Ne.symm hne)
      (coefficient / tripleBracket (vec 0) (vec 1) (vec 3))
      (eq_div_smul_of_smul_eq_smul hbasisNe hcollapsed)
  have hcoefANe : tripleBracket (vec 2) (vec 1) (vec 3) ≠ 0 := fun hzero =>
    hcollapse 2 1 (tripleBracket (vec 0) (vec 2) (vec 3)) (by decide)
      (by rw [hexpandTwo, hzero, zero_smul, zero_add])
  have hcoefBNe : tripleBracket (vec 0) (vec 2) (vec 3) ≠ 0 := fun hzero =>
    hcollapse 2 0 (tripleBracket (vec 2) (vec 1) (vec 3)) (by decide)
      (by rw [hexpandTwo, hzero, zero_smul, add_zero])
  have hcoefCNe : tripleBracket (vec 4) (vec 1) (vec 3) ≠ 0 := fun hzero =>
    hcollapse 4 3 (tripleBracket (vec 0) (vec 1) (vec 4)) (by decide)
      (by rw [hexpandFour, hzero, zero_smul, zero_add])
  have hcoefDNe : tripleBracket (vec 0) (vec 1) (vec 4) ≠ 0 := fun hzero =>
    hcollapse 4 0 (tripleBracket (vec 4) (vec 1) (vec 3)) (by decide)
      (by rw [hexpandFour, hzero, zero_smul, add_zero])
  have hcoefENe : tripleBracket (vec 0) (vec 5) (vec 3) ≠ 0 := fun hzero =>
    hcollapse 5 3 (tripleBracket (vec 0) (vec 1) (vec 5)) (by decide)
      (by rw [hexpandFive, hzero, zero_smul, zero_add])
  have hcoefFNe : tripleBracket (vec 0) (vec 1) (vec 5) ≠ 0 := fun hzero =>
    hcollapse 5 1 (tripleBracket (vec 0) (vec 5) (vec 3)) (by decide)
      (by rw [hexpandFive, hzero, zero_smul, add_zero])
  refine ⟨tripleBracket (vec 0) (vec 1) (vec 3), tripleBracket (vec 2) (vec 1) (vec 3),
    tripleBracket (vec 0) (vec 2) (vec 3), tripleBracket (vec 4) (vec 1) (vec 3),
    tripleBracket (vec 0) (vec 1) (vec 4), tripleBracket (vec 0) (vec 5) (vec 3),
    tripleBracket (vec 0) (vec 1) (vec 5),
    hbasisNe, hcoefANe, hcoefBNe, hcoefCNe, hcoefDNe, hcoefENe, hcoefFNe, ?_,
    hexpandTwo, hexpandFour, hexpandFive⟩
  intro hsumZero
  have hcubed := tripleBracket_smul_slots (tripleBracket (vec 0) (vec 1) (vec 3))
    (tripleBracket (vec 0) (vec 1) (vec 3)) (tripleBracket (vec 0) (vec 1) (vec 3))
    (vec 2) (vec 4) (vec 5)
  rw [tripleBracket_of_two_term_expansions (vec 0) (vec 1) (vec 3)
    (tripleBracket (vec 2) (vec 1) (vec 3)) (tripleBracket (vec 0) (vec 2) (vec 3))
    (tripleBracket (vec 4) (vec 1) (vec 3)) (tripleBracket (vec 0) (vec 1) (vec 4))
    (tripleBracket (vec 0) (vec 5) (vec 3)) (tripleBracket (vec 0) (vec 1) (vec 5))
    _ _ _ hexpandTwo hexpandFour hexpandFive, hsumZero, zero_mul, neg_zero] at hcubed
  rcases mul_eq_zero.mp hcubed.symm with hleft | hright
  · exact absurd hleft (mul_ne_zero (mul_ne_zero hbasisNe hbasisNe) hbasisNe)
  · exact hoffLineNe hright

/-- **THE `#4` RIGIDITY THEOREM, on bare vectors.**  The slide parameter is
`(B C F) / (A D E)`, read off the coordinates; the two forbidden values fall out
of the nonvanishing of the coefficients and of `{2,4,5}`. -/
theorem exists_threeLinesRealization_of_brackets (vec : Fin 6 → (Fin 3 → ℝ))
    (hnonparallel : ∀ keptIndex dropIndex : Fin 6, keptIndex ≠ dropIndex →
      ∀ ratio : ℝ, vec dropIndex ≠ ratio • vec keptIndex)
    (hbasisNe : tripleBracket (vec 0) (vec 1) (vec 3) ≠ 0)
    (hoffLineNe : tripleBracket (vec 2) (vec 4) (vec 5) ≠ 0)
    (hlineFirst : tripleBracket (vec 0) (vec 1) (vec 2) = 0)
    (hlineSecond : tripleBracket (vec 0) (vec 3) (vec 4) = 0)
    (hlineThird : tripleBracket (vec 1) (vec 3) (vec 5) = 0) :
    ∃ slide : ℝ, IsAdmissibleThreeLinesParameter slide ∧
      ∃ basisChange : Matrix (Fin 3) (Fin 3) ℝ, ∃ scale : Fin 6 → ℝ,
        IsUnit basisChange.det ∧ (∀ index, scale index ≠ 0) ∧
          ∀ index, vec index = scale index • (basisChange *ᵥ threeLinesDirection slide index) := by
  obtain ⟨bigDelta, coefA, coefB, coefC, coefD, coefE, coefF, hbigDeltaNe, hcoefANe, hcoefBNe,
    hcoefCNe, hcoefDNe, hcoefENe, hcoefFNe, hsumNe, hexpandTwo, hexpandFour, hexpandFive⟩ :=
    exists_threeLinesCoordinates vec hnonparallel hbasisNe hoffLineNe hlineFirst hlineSecond
      hlineThird
  have hdenominatorNe : coefA * coefD * coefE ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcoefANe hcoefDNe) hcoefENe
  have hnumeratorNe : coefB * coefC * coefF ≠ 0 :=
    mul_ne_zero (mul_ne_zero hcoefBNe hcoefCNe) hcoefFNe
  have hcolFirstNe : coefA * coefC ≠ 0 := mul_ne_zero hcoefANe hcoefCNe
  have hcolMidNe : coefB * coefC ≠ 0 := mul_ne_zero hcoefBNe hcoefCNe
  have hcolLastNe : coefA * coefD ≠ 0 := mul_ne_zero hcoefANe hcoefDNe
  -- The slide is pinned by ONE polynomial identity; naming it that way keeps every
  -- downstream step division-free.
  obtain ⟨slide, hslideSpec⟩ : ∃ slide : ℝ,
      coefE * (slide * (coefA * coefD)) = coefB * coefC * coefF :=
    ⟨coefB * coefC * coefF / (coefA * coefD * coefE), by field_simp⟩
  have hslideNe : slide ≠ 0 := by
    intro hzero
    refine hnumeratorNe ?_
    rw [hzero] at hslideSpec
    linear_combination -hslideSpec
  have hslideNeNegOne : slide ≠ -1 := by
    intro hnegOne
    refine hsumNe ?_
    rw [hnegOne] at hslideSpec
    linear_combination -hslideSpec
  refine ⟨slide, ⟨hslideNe, hslideNeNegOne⟩,
    columnMatrix ((coefA * coefC) • vec 0) ((coefB * coefC) • vec 1) ((coefA * coefD) • vec 3),
    fun index => (threeLinesScale coefA coefB coefC coefD coefE bigDelta) index, ?_, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero, det_columnMatrix, tripleBracket_smul_slots]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcolFirstNe hcolMidNe) hcolLastNe) hbasisNe
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_div_ne_zero hcolFirstNe
    · exact one_div_ne_zero hcolMidNe
    · exact one_div_ne_zero (mul_ne_zero hcoefCNe hbigDeltaNe)
    · exact one_div_ne_zero hcolLastNe
    · exact one_div_ne_zero (mul_ne_zero hcoefANe hbigDeltaNe)
    · exact div_ne_zero hcoefENe (mul_ne_zero hcolMidNe hbigDeltaNe)
  · intro index
    rcases fin_six_cases index with rfl | rfl | rfl | rfl | rfl | rfl
    · refine eq_div_smul_of_smul_eq_smul hcolFirstNe ?_
      rw [columnMatrix_mulVec, threeLinesDirection_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul hcolMidNe ?_
      rw [columnMatrix_mulVec, threeLinesDirection_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefCNe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec, threeLinesDirection_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandTwo]
      module
    · refine eq_div_smul_of_smul_eq_smul hcolLastNe ?_
      rw [columnMatrix_mulVec, threeLinesDirection_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcoefANe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec, threeLinesDirection_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFour]
      module
    · refine eq_div_smul_of_smul_eq_smul (mul_ne_zero hcolMidNe hbigDeltaNe) ?_
      rw [columnMatrix_mulVec, threeLinesDirection_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [mul_smul, hexpandFive]
      match_scalars <;> first | ring1 | linear_combination -hslideSpec

/-- **THE `#4` COVERING.**  Every primitive design realizing the three-line
pattern sits on the `#4` chart at some admissible slide. -/
theorem parameterizedChartCovers_threeLinesDirection :
    ParameterizedChartCovers threeLinesDirection IsAdmissibleThreeLinesParameter
      (lineFamilyPattern threeLinesFamily) := by
  intro design relabel hprimitive hpattern
  have hsymmNe : ∀ leftIndex rightIndex : Fin 6, leftIndex ≠ rightIndex →
      relabel.symm leftIndex ≠ relabel.symm rightIndex := by
    intro leftIndex rightIndex hne heq
    exact hne (by simpa using congrArg relabel heq)
  have hbracket : ∀ leftIndex midIndex rightIndex : Fin 6,
      leftIndex ≠ midIndex → leftIndex ≠ rightIndex → midIndex ≠ rightIndex →
      (tripleBracket (design.atom (relabel.symm leftIndex))
          (design.atom (relabel.symm midIndex)) (design.atom (relabel.symm rightIndex)) = 0
        ↔ lineFamilyPattern threeLinesFamily leftIndex midIndex rightIndex) := by
    intro leftIndex midIndex rightIndex hleftMid hleftRight hmidRight
    have hraw := hpattern (relabel.symm leftIndex) (relabel.symm midIndex)
      (relabel.symm rightIndex) (hsymmNe _ _ hleftMid) (hsymmNe _ _ hleftRight)
      (hsymmNe _ _ hmidRight)
    simpa only [atomBracket, Equiv.apply_symm_apply] using hraw
  obtain ⟨slide, hadmissible, basisChange, scale, hunit, hscaleNe, hrealize⟩ :=
    exists_threeLinesRealization_of_brackets (fun index => design.atom (relabel.symm index))
      (fun keptIndex dropIndex hne ratio =>
        hprimitive (relabel.symm keptIndex) (relabel.symm dropIndex) ratio (hsymmNe _ _ hne))
      (fun hzero => (by decide : ¬ lineFamilyPattern threeLinesFamily 0 1 3)
        ((hbracket 0 1 3 (by decide) (by decide) (by decide)).mp hzero))
      (fun hzero => (by decide : ¬ lineFamilyPattern threeLinesFamily 2 4 5)
        ((hbracket 2 4 5 (by decide) (by decide) (by decide)).mp hzero))
      ((hbracket 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 0 3 4 (by decide) (by decide) (by decide)).mpr (by decide))
      ((hbracket 1 3 5 (by decide) (by decide) (by decide)).mpr (by decide))
  refine ⟨slide, hadmissible, basisChange, fun label => scale (relabel label), hunit,
    fun label => hscaleNe (relabel label), fun label => ?_⟩
  have hstep := hrealize (relabel label)
  rwa [Equiv.symm_apply_apply] at hstep

/-- **THE `#4` STRATUM OBLIGATION FROM THE CHART.**  Tie-freeness of the one-
parameter `#4` chart at every admissible slide gives the tree's residual
obligation for entry `#4`. -/
theorem stressFreeStratumIsTieFree_threeLines_of_chart
    (hchart : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide)) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) :=
  stressFreeStratumIsTieFree_of_parameterizedChart hchart
    parameterizedChartCovers_threeLinesDirection

/-- The pattern discharged above is entry `#5` of the tree's residual list. -/
theorem graphicKFourFamily_mem_stressFreeResidualFamiliesSix :
    ([[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] : List (List (Fin 6)))
      ∈ stressFreeResidualFamiliesSix := by decide

/-- The four surviving classes the K4 chart does NOT discharge: `U(3,6)`, one
three-point line, two meeting three-point lines, three three-point lines. -/
def nonRigidResidualFamiliesSix : List (List (List (Fin 6))) :=
  [ []
  , [[0, 1, 2]]
  , [[0, 1, 2], [0, 3, 4]]
  , [[0, 1, 2], [0, 3, 4], [1, 3, 5]] ]

/-- **THE HINGE, WITH `M(K4)` MOVED ONTO THE CHART.**  The stress-free hinge now
follows from the standing enumeration input, the four non-rigid classes, and ONE
statement about eleven positive numbers against six fixed rational vectors.  This
is the shape the certificate corpus can discharge. -/
theorem stressFreeHingeHoldsSixThree_of_kFourChart
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hnonRigid : ∀ lines ∈ nonRigidResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines))
    (hchart : DirectionChartIsTieFree kFourDirection) :
    StressFreeHingeHoldsSixThree := by
  refine stressFreeHingeHoldsSixThree_of_residualFamilies hcomplete fun lines hlines => ?_
  simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil, or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl
  · exact hnonRigid _ (by decide)
  · exact hnonRigid _ (by decide)
  · exact hnonRigid _ (by decide)
  · exact hnonRigid _ (by decide)
  · exact stressFreeStratumIsTieFree_graphicKFour_of_chart hchart

/-- The three classes NEITHER chart discharges: `U(3,6)`, one three-point line,
two meeting three-point lines. -/
def chartFreeResidualFamiliesSix : List (List (List (Fin 6))) :=
  [ []
  , [[0, 1, 2]]
  , [[0, 1, 2], [0, 3, 4]] ]

/-- **THE HINGE, WITH BOTH CHARTS IN PLACE.**  Entries `#4` and `#5` — the two
classes whose rigidity is proved here — are moved onto their charts, leaving
three classes and the standing enumeration input. -/
theorem stressFreeHingeHoldsSixThree_of_bothCharts
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hchartFree : ∀ lines ∈ chartFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines))
    (hthreeLinesChart : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hkFourChart : DirectionChartIsTieFree kFourDirection) :
    StressFreeHingeHoldsSixThree := by
  refine stressFreeHingeHoldsSixThree_of_residualFamilies hcomplete fun lines hlines => ?_
  simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil, or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl
  · exact hchartFree _ (by decide)
  · exact hchartFree _ (by decide)
  · exact hchartFree _ (by decide)
  · exact stressFreeStratumIsTieFree_threeLines_of_chart hthreeLinesChart
  · exact stressFreeStratumIsTieFree_graphicKFour_of_chart hkFourChart

end Gtz
