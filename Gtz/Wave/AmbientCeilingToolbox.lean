import Gtz.Wave.CeilingMarginKill
import Gtz.Quantitative.SixThreeCrux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The ambient ceiling toolbox — the full consumer calculus of the block ceiling

The ceiling caps every compressed gap block at the chart objective, and the
margin kill turns a dominated block into a contradiction.  This file builds
the complete ambient interface on top of the two: a branch kill names its
atoms and its scalar inequalities, and the toolbox does everything else.

The layers, from the bottom:

1. **The sparse lift calculus.**  A probe on `Fin k` lifts along an
   injective enumeration into an ambient sparse vector.  The lift keeps
   the dot product and turns the compressed quadratic form into the
   ambient one.  This generalizes the lift of the fully-private-block
   kill and retires the per-module reconstructions.
2. **The ambient margin kill.**  A card-`rank` subset whose ambient gap
   form dominates `margin * |v|^2` with `chartObjective < margin` kills
   the chart point.  The subset enters as a `Finset`, the probes as
   ambient vectors that vanish off the subset.
3. **The domination kills.**  The margin-zero instance: at a negative
   objective no subset chart-dominates.  This subsumes the diagonal-Gram
   conditioning of the corner kills: the certificate is a subset, not a
   matrix identity.
4. **The explicit-triple interface.**  A branch kill names three distinct
   atoms and one scalar inequality in nine gap entries, quantified over
   three real coefficients.  The triple lift discharges the rest.  The
   margin variant carries an explicit margin above the objective.
5. **The parallel combination layer.**  Two directions with a vanishing
   cross determinant on an atom pair combine into a vector that vanishes
   on the pair, stays inside their span, and keeps their joint support
   elsewhere.  This is the entry point of the both-parallel kill: the
   combinations concentrate on the single atoms, and the ceiling then
   reads the concentrated subset.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.sparseLift` with `Gtz.sparseLift_apply_enum`,
  `Gtz.sparseLift_eq_zero_of_forall_ne`, `Gtz.sparseLift_dotProduct_self`,
  `Gtz.sparseLift_dotProduct_mulVec` — **THE LIFT CALCULUS.**
* `Gtz.false_of_gap_margin_of_supported` — **THE AMBIENT MARGIN KILL.**
* `Gtz.false_of_chartDominates_of_negative`,
  `Gtz.SixThreeCrux.false_of_chartDominates` — **THE DOMINATION KILLS.**
* `Gtz.chartPointGap_apply` — the gap entry dictionary.
* `Gtz.card_triple_of_distinct`, `Gtz.notMem_triple` — the triple
  vocabulary.
* `Gtz.tripleLift` with its four value laws,
  `Gtz.tripleLift_dotProduct_self`, `Gtz.tripleLift_dotProduct_mulVec` —
  **THE TRIPLE CALCULUS.**
* `Gtz.SixThreeCrux.false_of_gap_triple_supported`,
  `Gtz.SixThreeCrux.false_of_gap_triple_entries`,
  `Gtz.SixThreeCrux.false_of_gap_triple_margin_entries` — **THE TRIPLE
  KILLS.**
* `Gtz.parallel_combination_apply_pair_left`,
  `Gtz.parallel_combination_apply_pair_right`,
  `Gtz.parallel_combination_apply_of_vanish`,
  `Gtz.parallel_combination_mem_span`,
  `Gtz.eq_smul_of_parallel_combination_eq_zero` — **THE PARALLEL LAYER.**

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
calculus and the chart statements are unconditional.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Layer 1 — the sparse lift calculus -/

/-- The ambient lift of a probe along an enumeration: the coordinate at an
enumerated atom is the probe value, and every other coordinate is zero. -/
noncomputable def sparseLift {liftCount : ℕ} (enum : Fin liftCount → Fin size)
    (probe : Fin liftCount → ℝ) : Fin size → ℝ :=
  fun atomIndex => ∑ liftIndex : Fin liftCount,
    if enum liftIndex = atomIndex then probe liftIndex else 0

/-- The lift reads the probe at each enumerated atom. -/
theorem sparseLift_apply_enum {liftCount : ℕ} {enum : Fin liftCount → Fin size}
    (henum : Function.Injective enum) (probe : Fin liftCount → ℝ)
    (liftIndex : Fin liftCount) :
    sparseLift enum probe (enum liftIndex) = probe liftIndex := by
  simp only [sparseLift]
  rw [Finset.sum_eq_single liftIndex
    (fun otherIndex _ hne => if_neg fun heq => hne (henum heq))
    (fun hnot => absurd (Finset.mem_univ _) hnot)]
  rw [if_pos rfl]

/-- The lift vanishes off the enumeration. -/
theorem sparseLift_eq_zero_of_forall_ne {liftCount : ℕ}
    {enum : Fin liftCount → Fin size} (probe : Fin liftCount → ℝ)
    {atomIndex : Fin size} (hoff : ∀ liftIndex, enum liftIndex ≠ atomIndex) :
    sparseLift enum probe atomIndex = 0 := by
  simp only [sparseLift]
  exact Finset.sum_eq_zero fun liftIndex _ => if_neg (hoff liftIndex)

/-- The lift keeps the dot product. -/
theorem sparseLift_dotProduct_self {liftCount : ℕ}
    {enum : Fin liftCount → Fin size} (henum : Function.Injective enum)
    (probe : Fin liftCount → ℝ) :
    sparseLift enum probe ⬝ᵥ sparseLift enum probe = probe ⬝ᵥ probe := by
  have hstep : ∑ atomIndex ∈ Finset.univ.image enum,
      sparseLift enum probe atomIndex * sparseLift enum probe atomIndex
      = ∑ liftIndex : Fin liftCount,
          sparseLift enum probe (enum liftIndex)
            * sparseLift enum probe (enum liftIndex) :=
    Finset.sum_image fun firstIndex _ secondIndex _ heq => henum heq
  have hfull : sparseLift enum probe ⬝ᵥ sparseLift enum probe
      = ∑ atomIndex ∈ Finset.univ.image enum,
          sparseLift enum probe atomIndex * sparseLift enum probe atomIndex := by
    show (∑ atomIndex : Fin size,
        sparseLift enum probe atomIndex * sparseLift enum probe atomIndex) = _
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    rw [sparseLift_eq_zero_of_forall_ne probe fun liftIndex heq =>
      hnot (Finset.mem_image.mpr ⟨liftIndex, Finset.mem_univ _, heq⟩), zero_mul]
  have hrhs : probe ⬝ᵥ probe
      = ∑ liftIndex : Fin liftCount, probe liftIndex * probe liftIndex := rfl
  rw [hfull, hstep, hrhs]
  refine Finset.sum_congr rfl fun liftIndex _ => ?_
  rw [sparseLift_apply_enum henum]

/-- The lift turns the ambient quadratic form into the compressed one. -/
theorem sparseLift_dotProduct_mulVec {liftCount : ℕ}
    {enum : Fin liftCount → Fin size} (henum : Function.Injective enum)
    (form : Matrix (Fin size) (Fin size) ℝ) (probe : Fin liftCount → ℝ) :
    sparseLift enum probe ⬝ᵥ (form *ᵥ sparseLift enum probe)
      = probe ⬝ᵥ (form.submatrix enum enum *ᵥ probe) := by
  have hinner : ∀ atomIndex : Fin size,
      (form *ᵥ sparseLift enum probe) atomIndex
      = ∑ liftIndex : Fin liftCount,
          form atomIndex (enum liftIndex) * probe liftIndex := by
    intro atomIndex
    show (∑ otherIndex : Fin size,
        form atomIndex otherIndex * sparseLift enum probe otherIndex) = _
    have hrestrict : (∑ otherIndex : Fin size,
        form atomIndex otherIndex * sparseLift enum probe otherIndex)
        = ∑ otherIndex ∈ Finset.univ.image enum,
            form atomIndex otherIndex * sparseLift enum probe otherIndex := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro otherIndex _ hnot
      rw [sparseLift_eq_zero_of_forall_ne probe fun liftIndex heq =>
        hnot (Finset.mem_image.mpr ⟨liftIndex, Finset.mem_univ _, heq⟩), mul_zero]
    have hstep : ∑ otherIndex ∈ Finset.univ.image enum,
        form atomIndex otherIndex * sparseLift enum probe otherIndex
        = ∑ liftIndex : Fin liftCount,
            form atomIndex (enum liftIndex)
              * sparseLift enum probe (enum liftIndex) :=
      Finset.sum_image fun firstIndex _ secondIndex _ heq => henum heq
    rw [hrestrict, hstep]
    refine Finset.sum_congr rfl fun liftIndex _ => ?_
    rw [sparseLift_apply_enum henum]
  have hrhs : probe ⬝ᵥ (form.submatrix enum enum *ᵥ probe)
      = ∑ liftIndex : Fin liftCount, probe liftIndex
          * ∑ innerIndex : Fin liftCount,
              form (enum liftIndex) (enum innerIndex) * probe innerIndex := rfl
  have hstep : ∑ atomIndex ∈ Finset.univ.image enum,
      sparseLift enum probe atomIndex * (form *ᵥ sparseLift enum probe) atomIndex
      = ∑ liftIndex : Fin liftCount,
          sparseLift enum probe (enum liftIndex)
            * (form *ᵥ sparseLift enum probe) (enum liftIndex) :=
    Finset.sum_image fun firstIndex _ secondIndex _ heq => henum heq
  show (∑ atomIndex : Fin size,
      sparseLift enum probe atomIndex
        * (form *ᵥ sparseLift enum probe) atomIndex) = _
  have hrestrict : (∑ atomIndex : Fin size,
      sparseLift enum probe atomIndex
        * (form *ᵥ sparseLift enum probe) atomIndex)
      = ∑ atomIndex ∈ Finset.univ.image enum,
          sparseLift enum probe atomIndex
            * (form *ᵥ sparseLift enum probe) atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    rw [sparseLift_eq_zero_of_forall_ne probe fun liftIndex heq =>
      hnot (Finset.mem_image.mpr ⟨liftIndex, Finset.mem_univ _, heq⟩), zero_mul]
  rw [hrestrict, hstep, hrhs]
  refine Finset.sum_congr rfl fun liftIndex _ => ?_
  rw [sparseLift_apply_enum henum, hinner (enum liftIndex)]

/-! ## Layer 2 — the ambient margin kill -/

/-- **THE AMBIENT MARGIN KILL.**  A card-`rank` subset whose ambient gap
form dominates a margin above the chart objective kills the chart point.
The probes are ambient vectors that vanish off the subset. -/
theorem false_of_gap_margin_of_supported [Nonempty (Fin rank)]
    (point : ChartPoint size rank)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {margin : ℝ} (hgt : chartObjective point < margin)
    (hquad : ∀ probe : Fin size → ℝ,
      (∀ atomIndex, atomIndex ∉ selected → probe atomIndex = 0) →
      margin * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (chartPointGap point *ᵥ probe)) :
    False := by
  have hchartSymm : ∀ rowIndex colIndex,
      point.chart rowIndex colIndex = point.chart colIndex rowIndex := by
    intro rowIndex colIndex
    have hentry := congrFun (congrFun point.isSymmetric colIndex) rowIndex
    rw [Matrix.transpose_apply] at hentry
    exact hentry
  refine false_of_gap_submatrix_margin point hchartSymm hcard hgt ?_
  intro probe
  have henum : Function.Injective (selected.orderEmbOfFin hcard) :=
    (selected.orderEmbOfFin hcard).injective
  have hsupport : ∀ atomIndex, atomIndex ∉ selected →
      sparseLift (selected.orderEmbOfFin hcard) probe atomIndex = 0 := by
    intro atomIndex hnot
    refine sparseLift_eq_zero_of_forall_ne probe fun liftIndex heq => hnot ?_
    have hmem := Finset.orderEmbOfFin_mem selected hcard liftIndex
    rwa [heq] at hmem
  have hbound := hquad (sparseLift (selected.orderEmbOfFin hcard) probe) hsupport
  rw [sparseLift_dotProduct_self henum, sparseLift_dotProduct_mulVec henum]
    at hbound
  rw [chartGapRaw_chartConfig]
  exact hbound

/-! ## Layer 3 — the domination kills -/

/-- **THE DOMINATION KILL.**  At a chart point with a negative objective,
no card-`rank` subset chart-dominates: its block value would be
nonnegative, against the ceiling. -/
theorem false_of_chartDominates_of_negative [Nonempty (Fin rank)]
    (point : ChartPoint size rank) (hneg : chartObjective point < 0)
    {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hdominates : ChartDominates point selected) : False := by
  have hblock :=
    (zero_le_chartBlockValue_iff_chartDominates point hcard).mpr hdominates
  have hceiling := chartBlockValue_le_chartObjective point hcard
  linarith

/-- The crux workhorse: one nonnegative gap block on a card-3 subset of
supported probes kills the crux. -/
theorem SixThreeCrux.false_of_chartDominates (crux : SixThreeCrux)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hdominates : ChartDominates (chartPointOfDesign crux.design) selected) :
    False :=
  false_of_chartDominates_of_negative (chartPointOfDesign crux.design)
    crux.hasNegativeChartValue hcard hdominates

/-- The gap entry dictionary: an entry of the chart gap is the chart entry
minus the diagonal weight. -/
theorem chartPointGap_apply (point : ChartPoint size rank)
    (rowIndex colIndex : Fin size) :
    chartPointGap point rowIndex colIndex
      = point.chart rowIndex colIndex
        - if rowIndex = colIndex then point.weight rowIndex else 0 := by
  rw [chartPointGap, Matrix.sub_apply, Matrix.diagonal_apply]

/-! ## Layer 4 — the explicit-triple interface -/

/-- Three distinct atoms make a card-3 subset. -/
theorem card_triple_of_distinct {x y z : Fin size} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ({x, y, z} : Finset (Fin size)).card = 3 := by
  have hnotx : x ∉ ({y, z} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hxy heq
    · exact hxz (Finset.mem_singleton.mp hmem')
  have hnoty : y ∉ ({z} : Finset (Fin size)) := fun hmem =>
    hyz (Finset.mem_singleton.mp hmem)
  rw [Finset.card_insert_of_notMem hnotx, Finset.card_insert_of_notMem hnoty,
    Finset.card_singleton]

/-- Membership off a triple is the conjunction of the three inequalities. -/
theorem notMem_triple {u x y z : Fin size} :
    u ∉ ({x, y, z} : Finset (Fin size)) ↔ u ≠ x ∧ u ≠ y ∧ u ≠ z := by
  simp [not_or]

/-- The three-coordinate probe: the value at each named atom, zero
elsewhere.  The lift of the scalar interface. -/
def tripleLift (x y z : Fin size) (a b c : ℝ) : Fin size → ℝ :=
  fun atomIndex =>
    if atomIndex = x then a else if atomIndex = y then b
      else if atomIndex = z then c else 0

/-- The triple lift at the first atom. -/
theorem tripleLift_apply_first {x y z : Fin size} {a b c : ℝ} :
    tripleLift x y z a b c x = a := by
  simp [tripleLift]

/-- The triple lift at the second atom. -/
theorem tripleLift_apply_second {x y z : Fin size} {a b c : ℝ} (hxy : x ≠ y) :
    tripleLift x y z a b c y = b := by
  simp [tripleLift, Ne.symm hxy]

/-- The triple lift at the third atom. -/
theorem tripleLift_apply_third {x y z : Fin size} {a b c : ℝ} (hxz : x ≠ z)
    (hyz : y ≠ z) : tripleLift x y z a b c z = c := by
  simp [tripleLift, Ne.symm hxz, Ne.symm hyz]

/-- The triple lift off the triple. -/
theorem tripleLift_apply_off {u x y z : Fin size} {a b c : ℝ} (hux : u ≠ x)
    (huy : u ≠ y) (huz : u ≠ z) : tripleLift x y z a b c u = 0 := by
  simp only [tripleLift]
  rw [if_neg hux, if_neg huy, if_neg huz]

/-- The triple lift keeps the dot product. -/
theorem tripleLift_dotProduct_self {x y z : Fin size} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (a b c : ℝ) :
    tripleLift x y z a b c ⬝ᵥ tripleLift x y z a b c
      = a * a + b * b + c * c := by
  have hnotx : x ∉ ({y, z} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hxy heq
    · exact hxz (Finset.mem_singleton.mp hmem')
  have hnoty : y ∉ ({z} : Finset (Fin size)) := fun hmem =>
    hyz (Finset.mem_singleton.mp hmem)
  show (∑ atomIndex : Fin size,
      tripleLift x y z a b c atomIndex * tripleLift x y z a b c atomIndex) = _
  have hrestrict : (∑ atomIndex : Fin size,
      tripleLift x y z a b c atomIndex * tripleLift x y z a b c atomIndex)
      = ∑ atomIndex ∈ ({x, y, z} : Finset (Fin size)),
          tripleLift x y z a b c atomIndex * tripleLift x y z a b c atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    obtain ⟨hux, huy, huz⟩ := notMem_triple.mp hnot
    rw [tripleLift_apply_off hux huy huz, zero_mul]
  rw [hrestrict, Finset.sum_insert hnotx, Finset.sum_insert hnoty,
    Finset.sum_singleton, tripleLift_apply_first, tripleLift_apply_second hxy,
    tripleLift_apply_third hxz hyz]
  ring

/-- **THE TRIPLE EXPANSION.**  The ambient quadratic form of the triple
lift is the nine-entry scalar form on the three named atoms. -/
theorem tripleLift_dotProduct_mulVec {x y z : Fin size} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (form : Matrix (Fin size) (Fin size) ℝ)
    (a b c : ℝ) :
    tripleLift x y z a b c ⬝ᵥ (form *ᵥ tripleLift x y z a b c)
      = a * (form x x * a + form x y * b + form x z * c)
        + b * (form y x * a + form y y * b + form y z * c)
        + c * (form z x * a + form z y * b + form z z * c) := by
  have hnotx : x ∉ ({y, z} : Finset (Fin size)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with heq | hmem'
    · exact hxy heq
    · exact hxz (Finset.mem_singleton.mp hmem')
  have hnoty : y ∉ ({z} : Finset (Fin size)) := fun hmem =>
    hyz (Finset.mem_singleton.mp hmem)
  have hinner : ∀ atomIndex : Fin size,
      (form *ᵥ tripleLift x y z a b c) atomIndex
      = form atomIndex x * a + form atomIndex y * b + form atomIndex z * c := by
    intro atomIndex
    show (∑ otherIndex : Fin size,
        form atomIndex otherIndex * tripleLift x y z a b c otherIndex) = _
    have hrestrict : (∑ otherIndex : Fin size,
        form atomIndex otherIndex * tripleLift x y z a b c otherIndex)
        = ∑ otherIndex ∈ ({x, y, z} : Finset (Fin size)),
            form atomIndex otherIndex * tripleLift x y z a b c otherIndex := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro otherIndex _ hnot
      obtain ⟨hux, huy, huz⟩ := notMem_triple.mp hnot
      rw [tripleLift_apply_off hux huy huz, mul_zero]
    rw [hrestrict, Finset.sum_insert hnotx, Finset.sum_insert hnoty,
      Finset.sum_singleton, tripleLift_apply_first,
      tripleLift_apply_second hxy, tripleLift_apply_third hxz hyz]
    ring
  show (∑ atomIndex : Fin size, tripleLift x y z a b c atomIndex
      * (form *ᵥ tripleLift x y z a b c) atomIndex) = _
  have hrestrict : (∑ atomIndex : Fin size, tripleLift x y z a b c atomIndex
      * (form *ᵥ tripleLift x y z a b c) atomIndex)
      = ∑ atomIndex ∈ ({x, y, z} : Finset (Fin size)),
          tripleLift x y z a b c atomIndex
            * (form *ᵥ tripleLift x y z a b c) atomIndex := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro atomIndex _ hnot
    obtain ⟨hux, huy, huz⟩ := notMem_triple.mp hnot
    rw [tripleLift_apply_off hux huy huz, zero_mul]
  rw [hrestrict, Finset.sum_insert hnotx, Finset.sum_insert hnoty,
    Finset.sum_singleton, tripleLift_apply_first, tripleLift_apply_second hxy,
    tripleLift_apply_third hxz hyz, hinner x, hinner y, hinner z]
  ring

/-- **THE SUPPORTED TRIPLE KILL.**  Three distinct atoms whose ambient gap
form is nonnegative on the supported probes kill the crux. -/
theorem SixThreeCrux.false_of_gap_triple_supported (crux : SixThreeCrux)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hquad : ∀ probe : Fin 6 → ℝ,
      (∀ atomIndex, atomIndex ≠ x → atomIndex ≠ y → atomIndex ≠ z →
        probe atomIndex = 0) →
      0 ≤ probe ⬝ᵥ (chartPointGap (chartPointOfDesign crux.design) *ᵥ probe)) :
    False := by
  refine false_of_gap_margin_of_supported (chartPointOfDesign crux.design)
    (card_triple_of_distinct hxy hxz hyz) (margin := 0)
    crux.hasNegativeChartValue ?_
  intro probe hsupport
  rw [zero_mul]
  refine hquad probe fun atomIndex hux huy huz => hsupport atomIndex ?_
  exact notMem_triple.mpr ⟨hux, huy, huz⟩

/-- Every probe supported on a triple IS a triple lift. -/
theorem eq_tripleLift_of_supported {x y z : Fin size} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) {probe : Fin size → ℝ}
    (hsupport : ∀ atomIndex, atomIndex ≠ x → atomIndex ≠ y → atomIndex ≠ z →
      probe atomIndex = 0) :
    tripleLift x y z (probe x) (probe y) (probe z) = probe := by
  funext atomIndex
  by_cases hux : atomIndex = x
  · rw [hux, tripleLift_apply_first]
  · by_cases huy : atomIndex = y
    · rw [huy, tripleLift_apply_second hxy]
    · by_cases huz : atomIndex = z
      · rw [huz, tripleLift_apply_third hxz hyz]
      · rw [tripleLift_apply_off hux huy huz, hsupport atomIndex hux huy huz]

/-- **THE ENTRY TRIPLE KILL.**  Three distinct atoms and one scalar
inequality in the nine gap entries kill the crux.  This is the interface
a branch kill consumes: name the atoms, prove the inequality. -/
theorem SixThreeCrux.false_of_gap_triple_entries (crux : SixThreeCrux)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hquad : ∀ a b c : ℝ,
      0 ≤ a * (chartPointGap (chartPointOfDesign crux.design) x x * a
            + chartPointGap (chartPointOfDesign crux.design) x y * b
            + chartPointGap (chartPointOfDesign crux.design) x z * c)
        + b * (chartPointGap (chartPointOfDesign crux.design) y x * a
            + chartPointGap (chartPointOfDesign crux.design) y y * b
            + chartPointGap (chartPointOfDesign crux.design) y z * c)
        + c * (chartPointGap (chartPointOfDesign crux.design) z x * a
            + chartPointGap (chartPointOfDesign crux.design) z y * b
            + chartPointGap (chartPointOfDesign crux.design) z z * c)) :
    False := by
  refine crux.false_of_gap_triple_supported hxy hxz hyz ?_
  intro probe hsupport
  rw [← eq_tripleLift_of_supported hxy hxz hyz hsupport,
    tripleLift_dotProduct_mulVec hxy hxz hyz]
  exact hquad (probe x) (probe y) (probe z)

/-- **THE MARGIN TRIPLE KILL.**  The entry interface with an explicit
margin above the objective: the nine-entry form dominates
`margin * (a^2 + b^2 + c^2)`. -/
theorem SixThreeCrux.false_of_gap_triple_margin_entries (crux : SixThreeCrux)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {margin : ℝ}
    (hgt : chartObjective (chartPointOfDesign crux.design) < margin)
    (hquad : ∀ a b c : ℝ,
      margin * (a * a + b * b + c * c)
        ≤ a * (chartPointGap (chartPointOfDesign crux.design) x x * a
            + chartPointGap (chartPointOfDesign crux.design) x y * b
            + chartPointGap (chartPointOfDesign crux.design) x z * c)
        + b * (chartPointGap (chartPointOfDesign crux.design) y x * a
            + chartPointGap (chartPointOfDesign crux.design) y y * b
            + chartPointGap (chartPointOfDesign crux.design) y z * c)
        + c * (chartPointGap (chartPointOfDesign crux.design) z x * a
            + chartPointGap (chartPointOfDesign crux.design) z y * b
            + chartPointGap (chartPointOfDesign crux.design) z z * c)) :
    False := by
  refine false_of_gap_margin_of_supported (chartPointOfDesign crux.design)
    (card_triple_of_distinct hxy hxz hyz) hgt ?_
  intro probe hsupport
  have hsupport' : ∀ atomIndex, atomIndex ≠ x → atomIndex ≠ y →
      atomIndex ≠ z → probe atomIndex = 0 := fun atomIndex hux huy huz =>
    hsupport atomIndex (notMem_triple.mpr ⟨hux, huy, huz⟩)
  rw [← eq_tripleLift_of_supported hxy hxz hyz hsupport',
    tripleLift_dotProduct_mulVec hxy hxz hyz,
    tripleLift_dotProduct_self hxy hxz hyz]
  exact hquad (probe x) (probe y) (probe z)

/-! ## Layer 5 — the parallel combination layer -/

/-- The parallel combination vanishes at the pair's left atom, with no
hypothesis: the two products cancel. -/
theorem parallel_combination_apply_pair_left (firstDir secondDir : Fin size → ℝ)
    (leftAtom : Fin size) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) leftAtom
      = 0 := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The parallel combination vanishes at the pair's right atom exactly
under the vanishing cross determinant. -/
theorem parallel_combination_apply_pair_right
    (firstDir secondDir : Fin size → ℝ) {leftAtom rightAtom : Fin size}
    (hdet : firstDir leftAtom * secondDir rightAtom
      - firstDir rightAtom * secondDir leftAtom = 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) rightAtom
      = 0 := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -hdet

/-- The parallel combination vanishes wherever the two directions both
vanish: it keeps the joint support. -/
theorem parallel_combination_apply_of_vanish
    (firstDir secondDir : Fin size → ℝ) (leftAtom : Fin size)
    {atomIndex : Fin size} (hfirst : firstDir atomIndex = 0)
    (hsecond : secondDir atomIndex = 0) :
    (secondDir leftAtom • firstDir - firstDir leftAtom • secondDir) atomIndex
      = 0 := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hfirst, hsecond,
    mul_zero, sub_zero]

/-- The parallel combination stays inside the span of the two
directions. -/
theorem parallel_combination_mem_span (firstDir secondDir : Fin size → ℝ)
    (leftAtom : Fin size) :
    secondDir leftAtom • firstDir - firstDir leftAtom • secondDir
      ∈ Submodule.span ℝ ({firstDir, secondDir} : Set (Fin size → ℝ)) :=
  sub_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
    (Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_insert_of_mem _ rfl)))

/-- A vanishing parallel combination is a proportionality: the first
direction is the explicit multiple of the second. -/
theorem eq_smul_of_parallel_combination_eq_zero
    {firstDir secondDir : Fin size → ℝ} {leftAtom : Fin size}
    (hzero : secondDir leftAtom • firstDir - firstDir leftAtom • secondDir = 0)
    (hne : secondDir leftAtom ≠ 0) :
    firstDir = (firstDir leftAtom / secondDir leftAtom) • secondDir := by
  funext atomIndex
  have hentry := congrFun hzero atomIndex
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hentry
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith [hentry]

end Gtz
