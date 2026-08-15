/-
# The consolidated statement as three polynomial inequalities

`Gtz.ConsolidatedStrictTriple` carries every on-path registry obligation.  It is
stated with a `Matrix.PosDef` conclusion, so every attack on it has had to
supply a positive-definiteness proof at some selection.

That is not necessary.  `Gtz.posDef_directionChartGap_compl_triple_iff` decides a
selection omitting three labels EXACTLY, by the three leading principal minors of
the complement matrix of the omitted labels.  At size six a card-three selection
omits exactly three labels, so the whole statement becomes

    at every chart point some triple of labels has three positive minors,

with no matrix, no eigenvalue and no positive-definiteness left in it.  That
equivalence is `Gtz.consolidatedStrictTriple_iff_complementMinors` below.

## What this reorganizes

The corpus carries several SUFFICIENT cells for a selection to dominate
strictly: the deflated pair criterion, the total-pivot bound, the pivot-third
cell.  Each was landed against its own consumer and measured on its own.  All of
them are instances of the exact criterion, and this file proves it for the
deflated pair and everything below it.  A census over 203,761 exact chart points
across six boxes found the exact criterion firing at EVERY point, against 86.6
to 96.3 percent for the deflated pair and 29.9 to 62.1 percent for the trace
bound, so the gap between them is real and is entirely the price of sufficiency.

## What it does not do

The equivalence moves no difficulty.  The existential over the twenty triples is
untouched, and it is where the campaign's remaining work sits.  What changes is
that a candidate designation may now be checked by evaluating three polynomials
rather than by proving a matrix positive definite.
-/
import Gtz.Wave.ComplementTripleCriterion
import Gtz.Wave.ConsolidatedStrictTriple
import Gtz.Design.DeflatedPairCriterion
import Gtz.Design.ComplementDiagonalDominance

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## 1. The predicate -/

/-- **The three leading minors of the complement matrix of a triple.**  This is
the exact criterion of `Gtz.posDef_directionChartGap_compl_triple_iff`, named so
it can be quantified over. -/
def ChartComplementMinors (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (i j k : Fin size) : Prop :=
  0 < complementMatrixEntry direction mass weight i i ∧
    0 < complementMatrixEntry direction mass weight i i
        * complementMatrixEntry direction mass weight j j
      - complementMatrixEntry direction mass weight i j ^ 2 ∧
    0 < complementTripleDeterminant direction mass weight i j k

/-- The named predicate is the criterion the corpus already decides. -/
theorem posDef_compl_triple_iff_chartComplementMinors
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    {i j k : Fin size} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hboostI : 0 < mass i / weight i) (hboostJ : 0 < mass j / weight j)
    (hboostK : 0 < mass k / weight k)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef) :
    (directionChartGap direction mass weight
        (Finset.univ \ ({i, j, k} : Finset (Fin size)))).PosDef
      ↔ ChartComplementMinors direction mass weight i j k :=
  posDef_directionChartGap_compl_triple_iff direction mass weight hij hik hjk
    hboostI hboostJ hboostK huniv

/-! ## 2. The complement of a card-three selection at size six

A selection of three labels out of six omits three labels, and the double
complement returns the selection.  Both directions of the equivalence need this
bookkeeping and nothing else.
-/

/-- The complement of a card-three selection at size six has three labels. -/
theorem card_sdiff_eq_three_of_card_eq_three {selected : Finset (Fin 6)}
    (hcard : selected.card = 3) : (Finset.univ \ selected).card = 3 := by
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, hcard]

/-- Removing the complement returns the selection. -/
theorem sdiff_sdiff_univ_self (selected : Finset (Fin 6)) :
    Finset.univ \ (Finset.univ \ selected) = selected := by
  rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]

/-- A card-three selection is the complement of an explicit triple of distinct
labels. -/
theorem exists_triple_compl_eq_of_card_eq_three {selected : Finset (Fin 6)}
    (hcard : selected.card = 3) :
    ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      Finset.univ \ ({i, j, k} : Finset (Fin 6)) = selected := by
  obtain ⟨i, j, k, hij, hik, hjk, htriple⟩ :=
    Finset.card_eq_three.mp (card_sdiff_eq_three_of_card_eq_three hcard)
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  rw [← htriple, sdiff_sdiff_univ_self]

/-- The complement of an explicit triple of distinct labels has card three. -/
theorem card_sdiff_triple_eq_three {i j k : Fin 6}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Finset.univ \ ({i, j, k} : Finset (Fin 6))).card = 3 := by
  have htripleCard : ({i, j, k} : Finset (Fin 6)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩
  rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin, htripleCard]

/-! ## 3. The boosts of a chart point -/

/-- Every boost of a chart point is strictly positive. -/
theorem chartPoint_boost_pos (point : DirectionChartPoint 6) (label : Fin 6) :
    0 < point.mass label / point.weight label :=
  div_pos (point.mass_pos label) (point.weight_pos label)

/-! ## 4. The equivalence

The consolidated statement is a statement about polynomials in the masses, the
weights and the entries of the inverse of the full gap.  Nothing in it needs a
matrix.
-/

/-- **THE CONSOLIDATED STATEMENT IN MINOR FORM.**  Every chart point of a
spanning, pair-independent direction family carries a card-three selection whose
gap is positive definite exactly when it carries a triple of distinct labels
whose complement matrix has three positive leading minors. -/
theorem consolidatedStrictTriple_iff_complementMinors :
    ConsolidatedStrictTriple ↔
      ∀ direction : Fin 6 → (Fin 3 → ℝ),
        (∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) →
        DirectionsArePairIndependent direction →
        ∀ point : DirectionChartPoint 6,
          ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            ChartComplementMinors direction point.mass point.weight i j k := by
  constructor
  · intro hconsolidated direction hspan hpair point
    obtain ⟨selected, hcard, hposDef⟩ := hconsolidated direction hspan hpair point
    obtain ⟨i, j, k, hij, hik, hjk, hcompl⟩ := exists_triple_compl_eq_of_card_eq_three hcard
    have huniv := posDef_directionChartGap_univ_of_span direction point hspan
    refine ⟨i, j, k, hij, hik, hjk, ?_⟩
    refine (posDef_compl_triple_iff_chartComplementMinors direction point.mass
      point.weight hij hik hjk (chartPoint_boost_pos point i) (chartPoint_boost_pos point j)
      (chartPoint_boost_pos point k) huniv).mp ?_
    rwa [hcompl]
  · intro hminors direction hspan hpair point
    obtain ⟨i, j, k, hij, hik, hjk, hpos⟩ := hminors direction hspan hpair point
    have huniv := posDef_directionChartGap_univ_of_span direction point hspan
    refine ⟨Finset.univ \ ({i, j, k} : Finset (Fin 6)), card_sdiff_triple_eq_three hij hik hjk, ?_⟩
    exact (posDef_compl_triple_iff_chartComplementMinors direction point.mass
      point.weight hij hik hjk (chartPoint_boost_pos point i) (chartPoint_boost_pos point j)
      (chartPoint_boost_pos point k) huniv).mpr hpos

/-! ## 5. The sufficient cells are instances

Each landed sufficient cell produces a positive-definite selection, so by the
equivalence each produces the three minors.  These are the bridges that say the
cells are not independent facts.
-/

/-- **The deflated pair criterion produces the minors.**  So the deflated pair
cell is an instance of the exact criterion rather than an independent test. -/
theorem chartComplementMinors_of_deflatedPair
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hgapA : fullPivot direction mass weight a + fullPivot direction mass weight c < 1)
    (hgapB : fullPivot direction mass weight b + fullPivot direction mass weight c < 1)
    (hcross : pairBoostedCrossSq direction mass weight a b
      < (1 - fullPivot direction mass weight c - fullPivot direction mass weight a)
        * (1 - fullPivot direction mass weight c - fullPivot direction mass weight b)) :
    ChartComplementMinors direction mass weight a b c := by
  refine (posDef_compl_triple_iff_chartComplementMinors direction mass weight hab hac hbc
    (hboost a) (hboost b) (hboost c) huniv).mp ?_
  exact posDef_directionChartGap_compl_triple_of_deflatedPair direction mass weight a b c
    (fun label => le_of_lt (hboost label)) huniv hab hac hbc hgapA hgapB hcross

/-- **The total-pivot bound produces the minors.**  The trace cell is an instance
of the exact criterion. -/
theorem chartComplementMinors_of_sum_fullPivot_lt_one
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htotal : fullPivot direction mass weight a + fullPivot direction mass weight b
      + fullPivot direction mass weight c < 1) :
    ChartComplementMinors direction mass weight a b c := by
  have hmemA : a ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hmemB : b ∈ ({a, b, c} : Finset (Fin size)) := by simp
  have hsum : ∑ label ∈ ({a, b, c} : Finset (Fin size)),
      fullPivot direction mass weight label
      = fullPivot direction mass weight a + fullPivot direction mass weight b
        + fullPivot direction mass weight c := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
      Finset.sum_singleton]
    ring
  refine (posDef_compl_triple_iff_chartComplementMinors direction mass weight hab hac hbc
    (hboost a) (hboost b) (hboost c) huniv).mp ?_
  refine posDef_directionChartGap_compl_of_sum_fullPivot_lt_one direction mass weight
    {a, b, c} a b (fun label => le_of_lt (hboost label)) huniv hmemA hmemB hab ?_
  rw [hsum]
  linarith

/-- **The pivot-third cell produces the minors.**  Three labels below one third
total below one, so this is an instance of the previous bridge. -/
theorem chartComplementMinors_of_pivotThird
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (a b c : Fin size)
    (hboost : ∀ label, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpa : fullPivot direction mass weight a < 1 / 3)
    (hpb : fullPivot direction mass weight b < 1 / 3)
    (hpc : fullPivot direction mass weight c < 1 / 3) :
    ChartComplementMinors direction mass weight a b c :=
  chartComplementMinors_of_sum_fullPivot_lt_one direction mass weight a b c hboost huniv
    hab hac hbc (by linarith)

/-- The complement of the complement of a triple is the triple. -/
theorem compl_sdiff_triple (i j k : Fin size) :
    (Finset.univ \ ({i, j, k} : Finset (Fin size)))ᶜ = {i, j, k} := by
  rw [← Finset.compl_eq_univ_sdiff, compl_compl]

/-- **Row dominance produces the minors.**  The diagonal-dominance cell is an
instance of the exact criterion too, so after this bridge the corpus carries no
chart-level cell that is independent of the three minors. -/
theorem chartComplementMinors_of_rowSlack
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (i j k : Fin size)
    (hboost : ∀ label, 0 < mass label / weight label)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hslack : ∀ a ∈ ({i, j, k} : Finset (Fin size)),
      0 < complementRowSlack direction mass weight ({i, j, k} : Finset (Fin size)) a) :
    ChartComplementMinors direction mass weight i j k := by
  refine (posDef_compl_triple_iff_chartComplementMinors direction mass weight hij hik hjk
    (hboost i) (hboost j) (hboost k) huniv).mp ?_
  have hcompl := compl_sdiff_triple (size := size) i j k
  refine posDef_directionChartGap_of_rowSlack_pos direction mass weight
    (Finset.univ \ ({i, j, k} : Finset (Fin size))) ?_ huniv ?_
  · intro label _
    exact hboost label
  · rw [hcompl]
    exact hslack

/-! ## 6. A sufficient cell closes the statement

Any rule producing one of the sufficient cells at every chart point closes the
consolidated statement, now read through the minors.
-/

/-- **A deflated-pair designation closes the statement.**  If some rule names, at
every chart point, a triple satisfying the deflated pair criterion, the
consolidated statement follows. -/
theorem consolidatedStrictTriple_of_deflatedPair_designation
    (hdesignate : ∀ direction : Fin 6 → (Fin 3 → ℝ),
      (∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) →
      DirectionsArePairIndependent direction →
      ∀ point : DirectionChartPoint 6,
        ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          fullPivot direction point.mass point.weight a
              + fullPivot direction point.mass point.weight c < 1 ∧
          fullPivot direction point.mass point.weight b
              + fullPivot direction point.mass point.weight c < 1 ∧
          pairBoostedCrossSq direction point.mass point.weight a b
            < (1 - fullPivot direction point.mass point.weight c
                - fullPivot direction point.mass point.weight a)
              * (1 - fullPivot direction point.mass point.weight c
                - fullPivot direction point.mass point.weight b)) :
    ConsolidatedStrictTriple := by
  refine consolidatedStrictTriple_iff_complementMinors.mpr ?_
  intro direction hspan hpair point
  obtain ⟨a, b, c, hab, hac, hbc, hgapA, hgapB, hcross⟩ := hdesignate direction hspan hpair point
  have huniv := posDef_directionChartGap_univ_of_span direction point hspan
  exact ⟨a, b, c, hab, hac, hbc,
    chartComplementMinors_of_deflatedPair direction point.mass point.weight a b c
      (chartPoint_boost_pos point) huniv hab hac hbc hgapA hgapB hcross⟩

/-- **A total-pivot designation closes the statement.** -/
theorem consolidatedStrictTriple_of_totalPivot_designation
    (hdesignate : ∀ direction : Fin 6 → (Fin 3 → ℝ),
      (∀ probe : Fin 3 → ℝ, (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) →
      DirectionsArePairIndependent direction →
      ∀ point : DirectionChartPoint 6,
        ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          fullPivot direction point.mass point.weight a
            + fullPivot direction point.mass point.weight b
            + fullPivot direction point.mass point.weight c < 1) :
    ConsolidatedStrictTriple := by
  refine consolidatedStrictTriple_iff_complementMinors.mpr ?_
  intro direction hspan hpair point
  obtain ⟨a, b, c, hab, hac, hbc, htotal⟩ := hdesignate direction hspan hpair point
  have huniv := posDef_directionChartGap_univ_of_span direction point hspan
  exact ⟨a, b, c, hab, hac, hbc,
    chartComplementMinors_of_sum_fullPivot_lt_one direction point.mass point.weight a b c
      (chartPoint_boost_pos point) huniv hab hac hbc htotal⟩

end Gtz
