import Mathlib
import Gtz.Reduction.ChartRelabel
import Gtz.Quantitative.SixThreeCrux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The crux relabelling action

Relabelling the atoms of a design by a permutation transports every `(6,3)`
crux to a `(6,3)` crux: the projection conjugates, the chart objective does not
move (the landed configuration-level equivariance), the minimiser field
survives verbatim, and the six design-side fields transport through the landed
domination equivariance.  The argmax family of the relabelled crux is the image
of the original family under the inverse permutation, with the same
cardinality — so every statement proved at an orbit representative of an
active family transports to the whole orbit.
-/

namespace Gtz

open Matrix

/-! ## The design-level bridges -/

/-- Relabelling a design conjugates its projection form. -/
theorem projectionOfDesign_relabelDesign {m k : ℕ} (design : WeightedDesign m k)
    (relabel : Equiv.Perm (Fin m)) :
    projectionOfDesign (relabelDesign design relabel)
      = (projectionOfDesign design).submatrix relabel relabel := by
  ext rowIndex colIndex
  rw [Matrix.submatrix_apply, projectionOfDesign_apply, projectionOfDesign_apply]
  rfl

/-- The chart configuration of a relabelled design is the relabelled chart
configuration. -/
theorem chartConfig_chartPointOfDesign_relabelDesign {m k : ℕ}
    (design : WeightedDesign m k) (relabel : Equiv.Perm (Fin m)) :
    (((chartPointOfDesign (relabelDesign design relabel)).chart,
        (chartPointOfDesign (relabelDesign design relabel)).weight) :
      (Fin m → Fin m → ℝ) × (Fin m → ℝ))
      = relabelChartConfig relabel
          (((chartPointOfDesign design).chart, (chartPointOfDesign design).weight) :
            (Fin m → Fin m → ℝ) × (Fin m → ℝ)) := by
  refine Prod.ext ?_ rfl
  show (projectionOfDesign (relabelDesign design relabel) : Fin m → Fin m → ℝ) = _
  funext rowIndex colIndex
  rw [projectionOfDesign_relabelDesign]
  rfl

/-- **The chart objective of a design is relabelling-invariant.** -/
theorem chartObjective_chartPointOfDesign_relabelDesign {m k : ℕ} [Nonempty (Fin k)]
    (design : WeightedDesign m k) (relabel : Equiv.Perm (Fin m)) :
    chartObjective (chartPointOfDesign (relabelDesign design relabel))
      = chartObjective (chartPointOfDesign design) := by
  have hrank : k ≤ m := rank_le_size_of_chartPoint (chartPointOfDesign design)
  rw [chartObjective_eq_chartObjectiveRaw _ hrank, chartObjective_eq_chartObjectiveRaw _ hrank,
    chartConfig_chartPointOfDesign_relabelDesign design relabel,
    chartObjectiveRaw_relabelChartConfig hrank relabel]

/-- Round trip: mapping through a permutation and back is the identity. -/
theorem map_toEmbedding_map_symm_toEmbedding {m : ℕ} (selected : Finset (Fin m))
    (relabel : Equiv.Perm (Fin m)) :
    (selected.map relabel.symm.toEmbedding).map relabel.toEmbedding = selected := by
  rw [Finset.map_map]
  ext atomIndex
  simp only [Finset.mem_map, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨sourceAtom, hsourceMem, rfl⟩
    simpa using hsourceMem
  · intro hmem
    exact ⟨atomIndex, hmem, by simp⟩

/-- Round trip, the other way around. -/
theorem map_symm_toEmbedding_map_toEmbedding {m : ℕ} (selected : Finset (Fin m))
    (relabel : Equiv.Perm (Fin m)) :
    (selected.map relabel.toEmbedding).map relabel.symm.toEmbedding = selected := by
  rw [Finset.map_map]
  ext atomIndex
  simp only [Finset.mem_map, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨sourceAtom, hsourceMem, rfl⟩
    simpa using hsourceMem
  · intro hmem
    exact ⟨atomIndex, hmem, by simp⟩

/-- **Membership transport for the argmax family**: a block is argmax for the
relabelled design exactly when its image block is argmax for the original. -/
theorem mem_chartArgmaxFamily_relabelDesign_iff {m k : ℕ} [Nonempty (Fin k)]
    (design : WeightedDesign m k) (relabel : Equiv.Perm (Fin m))
    (selected : Finset (Fin m)) :
    selected ∈ chartArgmaxFamily (chartPointOfDesign (relabelDesign design relabel))
      ↔ selected.map relabel.toEmbedding
          ∈ chartArgmaxFamily (chartPointOfDesign design) := by
  rw [mem_chartArgmaxFamily_iff, mem_chartArgmaxFamily_iff]
  have hblock : chartBlockValue k
        (((chartPointOfDesign (relabelDesign design relabel)).chart,
          (chartPointOfDesign (relabelDesign design relabel)).weight) :
          (Fin m → Fin m → ℝ) × (Fin m → ℝ)) selected
      = chartBlockValue k
          (((chartPointOfDesign design).chart, (chartPointOfDesign design).weight) :
            (Fin m → Fin m → ℝ) × (Fin m → ℝ))
          (selected.map relabel.toEmbedding) := by
    rw [chartConfig_chartPointOfDesign_relabelDesign design relabel]
    exact chartBlockValue_relabelChartConfig relabel _ selected
  rw [hblock, chartObjective_chartPointOfDesign_relabelDesign design relabel,
    Finset.card_map]

/-- **The argmax family transports as the inverse image family**, with equal
cardinality. -/
theorem chartArgmaxFamily_relabelDesign {m k : ℕ} [Nonempty (Fin k)]
    (design : WeightedDesign m k) (relabel : Equiv.Perm (Fin m)) :
    chartArgmaxFamily (chartPointOfDesign (relabelDesign design relabel))
      = (chartArgmaxFamily (chartPointOfDesign design)).image
          (fun block => block.map relabel.symm.toEmbedding) := by
  ext selected
  rw [mem_chartArgmaxFamily_relabelDesign_iff, Finset.mem_image]
  constructor
  · intro hmem
    exact ⟨selected.map relabel.toEmbedding, hmem,
      map_symm_toEmbedding_map_toEmbedding selected relabel⟩
  · rintro ⟨block, hblockMem, rfl⟩
    rwa [map_toEmbedding_map_symm_toEmbedding block relabel]

theorem card_chartArgmaxFamily_relabelDesign {m k : ℕ} [Nonempty (Fin k)]
    (design : WeightedDesign m k) (relabel : Equiv.Perm (Fin m)) :
    (chartArgmaxFamily (chartPointOfDesign (relabelDesign design relabel))).card
      = (chartArgmaxFamily (chartPointOfDesign design)).card := by
  rw [chartArgmaxFamily_relabelDesign]
  exact Finset.card_image_of_injective _
    (Finset.map_injective relabel.symm.toEmbedding)

/-! ## The crux transport -/

/-- **THE CRUX RELABELLING ACTION.**  Every field of a `(6,3)` crux transports
along an atom permutation. -/
noncomputable def SixThreeCrux.relabel (crux : SixThreeCrux)
    (relabelPerm : Equiv.Perm (Fin 6)) : SixThreeCrux where
  design := relabelDesign crux.design relabelPerm
  isChartMinimiser := by
    intro point
    rw [chartObjective_chartPointOfDesign_relabelDesign]
    exact crux.isChartMinimiser point
  hasNegativeChartValue := by
    rw [chartObjective_chartPointOfDesign_relabelDesign]
    exact crux.hasNegativeChartValue
  hasNoDominatingTriple := by
    intro selected hcard
    rw [dominates_relabelDesign_iff]
    exact crux.hasNoDominatingTriple (selected.map relabelPerm.toEmbedding)
      (by rw [Finset.card_map]; exact hcard)
  isAllHeavy := fun atomIndex => crux.isAllHeavy (relabelPerm atomIndex)
  hasStrictlyDominatingCoSingletons := by
    intro atomIndex
    have hcompl : ({atomIndex}ᶜ : Finset (Fin 6)).map relabelPerm.toEmbedding
        = ({relabelPerm atomIndex}ᶜ : Finset (Fin 6)) := by
      ext targetAtom
      simp only [Finset.mem_map, Finset.mem_compl, Finset.mem_singleton,
        Equiv.coe_toEmbedding]
      constructor
      · rintro ⟨sourceAtom, hsourceNe, rfl⟩
        intro hcontra
        exact hsourceNe (relabelPerm.injective hcontra)
      · intro hne
        exact ⟨relabelPerm.symm targetAtom,
          fun hcontra => hne (by simpa using congrArg relabelPerm hcontra),
          by simp⟩
    have hsubset := subsetSum_relabelDesign crux.design relabelPerm
      ({atomIndex}ᶜ : Finset (Fin 6))
    rw [hcompl] at hsubset
    rw [hsubset]
    exact crux.hasStrictlyDominatingCoSingletons (relabelPerm atomIndex)
  hasNoParallelPair := by
    intro hpair
    obtain ⟨keptLabel, dropLabel, ratio, hne, heq⟩ := hpair
    exact crux.hasNoParallelPair
      ⟨relabelPerm keptLabel, relabelPerm dropLabel, ratio,
        fun hcontra => hne (relabelPerm.injective hcontra), heq⟩
  avoidsEqualShareStratum := by
    intro hshare
    refine crux.avoidsEqualShareStratum ⟨fun atomIndex => ?_, fun atomIndex => ?_⟩
    · have hweight : crux.design.weight (relabelPerm (relabelPerm.symm atomIndex))
          = ((6 : ℕ) : ℝ)⁻¹ := hshare.weight_eq (relabelPerm.symm atomIndex)
      simpa using hweight
    · have hleverage : leverageOf
            (crux.design.atom (relabelPerm (relabelPerm.symm atomIndex)))
          = ((3 : ℕ) : ℝ) := hshare.leverage_eq (relabelPerm.symm atomIndex)
      simpa using hleverage

/-- The relabelled crux's argmax family has the original's cardinality — the
statement the census composition consumes. -/
theorem SixThreeCrux.card_chartArgmaxFamily_relabel (crux : SixThreeCrux)
    (relabelPerm : Equiv.Perm (Fin 6)) :
    (chartArgmaxFamily (chartPointOfDesign ((crux.relabel relabelPerm).design))).card
      = (chartArgmaxFamily (chartPointOfDesign crux.design)).card :=
  card_chartArgmaxFamily_relabelDesign crux.design relabelPerm

end Gtz
