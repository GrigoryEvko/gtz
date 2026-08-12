import Gtz.Wave.StationaryRelabelTransport
import Gtz.Wave.DatumSupportDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The rank relabelling transport — the census dispatch bridge

The census dispatch fires a pattern kill at an orbit representative.  The
bridge has four bricks.  A permutation conjugation keeps the rank of a square
matrix, thus the transported datum keeps the assembly rank.  The datum tight
supports and the positive support transport as images.  The coefficient
matrices are NOT transported: the normal form is an existence statement, and
the dispatch derives fresh coordinates at the representative.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.finrank_range_toLin'_submatrix_perm` — a permutation conjugation
  keeps the rank of a square matrix.
* `Gtz.finrank_range_chartMultiplierAssembly_relabel` — the transported
  assembly keeps the rank.
* `Gtz.datumTightSupport_relabel` — the datum supports transport as images.
* `Gtz.positiveActiveSet_relabel` — the positive support transports as an
  image.
* `Gtz.SixThreeCrux.isChartStationaryData_relabel_rank` — **THE BRIDGE.**
  The relabelled crux carries the transported datum with the same assembly
  rank, at every rank.

## Vacuity

The crux statement is vacuous if `Gtz.GtzWeighted 6 3` holds.  The matrix
statements and the support statements are unconditional.
-/

namespace Gtz

open Matrix

/-- A permutation conjugation keeps the rank of a square matrix. -/
theorem finrank_range_toLin'_submatrix_perm {sideCount : ℕ}
    (form : Matrix (Fin sideCount) (Fin sideCount) ℝ)
    (relabelPerm : Equiv.Perm (Fin sideCount)) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (form.submatrix relabelPerm relabelPerm)))
      = Module.finrank ℝ (LinearMap.range (Matrix.toLin' form)) := by
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
  exact Matrix.rank_submatrix form relabelPerm relabelPerm

/-- The transported assembly keeps the rank: the relabelled datum's assembly
is the conjugated assembly, and a conjugation keeps the rank. -/
theorem finrank_range_chartMultiplierAssembly_relabel
    (relabelPerm : Equiv.Perm (Fin 6))
    (activeSet : Finset (Finset (Fin 6)))
    (multiplier : Finset (Fin 6) → ℝ) (tightDir : Finset (Fin 6) → Fin 6 → ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly (activeSet.image
            (fun block => block.map relabelPerm.symm.toEmbedding))
          (fun block => multiplier (block.map relabelPerm.toEmbedding))
          (fun block atomIndex => tightDir (block.map relabelPerm.toEmbedding)
            (relabelPerm atomIndex)))))
      = Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet multiplier tightDir))) := by
  rw [chartMultiplierAssembly_relabel]
  exact finrank_range_toLin'_submatrix_perm _ relabelPerm

/-- The datum tight supports transport as images along the inverse
permutation. -/
theorem datumTightSupport_relabel {size : ℕ}
    (relabelPerm : Equiv.Perm (Fin size))
    (tightDir : Finset (Fin size) → Fin size → ℝ) (block : Finset (Fin size)) :
    datumTightSupport (fun innerBlock atomIndex =>
        tightDir (innerBlock.map relabelPerm.toEmbedding) (relabelPerm atomIndex))
      block
      = (datumTightSupport tightDir (block.map relabelPerm.toEmbedding)).map
          relabelPerm.symm.toEmbedding := by
  ext atomIndex
  rw [mem_datumTightSupport]
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hne
    exact ⟨relabelPerm atomIndex, mem_datumTightSupport.mpr hne,
      Equiv.symm_apply_apply _ _⟩
  · rintro ⟨sourceAtom, hsourceMem, rfl⟩
    have hne := mem_datumTightSupport.mp hsourceMem
    rwa [Equiv.apply_symm_apply]

/-- The transported datum supports keep the cardinality — the statement the
census pattern match consumes together with the dichotomy. -/
theorem card_datumTightSupport_relabel {size : ℕ}
    (relabelPerm : Equiv.Perm (Fin size))
    (tightDir : Finset (Fin size) → Fin size → ℝ) (block : Finset (Fin size)) :
    (datumTightSupport (fun innerBlock atomIndex =>
        tightDir (innerBlock.map relabelPerm.toEmbedding) (relabelPerm atomIndex))
      block).card
      = (datumTightSupport tightDir (block.map relabelPerm.toEmbedding)).card := by
  rw [datumTightSupport_relabel, Finset.card_map]

/-- The positive support transports as an image along the inverse
permutation. -/
theorem positiveActiveSet_relabel {size : ℕ}
    (relabelPerm : Equiv.Perm (Fin size))
    (activeSet : Finset (Finset (Fin size))) (multiplier : Finset (Fin size) → ℝ) :
    positiveActiveSet (activeSet.image
        (fun block => block.map relabelPerm.symm.toEmbedding))
      (fun block => multiplier (block.map relabelPerm.toEmbedding))
      = (positiveActiveSet activeSet multiplier).image
          (fun block => block.map relabelPerm.symm.toEmbedding) := by
  ext block
  rw [mem_positiveActiveSet]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨⟨source, hsourceMem, rfl⟩, hpos⟩
    rw [map_toEmbedding_map_symm_toEmbedding] at hpos
    exact ⟨source, mem_positiveActiveSet.mpr ⟨hsourceMem, hpos⟩, rfl⟩
  · rintro ⟨source, hsourceMem, rfl⟩
    obtain ⟨hsourceActive, hpos⟩ := mem_positiveActiveSet.mp hsourceMem
    refine ⟨⟨source, hsourceActive, rfl⟩, ?_⟩
    rwa [map_toEmbedding_map_symm_toEmbedding]

/-- **THE BRIDGE.**  The relabelled crux carries the transported datum with
the same assembly rank.  The census dispatch composes this bridge with the
rank normal form at the orbit representative. -/
theorem SixThreeCrux.isChartStationaryData_relabel_rank
    (crux : SixThreeCrux) (relabelPerm : Equiv.Perm (Fin 6))
    {multiplier : Finset (Fin 6) → ℝ} {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    {assemblyRank : ℕ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hrank : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
        (chartMultiplierAssembly (chartArgmaxFamily (chartPointOfDesign crux.design))
          multiplier tightDir))) = assemblyRank) :
    IsChartStationaryData 3
        (chartPointOfDesign (crux.relabel relabelPerm).design).chart
        (chartPointOfDesign (crux.relabel relabelPerm).design).weight
        (chartObjective (chartPointOfDesign (crux.relabel relabelPerm).design))
        (chartArgmaxFamily (chartPointOfDesign (crux.relabel relabelPerm).design))
        (id : Finset (Fin 6) → Finset (Fin 6))
        (fun block => multiplier (block.map relabelPerm.toEmbedding))
        (fun block atomIndex => tightDir (block.map relabelPerm.toEmbedding)
          (relabelPerm atomIndex))
      ∧ Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly
            (chartArgmaxFamily (chartPointOfDesign (crux.relabel relabelPerm).design))
            (fun block => multiplier (block.map relabelPerm.toEmbedding))
            (fun block atomIndex => tightDir (block.map relabelPerm.toEmbedding)
              (relabelPerm atomIndex))))) = assemblyRank := by
  refine ⟨crux.isChartStationaryData_relabel relabelPerm hdata, ?_⟩
  have hfamilyEq : chartArgmaxFamily (chartPointOfDesign
        (crux.relabel relabelPerm).design)
      = (chartArgmaxFamily (chartPointOfDesign crux.design)).image
          (fun block => block.map relabelPerm.symm.toEmbedding) := by
    show chartArgmaxFamily (chartPointOfDesign (relabelDesign crux.design relabelPerm)) = _
    exact chartArgmaxFamily_relabelDesign crux.design relabelPerm
  rw [hfamilyEq, finrank_range_chartMultiplierAssembly_relabel relabelPerm]
  exact hrank

end Gtz
