import Gtz.Wave.AssemblyCoefficientLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coefficient trace — `tr M = rank(P Ξ)`

The coefficient projection `M = L (P B)` represents the chart restricted to
`range Ξ` in the chosen basis.  It is idempotent, so its trace is its rank,
and its rank is the captured rank: `B` carries `range M` onto `range (P B)`
injectively, and `range (P B) = range (P Ξ)` because the column space of `B`
is the assembly's range.  Against the rank split survivor list the trace of
`M` therefore reads TWO or THREE, and `basisCount - tr M` reads the
complement's captured rank.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.injective_toLin_tightBasisColumns_of_leftInverse` — a left inverse
  makes the column map injective.
* `Gtz.coefficient_trace_eq_capturedRank` — **THE TRACE LAW.**
  `tr (L (P B)) = rank (P Ξ)`, at every active count.

## Vacuity

Nothing here quantifies over a crux.  The statements hold at every stationary
datum with a chosen basis and left inverse.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
variable {basisCount : ℕ}

/-- A left inverse makes the column map injective. -/
theorem injective_toLin_tightBasisColumns_of_leftInverse
    (basisLabel : Fin basisCount → activeIndex)
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1) :
    Function.Injective (Matrix.toLin' (tightBasisColumns tightDir basisLabel)) := by
  have hcomp : (Matrix.toLin' L).comp
      (Matrix.toLin' (tightBasisColumns tightDir basisLabel)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hleft, Matrix.toLin'_one]
  have hleftInverse : Function.LeftInverse (Matrix.toLin' L)
      (Matrix.toLin' (tightBasisColumns tightDir basisLabel)) := by
    intro coeffVec
    have happly := DFunLike.congr_fun hcomp coeffVec
    simpa using happly
  exact hleftInverse.injective

/-- **THE TRACE LAW.**  The coefficient projection's trace is the captured
rank: `tr (L (P B)) = rank (P Ξ)`. -/
theorem coefficient_trace_eq_capturedRank
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (basisLabel : Fin basisCount → activeIndex)
    (hbasisSpan : Submodule.span ℝ
        (Set.range fun columnIndex => tightDir (basisLabel columnIndex))
      = LinearMap.range (Matrix.toLin'
          (chartMultiplierAssembly activeSet activeWeight tightDir)))
    (L : Matrix (Fin basisCount) (Fin size) ℝ)
    (hleft : L * tightBasisColumns tightDir basisLabel = 1) :
    Matrix.trace (L * (projection * tightBasisColumns tightDir basisLabel))
      = (Module.finrank ℝ (LinearMap.range (Matrix.toLin'
          (projection * chartMultiplierAssembly activeSet activeWeight tightDir))) : ℝ) := by
  classical
  set B := tightBasisColumns tightDir basisLabel with hBdef
  set assembly := chartMultiplierAssembly activeSet activeWeight tightDir with hassemblyDef
  have hrangeB : LinearMap.range (Matrix.toLin' B)
      = LinearMap.range (Matrix.toLin' assembly) :=
    range_tightBasisColumns_eq basisLabel hbasisSpan
  have hrepresentation : projection * B = B * (L * (projection * B)) :=
    (mul_leftInverse_mul_eq_of_range_le B L (projection * B) hleft
      (range_mul_le_of_commutes_of_range_eq hdata basisLabel hrangeB)).symm
  have hidempotent : (L * (projection * B)) * (L * (projection * B))
      = L * (projection * B) :=
    coefficient_idempotent_of_leftInverse projection B L (L * (projection * B))
      hleft hdata.isIdempotent hrepresentation
  rw [trace_eq_finrank_range_of_idempotent _ hidempotent]
  -- the rank of M transports through B onto the captured rank
  have hinjective : Function.Injective (Matrix.toLin' B) :=
    injective_toLin_tightBasisColumns_of_leftInverse basisLabel L hleft
  have hmapEq : Module.finrank ℝ (LinearMap.range (Matrix.toLin'
      (L * (projection * B))))
      = Module.finrank ℝ (LinearMap.range (Matrix.toLin' (B * (L * (projection * B))))) := by
    rw [Matrix.toLin'_mul B, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hinjective _).finrank_eq
  have hcapturedEq : LinearMap.range (Matrix.toLin' (B * (L * (projection * B))))
      = LinearMap.range (Matrix.toLin' (projection * assembly)) := by
    rw [← hrepresentation, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.range_comp, LinearMap.range_comp, hrangeB]
  rw [hmapEq, hcapturedEq]

end Gtz
