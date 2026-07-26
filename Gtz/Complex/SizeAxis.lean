/-
# THE COMPLETE COMPLEX SIZE AXIS

**Headline.**  For every rank at least two, complex weighted GTZ holds exactly at
the two smallest sizes:

    ComplexGtzWeighted size rank  ↔  size ≤ rank + 1.

Three cells carry the content and one is vacuous:

  * `size < rank`     — VACUOUS.  Parseval forces `rank ≤ size`
    (`rank_le_size_of_complexDesign`), so the design family is EMPTY there and the
    equivalence holds for a trivial reason, not because domination succeeds.  The
    headline docstring says so; do not read the `iff` below `size = rank` as
    content.
  * `size = rank`     — the universal subset dominates (A5,
    `complexGtzWeighted_square`).
  * `size = rank + 1` — the co-Parseval trace budget (A4,
    `complexGtzWeighted_corank_one`).
  * `size ≥ rank + 2` — FALSE, by the repository's shipped refutation
    `Gtz.not_complexGtzWeighted_of_rank_add_two_le_size`
    (`Gtz/Complex/SpikePaddingLadder.lean`), whose hypotheses `2 ≤ rank` and
    `rank + 2 ≤ size` compose with the positive half exactly, with no gap and no
    reshaping.

Ranks below two are handled separately and are TRUE at every size:
`complexGtzWeighted_rank_le_one`.  Rank one is the repository's shipped
`Gtz.complexGtzWeighted_rankOne`; rank zero is the empty subset over `0 × 0`
matrices.

**What is new.**  The positive half.  Before this file `Gtz/Complex/` had
`Gtz.complexGtzWeighted_rankOne` and the refutations, no complex Naimark duality
and no complex chart; the `size = rank` and `size = rank + 1` rungs did not
exist over ℂ in any form.  The negative half is entirely pre-existing and is
cited, not re-proved.

**The transport costs nothing.**  `Gtz.complexAtom` is definitionally
`Gtz.fieldAtom` at `Scalar = ℂ`, so `Gtz.ComplexWeightedDesign` and
`Gtz.FieldWeightedDesign ℂ` are the same structure field for field, and
`FieldDominates ↔ ComplexDominates` is `Iff.rfl`.

**A CAMPAIGN LEDGER CLAIM THIS FILE CONTRADICTS.**  The campaign's MEASURED entry
"the per-size infimum at `size = rank + 1` is exactly 1 and never attained" cannot
survive: the repository already proves, in the kernel, that corank-one ties exist
over EVERY weight vector (`Gtz.exists_isTie_of_weights`,
`Gtz/Ties/CorankOneTieExistence.lean`) and that at such a tie EVERY `rank`-subset
sits at `λ_min = 1` exactly (`Gtz.corankOne_isTie_exactlyTied`,
`Gtz/Ties/TotalTieCorankOne.lean`).  So the value 1 IS attained at `size = rank + 1`
over ℝ, on a section over the whole open weight simplex.  Those two theorems are
PROVED over ℝ in the repository; transporting a real tie design into
`Gtz.ComplexWeightedDesign` is NOT mechanized here, so the complex form of the
attainment statement remains OPEN.  The unattained cell is `size = rank`, where
the frame is unitary and `λ_min(S_univ) = 1 / max_c t_c > 1` strictly — also not
mechanized here, and flagged rather than asserted.

**The tie-law agreement.**  `forall_jensenRatio_eq_inv_rank_iff_isTie` proves that
A4's equality case — every Jensen ratio equal to `1/rank` — is EXACTLY the
repository's corank-one tie predicate `Gtz.IsTie`, through
`Gtz.isTie_iff_leverage_identity`.  That is the promised agreement theorem
between the brief's A4(iv) and the shipped law, and it is proved, not asserted.
-/
import Mathlib
import Gtz.Field.WeightedDesign
import Gtz.Field.CorankOne
import Gtz.Complex.ComplexWitness
import Gtz.Complex.PerRankConstantLedger
import Gtz.Complex.SpikePaddingLadder
import Gtz.Ties.CorankOneTieCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix
open scoped ComplexOrder

/-! ## The transport: a complex design IS a field design at ℂ -/

/-- The complex atom is definitionally the field-generic atom at `Scalar = ℂ`. -/
theorem fieldAtom_eq_complexAtom {rank : ℕ} (vector : Fin rank → ℂ) :
    fieldAtom vector = complexAtom vector := rfl

/-- A repository complex design, read as a field-generic design at ℂ.  Every
structure field is accepted as-is. -/
def ofComplexDesign {size rank : ℕ} (design : ComplexWeightedDesign size rank) :
    FieldWeightedDesign ℂ size rank where
  atom := design.atom
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := design.isParseval

/-- And conversely. -/
def toComplexDesign {size rank : ℕ} (design : FieldWeightedDesign ℂ size rank) :
    ComplexWeightedDesign size rank where
  atom := design.atom
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := design.isParseval

/-- Domination transports on the nose — no adapter lemma at all. -/
theorem fieldDominates_iff_complexDominates {size rank : ℕ}
    (design : ComplexWeightedDesign size rank) (selected : Finset (Fin size)) :
    FieldDominates (ofComplexDesign design) selected ↔ ComplexDominates design selected :=
  Iff.rfl

/-- **The two statements agree.** -/
theorem fieldGtzWeighted_iff_complexGtzWeighted (size rank : ℕ) :
    FieldGtzWeighted ℂ size rank ↔ ComplexGtzWeighted size rank := by
  constructor
  · intro hfield design
    obtain ⟨selected, hcard, hdominates⟩ := hfield (ofComplexDesign design)
    exact ⟨selected, hcard, hdominates⟩
  · intro hcomplex design
    obtain ⟨selected, hcard, hdominates⟩ := hcomplex (toComplexDesign design)
    exact ⟨selected, hcard, hdominates⟩

/-- The real twin of the transport, for the record: the field-generic statement at
`Scalar = ℝ` is the repository's `Gtz.GtzWeighted`. -/
def toRealDesign {size rank : ℕ} (design : FieldWeightedDesign ℝ size rank) :
    WeightedDesign size rank where
  atom := design.atom
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := design.isParseval

theorem fieldGtzWeighted_iff_gtzWeighted (size rank : ℕ) :
    FieldGtzWeighted ℝ size rank ↔ GtzWeighted size rank := by
  constructor
  · intro hfield design
    obtain ⟨selected, hcard, hdominates⟩ := hfield (ofRealDesign design)
    exact ⟨selected, hcard, hdominates⟩
  · intro hreal design
    obtain ⟨selected, hcard, hdominates⟩ := hreal (toRealDesign design)
    exact ⟨selected, hcard, hdominates⟩

/-! ## The vacuity boundary -/

/-- **Parseval forces `rank ≤ size` over ℂ**, so below the rank the complex design
family is EMPTY.  Any equivalence stated there is true for that reason and no
other; the headline docstring flags it. -/
theorem rank_le_size_of_complexDesign {size rank : ℕ}
    (design : ComplexWeightedDesign size rank) : rank ≤ size :=
  rank_le_size_of_fieldDesign (ofComplexDesign design)

/-! ## The positive half over ℂ -/

/-- **A5 over ℂ**: at `size = rank` the universal subset dominates. -/
theorem complexGtzWeighted_square (rank : ℕ) : ComplexGtzWeighted rank rank :=
  (fieldGtzWeighted_iff_complexGtzWeighted rank rank).mp (fieldGtzWeighted_square rank)

/-- **A4 over ℂ**: at `size = rank + 1` some single erasure dominates.  This is
the rung nothing in `Gtz/Complex/` had. -/
theorem complexGtzWeighted_corank_one (rank : ℕ) (hrank : 1 ≤ rank) :
    ComplexGtzWeighted (rank + 1) rank :=
  (fieldGtzWeighted_iff_complexGtzWeighted (rank + 1) rank).mp
    (fieldGtzWeighted_corank_one rank hrank)

/-- Ranks below two hold at every size: rank one is the repository's shipped
`Gtz.complexGtzWeighted_rankOne`, rank zero is the empty subset over `0 × 0`
matrices. -/
theorem complexGtzWeighted_rank_le_one (size rank : ℕ) (hrank : rank ≤ 1) :
    ComplexGtzWeighted size rank := by
  interval_cases rank
  · intro design
    refine ⟨∅, Finset.card_empty, ?_⟩
    have hzero : (∑ atomIndex ∈ (∅ : Finset (Fin size)), complexAtom (design.atom atomIndex))
        - (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := by
      ext rowIndex colIndex
      exact Fin.elim0 rowIndex
    show ComplexDominates design ∅
    rw [ComplexDominates, hzero]
    exact Matrix.PosSemidef.zero
  · exact complexGtzWeighted_rankOne size

/-! ## THE HEADLINE -/

/-- **THE COMPLETE COMPLEX SIZE-AXIS DESCRIPTION.**  At every rank at least two,
complex weighted GTZ holds exactly when the size is at most `rank + 1`.

Forward: contraposition of the shipped
`Gtz.not_complexGtzWeighted_of_rank_add_two_le_size`.
Backward: three cases — `size < rank` is VACUOUS (`rank_le_size_of_complexDesign`
says there is no design), `size = rank` is A5, `size = rank + 1` is A4.

CAVEAT, deliberately visible: the equivalence is true below `size = rank` because
the design family is empty there, not because domination succeeds.  The
mathematical content sits at `size = rank`, `size = rank + 1` and
`size ≥ rank + 2`. -/
theorem complexGtzWeighted_iff_size_le_rank_add_one (size rank : ℕ) (hrank : 2 ≤ rank) :
    ComplexGtzWeighted size rank ↔ size ≤ rank + 1 := by
  constructor
  · intro hgtz
    by_contra hsize
    push Not at hsize
    exact not_complexGtzWeighted_of_rank_add_two_le_size size rank hrank (by omega) hgtz
  · intro hsize
    rcases lt_trichotomy size rank with hlt | heq | hgt
    · intro design
      exact absurd (rank_le_size_of_complexDesign design) (by omega)
    · subst heq
      exact complexGtzWeighted_square size
    · have hsizeEq : size = rank + 1 := by omega
      subst hsizeEq
      exact complexGtzWeighted_corank_one rank (by omega)

/-- **The whole complex size axis in one statement**, ranks below two included.
At rank at most one every size works; at rank at least two exactly the sizes at
most `rank + 1` work. -/
theorem complexGtzWeighted_iff (size rank : ℕ) :
    ComplexGtzWeighted size rank ↔ (rank ≤ 1 ∨ size ≤ rank + 1) := by
  rcases Nat.lt_or_ge rank 2 with hsmall | hlarge
  · have hle : rank ≤ 1 := by omega
    exact ⟨fun _ => Or.inl hle, fun _ => complexGtzWeighted_rank_le_one size rank hle⟩
  · rw [complexGtzWeighted_iff_size_le_rank_add_one size rank hlarge]
    exact ⟨Or.inr, fun hdisjunction => hdisjunction.resolve_left (by omega)⟩

/-! ## A4(iv) IS the repository's corank-one tie law -/

/-- **THE AGREEMENT THEOREM.**  Over ℝ at corank one, A4's equality case — every
Jensen ratio equal to `1/rank` — is EXACTLY the repository's `Gtz.IsTie`.  The
bridge is `Gtz.jensenRatio_eq_inv_rank_iff_leverageIdentity` on one side and
`Gtz.isTie_iff_leverage_identity` on the other; both name the same affine relation
`rank · t_c · ℓ_c = (rank − 1) + t_c`, so the brief's A4(iv) and the shipped law
are one statement. -/
theorem forall_jensenRatio_eq_inv_rank_iff_isTie {rank : ℕ} (hrank : 1 ≤ rank)
    (design : WeightedDesign (rank + 1) rank) :
    (∀ atomIndex, jensenRatio (ofRealDesign design) atomIndex = 1 / (rank : ℝ))
      ↔ IsTie design := by
  have hsize : 2 ≤ rank + 1 := by omega
  rw [isTie_iff_leverage_identity hrank design]
  constructor
  · intro hall atomIndex
    have hlaw := (jensenRatio_eq_inv_rank_iff_leverageIdentity (ofRealDesign design)
      hsize hrank atomIndex).mp (hall atomIndex)
    rwa [fieldLeverageOf_eq_leverageOf] at hlaw
  · intro hall atomIndex
    refine (jensenRatio_eq_inv_rank_iff_leverageIdentity (ofRealDesign design)
      hsize hrank atomIndex).mpr ?_
    rw [fieldLeverageOf_eq_leverageOf]
    exact hall atomIndex

/-- The real corank-one rung, restated in the repository's own vocabulary: a
second proof of the shipped `Gtz.gtzWeighted_corank_one` that consumes no Naimark
duality. -/
theorem gtzWeighted_corank_one_viaTraceBudget (rank : ℕ) (hrank : 1 ≤ rank) :
    GtzWeighted (rank + 1) rank :=
  (fieldGtzWeighted_iff_gtzWeighted (rank + 1) rank).mp
    (fieldGtzWeighted_corank_one rank hrank)

/-- The real square rung, restated in the repository's own vocabulary: a second
proof of the shipped `Gtz.gtzWeighted_square`. -/
theorem gtzWeighted_square_viaCoParseval (rank : ℕ) : GtzWeighted rank rank :=
  (fieldGtzWeighted_iff_gtzWeighted rank rank).mp (fieldGtzWeighted_square rank)

end Gtz
