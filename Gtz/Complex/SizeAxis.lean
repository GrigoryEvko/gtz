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

**A CAMPAIGN LEDGER CLAIM THIS FILE REFUTES, IN THE KERNEL, OVER BOTH FIELDS.**
The campaign's MEASURED entry "the per-size infimum at `size = rank + 1` is exactly
1 and never attained" does not survive.  The value 1 IS attained at
`size = rank + 1`, and not at one lucky design but on a section over the whole open
weight simplex:

  * over ℝ — `exists_realDesign_exactlyTied`.  For EVERY admissible weight vector
    there is a design realising it at which every `rank`-subset dominates and none
    dominates strictly, i.e. sits at `λ_min = 1` exactly.  Composed from the
    repository's `Gtz.exists_isTie_of_weights` (`Gtz/Ties/CorankOneTieExistence.lean`)
    and `Gtz.corankOne_isTie_exactlyTied` (`Gtz/Ties/TotalTieCorankOne.lean`), both
    imported here, so these are dependencies now and not citations;
  * over ℂ — `exists_complexDesign_exactlyTied`, the same statement in
    `Gtz.ComplexWeightedDesign` / `Gtz.ComplexDominates`.  Its transport was the
    piece previously recorded as open.  It is closed by `complexifyDesign` plus the
    field-generic total tie `Gtz.forall_erasure_exactlyTied_of_forall_fieldDominates`;
    the route carries no positive-semidefiniteness transfer at all, because
    domination crosses the field boundary through the PIVOT, which is a real number
    (`coParsevalPivotValue_complexifyDesign`), and non-strictness is re-derived on
    the complex side from the budget.

The cell where the value is NOT attained is `size = rank`, where the frame is
unitary and `λ_min(S_univ) = 1 / max_c t_c`, strictly above one for `2 ≤ rank`
because every weight is then strictly below one.  That closed form is EXACT but is
NOT mechanized here, and it is flagged rather than asserted.  The campaign entry is
best read as having transcribed the rank-three profile's `m = 3` row — which is
`size = rank` — onto `size = rank + 1`.

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
import Gtz.Ties.CorankOneTieExistence
import Gtz.Ties.TotalTieCorankOne
import Gtz.Reduction.Reductions

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

/-! ## Complexifying a real design

A real design read over ℂ.  The point of this section is that domination transports
across the field boundary with NO positive-semidefiniteness transfer: the pivot
`coParsevalPivotValue` is a real number on both sides, and
`Gtz.fieldDominates_erase_iff_coParsevalPivot_le_one` turns domination of an erasure
into a real inequality.  So the only thing to check is that the pivot is unchanged,
which needs the co-Parseval operator and its inverse to complexify entrywise — and
the inverse does, because `Matrix.inv_eq_right_inv` only wants the mapped product to
be the identity. -/

/-- A real matrix read over ℂ, entrywise. -/
def complexifyMatrix {order : ℕ} (form : Matrix (Fin order) (Fin order) ℝ) :
    Matrix (Fin order) (Fin order) ℂ :=
  form.map (fun entry => ((entry : ℝ) : ℂ))

@[simp] theorem complexifyMatrix_apply {order : ℕ} (form : Matrix (Fin order) (Fin order) ℝ)
    (rowIndex colIndex : Fin order) :
    complexifyMatrix form rowIndex colIndex = ((form rowIndex colIndex : ℝ) : ℂ) := rfl

theorem complexifyMatrix_mul {order : ℕ} (left right : Matrix (Fin order) (Fin order) ℝ) :
    complexifyMatrix (left * right) = complexifyMatrix left * complexifyMatrix right := by
  ext rowIndex colIndex
  simp only [complexifyMatrix_apply, Matrix.mul_apply]
  push_cast
  rfl

theorem complexifyMatrix_one {order : ℕ} :
    complexifyMatrix (1 : Matrix (Fin order) (Fin order) ℝ) = 1 := by
  ext rowIndex colIndex
  rcases eq_or_ne rowIndex colIndex with rfl | hne
  · simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne, hne]

/-- The inverse complexifies too.  No determinant computation over ℂ is needed:
`Matrix.inv_eq_right_inv` accepts the mapped real identity. -/
theorem inv_complexifyMatrix {order : ℕ} (form : Matrix (Fin order) (Fin order) ℝ)
    (hunit : IsUnit form.det) :
    (complexifyMatrix form)⁻¹ = complexifyMatrix form⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← complexifyMatrix_mul, Matrix.mul_nonsing_inv _ hunit, complexifyMatrix_one]

/-- A real weighted design read as a field-generic design over ℂ: the atoms are
coerced coordinatewise, the weights are untouched. -/
def complexifyDesign {size rank : ℕ} (design : WeightedDesign size rank) :
    FieldWeightedDesign ℂ size rank where
  atom := fun atomIndex coordinate => ((design.atom atomIndex coordinate : ℝ) : ℂ)
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := by
    ext rowIndex colIndex
    have hreal := congrFun (congrFun design.isParseval rowIndex) colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
      Matrix.vecMulVec_apply] at hreal
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, fieldAtom,
      Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [show ((1 : Matrix (Fin rank) (Fin rank) ℂ) rowIndex colIndex)
        = ((((1 : Matrix (Fin rank) (Fin rank) ℝ) rowIndex colIndex : ℝ)) : ℂ) by
      rw [Matrix.one_apply, Matrix.one_apply]
      split <;> norm_num]
    rw [← hreal]
    push_cast
    ring_nf
    rfl

@[simp] theorem complexifyDesign_weight {size rank : ℕ} (design : WeightedDesign size rank) :
    (complexifyDesign design).weight = design.weight := rfl

theorem coParsevalOperator_complexifyDesign {size rank : ℕ}
    (design : WeightedDesign size rank) :
    coParsevalOperator (complexifyDesign design)
      = complexifyMatrix (coParsevalOperator (ofRealDesign design)) := by
  ext rowIndex colIndex
  simp only [coParsevalOperator, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    fieldAtom, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Complex.conj_ofReal, complexifyMatrix_apply, complexifyDesign, ofRealDesign]
  push_cast
  ring_nf
  simp

/-- **The pivot is field-blind.**  This is the one equality the whole transport rests
on, and both sides are real numbers. -/
theorem coParsevalPivotValue_complexifyDesign {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) (atomIndex : Fin size) :
    coParsevalPivotValue (complexifyDesign design) atomIndex
      = coParsevalPivotValue (ofRealDesign design) atomIndex := by
  have hunit : IsUnit (coParsevalOperator (ofRealDesign design)).det :=
    Matrix.isUnit_iff_isUnit_det _ |>.mp
      (coParsevalOperator_posDef (ofRealDesign design) hsize).isUnit
  have hscalar : coParsevalPivotScalar (complexifyDesign design) atomIndex
      = ((coParsevalPivotScalar (ofRealDesign design) atomIndex : ℝ) : ℂ) := by
    rw [coParsevalPivotScalar, coParsevalPivotScalar, coParsevalOperator_complexifyDesign,
      inv_complexifyMatrix _ hunit]
    simp only [dotProduct, Matrix.mulVec, complexifyMatrix_apply, complexifyDesign,
      ofRealDesign, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, star_trivial]
    push_cast
    rfl
  rw [coParsevalPivotValue, hscalar, coParsevalPivotValue]
  simp

/-- **Domination of an erasure crosses the field boundary.**  Both directions, from
the pivot criterion on each side. -/
theorem fieldDominates_erase_complexifyDesign_iff {size rank : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) (dropped : Fin size) :
    FieldDominates (complexifyDesign design) (Finset.univ.erase dropped)
      ↔ Dominates design (Finset.univ.erase dropped) := by
  rw [fieldDominates_erase_iff_coParsevalPivot_le_one (complexifyDesign design) hsize dropped,
    coParsevalPivotValue_complexifyDesign design hsize dropped,
    ← fieldDominates_erase_iff_coParsevalPivot_le_one (ofRealDesign design) hsize dropped,
    fieldDominates_iff_dominates]

/-- The transport back into the repository's complex vocabulary. -/
theorem complexDominates_toComplexDesign_iff {size rank : ℕ}
    (design : FieldWeightedDesign ℂ size rank) (selected : Finset (Fin size)) :
    ComplexDominates (toComplexDesign design) selected ↔ FieldDominates design selected :=
  Iff.rfl

/-! ## Attainment at `size = rank + 1`: the value one IS reached, over both fields -/

/-- **Attainment over ℝ.**  For every admissible weight vector there is a
corank-one design realising it at which every `rank`-subset sits at `λ_min = 1`
EXACTLY — it dominates, and it does not dominate strictly.  So the value one is
attained at `size = rank + 1`, on a section over the whole open weight simplex, and
the campaign's "never attained" reading of that cell is false. -/
theorem exists_realDesign_exactlyTied (rank : ℕ) (hrank : 1 ≤ rank)
    (weight : Fin (rank + 1) → ℝ) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) :
    ∃ design : WeightedDesign (rank + 1) rank, design.weight = weight ∧
      ∀ selected : Finset (Fin (rank + 1)), selected.card = rank →
        Dominates design selected ∧ ¬ (subsetSum design selected - 1).PosDef := by
  obtain ⟨design, hweight, htie⟩ := exists_isTie_of_weights hrank weight hpos hsum
  exact ⟨design, hweight, fun selected hcard =>
    corankOne_isTie_exactlyTied hrank design htie hcard⟩

/-- **Attainment over ℂ** — the transport that was previously recorded as open.
Complexify the real tie, carry domination across through the pivot, and recover
non-strictness on the complex side from the field-generic total tie.  No
positive-semidefiniteness transfer and no complex Householder construction. -/
theorem exists_complexDesign_exactlyTied (rank : ℕ) (hrank : 1 ≤ rank)
    (weight : Fin (rank + 1) → ℝ) (hpos : ∀ atomIndex, 0 < weight atomIndex)
    (hsum : ∑ atomIndex, weight atomIndex = 1) :
    ∃ design : ComplexWeightedDesign (rank + 1) rank, design.weight = weight ∧
      ∀ selected : Finset (Fin (rank + 1)), selected.card = rank →
        ComplexDominates design selected
          ∧ ¬ ((∑ atomIndex ∈ selected, complexAtom (design.atom atomIndex)) - 1).PosDef := by
  classical
  have hsize : 2 ≤ rank + 1 := by omega
  obtain ⟨realDesign, hweight, htie⟩ := exists_isTie_of_weights hrank weight hpos hsum
  have hcardErase : ∀ dropped : Fin (rank + 1),
      (Finset.univ.erase dropped).card = rank := by
    intro dropped
    rw [Finset.card_erase_of_mem (Finset.mem_univ dropped), Finset.card_univ, Fintype.card_fin]
    omega
  have hall : ∀ dropped : Fin (rank + 1),
      FieldDominates (complexifyDesign realDesign) (Finset.univ.erase dropped) := by
    intro dropped
    exact (fieldDominates_erase_complexifyDesign_iff realDesign hsize dropped).mpr
      (corankOne_isTie_dominates hrank realDesign htie (hcardErase dropped))
  refine ⟨toComplexDesign (complexifyDesign realDesign), hweight, fun selected hcard => ?_⟩
  obtain ⟨dropped, rfl⟩ := exists_erase_eq_of_card_eq selected hcard
  exact forall_erasure_exactlyTied_of_forall_fieldDominates hrank
    (complexifyDesign realDesign) hall dropped

/-! ## A6's two instantiations, discharged

`Gtz.FieldCorankTwoReducesToRankTwo` is left an open proposition in
`Gtz/Field/CorankOne.lean` only in the generic `Scalar`.  Both instantiations this
campaign cares about are theorems, and neither uses the `T^{-1/2}` whitening the
generic proof would need. -/

/-- Over ℝ the reduction's conclusion is the shipped `Gtz.gtzWeighted_corank_two`
read through the transport — the rank-two hypothesis is not even consumed. -/
theorem fieldCorankTwoReducesToRankTwo_real : FieldCorankTwoReducesToRankTwo ℝ := by
  intro _ rank hrank
  exact (fieldGtzWeighted_iff_gtzWeighted (rank + 2) rank).mpr
    (gtzWeighted_corank_two rank hrank)

/-- Over ℂ the reduction holds VACUOUSLY: its hypothesis asserts rank-two weighted
GTZ at every size, and that already fails at size four by the shipped refutation. -/
theorem fieldCorankTwoReducesToRankTwo_complex : FieldCorankTwoReducesToRankTwo ℂ := by
  intro hrankTwo
  exact absurd ((fieldGtzWeighted_iff_complexGtzWeighted 4 2).mp (hrankTwo 4))
    (not_complexGtzWeighted_of_rank_add_two_le_size 4 2 (by omega) (by omega))

end Gtz
