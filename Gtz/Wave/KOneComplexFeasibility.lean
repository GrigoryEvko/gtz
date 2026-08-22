/-
# The `K1` stratum is INHABITED over `ℂ`, and it is the only stratum that is

`Gtz/Wave/CorankStratumCollapse.lean` splits a dominating triple of an all-heavy
design by the number of vanishing inside pair gap minors: `0` is `K0`, `1` is `K1`,
`3` is the corank-two corner, and `2` is impossible
(`Gtz.tripleStratum_trichotomy`).  Four campaign modules — `Gtz/Wave/KOneAnchor.lean`,
`Gtz/Wave/KOneBracketLedger.lean`, `Gtz/Wave/KOneNormalForm.lean` and
`Gtz/Wave/KOneTransverse.lean` — build a complete exact theory of the `K1` stratum
and end at one question: is the stratum EMPTY at `(6,3)`?

**This module answers the field question, and the answer is a NO-GO.**

`Gtz.complexHingeSixDesign` (`Gtz/Complex/ComplexHingeRefutation.lean`) is an exact
complex `(6,3)` tie with no parallel pair.  Its dominating triples are computed
here, and EVERY ONE OF THEM IS `K1`:

* `Gtz.complexHingeSix_spike_mem_of_dominates` — a dominating triple contains the
  spike, because a triple that misses it carries `-1` on the third diagonal entry
  and a positive semidefinite matrix has a nonnegative diagonal.
* `Gtz.complexHingeSix_planeMinor_eq_zero_of_dominates` — the two remaining atoms
  have VANISHING pair gap minor, because the gap of a spike triple is block
  diagonal with determinant `24` times the planar pair excess, every planar pair
  excess is at most zero (`Gtz.complexHingePlaneExcess_nonpos`), and a positive
  semidefinite matrix has a nonnegative determinant.
* `Gtz.complexHingeSix_minor_spike_pos` — the two pair minors THROUGH the spike are
  `24` or `36`, both strictly positive.

So `Gtz.complexHingeSix_every_dominator_isKOne` holds: the complex witness carries
a `K1` dominator, carries no `K0` dominator and carries no corner dominator.

## What this forbids

`Gtz.ComplexHasKOneDominator` is `Gtz.complexPairGapMinor` in exactly the shape the
real stratum uses, with `p_cd ^ 2` read as `<g_c,g_d> <g_d,g_c>`.  Every real
instrument of the `K1` arm — the leverage floor `A > 1`, the sharp weight cap
`A (t_y b_z ^ 2 + t_z b_y ^ 2) <= 1`, the erased weight cap `t_x [xyz] ^ 2 <= A`,
the strict bracket floor `[xyz] ^ 2 > A`, the wedge ceiling, the bracket budget,
the strong-pair count of `Gtz/Wave/ElliptopeTrichotomy.lean` and the whole
trichotomy — is FIELD-BLIND, so it admits `Gtz.complexHingeSixDesign` as a feasible
point and CANNOT empty `K1`.

  **`Gtz.not_complexKOneStratumEmpty_six_three`: the sentence "a primitive `(6,3)`
  tie has no `K1` dominator" is FALSE over `ℂ`.  Any proof of it over `ℝ` must
  consume realness.**

This is the sharpest form of the campaign's field discipline yet recorded, because
`K1` is not merely reachable over `ℂ` — over `ℂ` it is the ONLY reachable stratum
at the target cell.

## Where the realness must enter

The complex witness shows its own real obstruction.  Five of its six atoms lie in
one plane and its sixth atom is orthogonal to the other five.  Over `ℝ` neither is
permitted at a primitive `(6,3)` tie: `Gtz.card_coplanar_le_three_of_isPrimitiveDesign_of_isTie`
caps a plane at THREE atoms, and that cap is a stress statement whose whole content
is `dim Sym_3(ℝ) = 6` against `dim Herm_3(ℂ) = 9`.  The companion module
`Gtz/Wave/KOneRealIngredient.lean` spends exactly that cap on the `K1` stratum.

[MEASURED at 512 bits, `scratchpad/k1complex/verify2.jl`, domination decided by the
seven principal minors and cross-checked against the eigenvalues.  Parseval
residual `1.5e-154`.  Leverages `2, 2, 2, 2, 5/2, 25` — all heavy.  Fifteen pair
gap minors: three vanish (`{2,3}`, `{2,4}`, `{3,4}`), five are `24`, `24`, `24`,
`24`, `36`, and seven are strictly negative.  Of the twenty triples exactly three
dominate — `{2,3,5}`, `{2,4,5}`, `{3,4,5}` — each with gap eigenvalues
`0, 2, 24` or `0, 5/2, 24`, hence corank exactly one, and each with exactly one
vanishing inside minor.  A first pass used a Jacobi sweep whose rotation angle
degenerates when the two diagonal entries agree and reported `+1` where the true
smallest eigenvalue is `0`: NEVER decide domination by an eigenvalue routine when
the principal minors are available.]
-/
import Gtz.Complex.ComplexHingeRefutation
import Gtz.Complex.ComplexTransportLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

variable {m k : ℕ}

/-! ## Part 1 — the pair gap minor over `ℂ`

`Gtz.pairGapMinor a b` is `(l_a - 1)(l_b - 1) - (a . b) ^ 2`.  Over `ℂ` the square
of the pairing is the product of the two pairings, which is exactly
`Gtz.complexOverlap`.  Nothing else changes. -/

/-- The **complex pair gap minor**, the transport of `Gtz.pairGapMinor`. -/
noncomputable def complexPairGapMinor (D : ComplexWeightedDesign m k) (first second : Fin m) : ℂ :=
  (complexLeverage D first - 1) * (complexLeverage D second - 1)
    - complexOverlap D first second

theorem complexPairGapMinor_comm (D : ComplexWeightedDesign m k) (first second : Fin m) :
    complexPairGapMinor D first second = complexPairGapMinor D second first := by
  rw [complexPairGapMinor, complexPairGapMinor, complexOverlap_comm]
  ring

/-- The **complex `K1` dominator**: a dominating triple with exactly one vanishing
inside pair gap minor.  The erased atom is `erased`, the live pair is
`{liveLeft, liveRight}`.  This is the middle case of `Gtz.tripleStratum_trichotomy`,
transported. -/
def ComplexHasKOneDominator (D : ComplexWeightedDesign m 3) : Prop :=
  ∃ erased liveLeft liveRight : Fin m,
    erased ≠ liveLeft ∧ erased ≠ liveRight ∧ liveLeft ≠ liveRight
      ∧ ComplexDominates D {erased, liveLeft, liveRight}
      ∧ complexPairGapMinor D liveLeft liveRight = 0
      ∧ 0 < complexPairGapMinor D erased liveLeft
      ∧ 0 < complexPairGapMinor D erased liveRight

/-! ## Part 2 — the Gram data of the `(6,3)` complex witness -/

@[simp] theorem complexHingeSixDesign_atom :
    complexHingeSixDesign.atom = complexHingeSixAtom := rfl

/-- The spike carries leverage `25`. -/
theorem complexHingeSix_leverage_five : complexLeverage complexHingeSixDesign 5 = 25 := by
  show star (complexHingeSixAtom 5) ⬝ᵥ complexHingeSixAtom 5 = 25
  rw [complexHingeSixAtom_five, starDot_spike]

/-- Every planar atom carries leverage `2` or `5/2`. -/
theorem complexHingeSix_leverage_plane (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    complexLeverage complexHingeSixDesign atomLabel = 2
      ∨ complexLeverage complexHingeSixDesign atomLabel = 5 / 2 := by
  have hread : ∀ label : Fin 6, complexLeverage complexHingeSixDesign label
      = star (complexHingeSixAtom label) ⬝ᵥ complexHingeSixAtom label := fun _ => rfl
  fin_cases atomLabel
  · exact Or.inl (by rw [hread, show ((⟨0, by omega⟩ : Fin 6)) = 0 from rfl,
      complexHingeSixAtom_zero, starDot_liftPlane, complexHingeNorm 0])
  · exact Or.inl (by rw [hread, show ((⟨1, by omega⟩ : Fin 6)) = 1 from rfl,
      complexHingeSixAtom_one, starDot_liftPlane, complexHingeNorm 1])
  · exact Or.inl (by rw [hread, show ((⟨2, by omega⟩ : Fin 6)) = 2 from rfl,
      complexHingeSixAtom_two, starDot_liftPlane, complexHingeNorm 2])
  · exact Or.inl (by rw [hread, show ((⟨3, by omega⟩ : Fin 6)) = 3 from rfl,
      complexHingeSixAtom_three, starDot_liftPlane, complexHingeNorm 3])
  · exact Or.inr (by rw [hread, show ((⟨4, by omega⟩ : Fin 6)) = 4 from rfl,
      complexHingeSixAtom_four, starDot_liftPlane, spreadAtom_norm])
  · exact absurd rfl hlabel

/-- **THE WITNESS IS ALL-HEAVY.**  Every leverage is at least `2`. -/
theorem complexHingeSix_allHeavy (atomLabel : Fin 6) :
    (1 : ℂ) < complexLeverage complexHingeSixDesign atomLabel := by
  by_cases hlabel : atomLabel = 5
  · rw [hlabel, complexHingeSix_leverage_five]; norm_num [Complex.lt_def]
  · rcases complexHingeSix_leverage_plane atomLabel hlabel with hvalue | hvalue <;>
      rw [hvalue] <;> norm_num [Complex.lt_def]

/-- The spike is orthogonal to every other atom, so its overlaps vanish. -/
theorem complexHingeSix_overlap_five (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    complexOverlap complexHingeSixDesign atomLabel 5 = 0 := by
  show (star (complexHingeSixAtom atomLabel) ⬝ᵥ complexHingeSixAtom 5)
      * (star (complexHingeSixAtom 5) ⬝ᵥ complexHingeSixAtom atomLabel) = 0
  rw [complexHingeSixOrth atomLabel hlabel, zero_mul]

/-- **THE PAIR MINORS THROUGH THE SPIKE ARE STRICTLY POSITIVE.**  They are `24` at a
leverage-`2` atom and `36` at the fifth planar atom. -/
theorem complexHingeSix_minor_spike_pos (atomLabel : Fin 6) (hlabel : atomLabel ≠ 5) :
    0 < complexPairGapMinor complexHingeSixDesign atomLabel 5 := by
  rw [complexPairGapMinor, complexHingeSix_leverage_five,
    complexHingeSix_overlap_five atomLabel hlabel]
  rcases complexHingeSix_leverage_plane atomLabel hlabel with hvalue | hvalue <;>
    rw [hvalue] <;> norm_num [Complex.lt_def]

/-- Away from the spike the minor is the planar pair excess of
`Gtz.complexHingePlaneExcess_nonpos`, because lifting preserves every Gram entry. -/
theorem complexHingeSix_minor_eq_planeExcess {first second : Fin 6}
    (hfirst : first ≠ 5) (hsecond : second ≠ 5) :
    complexPairGapMinor complexHingeSixDesign first second
      = (star (complexHingePlaneAtom first) ⬝ᵥ complexHingePlaneAtom first - 1)
          * (star (complexHingePlaneAtom second) ⬝ᵥ complexHingePlaneAtom second - 1)
        - (star (complexHingePlaneAtom first) ⬝ᵥ complexHingePlaneAtom second)
          * (star (complexHingePlaneAtom second) ⬝ᵥ complexHingePlaneAtom first) := by
  show (star (complexHingeSixAtom first) ⬝ᵥ complexHingeSixAtom first - 1)
      * (star (complexHingeSixAtom second) ⬝ᵥ complexHingeSixAtom second - 1)
      - (star (complexHingeSixAtom first) ⬝ᵥ complexHingeSixAtom second)
        * (star (complexHingeSixAtom second) ⬝ᵥ complexHingeSixAtom first) = _
  rw [complexHingeSixAtom_eq_liftPlane first hfirst,
    complexHingeSixAtom_eq_liftPlane second hsecond, starDot_liftPlane, starDot_liftPlane,
    starDot_liftPlane, starDot_liftPlane]

/-! ## Part 3 — every dominating triple of the witness is `K1` -/

/-- **A DOMINATING TRIPLE CONTAINS THE SPIKE.**  A triple that misses it has `-1` on
the third diagonal entry, and a positive semidefinite matrix has a nonnegative
diagonal. -/
theorem complexHingeSix_spike_mem_of_dominates {selected : Finset (Fin 6)}
    (hdominates : ComplexDominates complexHingeSixDesign selected) : (5 : Fin 6) ∈ selected := by
  classical
  by_contra hspike
  have hgap : ((∑ atomLabel ∈ selected, complexAtom (complexHingeSixAtom atomLabel)) - 1) 2 2
      = -1 := by
    rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.one_apply_eq,
      Finset.sum_eq_zero fun probe hprobe =>
        complexAtomSix_diag_two probe (by rintro rfl; exact hspike hprobe)]
    ring
  have hpsd : ((∑ atomLabel ∈ selected, complexAtom (complexHingeSixAtom atomLabel))
      - 1).PosSemidef := hdominates
  have hnonneg : (0 : ℂ) ≤ ((∑ atomLabel ∈ selected,
      complexAtom (complexHingeSixAtom atomLabel)) - 1) 2 2 := hpsd.diag_nonneg (i := 2)
  rw [hgap] at hnonneg
  norm_num [Complex.le_def] at hnonneg

/-- **THE LIVE PAIR OF A DOMINATOR HAS VANISHING MINOR.**  The gap of a spike triple
is block diagonal, so its determinant is `24` times the planar pair excess; that
excess is at most zero at every planar pair, and a positive semidefinite matrix has
a nonnegative determinant.  So the excess is exactly zero. -/
theorem complexHingeSix_planeMinor_eq_zero_of_dominates {first second : Fin 6}
    (hfirst : first ≠ 5) (hsecond : second ≠ 5) (hdistinct : first ≠ second)
    (hdominates : ComplexDominates complexHingeSixDesign {first, second, 5}) :
    complexPairGapMinor complexHingeSixDesign first second = 0 := by
  classical
  obtain ⟨value, hle, hexcess⟩ := complexHingePlaneExcess_nonpos first second hfirst hsecond
  have hpsd : ((∑ atomLabel ∈ ({first, second, 5} : Finset (Fin 6)),
      complexAtom (complexHingeSixAtom atomLabel)) - 1).PosSemidef := hdominates
  have hexpand : (∑ atomLabel ∈ ({first, second, 5} : Finset (Fin 6)),
        complexAtom (complexHingeSixAtom atomLabel))
      = complexAtom (complexHingeSixAtom first)
        + (complexAtom (complexHingeSixAtom second) + complexAtom (complexHingeSixAtom 5)) := by
    rw [Finset.sum_insert (by simp [hdistinct, hfirst]), Finset.sum_insert (by simp [hsecond]),
      Finset.sum_singleton]
  have hdet : ((∑ atomLabel ∈ ({first, second, 5} : Finset (Fin 6)),
      complexAtom (complexHingeSixAtom atomLabel)) - 1).det = 24 * ((value : ℝ) : ℂ) := by
    rw [hexpand, complexHingeSixAtom_five, complexHingeSixAtom_eq_liftPlane first hfirst,
      complexHingeSixAtom_eq_liftPlane second hsecond, det_spikeTriple, hexcess]
  have hnonneg : (0 : ℂ) ≤ 24 * ((value : ℝ) : ℂ) := by
    rw [← hdet]; exact hpsd.det_nonneg
  have hreal : (0 : ℝ) ≤ 24 * value := by
    have hcast : ((24 * value : ℝ) : ℂ) = 24 * ((value : ℝ) : ℂ) := by push_cast; ring
    rw [← hcast] at hnonneg
    simpa using (Complex.le_def.mp hnonneg).1
  have hzero : value = 0 := by linarith
  rw [complexHingeSix_minor_eq_planeExcess hfirst hsecond, hexcess, hzero]
  norm_num

/-- **EVERY DOMINATING TRIPLE OF THE COMPLEX WITNESS IS `K1`.**  It contains the
spike, the other two atoms are its live pair with vanishing minor, and the two
minors through the spike are strictly positive.  So the witness carries no `K0`
dominator and no corner dominator: over `ℂ`, at the target cell, `K1` is the only
reachable stratum. -/
theorem complexHingeSix_every_dominator_isKOne {selected : Finset (Fin 6)}
    (hcard : selected.card = 3)
    (hdominates : ComplexDominates complexHingeSixDesign selected) :
    ∃ liveLeft liveRight : Fin 6, liveLeft ≠ 5 ∧ liveRight ≠ 5 ∧ liveLeft ≠ liveRight
      ∧ selected = {liveLeft, liveRight, 5}
      ∧ complexPairGapMinor complexHingeSixDesign liveLeft liveRight = 0
      ∧ 0 < complexPairGapMinor complexHingeSixDesign liveLeft 5
      ∧ 0 < complexPairGapMinor complexHingeSixDesign liveRight 5 := by
  classical
  have hspike := complexHingeSix_spike_mem_of_dominates hdominates
  have hcardTwo : (selected.erase 5).card = 2 := by
    rw [Finset.card_erase_of_mem hspike, hcard]
  obtain ⟨firstLabel, secondLabel, hdistinct, herase⟩ := Finset.card_eq_two.mp hcardTwo
  have hfirstMem : firstLabel ∈ selected.erase 5 := by rw [herase]; simp
  have hsecondMem : secondLabel ∈ selected.erase 5 := by rw [herase]; simp
  have hfirst : firstLabel ≠ 5 := (Finset.mem_erase.mp hfirstMem).1
  have hsecond : secondLabel ≠ 5 := (Finset.mem_erase.mp hsecondMem).1
  have hsel : selected = {firstLabel, secondLabel, 5} := by
    rw [← Finset.insert_erase hspike, herase]
    ext probe
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  refine ⟨firstLabel, secondLabel, hfirst, hsecond, hdistinct, hsel, ?_,
    complexHingeSix_minor_spike_pos firstLabel hfirst,
    complexHingeSix_minor_spike_pos secondLabel hsecond⟩
  exact complexHingeSix_planeMinor_eq_zero_of_dominates hfirst hsecond hdistinct (hsel ▸ hdominates)

/-! ## Part 4 — the headline, and the no-go it produces -/

/-- **THE COMPLEX WITNESS CARRIES A `K1` DOMINATOR.**  Read at `{2, 3, 5}`: the live
pair `{2, 3}` has minor `0` and the two minors through the spike are `24`. -/
theorem complexHingeSixDesign_hasKOneDominator :
    ComplexHasKOneDominator complexHingeSixDesign := by
  classical
  have hsel : ({5, 2, 3} : Finset (Fin 6)) = {2, 3, 5} := by decide
  refine ⟨5, 2, 3, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · rw [hsel]; exact complexHingeSixDominates
  · exact complexHingeSix_planeMinor_eq_zero_of_dominates (by decide) (by decide) (by decide)
      complexHingeSixDominates
  · rw [complexPairGapMinor_comm]
    exact complexHingeSix_minor_spike_pos 2 (by decide)
  · rw [complexPairGapMinor_comm]
    exact complexHingeSix_minor_spike_pos 3 (by decide)

/-- **THE `K1` STRATUM IS NOT EMPTY OVER `ℂ` AT `(6,3)`.**  The sentence a real lane
wants — every primitive `(6,3)` tie has no `K1` dominator — is FALSE over `ℂ`.

CONSEQUENCE FOR THE ROUTE.  Every instrument whose ingredients all survive the
passage to `ℂ` admits `Gtz.complexHingeSixDesign` as a feasible point, so no such
instrument can empty `K1`.  That retires, at this stratum, the whole field-blind
apparatus: the leverage floor, the two weight caps, the strict bracket floor, the
wedge ceiling, the bracket budget, the strong-pair count and the trichotomy itself.
A `K1` kill must consume realness. -/
theorem not_complexKOneStratumEmpty_six_three :
    ¬ (∀ D : ComplexWeightedDesign 6 3, ComplexIsTie D → ¬ ComplexHasParallelPair D →
        ¬ ComplexHasKOneDominator D) :=
  fun hempty => hempty complexHingeSixDesign complexHingeSixDesign_isTie
    not_complexHingeSixDesign_hasParallelPair complexHingeSixDesign_hasKOneDominator

/-- **THE FEASIBLE POINT, PACKAGED.**  Every clause a field-blind `K1` instrument
could read, at one design: it is an exact complex tie, it has no parallel pair, it
is all-heavy, it carries a `K1` dominator, and every one of its dominators is `K1`. -/
theorem complexHingeSix_kOne_feasible_point :
    ComplexIsTie complexHingeSixDesign
      ∧ ¬ ComplexHasParallelPair complexHingeSixDesign
      ∧ (∀ atomLabel : Fin 6, (1 : ℂ) < complexLeverage complexHingeSixDesign atomLabel)
      ∧ ComplexHasKOneDominator complexHingeSixDesign
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 →
          ComplexDominates complexHingeSixDesign selected →
          ∃ liveLeft liveRight : Fin 6, liveLeft ≠ 5 ∧ liveRight ≠ 5 ∧ liveLeft ≠ liveRight
            ∧ selected = {liveLeft, liveRight, 5}
            ∧ complexPairGapMinor complexHingeSixDesign liveLeft liveRight = 0
            ∧ 0 < complexPairGapMinor complexHingeSixDesign liveLeft 5
            ∧ 0 < complexPairGapMinor complexHingeSixDesign liveRight 5) :=
  ⟨complexHingeSixDesign_isTie, not_complexHingeSixDesign_hasParallelPair,
    complexHingeSix_allHeavy, complexHingeSixDesign_hasKOneDominator,
    fun _ hcard hdominates => complexHingeSix_every_dominator_isKOne hcard hdominates⟩

end Gtz
