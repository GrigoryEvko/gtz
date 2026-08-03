/-
# Vertex exclusion in phase-free coordinates

`Gtz.Quantitative.PhaseFreeNoGo` builds the phase-free relaxation
`Gtz.IsPhaseFreeAdmissible` — fifteen relations satisfied by every all-heavy real
weighted `(size,3)` design and, with `pairing` read as squared modulus and
`triangle` as the real part of the Bargmann invariant, by every complex one — and
then refutes `Gtz.PhaseFreeCovering` outright at sizes six and seven.  That
refutation is a statement about ONE certificate shape: a single triple carrying
both discriminant legs.  It leaves untouched the question this file addresses,
which is how far a triple-covering argument reaches BEFORE the complex
counterexamples stop it, and exactly which points survive.

The answer is a two-mechanism decomposition of the admissible stratum, plus an
explicit residue.  Write

* `eg` for `Gtz.PhaseFreeData.excessGap`, the sign-blind part of the determinant
  leg, and `t` for `triangle`; the whole file rests on the identity
  `determinantLeg = eg + 2 * t` (`Gtz.PhaseFreeData.determinantLeg_eq_excessGap_add`);
* `s_a` for `Gtz.PhaseFreeData.atomShare`, the mass `w_a * |g_a|^2` an atom
  carries, and call an edge LIGHT when `s_a + s_b <= 1`;
* `R_ab` for `pairing a b * (1 - s_a - s_b)`, the right-hand side of the erase
  law `Gtz.PhaseFreeData.sum_triangle_erasePair`.

The two mechanisms are

* the SIGN-BLIND certificate `Gtz.PhaseFreeData.IsSignBlindGoodTriple`
  (`0 <= eg` and `4 * pairing product <= eg ^ 2`): such a triple dominates at
  every value of the triangle the cap permits, so the moduli alone decide it;
* the EDGE OBSTRUCTION `Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_sum_le`:
  a failing star triple pins its triangle strictly below an explicit bound, the
  erase law adds those bounds against `R_ab`, and a light edge has `R_ab >= 0`.

`Gtz.PhaseFreeData.IsExceptional` is the exact residue — no sign-blind triple
anywhere, and every light edge carrying a star triple that either leaves the
nonneg-trace class or breaks the band — and
`Gtz.exists_covering_witness_of_not_isExceptional` proves that everything outside
it carries the covering witness.  Contrapositively
(`Gtz.isExceptional_of_not_exists_covering_witness`) a point at which no triple
dominates is exceptional; through `Gtz.AllHeavyNonDominating` that caged
statement reaches the shipped `Gtz.SixThreeCrux`.

## What is NOT claimed

`Gtz.PhaseFreeData.IsExceptional` is not proved empty and is not proved
inhabited here.  Both known complex counterexamples of `PhaseFreeNoGo`
(`Gtz.trineSixData`, `Gtz.trineSevenData`) satisfy the first clause, so the
residue is certainly not a formality.

## Relation to the design-side twins

Every object here has a shipped design-level counterpart, and none of them is
usable at this type because `Gtz.PhaseFreeData` is not a design:

| here (phase-free)                            | shipped (design)                              |
| -------------------------------------------- | --------------------------------------------- |
| `Gtz.PhaseFreeData.excessGap`                | `Gtz.excessGap`                                |
| `Gtz.PhaseFreeData.IsSignBlindGoodTriple`    | `Gtz.IsSignBlindGoodTriple`                    |
| `Gtz.PhaseFreeData.determinantLeg_nonneg_of_isSignBlindGoodTriple` | `Gtz.discriminantTie_nonneg_of_isSignBlindGoodTriple` |
| `Gtz.PhaseFreeData.traceLeg_nonneg_of_excessGap_nonneg` | `Gtz.discriminantTrace_nonneg_of_excessGap_nonneg` |
| `Gtz.PhaseFreeData.atomShare`                | `Gtz.atomShare`                                |
| `Gtz.PhaseFreeData.sum_triangle_erasePair`   | `Gtz.sum_erasePair_weight_mul_atomPairing`     |
| `Gtz.PhaseFreeData.excessGap_swap`           | `Gtz.excessGap_swap`                           |

The design side already knows the limits of the sign-blind certificate on its
own: `Gtz.icosaDesign_no_isSignBlindGoodTriple` and
`Gtz.not_signBlindGoodTripleCovering_six`.  Nothing below contradicts that — the
sign-blind mechanism is one of two here, and the exceptional locus is precisely
where neither reaches.
-/
import Gtz.Quantitative.PhaseFreeNoGo
import Gtz.Quantitative.SixThreeCrux

namespace Gtz

open Finset

/-! ## Two facts of real arithmetic, and a warning

The band condition has two readings.  The POINTWISE one, `0 ≤ eg + 2 * |t|`,
mentions the actual triangle.  The FIELD-BLIND one, `0 ≤ eg` or
`eg ^ 2 ≤ 4 * (pairing product)`, mentions only squared moduli and is therefore
the only reading a certificate over `ℂ` can evaluate.

They are NOT interchangeable.  Pointwise implies field-blind, because
`triangleCap` bounds `t ^ 2` by the pairing product.  The converse FAILS as soon
as the cap is strict: at `eg = -2`, `t = 0`, pairing product `1`, the field-blind
band holds with equality (`4 ≤ 4`) while `eg + 2 * |t| = -2 < 0`.  That is not a
corner case — a strict cap is exactly the complex deficit, and
`Gtz.trineSixData`, the counterexample that refutes `Gtz.PhaseFreeCovering 6`,
has `t = 0` at every triple with positive moduli.

So the edge obstruction below is stated pointwise, and the field-blind reading is
licensed only where the cap is an equality, which by
`Gtz.phaseFreeOfDesign_triangle_sq` is every real design. -/

/-- The pointwise band, from the pointwise square condition. -/
theorem zero_le_add_two_mul_abs_of_sq_le (gap triangleValue : ℝ)
    (hband : 0 ≤ gap ∨ gap ^ 2 ≤ 4 * triangleValue ^ 2) :
    0 ≤ gap + 2 * |triangleValue| := by
  rcases hband with hnonneg | hsquare
  · linarith [abs_nonneg triangleValue]
  · by_contra hcontra
    push Not at hcontra
    have habsNonneg : 0 ≤ |triangleValue| := abs_nonneg triangleValue
    have habsSquare : |triangleValue| ^ 2 = triangleValue ^ 2 := sq_abs triangleValue
    nlinarith [hcontra, habsNonneg, habsSquare, hsquare]

/-- **THE BRIDGE.**  Where the cap is an EQUALITY the two readings coincide, so a
moduli-only measurement legitimately discharges the pointwise hypothesis.  Where
it is strict only the left-to-right direction survives — see the warning above. -/
theorem zero_le_add_two_mul_abs_iff_of_sq_eq (gap triangleValue radiusSquare : ℝ)
    (hcap : triangleValue ^ 2 = radiusSquare) :
    0 ≤ gap + 2 * |triangleValue| ↔ (0 ≤ gap ∨ gap ^ 2 ≤ 4 * radiusSquare) := by
  subst hcap
  constructor
  · intro hband
    rcases le_or_gt 0 gap with hnonneg | hnegative
    · exact Or.inl hnonneg
    · refine Or.inr ?_
      have habsSquare : |triangleValue| ^ 2 = triangleValue ^ 2 := sq_abs triangleValue
      nlinarith [hband, hnegative, habsSquare, abs_nonneg triangleValue]
  · exact zero_le_add_two_mul_abs_of_sq_le gap triangleValue

/-- The failure direction of the bridge, recorded so nobody re-derives it: under a
STRICT cap the field-blind band is genuinely weaker.  Any argument that reads the
band off the moduli alone and then applies it pointwise is unsound at a complex
point, which is where `Gtz.PhaseFreeCovering` actually fails. -/
theorem not_forall_zero_le_add_two_mul_abs_of_sq_le :
    ¬ ∀ gap triangleValue radiusSquare : ℝ, triangleValue ^ 2 ≤ radiusSquare →
        gap ^ 2 ≤ 4 * radiusSquare → 0 ≤ gap + 2 * |triangleValue| := by
  intro hforall
  have hbad := hforall (-2) 0 1 (by norm_num) (by norm_num)
  rw [abs_zero] at hbad
  linarith

/-! ## K0: a light pair exists

Rank-uniform, design-free, phase-free-free: purely the averaging identity
`∑_{a ≠ b} (1 - s_a - s_b) = (size - 1) * (size - 2 * rank)`.  The shipped
`Gtz.exists_atomShare_le_rank_div_size` produces ONE atom below the average; a
PAIR is a genuinely second-order fact and does not follow from it. -/

/-- **K0.**  Any `size` reals summing to `rank`, with `2 * rank ≤ size`, contain a
pair summing to at most one.  No positivity, no design, no rank three.

The inequality is EQUALITY exactly at `size = 2 * rank`, where the punctured
double sum vanishes identically — so at the rank-three top `size = 6` every
light edge is light on the nose and none is strictly light.  That degeneracy is
a property of the cell `size = 2 * rank`, not of the argument. -/
theorem exists_pair_share_le_one {size : ℕ} (share : Fin size → ℝ) (rank : ℝ)
    (hsum : ∑ atomIndex, share atomIndex = rank)
    (hsize : 2 * rank ≤ (size : ℝ)) (htwo : 2 ≤ size) :
    ∃ first second : Fin size, first ≠ second ∧ share first + share second ≤ 1 := by
  classical
  have hcard : (Finset.univ : Finset (Fin size)).card = size := by simp
  have hpunctured : ∀ atomIndex : Fin size,
      ∑ other ∈ Finset.univ.erase atomIndex, (1 - share atomIndex - share other)
        = ((size : ℝ) - 1) * (1 - share atomIndex) - (rank - share atomIndex) := by
    intro atomIndex
    have hrest : ∑ other ∈ Finset.univ.erase atomIndex, share other
        = rank - share atomIndex := by
      have hpeel := Finset.add_sum_erase (Finset.univ : Finset (Fin size)) share
        (Finset.mem_univ atomIndex)
      rw [hsum] at hpeel
      linarith
    have hcardErase : (Finset.univ.erase atomIndex).card = size - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ atomIndex), hcard]
    have hone : (1 : ℕ) ≤ size := le_trans (by norm_num) htwo
    rw [Finset.sum_sub_distrib, Finset.sum_const, hrest, hcardErase, nsmul_eq_mul,
      Nat.cast_sub hone, Nat.cast_one]
  have hdouble : ∑ atomIndex : Fin size,
      (((size : ℝ) - 1) * (1 - share atomIndex) - (rank - share atomIndex))
        = ((size : ℝ) - 1) * ((size : ℝ) - 2 * rank) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, hsum, hcard]
    simp only [nsmul_eq_mul]
    ring
  have hsizeReal : (2 : ℝ) ≤ (size : ℝ) := by exact_mod_cast htwo
  have hdoubleNonneg : (0 : ℝ) ≤ ∑ atomIndex : Fin size,
      (((size : ℝ) - 1) * (1 - share atomIndex) - (rank - share atomIndex)) := by
    rw [hdouble]; nlinarith
  obtain ⟨chosen, -, hchosen⟩ :=
    Finset.exists_le_of_sum_le (f := fun _ : Fin size => (0 : ℝ))
      (g := fun atomIndex : Fin size =>
        ((size : ℝ) - 1) * (1 - share atomIndex) - (rank - share atomIndex))
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega)))
      (by simpa using hdoubleNonneg)
  rw [← hpunctured chosen] at hchosen
  have hstarNonempty : (Finset.univ.erase chosen).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ chosen), hcard]
    omega
  obtain ⟨partner, hpartnerMem, hpartner⟩ :=
    Finset.exists_le_of_sum_le (f := fun _ : Fin size => (0 : ℝ))
      (g := fun other : Fin size => 1 - share chosen - share other) hstarNonempty
      (by simpa using hchosen)
  exact ⟨chosen, partner, fun hcollide => (Finset.mem_erase.mp hpartnerMem).1 hcollide.symm,
    by linarith⟩

namespace PhaseFreeData

variable {size : ℕ}

/-! ## The dictionary

Every statement in this section is unconditional: it holds of an arbitrary
`Gtz.PhaseFreeData`, admissible or not. -/

/-- **The sign-blind part of the determinant leg**, in phase-free coordinates.
The design-level twin is `Gtz.excessGap`, which is this expression with `pairing`
spelled out as a squared `Gtz.atomPairing`. -/
def excessGap (point : PhaseFreeData size) (first second third : Fin size) : ℝ :=
  point.excess first * point.excess second * point.excess third
    - (point.excess third * point.pairing first second
        + point.excess second * point.pairing first third
        + point.excess first * point.pairing second third)

/-- **The mass an atom carries**, `w_a * |g_a|^2`.  Admissibility's `traceEqRank`
says these sum to the rank.  The design-level twin is `Gtz.atomShare`. -/
def atomShare (point : PhaseFreeData size) (atomIndex : Fin size) : ℝ :=
  point.weight atomIndex * (point.excess atomIndex + 1)

/-- **THE DICTIONARY.**  The determinant leg splits into a part that reads only
squared moduli and twice the Bargmann triangle.  Everything below is a
consequence of this single identity, and it holds with no hypotheses at all.
Design-level twin: `Gtz.discriminantTie_eq_excessGap_add_tripleProduct`. -/
theorem determinantLeg_eq_excessGap_add (point : PhaseFreeData size)
    (first second third : Fin size) :
    point.determinantLeg first second third
      = point.excessGap first second third + 2 * point.triangle first second third := by
  simp only [determinantLeg, excessGap]
  ring

/-- The determinant leg vanishes exactly at the midpoint of the band. -/
theorem determinantLeg_eq_zero_iff (point : PhaseFreeData size)
    (first second third : Fin size) :
    point.determinantLeg first second third = 0
      ↔ 2 * point.triangle first second third = -point.excessGap first second third := by
  rw [determinantLeg_eq_excessGap_add]
  constructor <;> intro hvalue <;> linarith

/-- The trace leg does not see the order of the two non-pivot atoms.  True of any
`PhaseFreeData`: the expression is literally a sum of two symmetric summands. -/
theorem traceLeg_swapPair (point : PhaseFreeData size) (pivot first second : Fin size) :
    point.traceLeg pivot first second = point.traceLeg pivot second first := by
  simp only [traceLeg]
  ring

/-! ## `S3` invariance of the determinant leg

`Gtz.PhaseFreeCovering` quantifies over ORDERED triples with both legs read at
the same ordering.  These lemmas are what make "the unordered triple dominates"
the right reading of that existential, and they are exactly what lets an edge
argument hand back a witness at whichever ordering the caller wants. -/

theorem excessGap_swap (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.excessGap first second third = point.excessGap second first third := by
  simp only [excessGap, hadmissible.pairingSymm first second]
  ring

theorem excessGap_swapPair (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.excessGap first second third = point.excessGap first third second := by
  simp only [excessGap, hadmissible.pairingSymm second third,
    hadmissible.pairingSymm first second, hadmissible.pairingSymm first third]
  ring

theorem triangle_swapPair (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.triangle first second third = point.triangle first third second := by
  rw [hadmissible.triangleSwap first second third,
    hadmissible.triangleRotate second first third]

theorem determinantLeg_swap (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.determinantLeg first second third = point.determinantLeg second first third := by
  rw [determinantLeg_eq_excessGap_add, determinantLeg_eq_excessGap_add,
    excessGap_swap point hadmissible, hadmissible.triangleSwap first second third]

theorem determinantLeg_swapPair (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.determinantLeg first second third = point.determinantLeg first third second := by
  rw [determinantLeg_eq_excessGap_add, determinantLeg_eq_excessGap_add,
    excessGap_swapPair point hadmissible, triangle_swapPair point hadmissible]

/-- The three-cycle.  With `Gtz.PhaseFreeData.determinantLeg_swap` this generates
the whole of `S3`. -/
theorem determinantLeg_rotate (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size) :
    point.determinantLeg first second third = point.determinantLeg third first second := by
  rw [determinantLeg_swapPair point hadmissible, determinantLeg_swap point hadmissible]

/-! ## The erase law

`IsPhaseFreeAdmissible.parsevalPair` sums the triangle over ALL atoms.  Peeling
the two collapsed diagonal terms turns it into a statement about the STAR of an
edge — the atoms outside it — and that is the single equation every edge
argument below consumes. -/

theorem triangle_repeat_first (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size) :
    point.triangle first second first
      = (point.excess first + 1) * point.pairing first second := by
  rw [hadmissible.triangleRotate first second first,
    hadmissible.triangleRotate second first first,
    hadmissible.triangleCollapse first second]

theorem triangle_repeat_second (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size) :
    point.triangle first second second
      = (point.excess second + 1) * point.pairing first second := by
  rw [hadmissible.triangleRotate first second second,
    hadmissible.triangleCollapse second first, hadmissible.pairingSymm second first]

/-- **THE ERASE LAW.**  The weighted star sum of the triangle over the atoms
OUTSIDE an edge equals the edge's own overlap scaled by the mass the edge leaves
behind.  Rank-free, size-free.

Design-level twin: `Gtz.sum_erasePair_weight_mul_atomPairing`, which is this
identity divided through by the edge overlap; the two agree because the
phase-free `pairing` is the SQUARED overlap and the phase-free `triangle`
carries an extra factor of the edge overlap. -/
theorem sum_triangle_erasePair (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size)
    (hdistinct : first ≠ second) :
    ∑ other ∈ (Finset.univ.erase first).erase second,
        point.weight other * point.triangle first second other
      = point.pairing first second
          * (1 - point.atomShare first - point.atomShare second) := by
  classical
  have hsecondMem : second ∈ Finset.univ.erase first :=
    Finset.mem_erase.mpr ⟨fun hcollide => hdistinct hcollide.symm, Finset.mem_univ second⟩
  have hpeelOuter := Finset.add_sum_erase (Finset.univ : Finset (Fin size))
    (fun other => point.weight other * point.triangle first second other)
    (Finset.mem_univ first)
  have hpeelInner := Finset.add_sum_erase (Finset.univ.erase first)
    (fun other => point.weight other * point.triangle first second other) hsecondMem
  rw [← hpeelInner, hadmissible.parsevalPair first second] at hpeelOuter
  rw [triangle_repeat_first point hadmissible,
    triangle_repeat_second point hadmissible] at hpeelOuter
  simp only [atomShare]
  linarith

/-- Admissibility's `traceEqRank`, said in the vocabulary of shares. -/
theorem sum_atomShare_eq_three (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) :
    ∑ atomIndex, point.atomShare atomIndex = 3 :=
  hadmissible.traceEqRank

/-- **K0 at an admissible point.**  A light edge exists as soon as the point has
at least `2 * 3` atoms.  At `size = 6` — the rank-three top, and the cell the
1997 conjecture is equivalent to — this holds with the punctured double sum
identically zero, so lightness is attained but never strict. -/
theorem exists_pair_atomShare_le_one (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (hsize : 6 ≤ size) :
    ∃ first second : Fin size,
      first ≠ second ∧ point.atomShare first + point.atomShare second ≤ 1 := by
  refine exists_pair_share_le_one point.atomShare 3
    (sum_atomShare_eq_three point hadmissible) ?_ (by omega)
  have hsizeReal : (6 : ℝ) ≤ (size : ℝ) := by exact_mod_cast hsize
  linarith

/-! ## The sign-blind certificate

The moduli-only mechanism.  Fully field-blind: it never mentions the triangle,
so it decides the triple over `ℂ` exactly as over `ℝ`. -/

/-- A triple is **sign-blind good** when its gap is nonnegative and beats the box
radius.  Squared throughout, so no square root appears anywhere.  Design-level
twin: `Gtz.IsSignBlindGoodTriple`, whose unsquared form `2 * |p p p| ≤ eg` is the
same condition because the phase-free `pairing` is already a square. -/
def IsSignBlindGoodTriple (point : PhaseFreeData size)
    (first second third : Fin size) : Prop :=
  0 ≤ point.excessGap first second third
    ∧ 4 * (point.pairing first second * point.pairing second third
        * point.pairing first third) ≤ point.excessGap first second third ^ 2

/-- **The determinant leg of a sign-blind good triple is nonnegative** — at every
value of the triangle the cap permits, hence at every phase.  Uses `triangleCap`
and nothing else: no Parseval, no trace, no rank, no size.
Design-level twin: `Gtz.discriminantTie_nonneg_of_isSignBlindGoodTriple`. -/
theorem determinantLeg_nonneg_of_isSignBlindGoodTriple (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size)
    (hsignBlind : point.IsSignBlindGoodTriple first second third) :
    0 ≤ point.determinantLeg first second third := by
  obtain ⟨hgapNonneg, hgapSquare⟩ := hsignBlind
  rw [determinantLeg_eq_excessGap_add]
  nlinarith [hadmissible.triangleCap first second third, hgapNonneg, hgapSquare,
    sq_nonneg (point.excessGap first second third
      + 2 * point.triangle first second third)]

/-- **The trace leg follows from the gap alone.**  Cancelling the third excess
turns nonnegativity of the gap into the two pair bounds the trace leg needs, so a
sign-blind good triple never has to be checked for membership in the
nonneg-trace class separately.  Design-level twin:
`Gtz.discriminantTrace_nonneg_of_excessGap_nonneg`. -/
theorem traceLeg_nonneg_of_excessGap_nonneg (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size)
    (hgapNonneg : 0 ≤ point.excessGap first second third) :
    0 ≤ point.traceLeg first second third := by
  have hfirstPos := hadmissible.excessPos first
  have hsecondPos := hadmissible.excessPos second
  have hthirdPos := hadmissible.excessPos third
  have hfirstPair := hadmissible.pairingNonneg first second
  have hsecondPair := hadmissible.pairingNonneg first third
  have hthirdPair := hadmissible.pairingNonneg second third
  rw [excessGap] at hgapNonneg
  have hpairFirstSecond : point.pairing first second
      ≤ point.excess first * point.excess second := by
    refine le_of_mul_le_mul_left ?_ hthirdPos
    nlinarith [hgapNonneg, mul_nonneg hsecondPos.le hsecondPair,
      mul_nonneg hfirstPos.le hthirdPair]
  have hpairFirstThird : point.pairing first third
      ≤ point.excess first * point.excess third := by
    refine le_of_mul_le_mul_left ?_ hsecondPos
    nlinarith [hgapNonneg, mul_nonneg hthirdPos.le hfirstPair,
      mul_nonneg hfirstPos.le hthirdPair]
  rw [traceLeg]
  linarith

/-- A sign-blind good triple is banded, so the two mechanisms never conflict: the
per-triple hypothesis of the edge obstruction below is implied by the sign-blind
certificate and cannot be contradictory with it. -/
theorem zero_le_excessGap_add_two_mul_abs_of_isSignBlindGoodTriple
    (point : PhaseFreeData size) (first second third : Fin size)
    (hsignBlind : point.IsSignBlindGoodTriple first second third) :
    0 ≤ point.excessGap first second third
      + 2 * |point.triangle first second third| :=
  zero_le_add_two_mul_abs_of_sq_le _ _ (Or.inl hsignBlind.1)

/-- **The orthogonal corner.**  Three pairwise orthogonal atoms are sign-blind
good for free: the gap collapses to the product of three positive excesses and
the box radius collapses to zero, so no inequality is needed at all.  This is the
phase-free reading of the shipped `Gtz.dominates_of_orthogonalTriple`, and it is
what keeps `Gtz.PhaseFreeData.IsExceptional` from being universally true. -/
theorem isSignBlindGoodTriple_of_pairing_eq_zero (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second third : Fin size)
    (hfirstSecond : point.pairing first second = 0)
    (hfirstThird : point.pairing first third = 0)
    (hsecondThird : point.pairing second third = 0) :
    point.IsSignBlindGoodTriple first second third := by
  have hgap : point.excessGap first second third
      = point.excess first * point.excess second * point.excess third := by
    rw [excessGap, hfirstSecond, hfirstThird, hsecondThird]
    ring
  have hgapPos : 0 < point.excessGap first second third := by
    rw [hgap]
    exact mul_pos (mul_pos (hadmissible.excessPos first) (hadmissible.excessPos second))
      (hadmissible.excessPos third)
  refine ⟨hgapPos.le, ?_⟩
  rw [hfirstSecond]
  nlinarith [hgapPos]

/-! ## The edge obstruction

The second mechanism, and the one that sees the field.  A failing star triple
pins its triangle strictly below a bound; the erase law adds those bounds; the
edge's own slack refuses the total. -/

/-- **THE EDGE OBSTRUCTION, master form.**  Let `bound` be any function that,
whenever a star triple of the edge `(first, second)` fails, strictly majorises
that triple's triangle.  If the weighted star sum of `bound` does not exceed the
edge's slack `R_ab`, some star triple carries a nonnegative determinant leg.

Every corollary below is one choice of `bound`.  No lightness, no band, no
positivity of the edge overlap, no rank and no size hypothesis enters here — the
only ingredients are the erase law and positivity of the weights. -/
theorem exists_star_determinantLeg_nonneg_of_sum_le (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size)
    (hdistinct : first ≠ second) (bound : Fin size → ℝ)
    (hbound : ∀ other ∈ (Finset.univ.erase first).erase second,
      point.determinantLeg first second other < 0 →
        point.triangle first second other < bound other)
    (hstarNonempty : ((Finset.univ.erase first).erase second).Nonempty)
    (hslack : ∑ other ∈ (Finset.univ.erase first).erase second,
        point.weight other * bound other
      ≤ point.pairing first second
          * (1 - point.atomShare first - point.atomShare second)) :
    ∃ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.determinantLeg first second other := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hstrict : ∀ other ∈ (Finset.univ.erase first).erase second,
      point.weight other * point.triangle first second other
        < point.weight other * bound other := by
    intro other hmember
    exact mul_lt_mul_of_pos_left (hbound other hmember (hcontra other hmember))
      (hadmissible.weightPos other)
  have hsumStrict := Finset.sum_lt_sum_of_nonempty hstarNonempty hstrict
  rw [sum_triangle_erasePair point hadmissible first second hdistinct] at hsumStrict
  linarith

/-- **THE EDGE OBSTRUCTION, non-strict form.**  The same statement with a
non-strict per-triple bound and a strict slack.  This is the version the box can
feed: `triangleCap` bounds the triangle by its radius WITHOUT strictness, so a
caller who wants the sharpest bound — the pointwise minimum of `-eg / 2` and the
radius — must come through here.

It also needs no nonemptiness hypothesis: over an empty star both sides of the
erase law are zero and the strict slack is already absurd. -/
theorem exists_star_determinantLeg_nonneg_of_sum_lt (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size)
    (hdistinct : first ≠ second) (bound : Fin size → ℝ)
    (hbound : ∀ other ∈ (Finset.univ.erase first).erase second,
      point.determinantLeg first second other < 0 →
        point.triangle first second other ≤ bound other)
    (hslack : ∑ other ∈ (Finset.univ.erase first).erase second,
        point.weight other * bound other
      < point.pairing first second
          * (1 - point.atomShare first - point.atomShare second)) :
    ∃ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.determinantLeg first second other := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hsum : ∑ other ∈ (Finset.univ.erase first).erase second,
      point.weight other * point.triangle first second other
        ≤ ∑ other ∈ (Finset.univ.erase first).erase second,
          point.weight other * bound other :=
    Finset.sum_le_sum fun other hmember =>
      mul_le_mul_of_nonneg_left (hbound other hmember (hcontra other hmember))
        (hadmissible.weightPos other).le
  rw [sum_triangle_erasePair point hadmissible first second hdistinct] at hsum
  linarith

/-- **K2a.**  A light edge whose whole star is banded carries a star triple with a
nonnegative determinant leg.

Read pointwise, the band `0 ≤ eg + 2 * |t|` forces every failing star triple to
have a STRICTLY NEGATIVE triangle, so the whole star sum is negative while the
erase law makes it the nonnegative number `R_ab`.  Because the argument is
pointwise it needs neither the torsion equality nor a vertex hypothesis, and — as
`Gtz.zero_le_add_two_mul_abs_of_sq_le` shows — the square condition
`eg ^ 2 ≤ 4 * t ^ 2` discharges it.

The band must stay POINTWISE.  Weakening `t ^ 2` to the pairing product, which is
what a field-blind certificate would read, makes the statement FALSE — see
`Gtz.not_forall_exists_star_determinantLeg_nonneg_of_moduliBand`, refuted by the
shipped `Gtz.trineSixData`.  The two readings agree exactly on design images
(`Gtz.phaseFreeOfDesign_zero_le_excessGap_add_two_mul_abs_iff`).

Positivity of the edge overlap is NOT a hypothesis: `pairingNonneg` already
supplies everything the slack needs. -/
theorem exists_star_determinantLeg_nonneg_of_lightEdge (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size)
    (hdistinct : first ≠ second)
    (hlight : point.atomShare first + point.atomShare second ≤ 1)
    (hband : ∀ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.excessGap first second other
        + 2 * |point.triangle first second other|)
    (hstarNonempty : ((Finset.univ.erase first).erase second).Nonempty) :
    ∃ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.determinantLeg first second other := by
  classical
  refine exists_star_determinantLeg_nonneg_of_sum_le point hadmissible first second
    hdistinct (fun _ => 0) ?_ hstarNonempty ?_
  · intro other hmember hfail
    rw [determinantLeg_eq_excessGap_add] at hfail
    have hbandOther := hband other hmember
    rcases le_or_gt 0 (point.triangle first second other) with hnonneg | hnegative
    · rw [abs_of_nonneg hnonneg] at hbandOther
      linarith
    · exact hnegative
  · rw [Finset.sum_congr rfl (fun other _ => mul_zero (point.weight other)),
      Finset.sum_const_zero]
    exact mul_nonneg (hadmissible.pairingNonneg first second) (by linarith)

/-- **The gap-sum obstruction.**  A second choice of `bound`, and the one that
needs no band and no lightness: failure of a star triple says exactly
`eg + 2 * t < 0`, so `t < -eg / 2` unconditionally.  The edge is then closed
whenever its slack is at least minus half the weighted star sum of the gaps.

This reaches HEAVY edges, which `Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge`
cannot, and it never mentions the box; the two corollaries are incomparable. -/
theorem exists_star_determinantLeg_nonneg_of_sum_excessGap (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) (first second : Fin size)
    (hdistinct : first ≠ second)
    (hstarNonempty : ((Finset.univ.erase first).erase second).Nonempty)
    (hslack : -(∑ other ∈ (Finset.univ.erase first).erase second,
        point.weight other * point.excessGap first second other) / 2
      ≤ point.pairing first second
          * (1 - point.atomShare first - point.atomShare second)) :
    ∃ other ∈ (Finset.univ.erase first).erase second,
      0 ≤ point.determinantLeg first second other := by
  classical
  refine exists_star_determinantLeg_nonneg_of_sum_le point hadmissible first second
    hdistinct (fun other => -point.excessGap first second other / 2) ?_ hstarNonempty ?_
  · intro other hmember hfail
    rw [determinantLeg_eq_excessGap_add] at hfail
    linarith
  · calc ∑ other ∈ (Finset.univ.erase first).erase second,
          point.weight other * (-point.excessGap first second other / 2)
        = ∑ other ∈ (Finset.univ.erase first).erase second,
            -(point.weight other * point.excessGap first second other) * (1 / 2) :=
          Finset.sum_congr rfl fun other _ => by ring
      _ = (∑ other ∈ (Finset.univ.erase first).erase second,
            -(point.weight other * point.excessGap first second other)) * (1 / 2) :=
          (Finset.sum_mul _ _ _).symm
      _ = -(∑ other ∈ (Finset.univ.erase first).erase second,
            point.weight other * point.excessGap first second other) * (1 / 2) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ _ := by linarith [hslack]

/-! ## The exceptional locus

Negating the two mechanisms leaves an explicit predicate.  It is the exact
residue: everything outside it carries the covering witness. -/

/-- The triple lies in the **nonnegative-trace class**: SOME choice of pivot makes
the trace leg of `Gtz.PhaseFreeCovering` nonnegative.  A triple outside it cannot
produce the witness however good its determinant leg is. -/
def HasNonnegTraceLeg (point : PhaseFreeData size) (first second third : Fin size) : Prop :=
  0 ≤ point.traceLeg first second third
    ∨ 0 ≤ point.traceLeg second first third
    ∨ 0 ≤ point.traceLeg third first second

/-- Any star triple of an edge that satisfies both per-triple hypotheses of
`Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge` and lies in the
nonnegative-trace class turns a nonnegative determinant leg into the ordered
witness `Gtz.PhaseFreeCovering` asks for, at whichever pivot works. -/
theorem exists_covering_witness_of_star (point : PhaseFreeData size)
    (hadmissible : IsPhaseFreeAdmissible point) {first second other : Fin size}
    (hdistinct : first ≠ second) (hotherFirst : other ≠ first) (hotherSecond : other ≠ second)
    (htrace : point.HasNonnegTraceLeg first second other)
    (hdeterminant : 0 ≤ point.determinantLeg first second other) :
    ∃ pivot pairFirst pairSecond : Fin size,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 ≤ point.traceLeg pivot pairFirst pairSecond
        ∧ 0 ≤ point.determinantLeg pivot pairFirst pairSecond := by
  rcases htrace with htrace | htrace | htrace
  · exact ⟨first, second, other, hdistinct, fun hcollide => hotherFirst hcollide.symm,
      fun hcollide => hotherSecond hcollide.symm, htrace, hdeterminant⟩
  · refine ⟨second, first, other, fun hcollide => hdistinct hcollide.symm,
      fun hcollide => hotherSecond hcollide.symm,
      fun hcollide => hotherFirst hcollide.symm, htrace, ?_⟩
    rwa [← determinantLeg_swap point hadmissible]
  · refine ⟨other, first, second, hotherFirst, hotherSecond, hdistinct, htrace, ?_⟩
    rwa [← determinantLeg_rotate point hadmissible]

/-- **THE EXCEPTIONAL LOCUS.**  A point is exceptional when BOTH mechanisms are
blind to it:

* no triple in the nonnegative-trace class is sign-blind good, and
* every light edge carries a star triple that either leaves the nonnegative-trace
  class or breaks the band.

Note what is absent from the second clause: positivity of the edge overlap.  The
star argument never needs it, so demanding it would only make this locus larger
and the theorem below weaker. -/
def IsExceptional (point : PhaseFreeData size) : Prop :=
  (∀ first second third : Fin size, first ≠ second → first ≠ third → second ≠ third →
      point.HasNonnegTraceLeg first second third →
        ¬ point.IsSignBlindGoodTriple first second third)
    ∧ (∀ first second : Fin size, first ≠ second →
        point.atomShare first + point.atomShare second ≤ 1 →
          ∃ other ∈ (Finset.univ.erase first).erase second,
            ¬ point.HasNonnegTraceLeg first second other
              ∨ point.excessGap first second other
                  + 2 * |point.triangle first second other| < 0)

end PhaseFreeData

/-! ## Vertex exclusion outside the exceptional locus -/

variable {size : ℕ}

/-- **VERTEX EXCLUSION OFF THE EXCEPTIONAL LOCUS.**  Every admissible point with
at least three atoms that is not exceptional carries the covering witness.

The proof is exactly the two mechanisms: negating the first clause hands back a
sign-blind good triple, whose determinant leg is nonnegative by the cap and whose
trace leg is nonnegative by the gap; negating the second hands back a light edge
whose whole star is banded and in the nonnegative-trace class, and the edge
obstruction closes it. -/
theorem exists_covering_witness_of_not_isExceptional {point : PhaseFreeData size}
    (hadmissible : IsPhaseFreeAdmissible point) (hsize : 3 ≤ size)
    (hnotExceptional : ¬ point.IsExceptional) :
    ∃ pivot pairFirst pairSecond : Fin size,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 ≤ point.traceLeg pivot pairFirst pairSecond
        ∧ 0 ≤ point.determinantLeg pivot pairFirst pairSecond := by
  classical
  rw [PhaseFreeData.IsExceptional, not_and_or] at hnotExceptional
  rcases hnotExceptional with hsignBlindBranch | hedgeBranch
  · push Not at hsignBlindBranch
    obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, -, hsignBlind⟩ :=
      hsignBlindBranch
    exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
      PhaseFreeData.traceLeg_nonneg_of_excessGap_nonneg point hadmissible first second third
        hsignBlind.1,
      PhaseFreeData.determinantLeg_nonneg_of_isSignBlindGoodTriple point hadmissible
        first second third hsignBlind⟩
  · push Not at hedgeBranch
    obtain ⟨first, second, hdistinct, hlight, hstar⟩ := hedgeBranch
    have hstarNonempty : ((Finset.univ.erase first).erase second : Finset (Fin size)).Nonempty := by
      rw [← Finset.card_pos,
        Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨fun hcollide => hdistinct hcollide.symm, Finset.mem_univ second⟩),
        Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨other, hmember, hdeterminant⟩ :=
      PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge point hadmissible
        first second hdistinct hlight (fun other hmember => (hstar other hmember).2)
        hstarNonempty
    exact PhaseFreeData.exists_covering_witness_of_star point hadmissible hdistinct
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
      (Finset.mem_erase.mp hmember).1 (hstar other hmember).1 hdeterminant

/-- **THE CRUX CAGE.**  Contrapositive of the above: an admissible point at which
NO triple dominates is exceptional.  This is a necessary condition on any
hypothetical counterexample, and it is sharp in the sense that it is exactly the
negation of the two mechanisms — nothing weaker survives, and nothing stronger is
proved here. -/
theorem isExceptional_of_not_exists_covering_witness {point : PhaseFreeData size}
    (hadmissible : IsPhaseFreeAdmissible point) (hsize : 3 ≤ size)
    (hallFail : ∀ pivot pairFirst pairSecond : Fin size,
      pivot ≠ pairFirst → pivot ≠ pairSecond → pairFirst ≠ pairSecond →
        ¬ (0 ≤ point.traceLeg pivot pairFirst pairSecond
            ∧ 0 ≤ point.determinantLeg pivot pairFirst pairSecond)) :
    point.IsExceptional := by
  by_contra hnotExceptional
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    htrace, hdeterminant⟩ :=
    exists_covering_witness_of_not_isExceptional hadmissible hsize hnotExceptional
  exact hallFail pivot pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct
    ⟨htrace, hdeterminant⟩

/-! ## The bridge to designs

`Gtz.SixThreeCrux` carries eight fields.  The cage consumes exactly two of them,
so stating it there would leave six dead.  `Gtz.AllHeavyNonDominating` is the
carrier that consumes exactly what the cage needs, at general size, and every
crux gives one. -/

/-- The cap holds with EQUALITY at every design image: the phase-free triangle is
the product of three overlaps and the phase-free pairing is an overlap squared.
Consequence, via `Gtz.zero_le_add_two_mul_abs_iff_of_sq_eq`: on design images the
pointwise band of `Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge`
IS the field-blind band, so a moduli-only measurement legitimately discharges it.
Away from design images the cap can be strict — that deficit is precisely the
squared imaginary part of the Bargmann invariant, and it is why
`Gtz.PhaseFreeCovering` is false while the design statement is open. -/
theorem phaseFreeOfDesign_triangle_sq (D : WeightedDesign size 3)
    (first second third : Fin size) :
    (phaseFreeOfDesign D).triangle first second third ^ 2
      = (phaseFreeOfDesign D).pairing first second
        * (phaseFreeOfDesign D).pairing second third
        * (phaseFreeOfDesign D).pairing first third := by
  simp only [phaseFreeOfDesign_triangle, phaseFreeOfDesign_pairing]
  ring

/-- **THE BAND IS FIELD-BLIND AT A DESIGN.**  Combining the previous equality with
`Gtz.zero_le_add_two_mul_abs_iff_of_sq_eq`: on design images the pointwise band
that `Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge` consumes
IS the moduli-only condition.  Off design images the implication runs one way
only, and that gap is the entire distance between the phase-free relaxation and
the real statement. -/
theorem phaseFreeOfDesign_zero_le_excessGap_add_two_mul_abs_iff (D : WeightedDesign size 3)
    (first second third : Fin size) :
    0 ≤ (phaseFreeOfDesign D).excessGap first second third
        + 2 * |(phaseFreeOfDesign D).triangle first second third|
      ↔ (0 ≤ (phaseFreeOfDesign D).excessGap first second third
          ∨ (phaseFreeOfDesign D).excessGap first second third ^ 2
            ≤ 4 * ((phaseFreeOfDesign D).pairing first second
                * (phaseFreeOfDesign D).pairing second third
                * (phaseFreeOfDesign D).pairing first third)) :=
  zero_le_add_two_mul_abs_iff_of_sq_eq _ _ _ (phaseFreeOfDesign_triangle_sq D first second third)

/-- An all-heavy design no triple of which dominates.  Exactly the two fields of
`Gtz.SixThreeCrux` that the cage reads, at general size. -/
structure AllHeavyNonDominating (size : ℕ) where
  /-- The design. -/
  design : WeightedDesign size 3
  /-- Every leverage strictly above one, so the phase-free image is admissible. -/
  isAllHeavy : AllHeavy design
  /-- The failure itself. -/
  hasNoDominatingTriple : ∀ selected : Finset (Fin size), selected.card = 3 →
    ¬ Dominates design selected

/-- Every `Gtz.SixThreeCrux` is such a carrier — so the cage below is strictly
more general than the same statement about a crux. -/
def SixThreeCrux.toAllHeavyNonDominating (crux : SixThreeCrux) : AllHeavyNonDominating 6 where
  design := crux.design
  isAllHeavy := crux.isAllHeavy
  hasNoDominatingTriple := crux.hasNoDominatingTriple

namespace AllHeavyNonDominating

variable (witness : AllHeavyNonDominating size)

/-- The phase-free image of the carrier is admissible. -/
theorem isPhaseFreeAdmissible : IsPhaseFreeAdmissible (phaseFreeOfDesign witness.design) :=
  isPhaseFreeAdmissible_of_design witness.design witness.isAllHeavy

/-- The carrier fails every ordered triple of the phase-free reading. -/
theorem phaseFree_allFail (pivot pairFirst pairSecond : Fin size)
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    ¬ (0 ≤ (phaseFreeOfDesign witness.design).traceLeg pivot pairFirst pairSecond
        ∧ 0 ≤ (phaseFreeOfDesign witness.design).determinantLeg
            pivot pairFirst pairSecond) := by
  rintro ⟨htrace, hdeterminant⟩
  rw [← discriminantTrace_eq_traceLeg] at htrace
  rw [← discriminantTie_eq_determinantLeg] at hdeterminant
  have hdominates :=
    (dominates_triple_iff_discriminantSystem witness.design hpivotFirst hpivotSecond
      hpairDistinct (witness.isAllHeavy pivot)).mpr ⟨htrace, hdeterminant⟩
  have hcard : ({pivot, pairFirst, pairSecond} : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
      Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]
  exact witness.hasNoDominatingTriple _ hcard hdominates

/-- **THE CAGE, ON DESIGNS.**  An all-heavy design no triple of which dominates
has an exceptional phase-free image.  At `size = 6` this applies to every
`Gtz.SixThreeCrux` through `Gtz.SixThreeCrux.toAllHeavyNonDominating`. -/
theorem isExceptional (hsize : 3 ≤ size) :
    (phaseFreeOfDesign witness.design).IsExceptional :=
  isExceptional_of_not_exists_covering_witness witness.isPhaseFreeAdmissible hsize
    witness.phaseFree_allFail

end AllHeavyNonDominating

/-- **THE CAGE, AT THE CELL.**  Every `Gtz.SixThreeCrux` — the carrier the whole
`(6,3)` layer is written against — has an exceptional phase-free image. -/
theorem SixThreeCrux.isExceptional_phaseFree (crux : SixThreeCrux) :
    (phaseFreeOfDesign crux.design).IsExceptional :=
  crux.toAllHeavyNonDominating.isExceptional (by omega)

/-! ## What emptiness of the residue would buy

Two interfaces, one on each side of `Gtz.phaseFreeOfDesign`.  They are the reason
the residue is worth isolating, and they are also where the two sides part
company: the phase-free one is DEAD, because `Gtz.PhaseFreeCovering 6` is refuted
and so its hypothesis is refuted with it, while the design-side one is open. -/

/-- Every admissible point being non-exceptional would give `Gtz.PhaseFreeCovering`
outright.  Combined with the shipped `Gtz.not_phaseFreeCovering_six` this is a
second proof that the residue is inhabited at size six — an alternative to
`Gtz.exists_isExceptional_six`, which names the witness instead. -/
theorem phaseFreeCovering_of_forall_not_isExceptional (hsize : 3 ≤ size)
    (hnone : ∀ point : PhaseFreeData size, IsPhaseFreeAdmissible point →
      ¬ point.IsExceptional) :
    PhaseFreeCovering size :=
  fun point hadmissible =>
    exists_covering_witness_of_not_isExceptional hadmissible hsize (hnone point hadmissible)

/-- **THE DESIGN-SIDE PAYOFF.**  An all-heavy design whose phase-free image is not
exceptional has a dominating triple.

This is the statement that does not die with `Gtz.PhaseFreeCovering`.  The
phase-free relaxation is false because it admits complex points; a DESIGN image
is not such a point — its `triangleCap` is an equality
(`Gtz.phaseFreeOfDesign_triangle_sq`) — so quantifying the residue over design
images only is strictly weaker than quantifying it over all admissible points,
and the two shipped counterexamples `Gtz.trineSixData` and `Gtz.trineSevenData`
do not inhabit it.  Whether some design image is exceptional is exactly what this
file leaves open. -/
theorem exists_dominates_of_not_isExceptional (D : WeightedDesign size 3)
    (hheavy : AllHeavy D) (hsize : 3 ≤ size)
    (hnotExceptional : ¬ (phaseFreeOfDesign D).IsExceptional) :
    ∃ selected : Finset (Fin size), selected.card = 3 ∧ Dominates D selected := by
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    htrace, hdeterminant⟩ :=
    exists_covering_witness_of_not_isExceptional (isPhaseFreeAdmissible_of_design D hheavy)
      hsize hnotExceptional
  rw [← discriminantTrace_eq_traceLeg] at htrace
  rw [← discriminantTie_eq_determinantLeg] at hdeterminant
  refine ⟨{pivot, pairFirst, pairSecond}, ?_,
    (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
      (hheavy pivot)).mpr ⟨htrace, hdeterminant⟩⟩
  rw [Finset.card_insert_of_notMem (by simp [hpivotFirst, hpivotSecond]),
    Finset.card_insert_of_notMem (by simp [hpairDistinct]), Finset.card_singleton]

/-- **THE CAGE, MADE EXISTENTIAL.**  Clause two of the residue is a statement
about every light edge, and by `Gtz.PhaseFreeData.exists_pair_atomShare_le_one`
there always IS one once the point has `2 * 3` atoms.  So an exceptional point
carries an ACTUAL star triple that leaves the nonneg-trace class or breaks the
band — the residue is never satisfied by having no light edge to check. -/
theorem exists_lightEdge_bad_star_of_isExceptional {point : PhaseFreeData size}
    (hadmissible : IsPhaseFreeAdmissible point) (hsize : 6 ≤ size)
    (hexceptional : point.IsExceptional) :
    ∃ first second : Fin size, first ≠ second
      ∧ point.atomShare first + point.atomShare second ≤ 1
      ∧ ∃ other ∈ (Finset.univ.erase first).erase second,
          ¬ point.HasNonnegTraceLeg first second other
            ∨ point.excessGap first second other
                + 2 * |point.triangle first second other| < 0 := by
  obtain ⟨first, second, hdistinct, hlight⟩ :=
    PhaseFreeData.exists_pair_atomShare_le_one point hadmissible hsize
  exact ⟨first, second, hdistinct, hlight, hexceptional.2 first second hdistinct hlight⟩

/-! ## Both sides are inhabited

A conditional theorem is worth what its hypotheses are worth.  These two records
say that neither of the two statements above is empty: the exceptional locus has
points in it, so the cage's conclusion is not the empty set, and the exceptional
locus is not everything, so vertex exclusion off it is not vacuous. -/

/-- **THE EXCEPTIONAL LOCUS IS INHABITED.**  `Gtz.trineSixData` — the complex
counterexample that refutes `Gtz.PhaseFreeCovering 6` — is exceptional, because
it fails every triple and the cage applies.  So the residue this file isolates is
not a formality, and no argument can close it by showing it empty in the
phase-free relaxation.  Whether the DESIGN images inside it are empty is a
different and open question: `trineSixData` is not one. -/
theorem exists_isExceptional_six :
    ∃ point : PhaseFreeData 6, IsPhaseFreeAdmissible point ∧ point.IsExceptional := by
  refine ⟨trineSixData, trineSixData_isPhaseFreeAdmissible,
    isExceptional_of_not_exists_covering_witness trineSixData_isPhaseFreeAdmissible
      (by omega) ?_⟩
  rintro pivot pairFirst pairSecond hpivotFirst - - ⟨-, hdeterminant⟩
  exact absurd hdeterminant
    (not_le.mpr (trineSixData_determinantLeg_neg pivot pairFirst pairSecond hpivotFirst))

/-- The same at size seven, the size that decides rank three for every `n`
through `Gtz.discriminantCovering_seven_iff_rank_three`. -/
theorem exists_isExceptional_seven :
    ∃ point : PhaseFreeData 7, IsPhaseFreeAdmissible point ∧ point.IsExceptional := by
  refine ⟨trineSevenData, trineSevenData_isPhaseFreeAdmissible,
    isExceptional_of_not_exists_covering_witness trineSevenData_isPhaseFreeAdmissible
      (by omega) ?_⟩
  rintro pivot pairFirst pairSecond hpivotFirst hpivotSecond hpairDistinct ⟨-, hdeterminant⟩
  exact absurd hdeterminant (not_le.mpr (trineSevenData_determinantLeg_neg pivot pairFirst
    pairSecond hpivotFirst hpivotSecond hpairDistinct))

/-- **THE MODULI READING OF THE EDGE OBSTRUCTION IS FALSE.**  Replacing the
pointwise band of `Gtz.PhaseFreeData.exists_star_determinantLeg_nonneg_of_lightEdge`
by the field-blind band — the reading a certificate over `ℂ` would evaluate — does
not merely weaken the theorem, it makes it untrue, and the shipped
`Gtz.trineSixData` is the counterexample.

Every one of its fifteen edges is light (every share is exactly `1/2`), every one
of its twenty triples satisfies the field-blind band (`eg = -2`, pairing product
`3`, so `4 ≤ 12`; and `eg = -10`, product `27`, so `100 ≤ 108` on the two
same-family triples), and yet no triple whatsoever has a nonnegative determinant
leg.  The pointwise band, by contrast, fails at all twenty, because every
triangle is zero while every gap is negative.

The moral is the one that separates this file from a field-blind argument: the
band may be READ off the moduli only where `triangleCap` is an equality, which by
`Gtz.phaseFreeOfDesign_triangle_sq` is exactly the real designs.  Any transcription
that drops that distinction is unsound at precisely the points where
`Gtz.PhaseFreeCovering` actually fails. -/
theorem not_forall_exists_star_determinantLeg_nonneg_of_moduliBand :
    ¬ ∀ (pointSize : ℕ) (point : PhaseFreeData pointSize), IsPhaseFreeAdmissible point →
        ∀ first second : Fin pointSize, first ≠ second →
          point.atomShare first + point.atomShare second ≤ 1 →
            (∀ other ∈ (Finset.univ.erase first).erase second,
              0 ≤ point.excessGap first second other
                ∨ point.excessGap first second other ^ 2
                  ≤ 4 * (point.pairing first second * point.pairing second other
                      * point.pairing first other)) →
            ((Finset.univ.erase first).erase second).Nonempty →
              ∃ other ∈ (Finset.univ.erase first).erase second,
                0 ≤ point.determinantLeg first second other := by
  intro hforall
  have hpairing : ∀ first second : Fin 6,
      trineSixData.pairing first second = trineOverlap first second := fun _ _ => rfl
  have hgap : ∀ first second third : Fin 6, trineSixData.excessGap first second third
      = 8 - (2 * trineOverlap first second + 2 * trineOverlap first third
          + 2 * trineOverlap second third) := by
    intro first second third
    show (2 : ℝ) * 2 * 2 - (2 * trineOverlap first second + 2 * trineOverlap first third
      + 2 * trineOverlap second third) = _
    norm_num
  have hlight : trineSixData.atomShare 0 + trineSixData.atomShare 1 ≤ 1 := by
    show (1 / 6 : ℝ) * (2 + 1) + 1 / 6 * (2 + 1) ≤ 1
    norm_num
  have hband : ∀ other ∈ (Finset.univ.erase (0 : Fin 6)).erase 1,
      0 ≤ trineSixData.excessGap 0 1 other
        ∨ trineSixData.excessGap 0 1 other ^ 2
          ≤ 4 * (trineSixData.pairing 0 1 * trineSixData.pairing 1 other
              * trineSixData.pairing 0 other) := by
    intro other hmember
    have hotherFirst : other ≠ 0 :=
      (Finset.mem_erase.mp (Finset.mem_of_mem_erase hmember)).1
    have hotherSecond : other ≠ 1 := (Finset.mem_erase.mp hmember).1
    clear hmember
    refine Or.inr ?_
    simp only [hgap, hpairing]
    fin_cases other <;> revert hotherFirst hotherSecond <;>
      norm_num [trineOverlap, trineFamily, Fin.ext_iff]
  have hstarNonempty : ((Finset.univ.erase (0 : Fin 6)).erase 1).Nonempty :=
    ⟨2, Finset.mem_erase.mpr ⟨by decide,
      Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ 2⟩⟩⟩
  obtain ⟨other, -, hdeterminant⟩ :=
    hforall 6 trineSixData trineSixData_isPhaseFreeAdmissible 0 1 (by decide) hlight hband
      hstarNonempty
  exact absurd hdeterminant (not_le.mpr (trineSixData_determinantLeg_neg 0 1 other (by decide)))

/-- Three pairwise orthogonal directions of squared length three at equal weight:
the smallest admissible phase-free point that is not a trine, written directly
rather than through `Gtz.phaseFreeOfDesign` so that no matrix identity has to be
discharged. -/
noncomputable def orthogonalTriplePoint : PhaseFreeData 3 where
  weight := fun _ => 1 / 3
  excess := fun _ => 2
  pairing := fun first second => if first = second then 9 else 0
  triangle := fun first second third => if first = second ∧ second = third then 27 else 0

theorem orthogonalTriplePoint_isPhaseFreeAdmissible :
    IsPhaseFreeAdmissible orthogonalTriplePoint where
  weightPos := fun _ => by norm_num [orthogonalTriplePoint]
  weightSumOne := by simp [orthogonalTriplePoint]
  excessPos := fun _ => by norm_num [orthogonalTriplePoint]
  traceEqRank := by norm_num [orthogonalTriplePoint, Fin.sum_univ_three]
  pairingSymm := fun first second => by
    simp only [orthogonalTriplePoint, eq_comm (a := first) (b := second)]
  pairingDiag := fun _ => by norm_num [orthogonalTriplePoint]
  pairingNonneg := fun first second => by
    simp only [orthogonalTriplePoint]; split_ifs <;> norm_num
  pairingCap := fun first second => by
    simp only [orthogonalTriplePoint]; split_ifs <;> norm_num
  triangleSwap := fun first second third => by
    simp only [orthogonalTriplePoint]
    by_cases hfirstSecond : first = second
    · subst hfirstSecond; simp
    · rw [if_neg (fun hpair => hfirstSecond hpair.1),
        if_neg (fun hpair => hfirstSecond hpair.1.symm)]
  triangleRotate := fun first second third => by
    simp only [orthogonalTriplePoint]
    by_cases hfirstSecond : first = second
    · subst hfirstSecond
      by_cases hsecondThird : first = third
      · subst hsecondThird; simp
      · rw [if_neg (fun hpair => hsecondThird hpair.2), if_neg (fun hpair => hsecondThird hpair.1)]
    · rw [if_neg (fun hpair => hfirstSecond hpair.1)]
      by_cases hsecondThird : second = third
      · subst hsecondThird
        rw [if_neg (fun hpair => hfirstSecond hpair.2.symm)]
      · rw [if_neg (fun hpair => hsecondThird hpair.1)]
  triangleCollapse := fun first second => by
    simp only [orthogonalTriplePoint]
    by_cases hpair : first = second
    · subst hpair; norm_num
    · rw [if_neg (fun hboth => hpair hboth.2), if_neg hpair]; norm_num
  parsevalDiag := fun atomIndex => by
    simp only [orthogonalTriplePoint, Fin.sum_univ_three]
    fin_cases atomIndex <;> norm_num [Fin.ext_iff]
  parsevalPair := fun first second => by
    simp only [orthogonalTriplePoint, Fin.sum_univ_three]
    fin_cases first <;> fin_cases second <;> norm_num [Fin.ext_iff]
  triangleCap := fun first second third => by
    simp only [orthogonalTriplePoint]
    by_cases hall : first = second ∧ second = third
    · obtain ⟨hone, htwo⟩ := hall
      subst hone; subst htwo; norm_num
    · rw [if_neg hall]
      have hnonneg : ∀ leftIndex rightIndex : Fin 3,
          (0 : ℝ) ≤ if leftIndex = rightIndex then 9 else 0 := by
        intro leftIndex rightIndex; split_ifs <;> norm_num
      simpa using mul_nonneg (mul_nonneg (hnonneg first second) (hnonneg second third))
        (hnonneg first third)
  leverageCap := fun _ => by norm_num [orthogonalTriplePoint]

/-- **THE EXCEPTIONAL LOCUS IS NOT EVERYTHING.**  A point carrying three pairwise
orthogonal atoms is outside it, so
`Gtz.exists_covering_witness_of_not_isExceptional` has content.  Orthogonality is
the one corner of the covering that needs no inequality; compare the shipped
design-level `Gtz.dominates_of_orthogonalTriple`.  The witness that inhabits this
hypothesis is `Gtz.orthogonalTriplePoint`, and
`Gtz.exists_not_isExceptional` records the conclusion. -/
theorem not_isExceptional_of_pairing_eq_zero {point : PhaseFreeData size}
    (hadmissible : IsPhaseFreeAdmissible point) {first second third : Fin size}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hpairFirstSecond : point.pairing first second = 0)
    (hpairFirstThird : point.pairing first third = 0)
    (hpairSecondThird : point.pairing second third = 0) :
    ¬ point.IsExceptional := by
  intro hexceptional
  have hsignBlind := PhaseFreeData.isSignBlindGoodTriple_of_pairing_eq_zero point hadmissible
    first second third hpairFirstSecond hpairFirstThird hpairSecondThird
  refine hexceptional.1 first second third hfirstSecond hfirstThird hsecondThird ?_ hsignBlind
  exact Or.inl (PhaseFreeData.traceLeg_nonneg_of_excessGap_nonneg point hadmissible
    first second third hsignBlind.1)

/-- **THE EXCEPTIONAL LOCUS IS NOT EVERYTHING.**  `Gtz.orthogonalTriplePoint` is
admissible and outside it, so `Gtz.exists_covering_witness_of_not_isExceptional`
is not vacuous. -/
theorem exists_not_isExceptional :
    ∃ point : PhaseFreeData 3, IsPhaseFreeAdmissible point ∧ ¬ point.IsExceptional := by
  refine ⟨orthogonalTriplePoint, orthogonalTriplePoint_isPhaseFreeAdmissible, ?_⟩
  refine not_isExceptional_of_pairing_eq_zero orthogonalTriplePoint_isPhaseFreeAdmissible
    (first := 0) (second := 1) (third := 2) (by decide) (by decide) (by decide) ?_ ?_ ?_ <;>
    norm_num [orthogonalTriplePoint, Fin.ext_iff]

/-! ## The equality case

The sign-blind certificate is TIGHT.  Where the gap exactly matches twice the box
radius, the determinant leg is still nonnegative but the box endpoint sends it to
zero, so no strictly positive margin is available there.  This is the algebraic
shape of the campaign's zero-margin boundary condition. -/

/-- **THE SIGN-BLIND CERTIFICATE IS TIGHT.**  At `eg^2 = 4 * (pairing product)`
the value `-eg / 2` saturates the cap and annihilates the determinant leg.  So on
that locus the certificate holds with zero margin, and no strengthening of it by
a positive constant can survive.  Field-blind: the statement mentions only
squared moduli. -/
theorem PhaseFreeData.exists_saturating_triangle_of_excessGap_sq_eq
    (point : PhaseFreeData size) (first second third : Fin size)
    (hsquare : point.excessGap first second third ^ 2
      = 4 * (point.pairing first second * point.pairing second third
          * point.pairing first third)) :
    ∃ triangleValue : ℝ,
      triangleValue ^ 2 = point.pairing first second * point.pairing second third
          * point.pairing first third
        ∧ point.excessGap first second third + 2 * triangleValue = 0 :=
  ⟨-point.excessGap first second third / 2, by nlinarith [hsquare], by ring⟩

end Gtz
