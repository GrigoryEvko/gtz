/-
# The floored spread region at rank three: its definition, its non-vacuity, the
# tie it excises, and the one hypothesis a certificate for it would discharge

`Gtz.Certificates.PositivstellensatzObstruction` kills the Putinar/Schmuedgen
half of the Positivstellensatz for the covering at every degree, because the
CLOSED tie-failure system is inhabited: exact ties sit inside it, so no strictly
positive certificate exists globally. The response is to certify a REGION that
contains no tie. This file fixes that region, proves it is neither empty nor
free, proves it does excise the split-tetrahedron tie, and names the sentence a
certificate would supply.

There is no certificate here. Rank three is not proved, and nothing below
claims it is.

## PROVED here

**The region.** `IsFlooredSpreadDesign D spread floor` is `AllHeavy D` together
with a pairwise SPREAD bound and a WEIGHT FLOOR:

  `HasSpreadAtLeast D spread` : every pair of distinct atoms has
    `atomPairing^2 <= (1 - spread) * (leverage * leverage)`, i.e. squared cosine
    at most `1 - spread`, i.e. squared sine at least `spread`;
  `HasWeightFloor D floor` : every weight is at least `floor`.

Both are antitone in their parameter (`hasSpreadAtLeast_mono`,
`hasWeightFloor_mono`), so the region GROWS as the parameters shrink and
`flooredSpreadCovering_mono` records that the covering restricted to it is
correspondingly harder.

**The region is not empty.** `icosaDesign_isFlooredSpreadDesign` puts the
maximal real equiangular `(6,3)` design in the region at the extreme parameters
`spread = 4/5` and `floor = 1/6`: its squared cosine is exactly `1/5`
(`icosaAtom_dot_sq_of_ne` gives `9/5` against leverage `3`) and its weights are
all exactly `1/6`, which is the largest floor six positive weights summing to
one can carry. Since `icosaDesign_dominates` is already proved in
`Gtz.Quantitative.RealnessEngine`, the region contains a design that is covered,
so `FlooredSpreadCovering` is not vacuously false at its witness either.

**The region excises the tie.** `splitTetraDesign_not_hasSpreadAtLeast` shows
the six-atom split tetrahedron of `Gtz.Ties.SplitTetrahedronTie` — an exact tie
for EVERY admissible split, at every weight — fails `HasSpreadAtLeast` for every
`spread > 0`, because it carries duplicated atoms and a duplicated pair has
squared cosine exactly `1`. This is the whole point of the spread parameter: the
obstruction of `PositivstellensatzObstruction` is a tie carrying a parallel pair,
and any positive spread removes THAT tie.

DO NOT STRENGTHEN THIS TO "ties carry parallel pairs". That sentence is
`Gtz.HingeHoldsAtSize`, which is OPEN at sizes six and seven — `0/9` and `1/23`
isomorphism classes discharged in `Gtz.Design.PrimitiveTightClassification` —
and PROVED FALSE at `(5,3)` by `Gtz.not_hingeHoldsAtSize_five_three`, the
diamond being an unsplit tie with pairwise non-parallel atoms.  What is shipped
here is the single witness, not the universal claim.  `splitTetraDesign_hasWeightFloor`
records the complementary fact that the floor alone does NOT remove it — at the
balanced split every weight is `1/8`, so the tie survives every floor up to
`1/8` and the spread parameter is doing work no floor can do.

**The near-orthogonality bridge.** `pairDefect D c d` is
`heavyExcess c * heavyExcess d - 4 * atomPairing c d ^ 2`, the slack in the
hypothesis of `dominates_of_dominantPairings`, and
`HasDominantPairingTriangle D` says three distinct atoms have all three pair
defects nonnegative. `symmetricLegs_nonneg_of_dominantPairingTriangle` turns
such a triangle into the two `S_3`-invariant leg inequalities of
`Gtz.Quantitative.PositivstellensatzRankThree`, so a design owning a triangle is
covered, and `flooredSpreadCovering_of_alwaysDominantPairingTriangle` lifts that
to the region.

**The logical position.** `flooredSpreadCovering_of_symmetricCovering` proves
the trivial direction `SymmetricCovering 6 -> FlooredSpreadCovering spread
floor`. The converse is NOT proved and is not expected to be: the region is a
proper part of the design space, and the complementary part is a separate
branch. What a certificate for this file's hypothesis buys is that branch, not
rank three.

## CITED (proved elsewhere in this repo, used in the proofs below)

`heavyExcess`, `atomPairing`, `atomPairing_comm`, `atomPairing_self`,
`discriminantMinorSum`, `discriminantTie`, `dominates_of_dominantPairings`
(`Gtz.Quantitative.DiscriminantSystem`); `dominates_triple_iff_symmetricLegs`,
`SymmetricCovering` (`Gtz.Quantitative.PositivstellensatzRankThree`);
`AllHeavy` (`Gtz.Reduction.Reductions`); `leverageOf` (`Gtz.Core.Basic`);
`icosaDesign`, `icosaDesign_atom`, `icosaAtom_leverage`,
`icosaAtom_dot_sq_of_ne` (`Gtz.Quantitative.RealnessEngine`);
`splitTetraDesign`, `splitTetraAtom`, `splitTetraDirIndex`
(`Gtz.Ties.SplitTetrahedronTie`); `tetraAtom_dot_self`
(`Gtz.Design.StressCertificate`).

## MEASURED (computed outside Lean, NOT proved here, stated as such)

These are the numbers the region was chosen against. All were computed in the
projection chart `P_cd = sqrt(t_c t_d) <g_c, g_d>` with `P^2 = P` and
`trace P = 3`, whose leg translation was verified symbolically over `Q` and
numerically against the raw definitions above to `1e-12` on hundreds of random
designs; Parseval and idempotency residuals stayed at `1e-14`.

* THE COMPLEX TRINE IS INSIDE THIS REGION. The shared-axis trine of
  `Gtz.Complex.SharpConstantLedger` has minimum pairwise squared sine exactly
  `2/3` and every weight exactly `1/6`, so it satisfies `HasSpreadAtLeast` and
  `HasWeightFloor` at every `spread <= 2/3`, `floor <= 1/6`, is all-heavy, and
  none of its twenty triples dominates. So NO certificate for
  `FlooredSpreadCovering` can be blind to realness, at any parameters this file
  is likely to be used at. This is the check `Gtz.Quantitative.PhaseFreeNoGo`
  demands, run and passed against the region rather than against the global
  system.
* REALNESS IS AVAILABLE, AND IT IS THE IDEAL. The trine's magnitude data
  satisfies the phase-free consequence of idempotency exactly — the row-norm
  identity `sum_{d != c} |P_cd|^2 = P_cc (1 - P_cc)` holds on the nose, at
  `1/4 = 1/2 * 1/2` — yet an exhaustive search over all `1024` gauge-canonical
  sign patterns finds NO real symmetric idempotent of rank three with those
  magnitudes. So the REAL equation `P^2 = P` excludes the trine while every
  phase-free consequence of it does not: the indefinite-sign multiplier the
  no-go requires is exactly an ideal multiplier of `P^2 - P`.
* THE NEAR-ORTHOGONALITY BRIDGE IS NOT ENOUGH ON ITS OWN.
  `flooredSpreadCovering_of_alwaysDominantPairingTriangle` has an antecedent
  that is FALSE at `spread = 1/5`, `floor = 1/20`: about `19%` of sampled region
  designs have a triangle-free `pairDefect` graph, and direct minimisation drives
  `max over triples of min over its three pairs of pairDefect` down to
  `-3.03e-1`, at a design whose value is `1 + 2.30` — it dominates comfortably,
  just not through this sufficient condition. Read through Mantel's theorem the
  bridge asks the `pairDefect` graph on six vertices to contain a triangle, and
  the complex trine realises the extremal triangle-free graph `K_{3,3}` exactly:
  its nine good pairs are precisely the cross-block ones, at defect exactly `0`.
* WHERE THE MARGIN ACTUALLY IS. Minimising `max over triples of the least
  eigenvalue of the triple Gram` over the region, the spread constraint is
  INACTIVE at the minimiser for every `spread` in `[0.02, 0.5]` — the minimiser
  sits at squared sine about `0.598` — and the margin is set by the floor alone,
  scaling as roughly `62 * floor^4`: `3.98e-4` at `floor = 1/20`, `6.21e-3` at
  `1/10`, `3.10e-2` at `0.15`. Ties are a square-root cusp, not the binding
  constraint: opening a duplicated pair to squared sine `s` costs about
  `0.8 * sqrt s` in value, which already exceeds the floor margin for
  `spread` above roughly `2.5e-7`. The quartic degeneration in the floor is the
  reason no certificate at a small floor should be expected to round to
  rationals.
* THE UNWEIGHTED TIE AGGREGATE IS BLIND TO SPREAD. Summing the tie leg over all
  `C(m,3)` triples, after clearing the positive factor `t_a t_b t_c`, gives the
  third elementary symmetric function of `P - diag t`, and Newton's identities
  with `P^2 = P` collapse it to
  `-2/3 + sum_c P_cc t_c + sum_c P_cc t_c^2 - sum_c t_c^2 - (1/3) sum_c t_c^3`,
  a function of the DIAGONAL of `P` and the weights only. Every off-diagonal
  entry cancels, so the spread constraint — which constrains only off-diagonals
  — cannot move it, and it is strictly negative at the split tetrahedron
  (`-3/16` at the balanced split, `-0.1204` at profile `(3,1,1,1)`) where the
  rainbow triples sit at exactly `0`. This is a closed-form sharpening of
  `not_hasUniformTieAggregateSeven`: no NONNEGATIVE weighting of the tie legs
  can be positive at a tie, so a usable aggregate must carry weights that vanish
  on the tie's failing triples, hence weights that see the off-diagonal.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.PositivstellensatzRankThree
import Gtz.Quantitative.RealnessEngine
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The two region parameters -/

/-- **The weight floor.** Every atom carries weight at least `floor`. Six
positive weights summing to one force `floor <= 1/6`, and `icosaDesign` attains
that extreme. -/
def HasWeightFloor (D : WeightedDesign m 3) (floor : ℝ) : Prop :=
  ∀ atomIndex : Fin m, floor ≤ D.weight atomIndex

/-- **The pairwise spread.** Every pair of distinct atoms has squared cosine at
most `1 - spread`, equivalently squared sine at least `spread`. Written without
division so it is a polynomial inequality in the Gram entries: the squared
pairing against the product of the two leverages. -/
def HasSpreadAtLeast (D : WeightedDesign m 3) (spread : ℝ) : Prop :=
  ∀ atomFirst atomSecond : Fin m, atomFirst ≠ atomSecond →
    atomPairing D atomFirst atomSecond ^ 2
      ≤ (1 - spread) * (leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond))

/-- **The floored spread region.** All-heavy, spread at least `spread`, every
weight at least `floor`. -/
def IsFlooredSpreadDesign (D : WeightedDesign m 3) (spread floor : ℝ) : Prop :=
  AllHeavy D ∧ HasSpreadAtLeast D spread ∧ HasWeightFloor D floor

theorem hasWeightFloor_mono {D : WeightedDesign m 3} {floor smallerFloor : ℝ}
    (hle : smallerFloor ≤ floor) (hfloor : HasWeightFloor D floor) :
    HasWeightFloor D smallerFloor :=
  fun atomIndex => hle.trans (hfloor atomIndex)

/-- Leverage is a sum of squares, hence nonnegative — the fact that lets the
spread bound be weakened. -/
theorem leverageOf_nonneg {rank : ℕ} (vec : Fin rank → ℝ) : 0 ≤ leverageOf vec :=
  Finset.sum_nonneg fun coordinate _ => sq_nonneg (vec coordinate)

theorem hasSpreadAtLeast_mono {D : WeightedDesign m 3} {spread smallerSpread : ℝ}
    (hle : smallerSpread ≤ spread) (hspread : HasSpreadAtLeast D spread) :
    HasSpreadAtLeast D smallerSpread := by
  intro atomFirst atomSecond hne
  refine (hspread atomFirst atomSecond hne).trans ?_
  have hleverageProduct : 0 ≤ leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond) :=
    mul_nonneg (leverageOf_nonneg _) (leverageOf_nonneg _)
  exact mul_le_mul_of_nonneg_right (by linarith) hleverageProduct

theorem isFlooredSpreadDesign_mono {D : WeightedDesign m 3}
    {spread floor smallerSpread smallerFloor : ℝ}
    (hspreadLe : smallerSpread ≤ spread) (hfloorLe : smallerFloor ≤ floor)
    (hregion : IsFlooredSpreadDesign D spread floor) :
    IsFlooredSpreadDesign D smallerSpread smallerFloor :=
  ⟨hregion.1, hasSpreadAtLeast_mono hspreadLe hregion.2.1,
    hasWeightFloor_mono hfloorLe hregion.2.2⟩

/-! ## The near-orthogonality bridge

`dominates_of_dominantPairings` proves a triple dominates as soon as every one
of its three pairs satisfies `4 * pairing^2 <= excess * excess`, and
`tetraDesign_pairing_boundary` shows the constant `4` is sharp there. The slack
in that hypothesis is the object a certificate would bound. -/

/-- The slack in the hypothesis of `dominates_of_dominantPairings` at one pair.
Nonnegativity of all three pair defects of a heavy triple forces domination. -/
def pairDefect (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  heavyExcess D atomFirst * heavyExcess D atomSecond
    - 4 * atomPairing D atomFirst atomSecond ^ 2

theorem pairDefect_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    pairDefect D atomFirst atomSecond = pairDefect D atomSecond atomFirst := by
  simp only [pairDefect, atomPairing_comm D atomFirst atomSecond]
  ring

/-- **A near-orthogonal triangle.** Three distinct atoms, pairwise inside the
stratum of `dominates_of_dominantPairings`. -/
def HasDominantPairingTriangle (D : WeightedDesign m 3) : Prop :=
  ∃ first second third : Fin m,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ pairDefect D first second
      ∧ 0 ≤ pairDefect D first third
      ∧ 0 ≤ pairDefect D second third

/-- **A triangle discharges both symmetric legs.** The pair defects are exactly
the hypotheses of `dominates_of_dominantPairings`, and
`dominates_triple_iff_symmetricLegs` reads the resulting domination back as the
two `S_3`-invariant inequalities of the rank-three frontier. -/
theorem symmetricLegs_nonneg_of_dominantPairingTriangle {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) (htriangle : HasDominantPairingTriangle D) :
    ∃ first second third : Fin m,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 0 ≤ discriminantMinorSum D first second third
        ∧ 0 ≤ discriminantTie D first second third := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hdefectFirstSecond, hdefectFirstThird, hdefectSecondThird⟩ := htriangle
  have hdominates : Dominates D {first, second, third} :=
    dominates_of_dominantPairings D hfirstSecond hfirstThird hsecondThird
      (hheavy first) (hheavy second) (hheavy third)
      (by have := hdefectFirstSecond; simp only [pairDefect] at this; linarith)
      (by have := hdefectFirstThird; simp only [pairDefect] at this; linarith)
      (by have := hdefectSecondThird; simp only [pairDefect] at this; linarith)
  obtain ⟨hminor, htie⟩ :=
    (dominates_triple_iff_symmetricLegs D hfirstSecond hfirstThird hsecondThird
      (hheavy first) (hheavy second) (hheavy third)).mp hdominates
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩

/-! ## The named hypothesis -/

/-- **THE SENTENCE A CERTIFICATE FOR THIS BRANCH WOULD SUPPLY.** Every all-heavy
weighted `(6,3)` design whose pairwise squared sines are at least `spread` and
whose weights are at least `floor` has a triple at which both `S_3`-invariant
legs are nonnegative.

This is `SymmetricCovering 6` restricted to the floored spread region. It is
strictly weaker than `SymmetricCovering 6` (the region is a proper part of the
design space) and it is the part of the rank-three frontier where the global
Positivstellensatz obstruction of
`Gtz.Certificates.PositivstellensatzObstruction` does not apply, because
`splitTetraDesign_not_hasSpreadAtLeast` removes the tie that inhabits the closed
tie-failure system. NOT PROVED. -/
def FlooredSpreadCovering (spread floor : ℝ) : Prop :=
  ∀ D : WeightedDesign 6 3, IsFlooredSpreadDesign D spread floor →
    ∃ first second third : Fin 6,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 0 ≤ discriminantMinorSum D first second third
        ∧ 0 ≤ discriminantTie D first second third

/-- The trivial direction: the unrestricted covering implies its restriction. -/
theorem flooredSpreadCovering_of_symmetricCovering (spread floor : ℝ)
    (hcovering : SymmetricCovering 6) : FlooredSpreadCovering spread floor :=
  fun D hregion => hcovering D hregion.1

/-- Shrinking either parameter enlarges the region, so the restricted covering at
the smaller parameters is the stronger statement. -/
theorem flooredSpreadCovering_mono {spread floor smallerSpread smallerFloor : ℝ}
    (hspreadLe : smallerSpread ≤ spread) (hfloorLe : smallerFloor ≤ floor)
    (hcovering : FlooredSpreadCovering smallerSpread smallerFloor) :
    FlooredSpreadCovering spread floor :=
  fun D hregion =>
    hcovering D (isFlooredSpreadDesign_mono hspreadLe hfloorLe hregion)

/-- One route to the hypothesis: if every region design owns a near-orthogonal
triangle then the restricted covering holds. The antecedent is MEASURED FALSE at
`spread = 1/5`, `floor = 1/20` (see the header), so this is recorded as the
bridge it is and not as a live route. -/
theorem flooredSpreadCovering_of_alwaysDominantPairingTriangle {spread floor : ℝ}
    (htriangle : ∀ D : WeightedDesign 6 3, IsFlooredSpreadDesign D spread floor →
      HasDominantPairingTriangle D) :
    FlooredSpreadCovering spread floor :=
  fun D hregion =>
    symmetricLegs_nonneg_of_dominantPairingTriangle hregion.1 (htriangle D hregion)

/-! ## The region is not empty

`icosaDesign` — the maximal real equiangular `(6,3)` design, six diagonals of the
icosahedron at uniform weight `1/6` — sits in the region at the extreme
parameters. Its squared cosine is exactly `1/5`, so its squared sine is exactly
`4/5`, and `1/6` is the largest floor six positive weights summing to one admit. -/

theorem icosaAtom_leverageOf (atomIndex : Fin 6) : leverageOf (icosaAtom atomIndex) = 3 := by
  rw [leverageOf, ← dotProduct_self_eq_sum_sq]
  exact icosaAtom_leverage atomIndex

/-- SHADOWED DUPLICATE — DO NOT CHANGE THE STATEMENT OF THIS OR THE NEXT THEOREM
WITHOUT READING THIS.  `Gtz.icosaDesign_leverage` and `Gtz.icosaDesign_allHeavy`
are ALSO declared, at the same fully-qualified names and with identical
statements but different proofs, in `Gtz/Quantitative/GoodTripleGraph.lean`.
Both modules are in `Gtz.lean`'s import closure, and Lean 4.32 does NOT reject
that: it silently keeps ONE constant.  Asking the environment
(`getModuleIdxFor?`) shows the surviving pair is
`Gtz.Quantitative.GoodTripleGraph`'s, so THE TWO PROOFS BELOW ARE DEAD CODE in
any module that imports both — they are elaborated when this file is checked in
isolation and then dropped.  Nothing is unsound today, precisely because the
statements agree; if they ever diverge, the divergence will be silent and the
`GoodTripleGraph` version will win.  Do not conclude from a green build that no
duplicate exists — a duplicate global with an identical type produces no
diagnostic whatsoever.  The clean repair is to delete both proofs here and
import `Gtz.Quantitative.GoodTripleGraph` (no cycle: it does not import this
file), but note `icosaDesign_isFlooredSpreadDesign` below consumes
`icosaDesign_allHeavy`, so the import is mandatory, not optional. -/
theorem icosaDesign_leverage (atomIndex : Fin 6) :
    leverageOf (icosaDesign.atom atomIndex) = 3 := by
  rw [icosaDesign_atom]
  exact icosaAtom_leverageOf atomIndex

theorem icosaDesign_allHeavy : AllHeavy icosaDesign := by
  intro atomIndex
  rw [icosaDesign_leverage]
  norm_num

theorem icosaDesign_hasSpreadAtLeast : HasSpreadAtLeast icosaDesign (4 / 5) := by
  intro atomFirst atomSecond hne
  rw [atomPairing, icosaDesign_atom, icosaAtom_dot_sq_of_ne hne,
    icosaAtom_leverageOf, icosaAtom_leverageOf]
  norm_num

theorem icosaDesign_hasWeightFloor : HasWeightFloor icosaDesign (1 / 6) :=
  fun _ => le_of_eq rfl

/-- **The region is inhabited**, at the extreme parameters `spread = 4/5` and
`floor = 1/6`; every smaller pair follows by `isFlooredSpreadDesign_mono`. -/
theorem icosaDesign_isFlooredSpreadDesign :
    IsFlooredSpreadDesign icosaDesign (4 / 5) (1 / 6) :=
  ⟨icosaDesign_allHeavy, icosaDesign_hasSpreadAtLeast, icosaDesign_hasWeightFloor⟩

/-! ## The region excises the split-tetrahedron tie

`Gtz.Ties.SplitTetrahedronTie.splitTetraDesign` is an exact tie for every
admissible split. It carries duplicated atoms — `splitTetraDirIndex` is
`![0,1,2,2,3,3]`, so atoms `2` and `3` are the SAME vector — and a duplicated
pair has squared cosine exactly `1`. Any positive spread therefore removes the
whole family, which is precisely what the global Positivstellensatz obstruction
needs removed. -/

section SplitTetrahedron

variable {splitA splitB : ℝ} (hAPos : 0 < splitA) (hALt : splitA < 1 / 4)
  (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4)

/-- Atoms `2` and `3` of the split tetrahedron are the same vector. -/
theorem splitTetraAtom_two_eq_three : splitTetraAtom 2 = splitTetraAtom 3 := rfl

include hAPos hALt hBPos hBLt in
/-- **The spread parameter removes the tie.** The duplicated pair `(2,3)` pairs
at exactly its leverage, so its squared cosine is `1` and no positive spread
tolerates it. -/
theorem splitTetraDesign_not_hasSpreadAtLeast {spread : ℝ} (hspreadPos : 0 < spread) :
    ¬ HasSpreadAtLeast (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) spread := by
  intro hspread
  have hpairing :
      atomPairing (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) 2 3 = 3 := by
    rw [atomPairing, splitTetraDesign_atom, ← splitTetraAtom_two_eq_three]
    exact tetraAtom_dot_self _
  have hleverageTwo :
      leverageOf ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom 2) = 3 := by
    rw [← atomPairing_self, atomPairing, splitTetraDesign_atom]
    exact tetraAtom_dot_self _
  have hleverageThree :
      leverageOf ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom 3) = 3 := by
    rw [← atomPairing_self, atomPairing, splitTetraDesign_atom, ← splitTetraAtom_two_eq_three]
    exact tetraAtom_dot_self _
  have hbound := hspread 2 3 (by decide)
  rw [hpairing, hleverageTwo, hleverageThree] at hbound
  nlinarith [hbound, hspreadPos]

include hAPos hALt hBPos hBLt in
/-- **The floor alone does NOT remove it.** At the balanced split every weight is
`1/8`, so the tie survives every floor up to `1/8`: the spread parameter is doing
work the floor cannot do. -/
theorem splitTetraDesign_balanced_hasWeightFloor
    (hAEq : splitA = 1 / 8) (hBEq : splitB = 1 / 8) :
    HasWeightFloor (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) (1 / 8) := by
  intro atomIndex
  rw [splitTetraDesign_weight]
  subst hAEq
  subst hBEq
  fin_cases atomIndex <;> norm_num

end SplitTetrahedron

end Gtz
