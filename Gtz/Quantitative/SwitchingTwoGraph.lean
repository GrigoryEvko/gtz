/-
# Switching, the two-graph, and the parity the sign-blind wall cannot see

`Gtz.not_signBlindGoodTripleCovering_six` refutes every certificate that reads
only `|p_cd|`, so the only material left in the tie leg is the SIGN of the
oriented triple product. `Gtz/LinAlg/SignForcing.lean` supplies that sign at the
level of three bare VECTORS -- `Gtz.triangleProduct`, its invariance
`Gtz.triangleProduct_smul` under arbitrary rescaling, and Lemma A. What it does
NOT supply, and what `Gtz/Quantitative/CheapAtomGate.lean` explicitly records as
missing ("the sign gauge `s_c = sign(gamma_6c)` ... is NOT mechanized"), is the
DESIGN-level layer: an action of the signs on `WeightedDesign` itself, a sign
pattern as an object, and a dictionary from that pattern to `discriminantTie`.
This file supplies exactly that.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

**The action (section 2).** `Gtz.switchedDesign` negates a chosen set of atoms.
It lands in `WeightedDesign m k` at EVERY rank, because `atomMatrix` is
quadratic: `(s g)(s g)^T = s^2 g g^T = g g^T` when `s^2 = 1`, so Parseval
survives verbatim. Everything domination depends on is then invariant on the
nose -- `Gtz.subsetSum_switchedDesign`, `Gtz.dominates_switchedDesign_iff`,
`Gtz.allHeavy_switchedDesign_iff`. This is the legitimacy lemma: it is what makes
the sign pattern a GAUGE rather than data, and without it every sign argument
below would be an argument about a chosen representative.

**The pattern and its invariant (sections 3-4).** `Gtz.edgeSign` is the `+-1`
sign of `Gtz.atomPairing`, and `Gtz.tripleParity` is the product of the three
edge signs of a triple. The edge sign is EQUIVARIANT
(`Gtz.edgeSign_switchedDesign`, `s_c s_d` times the old one) and the triple
parity is INVARIANT (`Gtz.tripleParity_switchedDesign`), because each atom meets
exactly two of the three edges. That is Seidel switching, and the parity is the
two-graph.

**The bridge (section 5).** `Gtz.discriminantTie_eq_excessGap_add_parity`:

  `discriminantTie = excessGap + 2 * tripleParity * |p_ab p_ac p_bc|`

refining the shipped `Gtz.discriminantTie_eq_excessGap_add_tripleProduct` by
pulling the sign out of the oriented product. Since `excessGap` and the absolute
value are exactly what a sign-blind certificate sees, this ISOLATES the entire
non-sign-blind content of the tie leg in one `+-1` factor, and
`Gtz.abs_discriminantTie_sub_excessGap` prices it: the two parities differ by
exactly `4 |p_ab p_ac p_bc|`. The case split is
`Gtz.discriminantTie_of_coherent` / `Gtz.discriminantTie_of_incoherent`, and
`Gtz.isSignBlindGoodTriple_iff_adverseTie_nonneg` says the shipped sign-blind
cell is precisely "the tie survives the ADVERSE parity".

**The two-graph axiom (section 7).** `Gtz.tripleParity_fourSet_product`: in every
four-atom set the four triple parities multiply to `1`, because each of the six
edges lies in exactly two of the four triangles. Hence
`Gtz.even_negativeParity_count_fourSet` -- the number of incoherent triangles in
a `4`-set is `0`, `2` or `4`, never odd. This is the defining axiom of a
two-graph, it holds with NO hypothesis, and it is the discrete structure that
realness buys.

**A counting constraint (section 8).** Combining the two-graph axiom with the
shipped Lemma A: among any five atoms with pairwise nonzero pairings, some
coherent triple passes through ANY prescribed one of them
(`Gtz.exists_tripleParity_eq_one_through_base`), hence at size at least five EVERY
atom of the design carries one (`Gtz.exists_coherentTriple_through_atom`). The
four-set axiom is what upgrades Lemma A's unlocated coherent triple to a located
one: `Gtz.tripleParity_eq_neg_one_of_base_incoherent` propagates incoherence from
a base to the triangles avoiding it, so a totally incoherent vertex would force a
totally incoherent five-set, and Lemma A forbids that.

**Calibration (section 6), at exact rational arithmetic and against the campaign's
own tie strata.** The tetrahedron and the rainbow triples of `splitSevenDesign`
both sit at `excessGap = 2`, `|product| = 1` and parity `-1`, so the bridge
returns `discriminantTie = 0` EXACTLY -- reproducing the shipped
`Gtz.tetraDesign_discriminantTie` and
`Gtz.splitSevenDesign_discriminantTie_of_rainbowDirections`. The margin at the tie
is genuinely zero, and it is the NEGATIVE parity that puts it there: at parity
`+1` the same numbers would give `+4`. At the icosahedron the parity decides
domination outright (`Gtz.icosaDesign_dominates_iff_tripleParity`), by exact
rational comparison of squares with no `Real.sqrt` anywhere.

## NOT proved here

* Nothing here produces a dominating triple in any open cell, and nothing
  lower-bounds the oriented product against `excessGap`. That bound is the open
  problem and this file does not touch it.
* `Gtz.dominates_of_coherent_of_excessGap_nonneg` is a genuinely non-sign-blind
  sufficient cell, but it is NOT exhibited to be strictly larger than the shipped
  `Gtz.dominates_of_isSignBlindGoodTriple`: no design is produced here that is
  coherent with `0 <= excessGap` and fails `2|product| <= excessGap`. All four
  calibration points have `excessGap < 0` wherever the parity is `+1`. The cell
  is offered as a dictionary entry, not as a measured enlargement.
* Coherence certifies NOTHING on its own, and the repo's own witness says so: a
  `splitSevenDesign` triple repeating a direction has parity `+1` and
  `discriminantTie = -8` (`Gtz.splitSevenDesign_tripleParity_of_repeatedDirection`).
* **THE SHARP COUNT AT SIX AND SEVEN LINES IS NOT REACHED, and that is a wall,
  not an omission.** Section 8 proves only that the incoherent triangles cannot be
  ALL of them at any one vertex. It does not produce a NUMBER -- no lower bound on
  how many of the `20` triples at `m = 6`, or the `35` at `m = 7`, must be
  coherent. Two routes were identified and both were declined as engineering, not
  as mathematics. (i) Switch at a base so every base edge is negative
  (`Gtz.switchSign`); then a base-avoiding set of atoms that is pairwise negative
  after switching is pairwise obtuse together with the base, so the obtuse bound
  caps it at `4` and the switched positive-edge graph has independence number at
  most `3`; since a graph on `n` vertices with `e` edges has an independent set of
  size at least `n - e`, that forces `e >= n - 3`, i.e. at least `m - 4` coherent
  triples through EVERY base. This needs `Gtz.switchedDesign` composed with the
  `Gtz.switchSign` gauge plus a `Finset` independence-number argument. (ii) Double
  count: every five-subset carries a coherent triple and every triple lies in
  `C(m-3,2)` of them, giving at least `C(m,5)/C(m-3,2)` coherent triples -- `2` at
  `m = 6` and `4` at `m = 7`, weaker than (i)'s `6` and `7`. Both are `Finset`
  cardinality engineering of a size this file did not take on.
* The sharper stratum-specific count at `(6,3)` -- at most seven of the ten triples
  through an atom are coherent -- is already landed as
  `Gtz.coherentCount_le_seven`, whose combinatorial core takes the edge signs as an
  abstract parameter. This file supplies the missing OBJECT that core abstracts
  over (`Gtz.edgeSign`) but does NOT complete its design-level assembly: the mirror
  balance hypothesis it consumes is not derived here.
* NO CLAIM IS MADE ABOUT THE COMPLEX CASE. The realness is structural and is
  argued in prose only: over `R` the gauge group on each atom is `{+1,-1}`, so the
  invariant of a triple is one BIT satisfying the exact four-set constraint above,
  whereas over `C` the gauge group is the circle. The mechanized measure of that
  separation in this repo is the field door of `Gtz/LinAlg/SignForcing.lean` --
  obtuse bound `4` over `R^3` against `7` over `C^3`, both exact -- not anything
  proved here.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.GoodTripleGraph
import Gtz.LinAlg.SignForcing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 1. Scalar cancellation: a sign meets each edge twice

Every invariance below is one of these two identities. The first is why a SQUARED
pairing forgets the gauge; the second is why the ORIENTED TRIPLE PRODUCT does,
and it is the whole reason the two-graph exists: in `(s_a s_b)(s_a s_c)(s_b s_c)`
each sign occurs exactly twice. -/

private theorem eq_one_or_neg_one_of_sq_eq_one {value : ℝ} (hsquare : value ^ 2 = 1) :
    value = 1 ∨ value = -1 := by
  have hfactor : (value - 1) * (value + 1) = 0 := by linear_combination hsquare
  rcases mul_eq_zero.mp hfactor with hlow | hhigh
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A gauged pairing has the same square: each of the two signs appears twice. -/
private theorem signPair_sq_cancel (signFirst signSecond value : ℝ)
    (hfirst : signFirst ^ 2 = 1) (hsecond : signSecond ^ 2 = 1) :
    (signFirst * signSecond * value) ^ 2 = value ^ 2 := by
  linear_combination (signSecond ^ 2 * value ^ 2) * hfirst + value ^ 2 * hsecond

/-- **The two-graph identity, in scalars.** The oriented product of the three
gauged edges of a triangle is the ungauged one, because each of the three signs
meets exactly two of the three edges. -/
private theorem signTriple_product_cancel (signFirst signSecond signThird
    valueFirst valueSecond valueThird : ℝ) (hfirst : signFirst ^ 2 = 1)
    (hsecond : signSecond ^ 2 = 1) (hthird : signThird ^ 2 = 1) :
    signFirst * signSecond * valueFirst * (signFirst * signThird * valueSecond)
        * (signSecond * signThird * valueThird)
      = valueFirst * valueSecond * valueThird := by
  linear_combination
    (signSecond ^ 2 * signThird ^ 2 * valueFirst * valueSecond * valueThird) * hfirst
      + (signThird ^ 2 * valueFirst * valueSecond * valueThird) * hsecond
      + (valueFirst * valueSecond * valueThird) * hthird

/-- Six `+-1` edge signs, each squared once, multiply to one. The arithmetic core
of the four-set two-graph axiom. -/
private theorem sixSign_square_product (edgeOne edgeTwo edgeThree edgeFour edgeFive
    edgeSix : ℝ) (hone : edgeOne ^ 2 = 1) (htwo : edgeTwo ^ 2 = 1)
    (hthree : edgeThree ^ 2 = 1) (hfour : edgeFour ^ 2 = 1) (hfive : edgeFive ^ 2 = 1)
    (hsix : edgeSix ^ 2 = 1) :
    edgeOne * edgeTwo * edgeThree * (edgeOne * edgeFour * edgeFive)
        * (edgeTwo * edgeFour * edgeSix) * (edgeThree * edgeFive * edgeSix) = 1 := by
  have hregroup : edgeOne * edgeTwo * edgeThree * (edgeOne * edgeFour * edgeFive)
      * (edgeTwo * edgeFour * edgeSix) * (edgeThree * edgeFive * edgeSix)
      = edgeOne ^ 2 * (edgeTwo ^ 2 * (edgeThree ^ 2
          * (edgeFour ^ 2 * (edgeFive ^ 2 * edgeSix ^ 2)))) := by ring
  rw [hregroup, hone, htwo, hthree, hfour, hfive, hsix]
  norm_num

/-! ## 2. The switching action on designs

Negating any set of atoms is an action on `WeightedDesign` at every rank, and it
fixes every quantity domination is defined from. This is the lemma that makes the
whole layer legitimate. -/

/-- A **switching sign vector**: one `+-1` per atom. Stated as `s^2 = 1` rather
than as a disjunction because that is the form every cancellation consumes. -/
def IsSwitchingSign (signs : Fin m → ℝ) : Prop :=
  ∀ atomIndex, signs atomIndex ^ 2 = 1

theorem isSwitchingSign_one : IsSwitchingSign (fun _ : Fin m => (1 : ℝ)) :=
  fun _ => one_pow 2

theorem IsSwitchingSign.eq_one_or_neg_one {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomIndex : Fin m) :
    signs atomIndex = 1 ∨ signs atomIndex = -1 :=
  eq_one_or_neg_one_of_sq_eq_one (hsigns atomIndex)

theorem IsSwitchingSign.ne_zero {signs : Fin m → ℝ} (hsigns : IsSwitchingSign signs)
    (atomIndex : Fin m) : signs atomIndex ≠ 0 := by
  intro hzero
  have hsquare := hsigns atomIndex
  rw [hzero] at hsquare
  norm_num at hsquare

/-- **THE SWITCHING ACTION.** Negate each atom by its sign. Parseval survives
verbatim at every rank because `atomMatrix` is quadratic, so this really is an
action on designs and not merely on vector families. -/
def switchedDesign (D : WeightedDesign m k) (signs : Fin m → ℝ)
    (hsigns : IsSwitchingSign signs) : WeightedDesign m k where
  atom := fun atomIndex => signs atomIndex • D.atom atomIndex
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    rw [← D.isParseval]
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [atomMatrix_smul, hsigns atomIndex, one_smul]

@[simp] theorem switchedDesign_atom (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomIndex : Fin m) :
    (switchedDesign D signs hsigns).atom atomIndex = signs atomIndex • D.atom atomIndex :=
  rfl

@[simp] theorem switchedDesign_weight (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) : (switchedDesign D signs hsigns).weight = D.weight :=
  rfl

/-- The rank-one atom is untouched: the gauge is invisible to `g g^T`. -/
theorem atomMatrix_switchedDesign (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomIndex : Fin m) :
    atomMatrix ((switchedDesign D signs hsigns).atom atomIndex)
      = atomMatrix (D.atom atomIndex) := by
  rw [switchedDesign_atom, atomMatrix_smul, hsigns atomIndex, one_smul]

/-- Every atom sum is untouched. -/
theorem subsetSum_switchedDesign (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (selected : Finset (Fin m)) :
    subsetSum (switchedDesign D signs hsigns) selected = subsetSum D selected :=
  Finset.sum_congr rfl fun atomIndex _ => atomMatrix_switchedDesign D hsigns atomIndex

/-- **DOMINATION IS A SWITCHING INVARIANT.** The lemma that makes the sign pattern
a gauge: negating atoms cannot create or destroy a dominating subset. -/
theorem dominates_switchedDesign_iff (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (selected : Finset (Fin m)) :
    Dominates (switchedDesign D signs hsigns) selected ↔ Dominates D selected := by
  rw [Dominates, Dominates, subsetSum_switchedDesign]

theorem leverageOf_switchedDesign (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomIndex : Fin m) :
    leverageOf ((switchedDesign D signs hsigns).atom atomIndex) = leverageOf (D.atom atomIndex) := by
  rw [← trace_atomMatrix, ← trace_atomMatrix, atomMatrix_switchedDesign]

theorem allHeavy_switchedDesign_iff (D : WeightedDesign m k) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) :
    AllHeavy (switchedDesign D signs hsigns) ↔ AllHeavy D := by
  constructor <;> intro hheavy atomIndex
  · have hhere := hheavy atomIndex
    rwa [leverageOf_switchedDesign] at hhere
  · rw [leverageOf_switchedDesign]
    exact hheavy atomIndex

/-! ### The rank-three scalars under switching -/

theorem heavyExcess_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomIndex : Fin m) :
    heavyExcess (switchedDesign D signs hsigns) atomIndex = heavyExcess D atomIndex := by
  rw [heavyExcess, heavyExcess, leverageOf_switchedDesign]

/-- **The gauge is visible on an edge**: the pairing picks up the product of the
two endpoint signs. This is the only place the gauge acts nontrivially. -/
theorem atomPairing_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomFirst atomSecond : Fin m) :
    atomPairing (switchedDesign D signs hsigns) atomFirst atomSecond
      = signs atomFirst * signs atomSecond * atomPairing D atomFirst atomSecond := by
  simp only [atomPairing, switchedDesign_atom, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- The squared pairing forgets the gauge. -/
theorem atomPairing_sq_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomFirst atomSecond : Fin m) :
    atomPairing (switchedDesign D signs hsigns) atomFirst atomSecond ^ 2
      = atomPairing D atomFirst atomSecond ^ 2 := by
  rw [atomPairing_switchedDesign]
  exact signPair_sq_cancel _ _ _ (hsigns atomFirst) (hsigns atomSecond)

/-- **The oriented triple product forgets the gauge too** -- the design-level form
of `Gtz.triangleProduct_smul_of_sq_eq_one`, and the fact the two-graph is built
on. -/
theorem atomPairingProduct_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (first second third : Fin m) :
    atomPairing (switchedDesign D signs hsigns) first second
        * atomPairing (switchedDesign D signs hsigns) first third
        * atomPairing (switchedDesign D signs hsigns) second third
      = atomPairing D first second * atomPairing D first third
          * atomPairing D second third := by
  rw [atomPairing_switchedDesign, atomPairing_switchedDesign, atomPairing_switchedDesign]
  exact signTriple_product_cancel _ _ _ _ _ _ (hsigns first) (hsigns second) (hsigns third)

theorem pairMinor_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (atomFirst atomSecond : Fin m) :
    pairMinor (switchedDesign D signs hsigns) atomFirst atomSecond
      = pairMinor D atomFirst atomSecond := by
  rw [pairMinor, pairMinor, heavyExcess_switchedDesign, heavyExcess_switchedDesign,
    atomPairing_sq_switchedDesign]

theorem excessGap_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (first second third : Fin m) :
    excessGap (switchedDesign D signs hsigns) first second third
      = excessGap D first second third := by
  rw [excessGap, excessGap, heavyExcess_switchedDesign, heavyExcess_switchedDesign,
    heavyExcess_switchedDesign, atomPairing_sq_switchedDesign,
    atomPairing_sq_switchedDesign, atomPairing_sq_switchedDesign]

/-- **The tie leg is a switching invariant.** Both of its halves are: the
sign-blind gap because it reads only squares, the oriented product because each
sign meets two edges. -/
theorem discriminantTie_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) (first second third : Fin m) :
    discriminantTie (switchedDesign D signs hsigns) first second third
      = discriminantTie D first second third := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct,
    discriminantTie_eq_excessGap_add_tripleProduct, excessGap_switchedDesign,
    atomPairingProduct_switchedDesign]

/-! ## 3. The sign pattern

`Gtz.edgeSign` is the sign pattern of the Gram, with the convention `sign 0 = +1`
so that it is `+-1` everywhere and the four-set axiom of section 7 needs no
nondegeneracy hypothesis. The convention costs exactly one thing, and it is
flagged where it is spent: the switching equivariance below needs the edge to be
nonzero, since at a vanishing pairing the design-level gauge acts trivially while
the graph-level gauge does not. That is the same nondegeneracy hypothesis Lemma A
already carries. -/

/-- **The edge sign** of a pair: `+1` when the pairing is nonnegative, `-1` when
it is negative. The sign pattern of the Gram, and the object
`Gtz.edgeSignSum` and `Gtz.coherentCount_le_seven` take as an abstract
parameter. -/
noncomputable def edgeSign (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) : ℝ :=
  if 0 ≤ atomPairing D atomFirst atomSecond then 1 else -1

theorem edgeSign_sq (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond ^ 2 = 1 := by
  rw [edgeSign]
  split <;> norm_num

theorem edgeSign_eq_one_or_neg_one (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond = 1 ∨ edgeSign D atomFirst atomSecond = -1 :=
  eq_one_or_neg_one_of_sq_eq_one (edgeSign_sq D atomFirst atomSecond)

theorem edgeSign_ne_zero (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond ≠ 0 := by
  intro hzero
  have hsquare := edgeSign_sq D atomFirst atomSecond
  rw [hzero] at hsquare
  norm_num at hsquare

theorem edgeSign_comm (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond = edgeSign D atomSecond atomFirst := by
  rw [edgeSign, edgeSign, atomPairing_comm]

/-- **The sign carries the pairing.** Unconditional, including at a vanishing
pairing where both sides are zero. -/
theorem edgeSign_mul_abs_atomPairing (D : WeightedDesign m 3) (atomFirst atomSecond : Fin m) :
    edgeSign D atomFirst atomSecond * |atomPairing D atomFirst atomSecond|
      = atomPairing D atomFirst atomSecond := by
  rw [edgeSign]
  split
  · rename_i hnonneg
    rw [one_mul, abs_of_nonneg hnonneg]
  · rename_i hnegative
    rw [abs_of_neg (not_le.mp hnegative)]
    ring

/-- The gauge multiplies the edge sign by the two endpoint signs -- Seidel
switching, at the level of the pattern. The nonzero hypothesis is where the
convention `sign 0 = +1` is paid for. -/
theorem edgeSign_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) {atomFirst atomSecond : Fin m}
    (hnonzero : atomPairing D atomFirst atomSecond ≠ 0) :
    edgeSign (switchedDesign D signs hsigns) atomFirst atomSecond
      = signs atomFirst * signs atomSecond * edgeSign D atomFirst atomSecond := by
  have hgauge : signs atomFirst * signs atomSecond = 1
      ∨ signs atomFirst * signs atomSecond = -1 := by
    rcases hsigns.eq_one_or_neg_one atomFirst with hfirst | hfirst <;>
      rcases hsigns.eq_one_or_neg_one atomSecond with hsecond | hsecond <;>
      rw [hfirst, hsecond] <;> norm_num
  simp only [edgeSign, atomPairing_switchedDesign D hsigns atomFirst atomSecond]
  rcases hgauge with hpositive | hnegative
  · rw [hpositive, one_mul, one_mul]
  · rw [hnegative]
    rcases lt_or_gt_of_ne hnonzero with hlow | hhigh
    · rw [if_pos (by linarith : (0:ℝ) ≤ -1 * atomPairing D atomFirst atomSecond),
        if_neg (not_le.mpr hlow)]
      ring
    · rw [if_neg (not_le.mpr (by linarith :
          -1 * atomPairing D atomFirst atomSecond < 0)), if_pos hhigh.le]
      ring

/-! ## 4. The triple parity: the two-graph

The parity of a triple is the product of its three edge signs. It is the
switching invariant, and it is the ONE BIT that no sign-blind certificate can
read. -/

/-- **THE TRIPLE PARITY.** `+1` on a COHERENT triangle, `-1` on an INCOHERENT
one. Switching-invariant (`Gtz.tripleParity_switchedDesign`), so it is a function
of the two-graph and not of a chosen sign representative. -/
noncomputable def tripleParity (D : WeightedDesign m 3) (first second third : Fin m) : ℝ :=
  edgeSign D first second * edgeSign D first third * edgeSign D second third

theorem tripleParity_sq (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third ^ 2 = 1 := by
  rw [tripleParity, mul_pow, mul_pow, edgeSign_sq, edgeSign_sq, edgeSign_sq]
  norm_num

/-- The parity is a BIT: it takes exactly the two values `+-1`. -/
theorem tripleParity_eq_one_or_neg_one (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third = 1 ∨ tripleParity D first second third = -1 :=
  eq_one_or_neg_one_of_sq_eq_one (tripleParity_sq D first second third)

theorem tripleParity_ne_zero (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third ≠ 0 := by
  rcases tripleParity_eq_one_or_neg_one D first second third with hvalue | hvalue <;>
    rw [hvalue] <;> norm_num

theorem tripleParity_comm_left (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third = tripleParity D second first third := by
  rw [tripleParity, tripleParity, edgeSign_comm D first second]
  ring

theorem tripleParity_comm_right (D : WeightedDesign m 3) (first second third : Fin m) :
    tripleParity D first second third = tripleParity D first third second := by
  rw [tripleParity, tripleParity, edgeSign_comm D third second]
  ring

/-- **The parity carries the oriented product.** Unconditional. -/
theorem tripleParity_mul_abs_atomPairingProduct (D : WeightedDesign m 3)
    (first second third : Fin m) :
    tripleParity D first second third
        * |atomPairing D first second * atomPairing D first third
            * atomPairing D second third|
      = atomPairing D first second * atomPairing D first third
          * atomPairing D second third := by
  rw [abs_mul, abs_mul, tripleParity,
    show edgeSign D first second * edgeSign D first third * edgeSign D second third
        * (|atomPairing D first second| * |atomPairing D first third|
          * |atomPairing D second third|)
      = edgeSign D first second * |atomPairing D first second|
        * (edgeSign D first third * |atomPairing D first third|)
        * (edgeSign D second third * |atomPairing D second third|) from by ring,
    edgeSign_mul_abs_atomPairing, edgeSign_mul_abs_atomPairing, edgeSign_mul_abs_atomPairing]

theorem tripleParity_eq_one_of_pos_atomPairingProduct (D : WeightedDesign m 3)
    {first second third : Fin m}
    (hpositive : 0 < atomPairing D first second * atomPairing D first third
      * atomPairing D second third) :
    tripleParity D first second third = 1 := by
  have hcarry := tripleParity_mul_abs_atomPairingProduct D first second third
  have habs : |atomPairing D first second * atomPairing D first third
      * atomPairing D second third|
      = atomPairing D first second * atomPairing D first third
        * atomPairing D second third := abs_of_pos hpositive
  rw [habs] at hcarry
  rcases tripleParity_eq_one_or_neg_one D first second third with hvalue | hvalue
  · exact hvalue
  · rw [hvalue] at hcarry; linarith

theorem tripleParity_eq_neg_one_of_neg_atomPairingProduct (D : WeightedDesign m 3)
    {first second third : Fin m}
    (hnegative : atomPairing D first second * atomPairing D first third
      * atomPairing D second third < 0) :
    tripleParity D first second third = -1 := by
  have hcarry := tripleParity_mul_abs_atomPairingProduct D first second third
  have habs : |atomPairing D first second * atomPairing D first third
      * atomPairing D second third|
      = -(atomPairing D first second * atomPairing D first third
        * atomPairing D second third) := abs_of_neg hnegative
  rw [habs] at hcarry
  rcases tripleParity_eq_one_or_neg_one D first second third with hvalue | hvalue
  · rw [hvalue] at hcarry; linarith
  · exact hvalue

/-- **THE PARITY IS THE SWITCHING INVARIANT.** Negating any set of atoms leaves it
fixed, because each atom meets exactly two of a triangle's three edges. This is
Seidel switching, and it is what makes the parity a two-graph invariant rather
than a property of a representative. -/
theorem tripleParity_switchedDesign (D : WeightedDesign m 3) {signs : Fin m → ℝ}
    (hsigns : IsSwitchingSign signs) {first second third : Fin m}
    (hfirstSecond : atomPairing D first second ≠ 0)
    (hfirstThird : atomPairing D first third ≠ 0)
    (hsecondThird : atomPairing D second third ≠ 0) :
    tripleParity (switchedDesign D signs hsigns) first second third
      = tripleParity D first second third := by
  rw [tripleParity, edgeSign_switchedDesign D hsigns hfirstSecond,
    edgeSign_switchedDesign D hsigns hfirstThird,
    edgeSign_switchedDesign D hsigns hsecondThird]
  exact signTriple_product_cancel _ _ _ _ _ _ (hsigns first) (hsigns second) (hsigns third)

/-! ## 5. The bridge to the discriminant system

The shipped `Gtz.discriminantTie_eq_excessGap_add_tripleProduct` splits the tie
leg into a sign-blind part and the oriented product. Refining the oriented product
into `parity` times `magnitude` puts every sign-blind quantity on one side and the
single bit on the other. -/

/-- **THE BRIDGE.** The tie leg is the sign-blind gap plus twice the parity times
the magnitude of the pairing product. Both `Gtz.excessGap` and the absolute value
are exactly what a sign-blind certificate reads, so the entire non-sign-blind
content of the tie leg is the `+-1` factor. -/
theorem discriminantTie_eq_excessGap_add_parity (D : WeightedDesign m 3)
    (first second third : Fin m) :
    discriminantTie D first second third
      = excessGap D first second third
        + 2 * tripleParity D first second third
            * |atomPairing D first second * atomPairing D first third
                * atomPairing D second third| := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct,
    show 2 * tripleParity D first second third
        * |atomPairing D first second * atomPairing D first third
            * atomPairing D second third|
      = 2 * (tripleParity D first second third
        * |atomPairing D first second * atomPairing D first third
            * atomPairing D second third|) from by ring,
    tripleParity_mul_abs_atomPairingProduct]

/-- At a COHERENT triangle the oriented term helps by its full magnitude. -/
theorem discriminantTie_of_coherent (D : WeightedDesign m 3) {first second third : Fin m}
    (hparity : tripleParity D first second third = 1) :
    discriminantTie D first second third
      = excessGap D first second third
        + 2 * |atomPairing D first second * atomPairing D first third
            * atomPairing D second third| := by
  rw [discriminantTie_eq_excessGap_add_parity, hparity]
  ring

/-- At an INCOHERENT triangle it hurts by exactly the same amount. -/
theorem discriminantTie_of_incoherent (D : WeightedDesign m 3) {first second third : Fin m}
    (hparity : tripleParity D first second third = -1) :
    discriminantTie D first second third
      = excessGap D first second third
        - 2 * |atomPairing D first second * atomPairing D first third
            * atomPairing D second third| := by
  rw [discriminantTie_eq_excessGap_add_parity, hparity]
  ring

/-- **THE PRICE OF THE BIT.** The tie leg departs from its sign-blind part by
exactly twice the magnitude of the pairing product, in the direction the parity
names. So the two parities of one magnitude profile are `4 |p_ab p_ac p_bc|`
apart -- that number is what a sign-blind certificate must forfeit. -/
theorem abs_discriminantTie_sub_excessGap (D : WeightedDesign m 3)
    (first second third : Fin m) :
    |discriminantTie D first second third - excessGap D first second third|
      = 2 * |atomPairing D first second * atomPairing D first third
          * atomPairing D second third| := by
  rw [discriminantTie_eq_excessGap_add_parity,
    show excessGap D first second third
        + 2 * tripleParity D first second third
          * |atomPairing D first second * atomPairing D first third
              * atomPairing D second third|
        - excessGap D first second third
      = tripleParity D first second third
          * (2 * |atomPairing D first second * atomPairing D first third
              * atomPairing D second third|) from by ring,
    abs_mul, abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 2 * |atomPairing D first second * atomPairing D first third
        * atomPairing D second third|)]
  rcases tripleParity_eq_one_or_neg_one D first second third with hvalue | hvalue <;>
    rw [hvalue] <;> norm_num

/-- **The shipped sign-blind cell is exactly "the tie survives the ADVERSE
parity".** `Gtz.IsSignBlindGoodTriple` demands `2|product| <= excessGap`, which is
precisely nonnegativity of the value the bridge returns at parity `-1`. That is
the logical form of the wall: the sign-blind family is the parity-independent part
of the tie leg, and `Gtz.not_signBlindGoodTripleCovering_six` says that part does
not cover. -/
theorem isSignBlindGoodTriple_iff_adverseTie_nonneg (D : WeightedDesign m 3)
    (first second third : Fin m) :
    IsSignBlindGoodTriple D first second third
      ↔ 0 ≤ excessGap D first second third
          - 2 * |atomPairing D first second * atomPairing D first third
              * atomPairing D second third| := by
  rw [IsSignBlindGoodTriple]
  constructor <;> intro hbound <;> linarith

/-- At a coherent triangle a NONNEGATIVE sign-blind gap already forces a
nonnegative tie leg -- the `2|product| <= excessGap` of the sign-blind cell is not
needed, because the oriented term is helping rather than hurting. -/
theorem discriminantTie_nonneg_of_coherent_of_excessGap_nonneg (D : WeightedDesign m 3)
    {first second third : Fin m} (hparity : tripleParity D first second third = 1)
    (hgap : 0 ≤ excessGap D first second third) :
    0 ≤ discriminantTie D first second third := by
  rw [discriminantTie_of_coherent D hparity]
  have habs := abs_nonneg (atomPairing D first second * atomPairing D first third
    * atomPairing D second third)
  linarith

/-- **A CERTIFICATE CELL THAT IS NOT SIGN-BLIND.** A coherent triple of distinct
heavy atoms with nonnegative sign-blind gap dominates.

HONESTY: this is a dictionary entry, not a measured enlargement of the certified
region. It is not sign-blind (it reads `Gtz.tripleParity`), so
`Gtz.not_signBlindGoodTripleCovering_seven` does not reach it, and its hypothesis
is formally weaker than `Gtz.IsSignBlindGoodTriple` in the coherent sector. But no
design is exhibited anywhere in this file that satisfies it and fails the shipped
sign-blind cell: at all four calibration points of section 6 the gap is negative
wherever the parity is `+1`. Nothing here bounds the oriented product from below
against the gap, and that bound is the open problem. -/
theorem dominates_of_coherent_of_excessGap_nonneg {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hparity : tripleParity D first second third = 1)
    (hgap : 0 ≤ excessGap D first second third) :
    Dominates D {first, second, third} :=
  (dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird hsecondThird
      (hheavy first)).mpr
    ⟨discriminantTrace_nonneg_of_excessGap_nonneg D (allHeavy_heavyExcess_pos hheavy first)
        (allHeavy_heavyExcess_pos hheavy second) (allHeavy_heavyExcess_pos hheavy third) hgap,
      discriminantTie_nonneg_of_coherent_of_excessGap_nonneg D hparity hgap⟩

/-! ## 6. Calibration at the campaign's tie strata

Every check below is exact rational arithmetic; no `Real.sqrt` appears. The two
tie strata must come out with margin EXACTLY zero, because the margin genuinely is
zero there, and they do. -/

theorem tetraDesign_edgeSign_zeroOne : edgeSign tetraDesign 0 1 = -1 := by
  rw [edgeSign, if_neg (by rw [tetraDesign_atomPairing_zeroOne]; norm_num)]

theorem tetraDesign_edgeSign_zeroTwo : edgeSign tetraDesign 0 2 = -1 := by
  rw [edgeSign, if_neg (by rw [tetraDesign_atomPairing_zeroTwo]; norm_num)]

theorem tetraDesign_edgeSign_oneTwo : edgeSign tetraDesign 1 2 = -1 := by
  rw [edgeSign, if_neg (by rw [tetraDesign_atomPairing_oneTwo]; norm_num)]

/-- **The regular tetrahedron's triple is INCOHERENT.** -/
theorem tetraDesign_tripleParity : tripleParity tetraDesign 0 1 2 = -1 := by
  rw [tripleParity, tetraDesign_edgeSign_zeroOne, tetraDesign_edgeSign_zeroTwo,
    tetraDesign_edgeSign_oneTwo]
  norm_num

/-- **THE TIGHTNESS CHECK AT THE `(4,3)` TIE.** Feeding the bridge the
tetrahedron's own numbers -- gap `2`, magnitude `1`, parity `-1` -- returns
`discriminantTie = 0` on the nose, reproducing the shipped
`Gtz.tetraDesign_discriminantTie`. The margin at the tie is exactly zero, and it
is the INCOHERENCE that puts it there: at parity `+1` these same magnitudes would
give `+4`. -/
theorem tetraDesign_bridge_at_tie :
    excessGap tetraDesign 0 1 2
        + 2 * tripleParity tetraDesign 0 1 2
          * |atomPairing tetraDesign 0 1 * atomPairing tetraDesign 0 2
              * atomPairing tetraDesign 1 2|
      = 0 := by
  rw [tetraDesign_excessGap, tetraDesign_tripleParity, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo, tetraDesign_atomPairing_oneTwo]
  norm_num

/-- The bridge agrees with the shipped tie value at the tetrahedron. -/
theorem tetraDesign_discriminantTie_via_parity : discriminantTie tetraDesign 0 1 2 = 0 := by
  rw [discriminantTie_eq_excessGap_add_parity]
  exact tetraDesign_bridge_at_tie

/-! ### The `(7,3)` tie stratum -/

theorem splitSevenDesign_edgeSign_of_differentDirection {atomFirst atomSecond : Fin 7}
    (hdifferent : splitSevenDirection atomFirst ≠ splitSevenDirection atomSecond) :
    edgeSign splitSevenDesign atomFirst atomSecond = -1 := by
  rw [edgeSign, if_neg (by
    rw [splitSevenDesign_atomPairing_of_differentDirection hdifferent]; norm_num)]

theorem splitSevenDesign_edgeSign_of_sameDirection {atomFirst atomSecond : Fin 7}
    (hsame : splitSevenDirection atomFirst = splitSevenDirection atomSecond) :
    edgeSign splitSevenDesign atomFirst atomSecond = 1 := by
  rw [edgeSign, if_pos (by
    rw [splitSevenDesign_atomPairing_of_sameDirection hsame]; norm_num)]

/-- **The `(7,3)` tie stratum is INCOHERENT.** A rainbow triple of the split
tetrahedron -- three distinct directions, which is exactly the stratum where the
shipped `Gtz.splitSevenDesign_discriminantTie_of_rainbowDirections` gives
`discriminantTie = 0` -- has all three edge signs `-1` and hence parity `-1`. -/
theorem splitSevenDesign_tripleParity_of_rainbowDirections {first second third : Fin 7}
    (hfirstSecond : splitSevenDirection first ≠ splitSevenDirection second)
    (hfirstThird : splitSevenDirection first ≠ splitSevenDirection third)
    (hsecondThird : splitSevenDirection second ≠ splitSevenDirection third) :
    tripleParity splitSevenDesign first second third = -1 := by
  rw [tripleParity, splitSevenDesign_edgeSign_of_differentDirection hfirstSecond,
    splitSevenDesign_edgeSign_of_differentDirection hfirstThird,
    splitSevenDesign_edgeSign_of_differentDirection hsecondThird]
  norm_num

theorem splitSevenDesign_excessGap_of_rainbowDirections {first second third : Fin 7}
    (hfirstSecond : splitSevenDirection first ≠ splitSevenDirection second)
    (hfirstThird : splitSevenDirection first ≠ splitSevenDirection third)
    (hsecondThird : splitSevenDirection second ≠ splitSevenDirection third) :
    excessGap splitSevenDesign first second third = 2 := by
  rw [excessGap, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess,
    splitSevenDesign_atomPairing_of_differentDirection hfirstSecond,
    splitSevenDesign_atomPairing_of_differentDirection hfirstThird,
    splitSevenDesign_atomPairing_of_differentDirection hsecondThird]
  norm_num

/-- **THE TIGHTNESS CHECK AT THE `(7,3)` TIE.** Same three numbers as the
tetrahedron -- gap `2`, magnitude `1`, parity `-1` -- and the bridge again returns
exactly zero, matching the shipped rainbow value. The `(7,3)` tie stratum carries
no margin for a parity-aware certificate to consume, which is the correct and
sobering reading. -/
theorem splitSevenDesign_bridge_at_rainbowTie {first second third : Fin 7}
    (hfirstSecond : splitSevenDirection first ≠ splitSevenDirection second)
    (hfirstThird : splitSevenDirection first ≠ splitSevenDirection third)
    (hsecondThird : splitSevenDirection second ≠ splitSevenDirection third) :
    discriminantTie splitSevenDesign first second third = 0 := by
  rw [discriminantTie_eq_excessGap_add_parity,
    splitSevenDesign_excessGap_of_rainbowDirections hfirstSecond hfirstThird hsecondThird,
    splitSevenDesign_tripleParity_of_rainbowDirections hfirstSecond hfirstThird hsecondThird,
    splitSevenDesign_atomPairing_of_differentDirection hfirstSecond,
    splitSevenDesign_atomPairing_of_differentDirection hfirstThird,
    splitSevenDesign_atomPairing_of_differentDirection hsecondThird]
  norm_num

/-- **COHERENCE ALONE CERTIFIES NOTHING, and here is the repo's own witness.** A
`splitSevenDesign` triple repeating a direction is COHERENT -- its pairings are
`3, -1, -1`, product `+3` -- and yet the shipped
`Gtz.splitSevenDesign_discriminantTie_of_repeatedDirection` gives
`discriminantTie = -8`. What kills it is the sign-blind gap, which is `-14` there.
So parity `+1` is genuinely not sufficient, and the cell
`Gtz.dominates_of_coherent_of_excessGap_nonneg` really does need its second
hypothesis. -/
theorem splitSevenDesign_tripleParity_of_repeatedDirection {first second third : Fin 7}
    (hfirstSecond : splitSevenDirection first = splitSevenDirection second)
    (hfirstThird : splitSevenDirection first ≠ splitSevenDirection third)
    (hsecondThird : splitSevenDirection second ≠ splitSevenDirection third) :
    tripleParity splitSevenDesign first second third = 1 := by
  rw [tripleParity, splitSevenDesign_edgeSign_of_sameDirection hfirstSecond,
    splitSevenDesign_edgeSign_of_differentDirection hfirstThird,
    splitSevenDesign_edgeSign_of_differentDirection hsecondThird]
  norm_num

theorem splitSevenDesign_excessGap_of_repeatedDirection {first second third : Fin 7}
    (hfirstSecond : splitSevenDirection first = splitSevenDirection second)
    (hfirstThird : splitSevenDirection first ≠ splitSevenDirection third)
    (hsecondThird : splitSevenDirection second ≠ splitSevenDirection third) :
    excessGap splitSevenDesign first second third = -14 := by
  rw [excessGap, splitSevenDesign_heavyExcess, splitSevenDesign_heavyExcess,
    splitSevenDesign_heavyExcess,
    splitSevenDesign_atomPairing_of_sameDirection hfirstSecond,
    splitSevenDesign_atomPairing_of_differentDirection hfirstThird,
    splitSevenDesign_atomPairing_of_differentDirection hsecondThird]
  norm_num

/-! ### The icosahedron: the parity decides domination outright -/

/-- Every distinct icosahedral triple has `|p_ab p_ac p_bc|^2 = 729/125`, the cube
of `9/5`. Squares only -- no `Real.sqrt` is needed anywhere in this section. -/
theorem icosaDesign_abs_atomPairingProduct_sq {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    |atomPairing icosaDesign first second * atomPairing icosaDesign first third
        * atomPairing icosaDesign second third| ^ 2 = 729 / 125 := by
  rw [sq_abs,
    show (atomPairing icosaDesign first second * atomPairing icosaDesign first third
        * atomPairing icosaDesign second third) ^ 2
      = atomPairing icosaDesign first second ^ 2 * atomPairing icosaDesign first third ^ 2
        * atomPairing icosaDesign second third ^ 2 from by ring,
    icosaDesign_atomPairing_sq_of_ne hfirstSecond,
    icosaDesign_atomPairing_sq_of_ne hfirstThird,
    icosaDesign_atomPairing_sq_of_ne hsecondThird]
  norm_num

/-- The icosahedral sign-blind gap is `-14/5` at every distinct triple: with all
six leverages equal and all fifteen squared pairings equal to `9/5`, the gap
cannot distinguish triples at all. -/
theorem icosaDesign_excessGap {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    excessGap icosaDesign first second third = -(14 / 5) := by
  rw [excessGap, icosaDesign_heavyExcess, icosaDesign_heavyExcess, icosaDesign_heavyExcess,
    icosaDesign_atomPairing_sq_of_ne hfirstSecond,
    icosaDesign_atomPairing_sq_of_ne hfirstThird,
    icosaDesign_atomPairing_sq_of_ne hsecondThird]
  norm_num

/-- **THE PARITY DECIDES DOMINATION AT THE ICOSAHEDRON.** A distinct icosahedral
triple dominates if and only if it is COHERENT. The sign-blind gap is the same
negative number `-14/5` at all twenty triples and the magnitude is the same at all
twenty, so nothing sign-blind can tell them apart -- yet ten dominate and ten do
not, and the parity is exactly the discriminator. This is the sharpest
demonstration in the repo that the bit of section 4 is load-bearing.

Proved by comparing SQUARES: `(2|product|)^2 = 2916/125` against `(14/5)^2 =
980/125`, so `2|product| > 14/5` with no `Real.sqrt` anywhere. Independently known
from `Gtz.icosaDesign_dominates_iff_pairingProduct`; what is new is that the
criterion is stated as the two-graph invariant. -/
theorem icosaDesign_dominates_iff_tripleParity {first second third : Fin 6}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    Dominates icosaDesign {first, second, third}
      ↔ tripleParity icosaDesign first second third = 1 := by
  have habsSq := icosaDesign_abs_atomPairingProduct_sq hfirstSecond hfirstThird hsecondThird
  have habsNonneg : (0:ℝ) ≤ |atomPairing icosaDesign first second
      * atomPairing icosaDesign first third * atomPairing icosaDesign second third| :=
    abs_nonneg _
  have hgap := icosaDesign_excessGap hfirstSecond hfirstThird hsecondThird
  have hbridge := discriminantTie_eq_excessGap_add_parity icosaDesign first second third
  rw [dominates_triple_iff_isElliptopeGoodTriangle icosaDesign_allHeavy hfirstSecond
    hfirstThird hsecondThird]
  constructor
  · rintro ⟨-, htie⟩
    rcases tripleParity_eq_one_or_neg_one icosaDesign first second third with hvalue | hvalue
    · exact hvalue
    · exfalso
      rw [hbridge, hgap, hvalue] at htie
      nlinarith [habsNonneg, habsSq, htie]
  · intro hvalue
    refine ⟨⟨icosaDesign_isCompatiblePair_of_ne hfirstSecond,
      icosaDesign_isCompatiblePair_of_ne hfirstThird,
      icosaDesign_isCompatiblePair_of_ne hsecondThird⟩, ?_⟩
    rw [hbridge, hgap, hvalue]
    nlinarith [habsNonneg, habsSq]

/-! ## 7. The two-graph axiom

The defining property of a two-graph, and the discrete structure that realness
buys: in every four-atom set the four triple parities multiply to one, because
each of the six edges lies in exactly two of the four triangles. It needs NO
hypothesis -- not all-heaviness, not nondegeneracy of the pairings, not even a
design. -/

/-- **THE TWO-GRAPH AXIOM.** The four triple parities of any four atoms multiply
to `1`. Each of the six edges appears in exactly two of the four triangles, so
every edge sign is squared away. -/
theorem tripleParity_fourSet_product (D : WeightedDesign m 3)
    (first second third fourth : Fin m) :
    tripleParity D first second third * tripleParity D first second fourth
        * tripleParity D first third fourth * tripleParity D second third fourth = 1 := by
  simp only [tripleParity]
  exact sixSign_square_product _ _ _ _ _ _ (edgeSign_sq D first second)
    (edgeSign_sq D first third) (edgeSign_sq D second third) (edgeSign_sq D first fourth)
    (edgeSign_sq D second fourth) (edgeSign_sq D third fourth)

/-- **Three coherent triangles of a four-set force the fourth.** -/
theorem tripleParity_eq_one_of_three_coherent (D : WeightedDesign m 3)
    {first second third fourth : Fin m}
    (hfirstSecondThird : tripleParity D first second third = 1)
    (hfirstSecondFourth : tripleParity D first second fourth = 1)
    (hfirstThirdFourth : tripleParity D first third fourth = 1) :
    tripleParity D second third fourth = 1 := by
  have hproduct := tripleParity_fourSet_product D first second third fourth
  rw [hfirstSecondThird, hfirstSecondFourth, hfirstThirdFourth] at hproduct
  linarith

/-- **Incoherence comes in pairs.** One incoherent triangle among three coherent
ones forces the fourth to be incoherent too -- so no four-set carries exactly one,
nor exactly three. -/
theorem tripleParity_eq_neg_one_of_one_incoherent (D : WeightedDesign m 3)
    {first second third fourth : Fin m}
    (hfirstSecondThird : tripleParity D first second third = -1)
    (hfirstSecondFourth : tripleParity D first second fourth = 1)
    (hfirstThirdFourth : tripleParity D first third fourth = 1) :
    tripleParity D second third fourth = -1 := by
  have hproduct := tripleParity_fourSet_product D first second third fourth
  rw [hfirstSecondThird, hfirstSecondFourth, hfirstThirdFourth] at hproduct
  linarith

/-- **THE COUNTING CONSTRAINT ON PARITIES, at four atoms.** The number of
INCOHERENT triangles in any four-atom set is `0`, `2` or `4` -- never odd. This is
the two-graph axiom in counting form and it holds unconditionally. -/
theorem even_negativeParity_count_fourSet (D : WeightedDesign m 3)
    (first second third fourth : Fin m) :
    Even ((if tripleParity D first second third = -1 then 1 else 0)
        + (if tripleParity D first second fourth = -1 then 1 else 0)
        + (if tripleParity D first third fourth = -1 then 1 else 0)
        + (if tripleParity D second third fourth = -1 then 1 else 0) : ℕ) := by
  have hproduct := tripleParity_fourSet_product D first second third fourth
  rcases tripleParity_eq_one_or_neg_one D first second third with hone | hone <;>
    rcases tripleParity_eq_one_or_neg_one D first second fourth with htwo | htwo <;>
    rcases tripleParity_eq_one_or_neg_one D first third fourth with hthree | hthree <;>
    rcases tripleParity_eq_one_or_neg_one D second third fourth with hfour | hfour <;>
    simp only [hone, htwo, hthree, hfour] at hproduct ⊢
  all_goals (try norm_num at hproduct)
  all_goals norm_num

/-! ## 8. A located coherent triple

Lemma A (`Gtz.exists_pos_atomPairingProduct_of_five_atoms`) produces a coherent
triple among any five atoms of a rank-three design, but says nothing about WHERE
it sits. The two-graph axiom upgrades it to a LOCATED statement: a coherent
triple through any prescribed atom. The mechanism is that incoherence at every
triangle through the base would propagate, by the four-set axiom, to every
triangle avoiding the base as well -- and Lemma A forbids a fully incoherent
five-set. -/

/-- **PARITY PROPAGATES OFF A BASE.** If the three triangles joining a base atom
to a triple are all incoherent, so is the triple itself. A direct reading of the
four-set axiom, and the mechanism behind the located statement below: incoherence
at a base cannot be confined to the base. -/
theorem tripleParity_eq_neg_one_of_base_incoherent (D : WeightedDesign m 3)
    {base first second third : Fin m}
    (hbaseFirstSecond : tripleParity D base first second = -1)
    (hbaseFirstThird : tripleParity D base first third = -1)
    (hbaseSecondThird : tripleParity D base second third = -1) :
    tripleParity D first second third = -1 := by
  have hproduct := tripleParity_fourSet_product D base first second third
  rw [hbaseFirstSecond, hbaseFirstThird, hbaseSecondThird] at hproduct
  linarith

/-- **THE NEGATIVE-PARITY CAP, restated.** Any five atoms with pairwise nonzero
pairings carry a COHERENT triple. This is `Gtz.exists_pos_atomPairingProduct_of_five_atoms`
in two-graph vocabulary; the threshold `5 = 3 + 2` is Lemma A's and is sharp, since
the four tetrahedron vertices have every triangle incoherent. -/
theorem exists_tripleParity_eq_one_of_five_atoms (D : WeightedDesign m 3)
    (pick : Fin 5 → Fin m)
    (hnonzero : ∀ first second : Fin 5, first ≠ second →
      atomPairing D (pick first) (pick second) ≠ 0) :
    ∃ first second third : Fin 5, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ tripleParity D (pick first) (pick second) (pick third) = 1 := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hpositive⟩ :=
    exists_pos_atomPairingProduct_of_five_atoms D pick hnonzero
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    tripleParity_eq_one_of_pos_atomPairingProduct D hpositive⟩

/-- **THE LOCATED COUNTING CONSTRAINT.** Among any five atoms of a rank-three
design with pairwise nonzero pairings, a coherent triple passes through the
PRESCRIBED atom `pick 0`. So no atom can have all ten of its triangles incoherent
inside any five-atom window.

The two-graph axiom is what does the upgrading: if every triangle at the base were
incoherent, then for any three of the other four the four-set identity at
`{base, i, j, k}` would read `(-1)(-1)(-1) * parity(i,j,k) = 1`, making the
base-avoiding triangle incoherent too. Every one of the ten triangles of the
five-set would then be incoherent, and Lemma A forbids that. -/
theorem exists_tripleParity_eq_one_through_base (D : WeightedDesign m 3)
    (pick : Fin 5 → Fin m)
    (hnonzero : ∀ first second : Fin 5, first ≠ second →
      atomPairing D (pick first) (pick second) ≠ 0) :
    ∃ first second : Fin 5, first ≠ 0 ∧ second ≠ 0 ∧ first ≠ second
      ∧ tripleParity D (pick 0) (pick first) (pick second) = 1 := by
  by_contra hnone
  push Not at hnone
  have hbase : ∀ first second : Fin 5, first ≠ 0 → second ≠ 0 → first ≠ second →
      tripleParity D (pick 0) (pick first) (pick second) = -1 := by
    intro first second hfirst hsecond hdistinct
    rcases tripleParity_eq_one_or_neg_one D (pick 0) (pick first) (pick second) with
      hvalue | hvalue
    · exact absurd hvalue (hnone first second hfirst hsecond hdistinct)
    · exact hvalue
  have hoffBase : ∀ first second third : Fin 5, first ≠ 0 → second ≠ 0 → third ≠ 0 →
      first ≠ second → first ≠ third → second ≠ third →
      tripleParity D (pick first) (pick second) (pick third) = -1 := by
    intro first second third hfirst hsecond hthird hfirstSecond hfirstThird hsecondThird
    have hproduct := tripleParity_fourSet_product D (pick 0) (pick first) (pick second)
      (pick third)
    rw [hbase first second hfirst hsecond hfirstSecond,
      hbase first third hfirst hthird hfirstThird,
      hbase second third hsecond hthird hsecondThird] at hproduct
    linarith
  have hall : ∀ first second third : Fin 5, first ≠ second → first ≠ third → second ≠ third →
      tripleParity D (pick first) (pick second) (pick third) = -1 := by
    intro first second third hfirstSecond hfirstThird hsecondThird
    rcases eq_or_ne first 0 with rfl | hfirst
    · exact hbase second third (Ne.symm hfirstSecond) (Ne.symm hfirstThird) hsecondThird
    · rcases eq_or_ne second 0 with rfl | hsecond
      · rw [tripleParity_comm_left]
        exact hbase first third hfirst (Ne.symm hsecondThird) hfirstThird
      · rcases eq_or_ne third 0 with rfl | hthird
        · rw [tripleParity_comm_right, tripleParity_comm_left]
          exact hbase first second hfirst hsecond hfirstSecond
        · exact hoffBase first second third hfirst hsecond hthird hfirstSecond hfirstThird
            hsecondThird
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hcoherent⟩ :=
    exists_tripleParity_eq_one_of_five_atoms D pick hnonzero
  rw [hall first second third hfirstSecond hfirstThird hsecondThird] at hcoherent
  norm_num at hcoherent

/-- **NO ATOM IS TOTALLY INCOHERENT.** In a rank-three design on at least five
atoms with pairwise nonzero pairings, EVERY atom carries a coherent triple. So the
incoherent triangles can never be all of them at any single vertex -- which is the
counting constraint on parities, stated where a consumer wants it, with the
five-atom window of `Gtz.exists_tripleParity_eq_one_through_base` transported to
an arbitrary base by a swap.

The threshold `5` is Lemma A's and is sharp: the four tetrahedron vertices have
every one of their four triangles incoherent
(`Gtz.triangleProduct_tetraAtom_eq_neg_one`). -/
theorem exists_coherentTriple_through_atom (D : WeightedDesign m 3) (hsize : 5 ≤ m)
    (base : Fin m)
    (hnonzero : ∀ first second : Fin m, first ≠ second → atomPairing D first second ≠ 0) :
    ∃ second third : Fin m, base ≠ second ∧ base ≠ third ∧ second ≠ third
      ∧ tripleParity D base second third = 1 := by
  classical
  have hpositive : 0 < m := by omega
  set pick : Fin 5 → Fin m :=
    fun index => Equiv.swap base ⟨0, hpositive⟩ (Fin.castLE hsize index) with hpick
  have hcastInjective : Function.Injective (Fin.castLE hsize : Fin 5 → Fin m) :=
    Fin.castLE_injective hsize
  have hinjective : Function.Injective pick := fun _ _ hequal =>
    hcastInjective ((Equiv.swap base (⟨0, hpositive⟩ : Fin m)).injective hequal)
  have hpickZero : pick 0 = base := by
    rw [hpick]
    show Equiv.swap base (⟨0, hpositive⟩ : Fin m) (Fin.castLE hsize 0) = base
    rw [show Fin.castLE hsize (0 : Fin 5) = (⟨0, hpositive⟩ : Fin m) from rfl,
      Equiv.swap_apply_right]
  obtain ⟨first, second, hfirst, hsecond, hdistinct, hcoherent⟩ :=
    exists_tripleParity_eq_one_through_base D pick
      (fun _ _ hne => hnonzero _ _ fun hequal => hne (hinjective hequal))
  refine ⟨pick first, pick second, ?_, ?_, ?_, ?_⟩
  · rw [← hpickZero]
    exact fun hequal => (Ne.symm hfirst) (hinjective hequal)
  · rw [← hpickZero]
    exact fun hequal => (Ne.symm hsecond) (hinjective hequal)
  · exact fun hequal => hdistinct (hinjective hequal)
  · rw [← hpickZero]
    exact hcoherent

end Gtz
