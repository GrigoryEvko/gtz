import Gtz.Wave.CorankTwoNonplanarSystem
import Gtz.Quantitative.SwitchingTwoGraph
import Gtz.Design.RhoNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The corank-two corner, priced against the one bit that realness buys

Every law the corner lane owns is field-blind.  Each statement and each proof of
the census, the gap window, the pair ledger, the corner rigidity and the frame
laws transports word for word to Hermitian atoms.  A complex `(6,3)` design with
a primitive non-planar corank-two corner satisfies all of them and refuses every
triple.  So the corner cannot be closed without the ground field, and the
campaign has already located the only place the ground field can act: the tie leg
of a triple splits as

  `discriminantTie = excessGap + 2·tripleParity·tripleRadius`

(`Gtz.discriminantTie_eq_excessGap_add_parity`), where `excessGap` and
`tripleRadius` read only leverages and squared pairings.  The `±1` factor is the
whole non-field-blind content, and `Gtz.phaseFree_certificates_cannot_prove_rank_three`
proves that no certificate blind to it can close rank three.

The corner lane and that vocabulary have never met.  This module joins them, and
the answer is negative for the eleven triples the corner pins.

## The corner pins its own bit

The rank-one gap pins the whole inside Gram
(`Gtz.insideGram_self_of_rankOneGap`, `Gtz.insideGram_offDiag_of_rankOneGap`), so
every inside scalar is an axis reading `a_e = g_e · u`:

  `(1+lam)·heavyExcess e = lam·a_e²`   (`Gtz.corner_heavyExcess_axis`),
  `(1+lam)·atomPairing e f = lam·a_e·a_f`   for `e ≠ f` .

Three consequences follow, and each is exact.

* **Every inside pair minor VANISHES**: `heavyExcess e · heavyExcess f = atomPairing e f²`
  (`Gtz.corner_inside_pairMinor_eq_zero`).  The pair Gram of any two inside atoms
  is singular.
* **The inside triple is COHERENT**: its oriented pairing product is
  `(lam/(1+lam))³·(a_x a_y a_z)²`, hence NONNEGATIVE
  (`Gtz.corner_inside_tripleProduct_nonneg`), and its parity bit is `+1`
  (`Gtz.corner_inside_tripleParity_eq_one`).
* **The nine two-inside triples have an exact tie leg.**  The sign-blind part is
  already nonpositive (`Gtz.corner_twoInside_excessGap`), and adding the oriented
  product completes a square:

    `(1+lam)·det(S_{x,y,d} − 1) = −lam·(a_y·(g_x·g_d) − a_x·(g_y·g_d))²`
    (`Gtz.corner_twoInside_det_square`).

## The no-go this produces

The parity bits of the inside triple and of the nine two-inside triples are all
FORCED by the axis readings.  Read the two-graph axiom
(`Gtz.tripleParity_fourSet_product`) on a four-set `C ∪ {d}`: its four triples are
the dominator and three two-inside triples, so all four bits are corner data and
the axiom is an identity in the axis readings.  The bit buys nothing on any
four-set that meets the complement in at most one atom
(`Gtz.corner_fourSet_parity_forced`).

The realness budget of a corank-two corner therefore sits ENTIRELY on the three
four-sets `{e} ∪ Cᶜ`, whose twelve triples are exactly the ten informative
refusals of `Gtz.isTie_iff_corner_refusals` counted with the dominator's three
choices of inside atom.  Those are the only triples whose Bargmann magnitude the
corner does not already pin.

The complex corner-tie witness on record agrees, and sharply.  Its sign pattern
obeys the two-graph axiom on all fifteen four-sets, so the PARITY form does not
separate the fields at a corner.  Its Bargmann magnitudes fall short of the real
extreme by up to 85 percent on the informative triples, while the dominator's own
triple sits at the extreme exactly, as the inside Gram forces.  The separation is
in the MAGNITUDE and not in the bit.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The inside scalars are axis readings -/

/-- **The inside excess is an axis reading.**  At a corank-two corner the heavy
excess of a dominator atom is the gap scale times its squared reading of the gap
axis, deflated by `1 + lam`. -/
theorem corner_heavyExcess_axis (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e : Fin m} (he : e ∈ C) :
    (1 + lam) * heavyExcess D e = lam * (D.atom e ⬝ᵥ u) ^ 2 := by
  have h := insideGram_self_of_rankOneGap D C hcard hlam hunit hgap he
  have hlev : leverageOf (D.atom e) = D.atom e ⬝ᵥ D.atom e :=
    (dotProduct_self_eq_sum_sq (D.atom e)).symm
  rw [heavyExcess, hlev]
  linarith

/-- **The inside pairing is an axis reading.**  For two distinct dominator atoms
the pairing is the gap scale times the product of their axis readings. -/
theorem corner_atomPairing_axis (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    (1 + lam) * atomPairing D e f = lam * ((D.atom e ⬝ᵥ u) * (D.atom f ⬝ᵥ u)) :=
  insideGram_offDiag_of_rankOneGap D C hcard hlam hunit hgap he hf hef

/-! ## 2. Every inside pair minor vanishes -/

/-- **THE INSIDE PAIR GRAM IS SINGULAR.**  At a corank-two corner the two-by-two
excess minor of any two dominator atoms is exactly zero.  The corner does not
merely bound the inside pairs: it pins each of them to the boundary. -/
theorem corner_inside_pairMinor_eq_zero (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {e f : Fin m} (he : e ∈ C) (hf : f ∈ C) (hef : e ≠ f) :
    heavyExcess D e * heavyExcess D f = atomPairing D e f ^ 2 := by
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hex := corner_heavyExcess_axis D C hcard hlam hunit hgap he
  have hef' := corner_heavyExcess_axis D C hcard hlam hunit hgap hf
  have hpair := corner_atomPairing_axis D C hcard hlam hunit hgap he hf hef
  have hkey : (1 + lam) ^ 2 * (heavyExcess D e * heavyExcess D f)
      = (1 + lam) ^ 2 * atomPairing D e f ^ 2 := by
    have hleft : (1 + lam) ^ 2 * (heavyExcess D e * heavyExcess D f)
        = ((1 + lam) * heavyExcess D e) * ((1 + lam) * heavyExcess D f) := by ring
    have hright : (1 + lam) ^ 2 * atomPairing D e f ^ 2
        = ((1 + lam) * atomPairing D e f) ^ 2 := by ring
    rw [hleft, hright, hex, hef', hpair]
    ring
  have hsq : (0 : ℝ) < (1 + lam) ^ 2 := by positivity
  exact mul_left_cancel₀ (ne_of_gt hsq) hkey

/-! ## 3. The dominator is a coherent triangle -/

/-- **THE ORIENTED PRODUCT OF THE DOMINATOR.**  The triple product of the three
inside pairings is the cubed deflated gap scale times the squared product of the
three axis readings. -/
theorem corner_inside_tripleProduct (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (1 + lam) ^ 3 * (atomPairing D x y * atomPairing D x z * atomPairing D y z)
      = lam ^ 3 * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u) * (D.atom z ⬝ᵥ u)) ^ 2 := by
  have h1 := corner_atomPairing_axis D C hcard hlam hunit hgap hx hy hxy
  have h2 := corner_atomPairing_axis D C hcard hlam hunit hgap hx hz hxz
  have h3 := corner_atomPairing_axis D C hcard hlam hunit hgap hy hz hyz
  have hexpand : (1 + lam) ^ 3
      * (atomPairing D x y * atomPairing D x z * atomPairing D y z)
      = ((1 + lam) * atomPairing D x y) * ((1 + lam) * atomPairing D x z)
        * ((1 + lam) * atomPairing D y z) := by ring
  rw [hexpand, h1, h2, h3]
  ring

/-- **THE DOMINATOR IS COHERENT.**  The oriented pairing product of the three
inside atoms is NONNEGATIVE, with no hypothesis beyond the corner itself. -/
theorem corner_inside_tripleProduct_nonneg (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    0 ≤ atomPairing D x y * atomPairing D x z * atomPairing D y z := by
  have hkey := corner_inside_tripleProduct D C hcard hlam hunit hgap hx hy hz hxy hxz hyz
  have hpos : (0 : ℝ) < (1 + lam) ^ 3 := by positivity
  have hrhs : 0 ≤ lam ^ 3 * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u) * (D.atom z ⬝ᵥ u)) ^ 2 := by
    have : (0 : ℝ) ≤ lam ^ 3 := by positivity
    positivity
  nlinarith [hkey, hpos, hrhs]

/-- **THE BIT OF THE DOMINATOR IS `+1`.**  Away from the vanishing-pairing locus
the parity of the dominator triple is `+1`: the corner never carries an
incoherent inside triangle. -/
theorem corner_inside_tripleParity_eq_one (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnzXY : atomPairing D x y ≠ 0) (hnzXZ : atomPairing D x z ≠ 0)
    (hnzYZ : atomPairing D y z ≠ 0) :
    tripleParity D x y z = 1 := by
  have hnonneg :=
    corner_inside_tripleProduct_nonneg D C hcard hlam hunit hgap hx hy hz hxy hxz hyz
  have hne : atomPairing D x y * atomPairing D x z * atomPairing D y z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hnzXY hnzXZ) hnzYZ
  have hpos : 0 < atomPairing D x y * atomPairing D x z * atomPairing D y z :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hparity := tripleParity_mul_abs_atomPairingProduct D x y z
  rw [abs_of_pos hpos] at hparity
  have hcancel : (tripleParity D x y z - 1)
      * (atomPairing D x y * atomPairing D x z * atomPairing D y z) = 0 := by
    linarith [hparity]
  rcases mul_eq_zero.mp hcancel with hzero | hzero
  · linarith [hzero]
  · exact absurd hzero hne

/-! ## 4. The nine two-inside triples, exactly -/

/-- **THE SIGN-BLIND PART OF A TWO-INSIDE TRIPLE.**  Two dominator atoms and one
outside atom have an `excessGap` that the axis readings alone determine, and it
is nonpositive.  The inside pair minor vanishes, so the leading product cancels
against the pair term. -/
theorem corner_twoInside_excessGap (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y : Fin m} (outLbl : Fin m) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    (1 + lam) * excessGap D x y outLbl
      = -(lam * ((D.atom y ⬝ᵥ u) ^ 2 * atomPairing D x outLbl ^ 2
          + (D.atom x ⬝ᵥ u) ^ 2 * atomPairing D y outLbl ^ 2)) := by
  have hminor := corner_inside_pairMinor_eq_zero D C hcard hlam hunit hgap hx hy hxy
  have hexX := corner_heavyExcess_axis D C hcard hlam hunit hgap hx
  have hexY := corner_heavyExcess_axis D C hcard hlam hunit hgap hy
  rw [excessGap]
  linear_combination (1 + lam) * heavyExcess D outLbl * hminor
    - atomPairing D y outLbl ^ 2 * hexX - atomPairing D x outLbl ^ 2 * hexY

/-- **THE ORIENTED PART OF A TWO-INSIDE TRIPLE.** -/
theorem corner_twoInside_tripleProduct (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y : Fin m} (outLbl : Fin m) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    (1 + lam) * (atomPairing D x y * atomPairing D x outLbl * atomPairing D y outLbl)
      = lam * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)) := by
  have hpair := corner_atomPairing_axis D C hcard hlam hunit hgap hx hy hxy
  linear_combination atomPairing D x outLbl * atomPairing D y outLbl * hpair

/-- **THE TIE LEG OF A TWO-INSIDE TRIPLE IS MINUS A SQUARE.**  The sign-blind part
and the oriented part of a two-inside triple complete a square in the axis
readings.  The census only refuses these nine triples.  Here their tie leg is
computed exactly, and its vanishing locus is named: it is where the two axis
readings and the two cross readings are proportional. -/
theorem corner_twoInside_det_square (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y outLbl : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hxOut : x ≠ outLbl) (hyOut : y ≠ outLbl) :
    (1 + lam) * (subsetSum D ({x, y, outLbl} : Finset (Fin m)) - 1).det
      = -(lam * ((D.atom y ⬝ᵥ u) * atomPairing D x outLbl
          - (D.atom x ⬝ᵥ u) * atomPairing D y outLbl) ^ 2) := by
  have hdet := det_subsetSum_sub_one_eq_discriminantTie D hxy hxOut hyOut
  have hsplit := discriminantTie_eq_excessGap_add_tripleProduct D x y outLbl
  have hgapPart := corner_twoInside_excessGap D C hcard hlam hunit hgap outLbl hx hy hxy
  have hprod := corner_twoInside_tripleProduct D C hcard hlam hunit hgap outLbl hx hy hxy
  rw [hdet, hsplit]
  linear_combination hgapPart + 2 * hprod

/-- The tie leg of every two-inside triple is nonpositive. -/
theorem corner_twoInside_det_nonpos (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y outLbl : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    (hxOut : x ≠ outLbl) (hyOut : y ≠ outLbl) :
    (subsetSum D ({x, y, outLbl} : Finset (Fin m)) - 1).det ≤ 0 := by
  have hkey := corner_twoInside_det_square D C hcard hlam hunit hgap hx hy hxy hxOut hyOut
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  nlinarith [hkey, hpos, sq_nonneg ((D.atom y ⬝ᵥ u) * atomPairing D x outLbl
    - (D.atom x ⬝ᵥ u) * atomPairing D y outLbl), hlam]

/-! ## 5. The bit buys nothing on a four-set that meets the complement once -/

/-- **THE PARITY OF A TWO-INSIDE TRIPLE IS FORCED.**  The bit of a two-inside
triple is the bit of the product of the two axis readings with the two cross
readings, with no nondegeneracy hypothesis.  It carries no information the corner
normal form does not already carry. -/
theorem corner_twoInside_tripleParity_forced (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y : Fin m} (outLbl : Fin m) (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    tripleParity D x y outLbl
      * |(D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)|
      = (D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl) := by
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hprod := corner_twoInside_tripleProduct D C hcard (le_of_lt hlam) hunit hgap
    outLbl hx hy hxy
  have hparity := tripleParity_mul_abs_atomPairingProduct D x y outLbl
  have habs : (1 + lam)
      * |atomPairing D x y * atomPairing D x outLbl * atomPairing D y outLbl|
      = lam * |(D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)| := by
    rw [← abs_of_pos hpos, ← abs_mul, hprod, abs_mul, abs_of_pos hlam]
  have hstep : tripleParity D x y outLbl
      * (lam * |(D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)|)
      = lam * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)) := by
    rw [← habs]
    calc tripleParity D x y outLbl
          * ((1 + lam)
            * |atomPairing D x y * atomPairing D x outLbl * atomPairing D y outLbl|)
        = (1 + lam) * (tripleParity D x y outLbl
            * |atomPairing D x y * atomPairing D x outLbl
                * atomPairing D y outLbl|) := by ring
      _ = (1 + lam)
            * (atomPairing D x y * atomPairing D x outLbl * atomPairing D y outLbl) := by
          rw [hparity]
      _ = lam * ((D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
            * (atomPairing D x outLbl * atomPairing D y outLbl)) := hprod
  have hzero : lam * (tripleParity D x y outLbl
      * |(D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)|
      - (D.atom x ⬝ᵥ u) * (D.atom y ⬝ᵥ u)
          * (atomPairing D x outLbl * atomPairing D y outLbl)) = 0 := by
    linear_combination hstep
  rcases mul_eq_zero.mp hzero with hcase | hcase
  · exact absurd hcase (ne_of_gt hlam)
  · linarith

/-- **THE TWO-GRAPH AXIOM IS SPENT ON A FOUR-SET THAT MEETS THE COMPLEMENT ONCE.**
The four triples of `C ∪ {d}` are the dominator and three two-inside triples.  The
dominator carries the bit `+1`, so the axiom says the three two-inside bits
multiply to one.  Every one of them is already forced by the axis readings, so the
axiom gives the corner nothing new. -/
theorem corner_fourSet_parity_forced (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z outLbl : Fin m} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnzXY : atomPairing D x y ≠ 0) (hnzXZ : atomPairing D x z ≠ 0)
    (hnzYZ : atomPairing D y z ≠ 0) :
    tripleParity D x y outLbl * tripleParity D x z outLbl
        * tripleParity D y z outLbl = 1 := by
  have haxiom := tripleParity_fourSet_product D x y z outLbl
  have hone := corner_inside_tripleParity_eq_one D C hcard hlam hunit hgap hx hy hz
    hxy hxz hyz hnzXY hnzXZ hnzYZ
  rw [hone, one_mul] at haxiom
  exact haxiom

end Gtz
