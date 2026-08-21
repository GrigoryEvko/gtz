/-
# The complementary volume row law: coplanarity is the exact dual of parallelism

The campaign owns one volume row law.  `Gtz.sum_weight_mul_sq_tripleBracket_crossNormSq`
says the weighted squared volumes of the triples THROUGH a pair total that pair's
squared area,

    sum over c of  t_c [p q c]^2  =  crossNormSq(g_p, g_q)  =  l_p l_q - <g_p,g_q>^2 ,

so a pair is parallel exactly when every triple through it is degenerate
(`Gtz.crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero`).  That is one half of
a dictionary whose other half nobody has written.

## The other half

At `(6,3)` the complement of a pair is a FOUR-set, carrying four triples.  This module
proves that those four volumes total the slack of the campaign's PAIRING CAP:

    (1 - t_p l_p)(1 - t_q l_q) - t_p t_q <g_p,g_q>^2
      =  t_x t_y t_z [x y z]^2 + t_x t_y t_w [x y w]^2
       + t_x t_z t_w [x z w]^2 + t_y t_z t_w [y z w]^2                     (`Gtz.pairCapSlack_eq_sum_complement_volumes`)

for `{x,y,z,w}` the complement of `{p,q}` in `Fin 6`.  Two consequences fall out with
nothing further computed.

* **The pairing cap is a sum of four squares.**  `Gtz.pairCapSlack_nonneg` reproves
  `t_p t_q <g_p,g_q>^2 <= (1 - t_p l_p)(1 - t_q l_q)` at `(6,3)` from the volumes alone,
  with no Schur complement and no positive semidefiniteness.
* **The cap is ATTAINED exactly when the four complementary atoms are COPLANAR**
  (`Gtz.pairCapSlack_eq_zero_iff_fourCoplanar`).

So the two halves read side by side, at every `(6,3)` design:

    crossNormSq(g_p,g_q) = 0   <->   g_p, g_q parallel        <->  every triple THROUGH {p,q} degenerate
    pairCapSlack(p,q)    = 0   <->   {p,q}^c coplanar         <->  every triple INSIDE {p,q}^c degenerate

Both sides are sums of the SAME twenty nonnegative volumes `nu_T = t_T [T]^2`, grouped
two different ways: `crossNormSq` collects the four triples containing the pair,
`pairCapSlack` the four triples missing it.  Since `sum over T of nu_T = 1` and each `nu_T`
sits in exactly three pairs on each side, the two totals over the fifteen pairs are both
`3` (`Gtz.sum_pairs_crossNormSq_eq_three` is NOT claimed here -- only the pointwise laws
are).

## Where it comes from, and why it is elementary

The proof is duality, but no chart, no whitening and no sharp design appear in the
statement.  Read the pair in the Naimark dual: `t_c ltilde_c = 1 - t_c l_c`
(`Gtz.naimark_coShare`) and `ptilde_pq = -p_pq` (`Gtz.naimark_dot_eq_neg`), so the cap
slack IS the dual pair's squared area scaled by the two weights.  Apply the LANDED row
law to the dual design, then transport each dual volume back with the LANDED bracket law
`t_S [S]^2 = t_{S^c} [S^c]tilde^2` (`Gtz.naimark_bracket_law`).  The four dual triples
`{p,q,c}` have complements running over exactly the four triples of `{p,q}^c`.

## What this does for the hinge

`Gtz.HingeHoldsAtSize 6 3` asks every `(6,3)` tie for a parallel pair.  The dictionary
above turns both candidate certificates into the SAME currency -- the zero set of the
twenty brackets -- and shows they are the two ways a pair can degenerate against that
zero set.  A parallel pair kills the four triples through it; four coplanar atoms kill
the four triples inside them.

[MEASURED before proving, in double precision.  The scaled identity
`det (I - P)[p,q] = pairCapSlack(p,q)` holds to `3.3e-16` over 600 pairs of 40 random
`(6,3)` designs, where `P` is the rank-three projection of the chart.  The Naimark flip
`C dominates D  <->  C^c dominates the sharp design` was reconfirmed with ZERO mismatches,
weak AND strict, over ten cells; and the sharp design is an INVOLUTION, `E(E(D)) = D` up
to an orthogonal congruence, to `3e-14` at all ten.  On the split `(5,3)` diamond -- the
one exact `(6,3)` tie the campaign owns -- the minimum over pairs of BOTH `det P[p,q]` and
`det (I-P)[p,q]` is zero: it carries a parallel pair AND four coplanar atoms at once.]
-/
import Gtz.Wave.TripleVolumeRowLaw
import Gtz.Wave.PairStarSizeLaw
import Gtz.Wave.NaimarkDualDesign
import Gtz.Wave.NaimarkDualExistence
import Gtz.Design.TripleGramSylvester

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}

/-! ## Part A -- the Gram determinant of a triple

The two degenerate-bracket lemmas this part needs are landed in
`Gtz.Wave.PairStarSizeLaw` as `Gtz.tripleBracket_repeat_outer` and
`Gtz.tripleBracket_repeat_right`, and are imported rather than restated. -/

/-- **THE GRAM DETERMINANT OF A TRIPLE IS ITS SQUARED BRACKET.**  The Gram is the
row matrix against its own transpose, so the determinant multiplies. -/
theorem det_naimarkGram_triple (D : WeightedDesign m 3) (p q x : Fin m) :
    (naimarkGram D ![p, q, x]).det
      = tripleBracket (D.atom p) (D.atom q) (D.atom x) ^ 2 := by
  have hshape : naimarkGram D ![p, q, x]
      = (Matrix.of ![D.atom p, D.atom q, D.atom x])
        * (Matrix.of ![D.atom p, D.atom q, D.atom x])ᵀ := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [naimarkGram, Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  rw [hshape, Matrix.det_mul, Matrix.det_transpose, tripleBracket]
  ring

/-- The same reading in the dual. -/
theorem det_naimarkCoGram_triple {D : WeightedDesign m k} (N : NaimarkDual D 3)
    (p q x : Fin m) :
    (naimarkCoGram N ![p, q, x]).det
      = tripleBracket (N.co p) (N.co q) (N.co x) ^ 2 := by
  have hshape : naimarkCoGram N ![p, q, x]
      = (Matrix.of ![N.co p, N.co q, N.co x])
        * (Matrix.of ![N.co p, N.co q, N.co x])ᵀ := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [naimarkCoGram, Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  rw [hshape, Matrix.det_mul, Matrix.det_transpose, tripleBracket]
  ring

/-! ## Part B -- the pairing-cap slack is the dual pair's squared area -/

/-- **THE PAIRING-CAP SLACK** of a pair: the amount by which the co-shares beat the
weighted squared pairing.  The campaign's cap says this is nonnegative. -/
noncomputable def pairCapSlack (D : WeightedDesign m k) (p q : Fin m) : ℝ :=
  (1 - D.weight p * leverageOf (D.atom p)) * (1 - D.weight q * leverageOf (D.atom q))
    - D.weight p * D.weight q * (D.atom p ⬝ᵥ D.atom q) ^ 2

/-- **THE CAP SLACK IS THE DUAL AREA.**  Duality turns the co-shares into dual shares
and negates the pairing, so the slack is the dual pair's squared area scaled by the two
weights.  This is the whole reason the complementary row law exists. -/
theorem pairCapSlack_eq_weight_mul_coCrossNormSq {D : WeightedDesign m k}
    (N : NaimarkDual D 3) {p q : Fin m} (hpq : p ≠ q) :
    pairCapSlack D p q
      = D.weight p * D.weight q * crossNormSq (N.co p) (N.co q) := by
  have hp : 1 - D.weight p * leverageOf (D.atom p) = D.weight p * leverageOf (N.co p) :=
    (naimark_coShare N p).symm
  have hq : 1 - D.weight q * leverageOf (D.atom q) = D.weight q * leverageOf (N.co q) :=
    (naimark_coShare N q).symm
  rw [pairCapSlack, hp, hq, crossNormSq_eq_leverage_mul_sub_sq, naimark_dot_eq_neg N hpq]
  ring

/-! ## Part C -- six distinct labels index `Fin 6` -/

/-- **SIX DISTINCT LABELS SPLIT `Fin 6` INTO TWO TRIPLES.**  The partition hypothesis
that `Gtz.naimark_bracket_law` consumes, from pairwise distinctness. -/
theorem bijective_sumElim_six {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Bijective (Sum.elim ![a, b, c] ![d, e, f]) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro leftIndex rightIndex hvalue
  cases leftIndex <;> cases rightIndex <;> rename_i leftSlot rightSlot <;>
    fin_cases leftSlot <;> fin_cases rightSlot <;> simp_all

/-- **SIX DISTINCT LABELS ENUMERATE `Fin 6`.**  The re-indexing the row law needs. -/
theorem bijective_six {a b c d e f : Fin 6}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Bijective (![a, b, c, d, e, f] : Fin 6 → Fin 6) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro leftIndex rightIndex hvalue
  fin_cases leftIndex <;> fin_cases rightIndex <;> simp_all

/-! ## Part D -- the complementary volume row law -/

/-- **THE COMPLEMENTARY VOLUME ROW LAW AT `(6,3)`.**  The four weighted squared volumes
of the triples MISSING a pair total that pair's cap slack.

This is the exact mirror of the landed row law
`Gtz.sum_weight_mul_sq_tripleBracket_crossNormSq`, which totals the four volumes
CONTAINING the pair to the pair's squared area.  Together the two laws split the twenty
volumes of a `(6,3)` design against a pair in the only two ways available. -/
theorem pairCapSlack_eq_sum_complement_volumes
    (D : WeightedDesign 6 3) (N : NaimarkDual D 3) {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    pairCapSlack D p q
      = D.weight x * D.weight y * D.weight z
          * tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
        + D.weight x * D.weight y * D.weight w
          * tripleBracket (D.atom x) (D.atom y) (D.atom w) ^ 2
        + D.weight x * D.weight z * D.weight w
          * tripleBracket (D.atom x) (D.atom z) (D.atom w) ^ 2
        + D.weight y * D.weight z * D.weight w
          * tripleBracket (D.atom y) (D.atom z) (D.atom w) ^ 2 := by
  classical
  -- the dual pair's squared area, expanded by the landed row law on the dual design
  have hrow := sum_weight_mul_sq_tripleBracket_crossNormSq N.dual p q
  simp only [NaimarkDual.dual_atom, NaimarkDual.dual_weight] at hrow
  have hbij := bijective_six hpq hpx hpy hpz hpw hqx hqy hqz hqw hxy hxz hxw hyz hyw hzw
  have hreindex : ∑ label : Fin 6, D.weight label
        * tripleBracket (N.co p) (N.co q) (N.co label) ^ 2
      = ∑ slot : Fin 6, D.weight (![p, q, x, y, z, w] slot)
        * tripleBracket (N.co p) (N.co q) (N.co (![p, q, x, y, z, w] slot)) ^ 2 :=
    (Fintype.sum_bijective _ hbij _ _ fun _ => rfl).symm
  have hslotFive : (![p, q, x, y, z, w] : Fin 6 → Fin 6) 5 = w := rfl
  rw [hreindex, Fin.sum_univ_six] at hrow
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_fin_one,
    hslotFive, tripleBracket_repeat_outer, tripleBracket_repeat_right] at hrow
  -- transport each dual volume to the complementary primal volume
  have htransport : ∀ (selOne selTwo selThree coThree : Fin 6),
      Function.Bijective (Sum.elim ![selOne, selTwo, selThree] ![p, q, coThree]) →
      D.weight selOne * D.weight selTwo * D.weight selThree
          * tripleBracket (D.atom selOne) (D.atom selTwo) (D.atom selThree) ^ 2
        = D.weight p * D.weight q * D.weight coThree
          * tripleBracket (N.co p) (N.co q) (N.co coThree) ^ 2 := by
    intro selOne selTwo selThree coThree hpart
    have hlaw := naimark_bracket_law N ![selOne, selTwo, selThree] ![p, q, coThree] hpart
    rw [det_naimarkGram_triple, det_naimarkCoGram_triple, Fin.prod_univ_three,
      Fin.prod_univ_three] at hlaw
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using hlaw
  have hx := htransport y z w x
    (bijective_sumElim_six hyz hyw hpy.symm hqy.symm hxy.symm hzw hpz.symm hqz.symm
      hxz.symm hpw.symm hqw.symm hxw.symm hpq hpx hqx)
  have hy := htransport x z w y
    (bijective_sumElim_six hxz hxw hpx.symm hqx.symm hxy hzw hpz.symm hqz.symm hyz.symm
      hpw.symm hqw.symm hyw.symm hpq hpy hqy)
  have hz := htransport x y w z
    (bijective_sumElim_six hxy hxw hpx.symm hqx.symm hxz hyw hpy.symm hqy.symm hyz
      hpw.symm hqw.symm hzw.symm hpq hpz hqz)
  have hw := htransport x y z w
    (bijective_sumElim_six hxy hxz hpx.symm hqx.symm hxw hyz hpy.symm hqy.symm hyw
      hpz.symm hqz.symm hzw hpq hpw hqw)
  rw [pairCapSlack_eq_weight_mul_coCrossNormSq N hpq, ← hrow]
  rw [hx, hy, hz, hw]
  ring

/-! ## Part E -- the dictionary -/

/-- **FOUR COPLANAR ATOMS**: every triple among the four is degenerate. -/
def FourCoplanar (D : WeightedDesign m 3) (x y z w : Fin m) : Prop :=
  tripleBracket (D.atom x) (D.atom y) (D.atom z) = 0
    ∧ tripleBracket (D.atom x) (D.atom y) (D.atom w) = 0
    ∧ tripleBracket (D.atom x) (D.atom z) (D.atom w) = 0
    ∧ tripleBracket (D.atom y) (D.atom z) (D.atom w) = 0

/-- **THE PAIRING CAP AT `(6,3)`, FROM THE VOLUMES ALONE.**  The slack is a sum of four
nonnegative volumes, so the cap holds with no Schur complement and no positive
semidefiniteness anywhere in the proof. -/
theorem pairCapSlack_nonneg (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    0 ≤ pairCapSlack D p q := by
  rw [pairCapSlack_eq_sum_complement_volumes D N hpq hpx hpy hpz hpw hqx hqy hqz hqw
    hxy hxz hxw hyz hyw hzw]
  have hx := (D.weight_pos x).le
  have hy := (D.weight_pos y).le
  have hz := (D.weight_pos z).le
  have hw := (D.weight_pos w).le
  positivity

/-- **THE CAP IS ATTAINED EXACTLY AT FOUR COPLANAR ATOMS.**  Four strictly positive
weights times four squares total zero exactly when every square vanishes. -/
theorem pairCapSlack_eq_zero_iff_fourCoplanar (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    pairCapSlack D p q = 0 ↔ FourCoplanar D x y z w := by
  have hlaw := pairCapSlack_eq_sum_complement_volumes D N hpq hpx hpy hpz hpw hqx hqy hqz
    hqw hxy hxz hxw hyz hyw hzw
  have hxp := D.weight_pos x
  have hyp := D.weight_pos y
  have hzp := D.weight_pos z
  have hwp := D.weight_pos w
  constructor
  · intro hzero
    rw [hzero] at hlaw
    have hone : 0 ≤ D.weight x * D.weight y * D.weight z
        * tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by positivity
    have htwo : 0 ≤ D.weight x * D.weight y * D.weight w
        * tripleBracket (D.atom x) (D.atom y) (D.atom w) ^ 2 := by positivity
    have hthree : 0 ≤ D.weight x * D.weight z * D.weight w
        * tripleBracket (D.atom x) (D.atom z) (D.atom w) ^ 2 := by positivity
    have hfour : 0 ≤ D.weight y * D.weight z * D.weight w
        * tripleBracket (D.atom y) (D.atom z) (D.atom w) ^ 2 := by positivity
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hterm : D.weight x * D.weight y * D.weight z
          * tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 = 0 := by linarith
      have hprod : (0 : ℝ) < D.weight x * D.weight y * D.weight z := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp hterm).resolve_left hprod.ne')
    · have hterm : D.weight x * D.weight y * D.weight w
          * tripleBracket (D.atom x) (D.atom y) (D.atom w) ^ 2 = 0 := by linarith
      have hprod : (0 : ℝ) < D.weight x * D.weight y * D.weight w := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp hterm).resolve_left hprod.ne')
    · have hterm : D.weight x * D.weight z * D.weight w
          * tripleBracket (D.atom x) (D.atom z) (D.atom w) ^ 2 = 0 := by linarith
      have hprod : (0 : ℝ) < D.weight x * D.weight z * D.weight w := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp hterm).resolve_left hprod.ne')
    · have hterm : D.weight y * D.weight z * D.weight w
          * tripleBracket (D.atom y) (D.atom z) (D.atom w) ^ 2 = 0 := by linarith
      have hprod : (0 : ℝ) < D.weight y * D.weight z * D.weight w := by positivity
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp hterm).resolve_left hprod.ne')
  · rintro ⟨hone, htwo, hthree, hfour⟩
    rw [hlaw, hone, htwo, hthree, hfour]
    ring

/-- **THE TWO HALVES OF THE DICTIONARY, SIDE BY SIDE.**  At every `(6,3)` design and
every pair, the pair's squared area vanishes exactly when the four triples THROUGH the
pair are degenerate, and the pair's cap slack vanishes exactly when the four triples
INSIDE its complement are degenerate.  The first half is the landed row law, the second
is this module.  Both sides read the same twenty volumes. -/
theorem crossNormSq_and_pairCapSlack_dictionary (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (crossNormSq (D.atom p) (D.atom q) = 0
        ↔ ∀ third, tripleBracket (D.atom p) (D.atom q) (D.atom third) = 0)
      ∧ (pairCapSlack D p q = 0 ↔ FourCoplanar D x y z w) :=
  ⟨crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero D p q,
    pairCapSlack_eq_zero_iff_fourCoplanar D N hpq hpx hpy hpz hpw hqx hqy hqz hqw
      hxy hxz hxw hyz hyw hzw⟩

/-! ## Part F -- the laws hold at every `(6,3)` design

Every design has a Naimark dual of the complementary rank, so the dual carried above as a
hypothesis can always be produced.  These are the forms a consumer uses. -/

/-- **THE COMPLEMENTARY ROW LAW, WITH NO DUAL IN THE STATEMENT.** -/
theorem pairCapSlack_eq_sum_complement_volumes' (D : WeightedDesign 6 3)
    {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    pairCapSlack D p q
      = D.weight x * D.weight y * D.weight z
          * tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
        + D.weight x * D.weight y * D.weight w
          * tripleBracket (D.atom x) (D.atom y) (D.atom w) ^ 2
        + D.weight x * D.weight z * D.weight w
          * tripleBracket (D.atom x) (D.atom z) (D.atom w) ^ 2
        + D.weight y * D.weight z * D.weight w
          * tripleBracket (D.atom y) (D.atom z) (D.atom w) ^ 2 := by
  obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
  exact pairCapSlack_eq_sum_complement_volumes D N hpq hpx hpy hpz hpw hqx hqy hqz hqw
    hxy hxz hxw hyz hyw hzw

/-- **THE PAIRING CAP AT `(6,3)`, UNCONDITIONAL.** -/
theorem pairCapSlack_nonneg' (D : WeightedDesign 6 3) {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    D.weight p * D.weight q * (D.atom p ⬝ᵥ D.atom q) ^ 2
      ≤ (1 - D.weight p * leverageOf (D.atom p))
        * (1 - D.weight q * leverageOf (D.atom q)) := by
  have hslack := pairCapSlack_eq_sum_complement_volumes' D hpq hpx hpy hpz hpw hqx hqy hqz
    hqw hxy hxz hxw hyz hyw hzw
  have hx := (D.weight_pos x).le
  have hy := (D.weight_pos y).le
  have hz := (D.weight_pos z).le
  have hw := (D.weight_pos w).le
  have hnonneg : (0 : ℝ) ≤ pairCapSlack D p q := by
    rw [hslack]; positivity
  rw [pairCapSlack] at hnonneg
  linarith

/-- **THE CAP IS ATTAINED EXACTLY AT FOUR COPLANAR ATOMS, UNCONDITIONAL.** -/
theorem pairCapSlack_eq_zero_iff_fourCoplanar' (D : WeightedDesign 6 3)
    {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    pairCapSlack D p q = 0 ↔ FourCoplanar D x y z w := by
  obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
  exact pairCapSlack_eq_zero_iff_fourCoplanar D N hpq hpx hpy hpz hpw hqx hqy hqz hqw
    hxy hxz hxw hyz hyw hzw

end Gtz
