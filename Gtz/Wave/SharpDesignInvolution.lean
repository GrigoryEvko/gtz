/-
# The sharp design, explicitly, and its involution

`Gtz.exists_naimark_sharp_design` ships the sharp design as an EXISTENTIAL: every
`(m,k)` design carries an `(m,m-k)` design on the same weights whose dominating
selections are the complements.  Nothing downstream can name that design, so nothing
downstream can iterate it.  This module names it, iterates it once, and shows the
iteration is FREE.

## What is landed

* `Gtz.SharpFrame` and `Gtz.naimarkSharpDesign` -- the construction as a DEFINITION.  The
  atoms are `ghat_c = whiten^T (sqrt(t_c/(1-t_c)) . gtilde_c)`, exactly the ones the
  existence proof builds, with the whitening congruence carried as data rather than
  obtained.  The names carry the `naimark` prefix because `Gtz.sharpDesign` is a concrete
  `(4,3)` tie of `Gtz/Ties/NonTetrahedralTie.lean` and has nothing to do with this one.
* `Gtz.dominates_iff_dominates_naimarkSharpDesign_compl` -- **THE TWO-SIDED FLIP**, as a
  usable biconditional: a `k`-selection dominates `D` exactly when its complement
  dominates the named sharp design.
* `Gtz.sharpNaimarkDual` -- **`D` IS ITS OWN SHARP DESIGN'S DUAL FRAME.**  For any
  congruence `B` with `B^T (S_all - 1) B = 1`, the vectors
  `sqrt((1-t_c)/t_c) . B^T g_c` are a Naimark dual of the sharp design.
* `Gtz.naimarkSharpAtom_secondSharpFrame` -- **THE INVOLUTION.**  Sharpening twice returns
  the original atoms ON THE NOSE, `E(E(D)) = D`, with no congruence left over.
* `Gtz.not_naimarkSharpAtom_eq_mulVec` -- **THE INVOLUTION IS FREE.**  At `m = 2k` the
  sharp design is never a congruence of `D`, so it is never `D`.  Every orbit has exactly
  two members.
* `Gtz.fourCoplanar_iff_crossNormSq_naimarkSharpAtom` -- **THE SECOND HALF OF THE `(6,3)`
  DICTIONARY**, which needed the sharp design to have a name.

## The involution, in four lines

Write `A = S_all - 1` for the total gap, positive definite at every design
(`Gtz.posDef_subsetSum_univ_sub_one`), and let `B` be any congruence with `B^T A B = 1`.

* Parseval gives `sum_c (1 - t_c) . g_c g_c^T = A`, so the rescaled vectors
  `sqrt((1-t_c)/t_c) . B^T g_c` satisfy the dual Parseval law of the sharp design.
* The dependency law is `N`'s own dependency read through `B` and the whitener, because
  the two per-atom scalars `sqrt(t_c/(1-t_c))` and `sqrt((1-t_c)/t_c)` are reciprocal and
  cancel exactly.
* That dual's OMEGA is `B^T S_all B = B^T A B + B^T B = 1 + B^T B`, so its sharp target is
  `B^T B` -- and `B^-1` whitens it, since `(B^-1)^T (B^T B) B^-1 = 1`.
* The second sharp atom is then
  `(B^-1)^T (sqrt(t_c/(1-t_c)) sqrt((1-t_c)/t_c) . B^T g_c) = (B B^-1)^T g_c = g_c`.

No matrix square root, no inverse of `Omega - 1`, and no orthogonal ambiguity: the two
whiteners are inverse congruences and they cancel.

## Why the involution is free

A fixed point would make the sharp atoms `R g_c` for an invertible `R`.  Pair the
dependency law of the dual against the whitener: that turns the dual atom into the sharp
atom, which the fixed-point hypothesis turns into `R g_c`.  What is left is

  `sum_c sqrt(t_c (1 - t_c)) . g_c (R g_c)^T = 0` ,

and `R` is invertible, so `sum_c sqrt(t_c (1 - t_c)) . g_c g_c^T = 0`.  That is a POSITIVE
combination of atom matrices, so every atom vanishes and Parseval reads `1 = 0`.

The coefficient `sqrt(t_c (1 - t_c))` is the positive diagonal `N` of the
projection-chart form of the same duality.  In the chart, with `P` the rank-`k` projection
of `Gtz/Wave/SharpShareCoAtom.lean` and `M = P - diag(t)`, the duality is
`M_E = -N M^-1 N`, and a fixed point wants `(N^-1/2 M N^-1/2)^2 = -1` for a real symmetric
matrix.  It is the same positivity, spent one step earlier and with no chart, no inverse
and no spectral theorem.  (The letter `M` is also used in
`Gtz/Wave/CorankOneRigidity.lean` for `1 - V V^T`, which is a DIFFERENT matrix.  No
declaration of this module is named after either one.)

## What this buys, and what it does NOT

The involution makes the sharp design a free action on the designs of `m = 2k`, so any
property the flip preserves has orbits of size exactly two.

**The flip preserves `Gtz.IsTie`.  IT DOES NOT PRESERVE `Gtz.HasParallelPair`.**
`Gtz.hinge_not_preserved_by_duality` (Gtz/Wave/CorankOneRigidity.lean) exchanges the cells
`(k+1,1)` and `(k+1,k)`, where the hinge is free on one side and FALSE on the other for
every `k` of at least two.  So no proof of the hinge can argue "the dual is a tie, so it
has a parallel pair, so the original does".  That refutation lives at a cell that is not
self-dual, where the dual of a pair is not a complementary quadruple and the dictionary of
Part F is vacuous on both sides.

At `(6,3)` the cell IS self-dual and the dictionary is a genuine bijection between the
fifteen pairs and the fifteen complementary quadruples.  Part F lands it in both
directions.  Turning it into a statement about COUNTEREXAMPLES needs one more equivalence,

  for a `(6,3)` tie:  has a parallel pair  <->  has four coplanar atoms ,

which this module does not prove and which the tree does not carry: no theorem anywhere
relates `Gtz.HasParallelPair` to `Gtz.FourCoplanar`.  A successor that wants the
counterexample-pair reduction must land that equivalence first.

A dimension count was tried and is dead: at the split `(5,3)` diamond -- the one exact
`(6,3)` tie the campaign owns -- the tie stratum has codimension NINE in the
seventeen-dimensional design variety, because twelve of the twenty triples are
simultaneously tight, while a parallel pair and four coplanar atoms are each codimension
TWO.  A codimension-nine set sits inside a codimension-two set with room to spare, so no
counting argument can refute the hinge.

[MEASURED before proving.  The flip: ZERO mismatches, weak AND strict, over 5125
selections at `(4,3) (5,3) (6,3) (5,2) (4,2) (7,4) (8,4) (7,3) (6,4) (9,5)`.  The
involution: `E(E(D)) = D` up to an orthogonal congruence to `3e-14` at all ten cells,
and confirmed independently by the coordinator at `2.5e-13` on Gram matrices at `(6,3)`,
`(5,3)` and `(7,4)`.  The chart form `M_E = -N M^-1 N` to `2.2e-14` at `(6,3)`, `(5,3)`,
`(7,4)` and `(8,4)`, with `M` of inertia `(k, 0, m-k)` in 200 of 200 designs at `(6,3)`
and `(8,4)`.]
-/
import Gtz.Wave.NaimarkSharpDesign
import Gtz.Wave.SharpShareCoAtom
import Gtz.Wave.ComplementVolumeRowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k r : ℕ} {D : WeightedDesign m k}

/-! ## Part A -- the sharp design as a definition -/

/-- **A WHITENING FRAME** for the sharp target: the congruence that
`Gtz.exists_naimark_sharp_design` obtains, carried as data so that the design it builds
can be named. -/
structure SharpFrame (N : NaimarkDual D r) where
  /-- The whitening congruence. -/
  whiten : Matrix (Fin r) (Fin r) ℝ
  /-- It is invertible. -/
  unit : IsUnit whiten.det
  /-- It carries the sharp target to the identity. -/
  spec : whitenᵀ * naimarkSharpTarget N * whiten = 1

/-- Every dual admits a whitening frame. -/
theorem exists_sharpFrame (N : NaimarkDual D r) (hm : 2 ≤ m) : Nonempty (SharpFrame N) := by
  obtain ⟨whiten, hunit, hspec⟩ := exists_congruence_to_one (naimarkSharpTarget_posDef N hm)
  exact ⟨⟨whiten, hunit, hspec⟩⟩

/-- The per-atom scalar of the sharp construction. -/
noncomputable def sharpScale (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  Real.sqrt (D.weight c / (1 - D.weight c))

/-- Its reciprocal, the scalar the dual frame carries. -/
noncomputable def coSharpScale (D : WeightedDesign m k) (c : Fin m) : ℝ :=
  Real.sqrt ((1 - D.weight c) / D.weight c)

theorem sharpScale_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 ≤ D.weight c / (1 - D.weight c) := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  positivity

theorem coSharpScale_nonneg (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 ≤ (1 - D.weight c) / D.weight c := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  positivity

/-- **THE TWO SCALARS ARE RECIPROCAL.**  Their product is one, which is why sharpening
twice leaves no scalar behind. -/
theorem sharpScale_mul_coSharpScale (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    sharpScale D c * coSharpScale D c = 1 := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  have hwne : D.weight c ≠ 0 := ne_of_gt hpos
  have hcone : (1 : ℝ) - D.weight c ≠ 0 := by intro hzero; linarith
  rw [sharpScale, coSharpScale, ← Real.sqrt_mul (sharpScale_nonneg D hm c)]
  rw [show D.weight c / (1 - D.weight c) * ((1 - D.weight c) / D.weight c) = 1 by
    field_simp]
  exact Real.sqrt_one

/-- **THE SHARP ATOM.**  The dual atom scaled and whitened. -/
noncomputable def naimarkSharpAtom {N : NaimarkDual D r} (F : SharpFrame N) (c : Fin m) :
    Fin r → ℝ :=
  F.whitenᵀ *ᵥ (sharpScale D c • N.co c)

theorem atomMatrix_naimarkSharpAtom {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (c : Fin m) :
    atomMatrix (naimarkSharpAtom F c)
      = F.whitenᵀ * ((D.weight c / (1 - D.weight c)) • atomMatrix (N.co c)) * F.whiten := by
  rw [naimarkSharpAtom, atomMatrix_conj, atomMatrix_smul, Matrix.transpose_transpose, sharpScale,
    Real.sq_sqrt (sharpScale_nonneg D hm c)]

/-- **THE SHARP DESIGN**, named.  The same atoms `Gtz.exists_naimark_sharp_design` builds,
now a definition that downstream can iterate. -/
noncomputable def naimarkSharpDesign {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m) :
    WeightedDesign m r where
  atom := naimarkSharpAtom F
  weight := D.weight
  weight_pos := D.weight_pos
  weight_sum_one := D.weight_sum_one
  isParseval := by
    have hstep : ∑ c, D.weight c • atomMatrix (naimarkSharpAtom F c)
        = F.whitenᵀ * (∑ c, naimarkSharpCoeff D c • atomMatrix (N.co c)) * F.whiten := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [atomMatrix_naimarkSharpAtom F hm c, naimarkSharpCoeff, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hstep, ← naimarkSharpTarget_eq N hm, F.spec]

@[simp] theorem naimarkSharpDesign_atom {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (c : Fin m) : (naimarkSharpDesign F hm).atom c = naimarkSharpAtom F c := rfl

@[simp] theorem naimarkSharpDesign_weight {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (c : Fin m) : (naimarkSharpDesign F hm).weight c = D.weight c := rfl

/-! ## Part B -- the two-sided flip -/

/-- **THE SHARP DESIGN READS THE DUAL READING.**  A selection dominates the sharp design
exactly when its dual reading clears the sharp target. -/
theorem dominates_naimarkSharpDesign_iff_reading {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) {cosel : Fin r → Fin m} (hcoinj : Function.Injective cosel) :
    Dominates (naimarkSharpDesign F hm) (Finset.image cosel Finset.univ)
      ↔ (naimarkReading N cosel - naimarkSharpTarget N).PosSemidef := by
  classical
  rw [Dominates, subsetSum, Finset.sum_image fun left _ right _ hlr => hcoinj hlr]
  have hshapes : ∑ j, atomMatrix ((naimarkSharpDesign F hm).atom (cosel j)) - 1
      = F.whitenᵀ * (naimarkReading N cosel - naimarkSharpTarget N) * F.whiten := by
    have hleftSum : ∑ j, atomMatrix ((naimarkSharpDesign F hm).atom (cosel j))
        = F.whitenᵀ * naimarkReading N cosel * F.whiten := by
      rw [naimarkReading, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [naimarkSharpDesign_atom, atomMatrix_naimarkSharpAtom F hm (cosel j)]
    rw [hleftSum, Matrix.mul_sub, Matrix.sub_mul, F.spec]
  have hsymm : (naimarkReading N cosel - naimarkSharpTarget N)ᵀ
      = naimarkReading N cosel - naimarkSharpTarget N := by
    rw [Matrix.transpose_sub, naimarkSharpTarget, naimarkOmega, naimarkReading,
      Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
    · congr 1
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  rw [hshapes]
  exact (posSemidef_congr_right hsymm F.unit).symm

/-- **THE TWO-SIDED FLIP, AS A BICONDITIONAL.**  A `k`-selection dominates `D` exactly
when its complement dominates the named sharp design.  The tree carried this only inside
an existential. -/
theorem dominates_iff_dominates_naimarkSharpDesign_compl {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) (sel : Fin k → Fin m) (cosel : Fin r → Fin m)
    (hpart : Function.Bijective (Sum.elim sel cosel)) :
    Dominates D (Finset.image sel Finset.univ)
      ↔ Dominates (naimarkSharpDesign F hm) (Finset.image cosel Finset.univ) := by
  have hcoinj : Function.Injective cosel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inr a) = Sum.elim sel cosel (Sum.inr b) := hab
    exact Sum.inr.inj (hpart.1 h)
  rw [naimark_dominates_iff_compl_reading N hm sel cosel hpart,
    dominates_naimarkSharpDesign_iff_reading F hm hcoinj]

/-! ## Part C -- `D` is its own sharp design's dual frame

`Gtz.totalGap`, `Gtz.posDef_totalGap` and `Gtz.totalGap_eq_sum` are landed in
`Gtz/Wave/SharpFiveSetCriterion.lean` and `Gtz/Wave/SharpShareCoAtom.lean`.  They are
imported, not restated. -/

/-- **THE CO-ATOM.**  `D`'s own atom, rescaled by the reciprocal scalar and carried
through a congruence of the total gap. -/
noncomputable def sharpCoAtom (D : WeightedDesign m k) (congr : Matrix (Fin k) (Fin k) ℝ)
    (c : Fin m) : Fin k → ℝ :=
  coSharpScale D c • (congrᵀ *ᵥ D.atom c)

/-- **`D` IS A NAIMARK DUAL OF ITS OWN SHARP DESIGN.**  The dual Parseval law is Parseval
at the total gap read through the congruence, and the dependency law is `N`'s own
dependency, because the two per-atom scalars are reciprocal. -/
noncomputable def sharpNaimarkDual {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (congruence : Matrix (Fin k) (Fin k) ℝ)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) :
    NaimarkDual (naimarkSharpDesign F hm) k where
  co := sharpCoAtom D congruence
  rankAdd := by have h := N.rankAdd; omega
  dependency := by
    intro i j
    have hterm : ∀ c : Fin m,
        (naimarkSharpDesign F hm).weight c * (naimarkSharpDesign F hm).atom c i
            * sharpCoAtom D congruence c j
          = ∑ a : Fin r, ∑ b : Fin k,
            F.whiten a i * congruence b j * (D.weight c * D.atom c b * N.co c a) := by
      intro c
      have hscal := sharpScale_mul_coSharpScale D hm c
      have hleft : (naimarkSharpDesign F hm).atom c i
          = sharpScale D c * ∑ a : Fin r, F.whiten a i * N.co c a := by
        show (F.whitenᵀ *ᵥ (sharpScale D c • N.co c)) i = _
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by
          rw [Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hright : sharpCoAtom D congruence c j
          = coSharpScale D c * ∑ b : Fin k, congruence b j * D.atom c b := by
        rw [sharpCoAtom, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        congr 1
      have hprod := Fintype.sum_mul_sum (fun a : Fin r => F.whiten a i * N.co c a)
        (fun b : Fin k => congruence b j * D.atom c b)
      have hgoal : ∑ a : Fin r, ∑ b : Fin k,
            F.whiten a i * congruence b j * (D.weight c * D.atom c b * N.co c a)
          = D.weight c * ((∑ a : Fin r, F.whiten a i * N.co c a)
              * ∑ b : Fin k, congruence b j * D.atom c b) := by
        rw [hprod, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [naimarkSharpDesign_weight, hleft, hright, hgoal]
      linear_combination (D.weight c * ((∑ a : Fin r, F.whiten a i * N.co c a)
        * ∑ b : Fin k, congruence b j * D.atom c b)) * hscal
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hdep := N.dependency b a
    rw [← Finset.mul_sum, hdep, mul_zero]
  coParseval := by
    have hterm : ∀ c : Fin m,
        (naimarkSharpDesign F hm).weight c • atomMatrix (sharpCoAtom D congruence c)
          = congruenceᵀ * ((1 - D.weight c) • atomMatrix (D.atom c)) * congruence := by
      intro c
      have hpos := D.weight_pos c
      have hlt := weight_lt_one D hm c
      have hwne : D.weight c ≠ 0 := ne_of_gt hpos
      rw [naimarkSharpDesign_weight, sharpCoAtom, atomMatrix_smul, atomMatrix_conj,
        Matrix.transpose_transpose, coSharpScale,
        Real.sq_sqrt (coSharpScale_nonneg D hm c), Matrix.mul_smul, Matrix.smul_mul,
        smul_smul]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_mul, ← Finset.mul_sum,
      ← totalGap_eq_sum, hcongr]

/-! ## Part D -- the involution -/

/-- **THE SECOND SHARP TARGET IS `Bᵀ B`.**  Sharpening the sharp design reads its own
`Omega` as `Bᵀ S_all B`, which is `1 + Bᵀ B` by the congruence. -/
theorem naimarkSharpTarget_sharpNaimarkDual {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) (congruence : Matrix (Fin k) (Fin k) ℝ)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) :
    naimarkSharpTarget (sharpNaimarkDual F hm congruence hcongr) = congruenceᵀ * congruence := by
  have hterm : ∀ c : Fin m,
      ((naimarkSharpDesign F hm).weight c / (1 - (naimarkSharpDesign F hm).weight c))
          • atomMatrix ((sharpNaimarkDual F hm congruence hcongr).co c)
        = congruenceᵀ * atomMatrix (D.atom c) * congruence := by
    intro c
    have hpos := D.weight_pos c
    have hlt := weight_lt_one D hm c
    show (D.weight c / (1 - D.weight c)) • atomMatrix (sharpCoAtom D congruence c) = _
    have hwne : D.weight c ≠ 0 := ne_of_gt hpos
    have hcone : (1 : ℝ) - D.weight c ≠ 0 := by intro hzero; linarith
    rw [sharpCoAtom, atomMatrix_smul, atomMatrix_conj, Matrix.transpose_transpose,
      coSharpScale, Real.sq_sqrt (coSharpScale_nonneg D hm c), smul_smul]
    rw [show D.weight c / (1 - D.weight c) * ((1 - D.weight c) / D.weight c) = 1 by
      field_simp, one_smul]
  rw [naimarkSharpTarget, naimarkOmega, Finset.sum_congr rfl fun c _ => hterm c,
    ← Finset.sum_mul, ← Finset.mul_sum, ← subsetSum]
  have hshift : subsetSum D Finset.univ = totalGap D + 1 := by
    rw [totalGap]; abel
  rw [hshift, Matrix.mul_add, Matrix.add_mul, hcongr, Matrix.mul_one]
  abel

/-- **THE SECOND WHITENER IS THE INVERSE CONGRUENCE.** -/
noncomputable def secondSharpFrame {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (congruence : Matrix (Fin k) (Fin k) ℝ) (hunit : IsUnit congruence.det)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) :
    SharpFrame (sharpNaimarkDual F hm congruence hcongr) where
  whiten := congruence⁻¹
  unit := Matrix.isUnit_nonsing_inv_det congruence hunit
  spec := by
    have hinv : congruence * congruence⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
    rw [naimarkSharpTarget_sharpNaimarkDual F hm congruence hcongr]
    calc (congruence⁻¹)ᵀ * (congruenceᵀ * congruence) * congruence⁻¹
        = (congruence * congruence⁻¹)ᵀ * (congruence * congruence⁻¹) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.transpose_one, Matrix.one_mul]

/-- **THE INVOLUTION.**  Sharpening twice returns the original atoms exactly.  The two
per-atom scalars are reciprocal and the two whiteners are inverse congruences, so nothing
survives the round trip. -/
theorem naimarkSharpAtom_secondSharpFrame {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (congruence : Matrix (Fin k) (Fin k) ℝ) (hunit : IsUnit congruence.det)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) (c : Fin m) :
    naimarkSharpAtom (secondSharpFrame F hm congruence hunit hcongr) c = D.atom c := by
  have hscal := sharpScale_mul_coSharpScale D hm c
  show (congruence⁻¹)ᵀ *ᵥ (sharpScale (naimarkSharpDesign F hm) c • sharpCoAtom D congruence c)
    = D.atom c
  have hweight : sharpScale (naimarkSharpDesign F hm) c = sharpScale D c := rfl
  rw [hweight, sharpCoAtom, smul_smul, hscal, one_smul, Matrix.mulVec_mulVec,
    ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one,
    Matrix.one_mulVec]

/-- **THE INVOLUTION, AS A DESIGN IDENTITY.**  The twice-sharpened design is the original
design, atom for atom and weight for weight. -/
theorem naimarkSharpDesign_secondSharpFrame {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (congruence : Matrix (Fin k) (Fin k) ℝ) (hunit : IsUnit congruence.det)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) :
    (∀ c, (naimarkSharpDesign (secondSharpFrame F hm congruence hunit hcongr) hm).atom c = D.atom c)
      ∧ ∀ c, (naimarkSharpDesign (secondSharpFrame F hm congruence hunit hcongr) hm).weight c
          = D.weight c :=
  ⟨naimarkSharpAtom_secondSharpFrame F hm congruence hunit hcongr, fun _ => rfl⟩

/-- **THE ROUND TRIP EXISTS.**  Every design of at least two atoms admits the whole
round trip: a dual, a whitening frame, a congruence of the total gap, and the second
frame that returns it to itself. -/
theorem exists_naimarkSharpDesign_involution (D : WeightedDesign m k) (hm : 2 ≤ m)
    (hr : k + r = m) :
    ∃ (N : NaimarkDual D r) (F : SharpFrame N) (congruence : Matrix (Fin k) (Fin k) ℝ)
      (hunit : IsUnit congruence.det) (hcongr : congruenceᵀ * totalGap D * congruence = 1),
      ∀ c, naimarkSharpAtom (secondSharpFrame F hm congruence hunit hcongr) c = D.atom c := by
  obtain ⟨N⟩ := exists_naimarkDual D hr
  obtain ⟨F⟩ := exists_sharpFrame N hm
  obtain ⟨congruence, hunit, hcongr⟩ := exists_congruence_to_one (posDef_totalGap D hm)
  exact ⟨N, F, congruence, hunit, hcongr,
    naimarkSharpAtom_secondSharpFrame F hm congruence hunit hcongr⟩

/-! ## Part E -- the involution is FREE

At `m = 2k` the sharp design lives in the same space as `D`, so the involution of Part D
acts on one set and can be asked for a fixed point.  It has none, at any design, for any
Naimark dual and any whitening frame, and not even up to a congruence.

The obstruction is one line of positivity.  Pair the dependency law of the dual against
the whitener: that turns the dual atom `co_c` into the sharp atom, which a fixed point
replaces by `R g_c`.  What is left is

  `sum_c sqrt(t_c (1 - t_c)) . g_c (R g_c)^T = 0` ,

and `R` is invertible, so `sum_c sqrt(t_c (1 - t_c)) . g_c g_c^T = 0`.  That is a POSITIVE
combination of atom matrices, so every atom vanishes and Parseval reads `1 = 0`.

The coefficient `sqrt(t_c (1 - t_c))` is exactly the positive diagonal `N` of the
projection-chart form of this duality, `M_E = -N M^{-1} N`, where a fixed point wants
`(N^{-1/2} M N^{-1/2})^2 = -1` for a real symmetric matrix.  It is the same positivity,
spent one step earlier and with no chart, no inverse and no spectral theorem. -/

theorem sharpScale_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < sharpScale D c := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  rw [sharpScale]
  exact Real.sqrt_pos.mpr (div_pos hpos (by linarith))

theorem coSharpScale_pos (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    0 < coSharpScale D c := by
  have hpos := D.weight_pos c
  have hlt := weight_lt_one D hm c
  rw [coSharpScale]
  exact Real.sqrt_pos.mpr (div_pos (by linarith) hpos)

/-- **A POSITIVE COMBINATION OF THE ATOM MATRICES IS NEVER ZERO.**  Read on the diagonal
at one coordinate: if the total vanishes then every atom vanishes at that coordinate, and
Parseval reads one there. -/
theorem sum_pos_smul_atom_sq_ne_zero (D : WeightedDesign m k) {coeff : Fin m → ℝ}
    (hcoeff : ∀ c, 0 < coeff c) (coord : Fin k) :
    ∑ c, coeff c * (D.atom c coord * D.atom c coord) ≠ 0 := by
  intro hzero
  have hnonneg : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ coeff c * (D.atom c coord * D.atom c coord) :=
    fun c _ => mul_nonneg (hcoeff c).le (mul_self_nonneg _)
  have hatom : ∀ c : Fin m, D.atom c coord = 0 := by
    intro c
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero c (Finset.mem_univ c)
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hcoeff c)))
  have hpars : (∑ c, D.weight c • atomMatrix (D.atom c)) coord coord
      = (1 : Matrix (Fin k) (Fin k) ℝ) coord coord := by rw [D.isParseval]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.one_apply_eq] at hpars
  have hcollapse : ∑ c, D.weight c * (D.atom c coord * D.atom c coord) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hatom c]; ring
  rw [hcollapse] at hpars
  exact zero_ne_one hpars

/-- **THE SHARP DESIGN IS NEVER A CONGRUENCE OF THE DESIGN.**  At `m = 2k` no Naimark
dual, no whitening frame and no invertible `R` make the sharp atoms `R g_c`.  Taking
`R = 1` this says the involution has no fixed point. -/
theorem not_naimarkSharpAtom_eq_mulVec (N : NaimarkDual D k) (F : SharpFrame N) (hm : 2 ≤ m)
    {R : Matrix (Fin k) (Fin k) ℝ} (hR : IsUnit R.det) :
    ¬ ∀ c : Fin m, naimarkSharpAtom F c = R *ᵥ D.atom c := by
  intro hfix
  -- the whitener pairing of a dual atom is the co-scaled image of the atom
  have hpair : ∀ (c : Fin m) (p : Fin k),
      ∑ a : Fin k, F.whiten a p * N.co c a = coSharpScale D c * (R *ᵥ D.atom c) p := by
    intro c p
    have hc := congrFun (hfix c) p
    rw [naimarkSharpAtom, Matrix.mulVec, dotProduct] at hc
    have hexpand : ∑ a : Fin k, F.whitenᵀ p a * (sharpScale D c • N.co c) a
        = sharpScale D c * ∑ a : Fin k, F.whiten a p * N.co c a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hexpand] at hc
    have hscal := sharpScale_mul_coSharpScale D hm c
    linear_combination coSharpScale D c * hc
      - (∑ a : Fin k, F.whiten a p * N.co c a) * hscal
  -- the dependency law, paired against the whitener
  have hdep : ∀ i p : Fin k,
      ∑ c : Fin m, D.weight c * coSharpScale D c * (D.atom c i * (R *ᵥ D.atom c) p) = 0 := by
    intro i p
    have hstep : ∀ c : Fin m,
        D.weight c * coSharpScale D c * (D.atom c i * (R *ᵥ D.atom c) p)
          = ∑ a : Fin k, F.whiten a p * (D.weight c * D.atom c i * N.co c a) := by
      intro c
      calc D.weight c * coSharpScale D c * (D.atom c i * (R *ᵥ D.atom c) p)
          = D.weight c * D.atom c i * (coSharpScale D c * (R *ᵥ D.atom c) p) := by ring
        _ = D.weight c * D.atom c i * ∑ a : Fin k, F.whiten a p * N.co c a := by
            rw [hpair c p]
        _ = ∑ a : Fin k, F.whiten a p * (D.weight c * D.atom c i * N.co c a) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl fun c _ => hstep c, Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.mul_sum, N.dependency i a, mul_zero]
  -- undo the congruence
  have hfinal : ∀ i l : Fin k,
      ∑ c : Fin m, D.weight c * coSharpScale D c * (D.atom c i * D.atom c l) = 0 := by
    intro i l
    have hinv : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ hR
    have hstep : ∀ c : Fin m,
        D.weight c * coSharpScale D c * (D.atom c i * D.atom c l)
          = ∑ p : Fin k, R⁻¹ l p
              * (D.weight c * coSharpScale D c * (D.atom c i * (R *ᵥ D.atom c) p)) := by
      intro c
      have hrow : ∑ p : Fin k, R⁻¹ l p * (R *ᵥ D.atom c) p = D.atom c l := by
        have hchain : R⁻¹ *ᵥ (R *ᵥ D.atom c) = D.atom c := by
          rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
        have hentry := congrFun hchain l
        rwa [Matrix.mulVec, dotProduct] at hentry
      calc D.weight c * coSharpScale D c * (D.atom c i * D.atom c l)
          = D.weight c * coSharpScale D c * D.atom c i
              * ∑ p : Fin k, R⁻¹ l p * (R *ᵥ D.atom c) p := by rw [hrow]; ring
        _ = ∑ p : Fin k, R⁻¹ l p
              * (D.weight c * coSharpScale D c * (D.atom c i * (R *ᵥ D.atom c) p)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by ring
    rw [Finset.sum_congr rfl fun c _ => hstep c, Finset.sum_comm]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← Finset.mul_sum, hdep i p, mul_zero]
  have hk : 0 < k := by have hrank := N.rankAdd; omega
  exact sum_pos_smul_atom_sq_ne_zero D
    (fun c => mul_pos (D.weight_pos c) (coSharpScale_pos D hm c)) ⟨0, hk⟩
    (hfinal ⟨0, hk⟩ ⟨0, hk⟩)

/-- **THE INVOLUTION HAS NO FIXED POINT.**  The sharp atoms are never the design's own
atoms.  With `Gtz.naimarkSharpAtom_secondSharpFrame` this makes the sharp design a FREE
involution on the designs of `m = 2k`: every orbit has exactly two members. -/
theorem not_naimarkSharpAtom_eq (N : NaimarkDual D k) (F : SharpFrame N) (hm : 2 ≤ m) :
    ¬ ∀ c : Fin m, naimarkSharpAtom F c = D.atom c := by
  intro hfix
  refine not_naimarkSharpAtom_eq_mulVec N F hm
    (R := (1 : Matrix (Fin k) (Fin k) ℝ)) (by simp) fun c => ?_
  rw [Matrix.one_mulVec]
  exact hfix c

/-- **THE SHARP DESIGN IS NEVER THE DESIGN**, as a statement about designs. -/
theorem naimarkSharpDesign_ne_self (N : NaimarkDual D k) (F : SharpFrame N) (hm : 2 ≤ m) :
    naimarkSharpDesign F hm ≠ D := by
  intro heq
  refine not_naimarkSharpAtom_eq N F hm fun c => ?_
  rw [← naimarkSharpDesign_atom F hm c, heq]

/-! ## Part F -- four coplanar atoms are a parallel pair of the sharp design

`Gtz.pairCapSlack_eq_zero_iff_fourCoplanar'` says the cap slack of a pair of a `(6,3)`
design vanishes exactly when the COMPLEMENTARY four atoms are coplanar, and
`Gtz.pairCapSlack_eq_weight_mul_coCrossNormSq` says that slack is the DUAL pair's squared
area.  The sharp atom is the dual atom scaled by a positive number and carried through an
invertible congruence, so the sharp pair area and the dual pair area vanish together.
Chaining the three gives the half of the `(6,3)` dictionary that no lane could state,
because it names the sharp design:

  **four atoms of `D` are coplanar  <->  the complementary pair of the SHARP design is
  parallel.**

Read on the sharp design, whose own sharp design is `D` by Part D, it reads the other way:
a parallel pair of `D` is four coplanar atoms of the sharp design. -/

/-- A vanishing pair area is dependence, at rank three. -/
theorem crossNormSq_eq_zero_iff_dependent (leftVec rightVec : Fin 3 → ℝ) :
    crossNormSq leftVec rightVec = 0
      ↔ (leftVec = 0 ∨ ∃ scale : ℝ, rightVec = scale • leftVec) := by
  rw [crossNormSq_eq_leverage_mul_sub_sq]
  exact leverageDefect_eq_zero_iff leftVec rightVec

/-- **THE SHARP DESIGN AND THE DUAL HAVE THE SAME PARALLEL PAIRS.**  The sharp atom is a
positive multiple of the dual atom carried through an invertible congruence, and neither
operation moves a pair on or off its line. -/
theorem crossNormSq_naimarkSharpAtom_eq_zero_iff {D : WeightedDesign m k}
    {N : NaimarkDual D 3} (F : SharpFrame N) (hm : 2 ≤ m) (p q : Fin m) :
    crossNormSq (naimarkSharpAtom F p) (naimarkSharpAtom F q) = 0
      ↔ crossNormSq (N.co p) (N.co q) = 0 := by
  have hdet : F.whitenᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mp F.unit
  have hp := ne_of_gt (sharpScale_pos D hm p)
  have hq := ne_of_gt (sharpScale_pos D hm q)
  rw [crossNormSq_eq_zero_iff_dependent, crossNormSq_eq_zero_iff_dependent]
  constructor
  · rintro (hzero | ⟨scale, hscale⟩)
    · left
      have hkill : F.whitenᵀ *ᵥ (sharpScale D p • N.co p) = 0 := by
        rw [← naimarkSharpAtom]; exact hzero
      have hsmul := Matrix.eq_zero_of_mulVec_eq_zero hdet hkill
      funext coord
      have hentry := congrFun hsmul coord
      rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hentry
      exact (mul_eq_zero.mp hentry).resolve_left hp
    · refine Or.inr ⟨scale * sharpScale D p / sharpScale D q, ?_⟩
      have hkill : F.whitenᵀ
            *ᵥ (sharpScale D q • N.co q - (scale * sharpScale D p) • N.co p) = 0 := by
        rw [Matrix.mulVec_sub, ← naimarkSharpAtom, hscale, ← smul_smul,
          Matrix.mulVec_smul, ← naimarkSharpAtom, sub_self]
      have hsmul := Matrix.eq_zero_of_mulVec_eq_zero hdet hkill
      funext coord
      have hentry := congrFun hsmul coord
      rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        Pi.zero_apply] at hentry
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hq]
      linear_combination hentry
  · rintro (hzero | ⟨scale, hscale⟩)
    · left
      rw [naimarkSharpAtom, hzero, smul_zero, Matrix.mulVec_zero]
    · refine Or.inr ⟨scale * sharpScale D q / sharpScale D p, ?_⟩
      have hvec : sharpScale D q • N.co q
          = (scale * sharpScale D q / sharpScale D p) • (sharpScale D p • N.co p) := by
        rw [hscale, smul_smul, smul_smul]
        congr 1
        field_simp
      rw [naimarkSharpAtom, naimarkSharpAtom, hvec, Matrix.mulVec_smul]

/-- **THE CAP SLACK VANISHES EXACTLY AT A PARALLEL PAIR OF THE SHARP DESIGN.** -/
theorem pairCapSlack_eq_zero_iff_crossNormSq_naimarkSharpAtom {D : WeightedDesign m k}
    {N : NaimarkDual D 3} (F : SharpFrame N) (hm : 2 ≤ m) {p q : Fin m} (hpq : p ≠ q) :
    pairCapSlack D p q = 0
      ↔ crossNormSq (naimarkSharpAtom F p) (naimarkSharpAtom F q) = 0 := by
  rw [crossNormSq_naimarkSharpAtom_eq_zero_iff F hm p q,
    pairCapSlack_eq_weight_mul_coCrossNormSq N hpq]
  have hweight : (0 : ℝ) < D.weight p * D.weight q :=
    mul_pos (D.weight_pos p) (D.weight_pos q)
  constructor
  · intro hzero
    have hsplit : D.weight p * D.weight q * crossNormSq (N.co p) (N.co q) = 0 := by
      linarith [hzero]
    exact (mul_eq_zero.mp hsplit).resolve_left (ne_of_gt hweight)
  · intro hzero
    rw [hzero, mul_zero]

/-- **THE OTHER HALF OF THE `(6,3)` DICTIONARY.**  Four atoms of a `(6,3)` design are
coplanar exactly when the COMPLEMENTARY pair of the sharp design is parallel.  The landed
`Gtz.crossNormSq_eq_zero_iff_forall_sq_tripleBracket_eq_zero` is the half that needs no
duality; this is the half that does, and it could not be stated until the sharp design had
a name. -/
theorem fourCoplanar_iff_crossNormSq_naimarkSharpAtom (D : WeightedDesign 6 3)
    (N : NaimarkDual D 3) (F : SharpFrame N) {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    FourCoplanar D x y z w
      ↔ crossNormSq (naimarkSharpAtom F p) (naimarkSharpAtom F q) = 0 := by
  rw [← pairCapSlack_eq_zero_iff_fourCoplanar' D hpq hpx hpy hpz hpw hqx hqy hqz hqw
    hxy hxz hxw hyz hyw hzw]
  exact pairCapSlack_eq_zero_iff_crossNormSq_naimarkSharpAtom F (by norm_num) hpq

/-- **FOUR COPLANAR ATOMS GIVE THE SHARP DESIGN A PARALLEL PAIR.**  So a `(6,3)` design
whose sharp design has NO parallel pair has no four coplanar atoms either. -/
theorem hasParallelPair_naimarkSharpDesign_of_fourCoplanar (D : WeightedDesign 6 3)
    (N : NaimarkDual D 3) (F : SharpFrame N) {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (hsix : (2 : ℕ) ≤ 6)
    (hflat : FourCoplanar D x y z w) :
    HasParallelPair (naimarkSharpDesign F hsix) := by
  have harea := (fourCoplanar_iff_crossNormSq_naimarkSharpAtom D N F hpq hpx hpy hpz hpw
    hqx hqy hqz hqw hxy hxz hxw hyz hyw hzw).mp hflat
  rcases (crossNormSq_eq_zero_iff_dependent _ _).mp harea with hzero | ⟨scale, hscale⟩
  · exact ⟨q, p, 0, hpq.symm, by
      rw [naimarkSharpDesign_atom, hzero, zero_smul]⟩
  · exact ⟨p, q, scale, hpq, by
      rw [naimarkSharpDesign_atom, naimarkSharpDesign_atom, hscale]⟩

/-- **A PARALLEL PAIR OF THE DESIGN IS FOUR COPLANAR ATOMS OF THE SHARP DESIGN.**  Read
the dictionary above on the sharp design, whose own sharp design is `D` by Part D.  So the
two candidate certificates of the `(6,3)` hinge trade places under the involution, and by
Part E the involution never fixes a design.

**THIS IS NOT A PROOF OF THE HINGE, AND NO PROOF CAN RUN THROUGH IT ALONE.**  The sharp
duality preserves `Gtz.IsTie` but it does NOT preserve `Gtz.HasParallelPair`:
`Gtz.hinge_not_preserved_by_duality` (Gtz/Wave/CorankOneRigidity.lean) exchanges the cells
`(k+1,1)` and `(k+1,k)`, where the hinge is free on one side and false on the other for
every `k` of at least two.  What survives at `(6,3)` is only the pointwise dictionary
above, because that cell is SELF-DUAL and the fifteen pairs match the fifteen
complementary quadruples.  Turning it into a statement about counterexamples needs the
equivalence "a `(6,3)` tie has a parallel pair exactly when it has four coplanar atoms",
which this module does NOT prove and which is not landed in the tree. -/
theorem fourCoplanar_naimarkSharpDesign_iff_crossNormSq (D : WeightedDesign 6 3)
    (N : NaimarkDual D 3) (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6)
    (congruence : Matrix (Fin 3) (Fin 3) ℝ) (hunit : IsUnit congruence.det)
    (hcongr : congruenceᵀ * totalGap D * congruence = 1) {p q x y z w : Fin 6}
    (hpq : p ≠ q) (hpx : p ≠ x) (hpy : p ≠ y) (hpz : p ≠ z) (hpw : p ≠ w)
    (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z) (hqw : q ≠ w)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    FourCoplanar (naimarkSharpDesign F hsix) x y z w
      ↔ crossNormSq (D.atom p) (D.atom q) = 0 := by
  have hkey := fourCoplanar_iff_crossNormSq_naimarkSharpAtom (naimarkSharpDesign F hsix)
    (sharpNaimarkDual F hsix congruence hcongr)
    (secondSharpFrame F hsix congruence hunit hcongr)
    hpq hpx hpy hpz hpw hqx hqy hqz hqw hxy hxz hxw hyz hyw hzw
  rw [naimarkSharpAtom_secondSharpFrame F hsix congruence hunit hcongr p,
    naimarkSharpAtom_secondSharpFrame F hsix congruence hunit hcongr q] at hkey
  exact hkey

end Gtz
