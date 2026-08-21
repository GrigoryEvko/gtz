import Gtz.Wave.TieGraphTrichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The four-set determinant law, and why the tie graph cannot see a doubling

Two exact facts about four atoms, and one structural negative that follows
from them.

## The four-set law

A four-atom set carries four triples, each omitting one atom.  Their gap
determinants are not independent: they total the four-set gap's own
determinant less its second invariant.

* `Gtz.sum_fourSet_gapDet_eq_det_sub_e2` — for ANY four vectors,

    `Σ_i det(S_{T_i} − 1) = det M − e₂(M)` ,  `M = S_{abcd} − 1` ,

  a polynomial identity in twelve variables, no hypothesis at all.  The
  route behind it is the rank-one downdate `det(M − g_ig_iᵀ) = det M(1 − r_i)`
  together with `Σ_i r_i = 3 + tr M⁻¹` and `det M · tr M⁻¹ = e₂(M)`, but the
  landed statement is inverse-free and needs none of that.
* `Gtz.isTie_heavyFour_det_le_e2` — hence at a tie, a heavy pairwise
  admissible four-set obeys `det M ≤ e₂(M)`.  The four-vertex saturation
  gives four sign conditions; the identity fuses them into ONE.

## The blindness

`Gtz.parallel_pairGapMinor_eq` computes the pair gap minor of a parallel
pair EXACTLY:

  `pairGapMinor g (ρ • g) = 1 − ℓ_p − ℓ_q` .

So a parallel pair carrying a heavy atom is INADMISSIBLE
(`Gtz.not_admissiblePair_of_parallel_of_heavy`), no live triple contains
both of its members (`Gtz.not_liveTriple_of_parallel`), and — the structural
point — **every heavy pairwise admissible configuration omits one member of
the pair** (`Gtz.heavyAdmissible_omits_parallel_member`).

At a doubling that says the admissible tie graph sees only the REDUCED
design, so no instrument phrased in the tie-graph vocabulary can separate a
doubling from its reduction.  Measured at the two fixtures: the heavy
admissible four-sets take the identical value set
`{(det, e₂, tr) = (12, 22, 11/6), (32, 32, 1)}` at BOTH `(5,3)` and `(6,3)`,
and the nine at `(6,3)` are exactly the fifteen less the six that carry both
spine copies.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The four-set determinant identity -/

set_option linter.unusedSimpArgs false in
/-- **THE FOUR-SET DETERMINANT LAW.**  For any four vectors the four triple
gap determinants total the four-set gap determinant less its second
invariant:

  `Σ_i det(S_{T_i} − 1) = det M − e₂(M)` ,  `M = S_{abcd} − 1` .

A polynomial identity in twelve variables — no positivity, no invertibility,
no hypothesis. -/
theorem sum_fourSet_gapDet_eq_det_sub_e2 (a b c d : Fin 3 → ℝ) :
    (atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix c + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix d - 1).det
        + (atomMatrix a + atomMatrix b + atomMatrix c - 1).det
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        - (((Matrix.trace
              (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)) ^ 2
            - Matrix.trace
              ((atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)
                * (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1))) / 2) := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, atomMatrix,
    Matrix.vecMulVec_apply, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- **THE FOUR-SET LAW IN TRIPLE COORDINATES.**  The same identity with each
triple determinant read as the landed `Gtz.tripleGapDet`, an explicit
polynomial in the six dot products of its triple. -/
theorem sum_fourSet_tripleGapDet_eq_det_sub_e2 (a b c d : Fin 3 → ℝ) :
    tripleGapDet b c d + tripleGapDet a c d + tripleGapDet a b d + tripleGapDet a b c
      = (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1).det
        - (((Matrix.trace
              (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)) ^ 2
            - Matrix.trace
              ((atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1)
                * (atomMatrix a + atomMatrix b + atomMatrix c + atomMatrix d - 1))) / 2) := by
  rw [← gapDet_triple_eq_tripleGapDet b c d, ← gapDet_triple_eq_tripleGapDet a c d,
    ← gapDet_triple_eq_tripleGapDet a b d, ← gapDet_triple_eq_tripleGapDet a b c]
  exact sum_fourSet_gapDet_eq_det_sub_e2 a b c d

/-- **THE FOUR SIGN CONDITIONS FUSE INTO ONE.**  At a tie a heavy pairwise
admissible four-set obeys `det M ≤ e₂(M)`: the four-vertex saturation makes
every triple determinant nonpositive, and the four-set law turns their sum
into the two invariants of the four-set gap. -/
theorem isTie_heavyFour_det_le_e2 (D : WeightedDesign m 3) (htie : IsTie D)
    {a b c d : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hha : HeavyAtom D a) (hhb : HeavyAtom D b) (hhc : HeavyAtom D c)
    (hhd : HeavyAtom D d)
    (pab : AdmissiblePair (D.atom a) (D.atom b))
    (pac : AdmissiblePair (D.atom a) (D.atom c))
    (pad : AdmissiblePair (D.atom a) (D.atom d))
    (pbc : AdmissiblePair (D.atom b) (D.atom c))
    (pbd : AdmissiblePair (D.atom b) (D.atom d))
    (pcd : AdmissiblePair (D.atom c) (D.atom d)) :
    (atomMatrix (D.atom a) + atomMatrix (D.atom b) + atomMatrix (D.atom c)
        + atomMatrix (D.atom d) - 1).det
      ≤ (((Matrix.trace (atomMatrix (D.atom a) + atomMatrix (D.atom b)
              + atomMatrix (D.atom c) + atomMatrix (D.atom d) - 1)) ^ 2
          - Matrix.trace ((atomMatrix (D.atom a) + atomMatrix (D.atom b)
              + atomMatrix (D.atom c) + atomMatrix (D.atom d) - 1)
            * (atomMatrix (D.atom a) + atomMatrix (D.atom b)
              + atomMatrix (D.atom c) + atomMatrix (D.atom d) - 1))) / 2) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    isTie_heavyFour_admissible_gapDet_nonpos D htie hab hac had hbc hbd hcd
      hha hhb hhc hhd pab pac pad pbc pbd pcd
  have hid := sum_fourSet_tripleGapDet_eq_det_sub_e2
    (D.atom a) (D.atom b) (D.atom c) (D.atom d)
  linarith [h1, h2, h3, h4, hid]

/-! ## 2. A parallel pair is inadmissible -/

/-- **THE PAIR GAP MINOR OF A PARALLEL PAIR.**  Exactly the deficit of the
two leverages:

  `pairGapMinor g (ρ • g) = 1 − ℓ_g − ℓ_{ρg}` .

The squared pairing cancels the leverage product entirely, so no angle
survives — only the two lengths. -/
theorem parallel_pairGapMinor_eq (g : Fin 3 → ℝ) (ratio : ℝ) :
    pairGapMinor g (ratio • g)
      = 1 - leverageOf g - leverageOf (ratio • g) := by
  simp only [pairGapMinor, leverageOf, dotProduct, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

/-- **A PARALLEL PAIR CARRYING A HEAVY ATOM IS INADMISSIBLE.**  Its minor is
`1 − ℓ_p − ℓ_q`, and a heavy atom alone already pushes the leverage total
past one. -/
theorem not_admissiblePair_of_parallel_of_heavy {g : Fin 3 → ℝ} {ratio : ℝ}
    (hheavy : 1 < leverageOf g) :
    ¬ AdmissiblePair g (ratio • g) := by
  rw [AdmissiblePair, parallel_pairGapMinor_eq]
  have hnn : 0 ≤ leverageOf (ratio • g) := by
    rw [leverageOf]
    positivity
  intro hpos
  linarith

/-- **NO LIVE TRIPLE CARRIES BOTH MEMBERS OF A PARALLEL PAIR.**  Liveness
demands every pair admissible, and the parallel pair never is once either
member is heavy — which liveness itself supplies. -/
theorem not_liveTriple_of_parallel (D : WeightedDesign m 3) {p q r : Fin m}
    {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p) :
    ¬ LiveTriple D p q r := by
  rintro ⟨hp, -, -, ppq, -, -⟩
  rw [hpar] at ppq
  exact not_admissiblePair_of_parallel_of_heavy hp ppq

/-- **THE BLINDNESS, STATED.**  Every heavy pairwise admissible configuration
omits one member of a parallel pair: the pair itself is never admissible, so
no admissible set contains both.  At a doubling the admissible tie graph
therefore sees only the reduced design, and no instrument phrased in that
vocabulary can separate a doubling from its reduction. -/
theorem heavyAdmissible_omits_parallel_member (D : WeightedDesign m 3)
    {p q : Fin m} {ratio : ℝ} (hpar : D.atom q = ratio • D.atom p)
    (hp : HeavyAtom D p) :
    ¬ AdmissiblePair (D.atom p) (D.atom q) := by
  rw [hpar]
  exact not_admissiblePair_of_parallel_of_heavy hp

end Gtz
