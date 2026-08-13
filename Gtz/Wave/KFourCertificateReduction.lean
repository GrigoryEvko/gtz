import Gtz.Wave.CycleSeamReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The K4 certificate reduction — the tetrahedral profile closes on one certificate

The dense K4 profile puts one shared atom on each of the six slot pairs.
This module reduces `RankFourKFourClosed` to one polynomial certificate
in edge coordinates.  The reduction consumes the landed edge frame: the
corner reads, the Gram edge entries, the unit norms, and the share
calculus of the seam module.

## The reduction chain

1. **The edge extraction.**  Each pair share of cardinality one names
   its edge atom, and the fifteen edge distinctions follow from the
   exclusive carriers.
2. **The support identification.**  Each slot support is exactly its
   three incident edges: the three edges embed, and the cardinalities
   agree.
3. **The certificate.**  `KFourCertificate` states the kill in edge
   coordinates: the twelve corner reads, idempotency, the trace, the
   weight sum, the four unit norms, the Gamma exchange symmetry, and
   the four Gamma diagonal reads give `False` at a negative value.
4. **The discharge.**  The certificate closes `RankFourKFourClosed` at
   the identity slot pattern: no relabeling is necessary, because the
   profile hypotheses quantify over all slot pairs.

## Key results

* `Gtz.KFourCertificate` — **THE K4 CERTIFICATE.**
* `Gtz.rankFourKFourClosed_of_certificate` — **THE DISCHARGE.**  The
  certificate implies closure three.

## Vacuity

The crux statements are vacuous if `Gtz.GtzWeighted 6 3` holds.  The
reduction is unconditional.
-/

namespace Gtz

open Matrix

/-! ## Layer 1 — the K4 certificate -/

/-- **THE K4 CERTIFICATE.**  The polynomial kill of the tetrahedral
profile in edge coordinates.  The edge atom of the slot pair `(i, j)`
carries the weight `wij` and the two coordinates `aij` (at slot `i`)
and `bij` (at slot `j`).  The hypotheses are the twelve corner reads,
idempotency, the trace, the weight sum, the four unit norms, the Gamma
matrix, the Gamma exchange symmetry, and the four Gamma diagonal
reads.  The conclusion is `False` at a negative value. -/
def KFourCertificate : Prop :=
  ∀ (value w01 w02 w03 w12 w13 w23 : ℝ)
    (a01 b01 a02 b02 a03 b03 a12 b12 a13 b13 a23 b23 : ℝ)
    (M Γ : Matrix (Fin 4) (Fin 4) ℝ),
    value < 0 →
    0 < w01 → 0 < w02 → 0 < w03 → 0 < w12 → 0 < w13 → 0 < w23 →
    w01 + w02 + w03 + w12 + w13 + w23 = 1 →
    M * M = M →
    M 0 0 + M 1 1 + M 2 2 + M 3 3 = 2 →
    a01 * M 0 0 + b01 * M 1 0 = (value + w01) * a01 →
    a01 * M 0 1 + b01 * M 1 1 = (value + w01) * b01 →
    a02 * M 0 0 + b02 * M 2 0 = (value + w02) * a02 →
    a02 * M 0 2 + b02 * M 2 2 = (value + w02) * b02 →
    a03 * M 0 0 + b03 * M 3 0 = (value + w03) * a03 →
    a03 * M 0 3 + b03 * M 3 3 = (value + w03) * b03 →
    a12 * M 1 1 + b12 * M 2 1 = (value + w12) * a12 →
    a12 * M 1 2 + b12 * M 2 2 = (value + w12) * b12 →
    a13 * M 1 1 + b13 * M 3 1 = (value + w13) * a13 →
    a13 * M 1 3 + b13 * M 3 3 = (value + w13) * b13 →
    a23 * M 2 2 + b23 * M 3 2 = (value + w23) * a23 →
    a23 * M 2 3 + b23 * M 3 3 = (value + w23) * b23 →
    a01 ^ 2 + a02 ^ 2 + a03 ^ 2 = 1 →
    b01 ^ 2 + a12 ^ 2 + a13 ^ 2 = 1 →
    b02 ^ 2 + b12 ^ 2 + a23 ^ 2 = 1 →
    b03 ^ 2 + b13 ^ 2 + b23 ^ 2 = 1 →
    Γ = !![1, a01 * b01, a02 * b02, a03 * b03;
           a01 * b01, 1, a12 * b12, a13 * b13;
           a02 * b02, a12 * b12, 1, a23 * b23;
           a03 * b03, a13 * b13, a23 * b23, 1] →
    (Γ * M)ᵀ = Γ * M →
    (Γ * M) 0 0 = value + w01 * a01 ^ 2 + w02 * a02 ^ 2 + w03 * a03 ^ 2 →
    (Γ * M) 1 1 = value + w01 * b01 ^ 2 + w12 * a12 ^ 2 + w13 * a13 ^ 2 →
    (Γ * M) 2 2 = value + w02 * b02 ^ 2 + w12 * b12 ^ 2 + w23 * a23 ^ 2 →
    (Γ * M) 3 3 = value + w03 * b03 ^ 2 + w13 * b13 ^ 2 + w23 * b23 ^ 2 →
    a01 ≠ 0 → b01 ≠ 0 → a02 ≠ 0 → b02 ≠ 0 → a03 ≠ 0 → b03 ≠ 0 →
    a12 ≠ 0 → b12 ≠ 0 → a13 ≠ 0 → b13 ≠ 0 → a23 ≠ 0 → b23 ≠ 0 →
    False

/-! ## Layer 2 — the discharge -/

set_option maxHeartbeats 1600000 in
/-- **THE DISCHARGE.**  The K4 certificate closes the tetrahedral
profile.  The six edges come out of the unit pair shares, the supports
identify with the incident edge triples, and the certificate consumes
the edge frame at the identity slot pattern. -/
theorem rankFourKFourClosed_of_certificate
    (hcert : KFourCertificate) : RankFourKFourClosed := by
  classical
  intro crux frame hmult hcard hshareOne
  -- the six edge atoms
  obtain ⟨e01, hs01⟩ := Finset.card_eq_one.mp
    (hshareOne 0 1 (by decide) : pairShare frame.tightDir frame.basisLabel 0 1
      = 1)
  obtain ⟨e02, hs02⟩ := Finset.card_eq_one.mp
    (hshareOne 0 2 (by decide) : pairShare frame.tightDir frame.basisLabel 0 2
      = 1)
  obtain ⟨e03, hs03⟩ := Finset.card_eq_one.mp
    (hshareOne 0 3 (by decide) : pairShare frame.tightDir frame.basisLabel 0 3
      = 1)
  obtain ⟨e12, hs12⟩ := Finset.card_eq_one.mp
    (hshareOne 1 2 (by decide) : pairShare frame.tightDir frame.basisLabel 1 2
      = 1)
  obtain ⟨e13, hs13⟩ := Finset.card_eq_one.mp
    (hshareOne 1 3 (by decide) : pairShare frame.tightDir frame.basisLabel 1 3
      = 1)
  obtain ⟨e23, hs23⟩ := Finset.card_eq_one.mp
    (hshareOne 2 3 (by decide) : pairShare frame.tightDir frame.basisLabel 2 3
      = 1)
  -- the edge memberships
  have hm01L := shareSet_singleton_mem_left frame.basisLabel hs01
  have hm01R := shareSet_singleton_mem_right frame.basisLabel hs01
  have hm02L := shareSet_singleton_mem_left frame.basisLabel hs02
  have hm02R := shareSet_singleton_mem_right frame.basisLabel hs02
  have hm03L := shareSet_singleton_mem_left frame.basisLabel hs03
  have hm03R := shareSet_singleton_mem_right frame.basisLabel hs03
  have hm12L := shareSet_singleton_mem_left frame.basisLabel hs12
  have hm12R := shareSet_singleton_mem_right frame.basisLabel hs12
  have hm13L := shareSet_singleton_mem_left frame.basisLabel hs13
  have hm13R := shareSet_singleton_mem_right frame.basisLabel hs13
  have hm23L := shareSet_singleton_mem_left frame.basisLabel hs23
  have hm23R := shareSet_singleton_mem_right frame.basisLabel hs23
  -- the fifteen edge distinctions from the exclusive carriers
  have hne0102 : e01 ≠ e02 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 0)
    (by decide : (2 : Fin 4) ≠ 1) hm01L hm01R hm02R
  have hne0103 : e01 ≠ e03 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 0)
    (by decide : (3 : Fin 4) ≠ 1) hm01L hm01R hm03R
  have hne0112 : e01 ≠ e12 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 0)
    (by decide : (2 : Fin 4) ≠ 1) hm01L hm01R hm12R
  have hne0113 : e01 ≠ e13 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 0)
    (by decide : (3 : Fin 4) ≠ 1) hm01L hm01R hm13R
  have hne0123 : e01 ≠ e23 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 0)
    (by decide : (2 : Fin 4) ≠ 1) hm01L hm01R hm23L
  have hne0203 : e02 ≠ e03 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (3 : Fin 4) ≠ 0)
    (by decide : (3 : Fin 4) ≠ 2) hm02L hm02R hm03R
  have hne0212 : e02 ≠ e12 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 0)
    (by decide : (1 : Fin 4) ≠ 2) hm02L hm02R hm12L
  have hne0213 : e02 ≠ e13 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 0)
    (by decide : (1 : Fin 4) ≠ 2) hm02L hm02R hm13L
  have hne0223 : e02 ≠ e23 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 2) (by decide : (3 : Fin 4) ≠ 0)
    (by decide : (3 : Fin 4) ≠ 2) hm02L hm02R hm23R
  have hne0312 : e03 ≠ e12 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 0)
    (by decide : (1 : Fin 4) ≠ 3) hm03L hm03R hm12L
  have hne0313 : e03 ≠ e13 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 3) (by decide : (1 : Fin 4) ≠ 0)
    (by decide : (1 : Fin 4) ≠ 3) hm03L hm03R hm13L
  have hne0323 : e03 ≠ e23 := atom_ne_of_exclusive_carriers hmult
    (by decide : (0 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 0)
    (by decide : (2 : Fin 4) ≠ 3) hm03L hm03R hm23L
  have hne1213 : e12 ≠ e13 := atom_ne_of_exclusive_carriers hmult
    (by decide : (1 : Fin 4) ≠ 2) (by decide : (3 : Fin 4) ≠ 1)
    (by decide : (3 : Fin 4) ≠ 2) hm12L hm12R hm13R
  have hne1223 : e12 ≠ e23 := atom_ne_of_exclusive_carriers hmult
    (by decide : (1 : Fin 4) ≠ 2) (by decide : (3 : Fin 4) ≠ 1)
    (by decide : (3 : Fin 4) ≠ 2) hm12L hm12R hm23R
  have hne1323 : e13 ≠ e23 := atom_ne_of_exclusive_carriers hmult
    (by decide : (1 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 1)
    (by decide : (2 : Fin 4) ≠ 3) hm13L hm13R hm23L
  -- the support identifications
  have hsupp0 : datumTightSupport frame.tightDir (frame.basisLabel 0)
      = {e01, e02, e03} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hm01L
      · exact hm02L
      · exact hm03L
    · refine le_of_eq ((hcard 0).trans ?_)
      rw [Finset.card_insert_of_notMem (by simp [hne0102, hne0103]),
        Finset.card_insert_of_notMem (by simp [hne0203]),
        Finset.card_singleton]
  have hsupp1 : datumTightSupport frame.tightDir (frame.basisLabel 1)
      = {e01, e12, e13} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hm01R
      · exact hm12L
      · exact hm13L
    · refine le_of_eq ((hcard 1).trans ?_)
      rw [Finset.card_insert_of_notMem (by simp [hne0112, hne0113]),
        Finset.card_insert_of_notMem (by simp [hne1213]),
        Finset.card_singleton]
  have hsupp2 : datumTightSupport frame.tightDir (frame.basisLabel 2)
      = {e02, e12, e23} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hm02R
      · exact hm12R
      · exact hm23L
    · refine le_of_eq ((hcard 2).trans ?_)
      rw [Finset.card_insert_of_notMem (by simp [hne0212, hne0223]),
        Finset.card_insert_of_notMem (by simp [hne1223]),
        Finset.card_singleton]
  have hsupp3 : datumTightSupport frame.tightDir (frame.basisLabel 3)
      = {e03, e13, e23} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro atomIndex hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hm03R
      · exact hm13R
      · exact hm23R
    · refine le_of_eq ((hcard 3).trans ?_)
      rw [Finset.card_insert_of_notMem (by simp [hne0313, hne0323]),
        Finset.card_insert_of_notMem (by simp [hne1323]),
        Finset.card_singleton]
  -- the coordinate names
  set a01 := frame.tightDir (frame.basisLabel 0) e01
  set b01 := frame.tightDir (frame.basisLabel 1) e01
  set a02 := frame.tightDir (frame.basisLabel 0) e02
  set b02 := frame.tightDir (frame.basisLabel 2) e02
  set a03 := frame.tightDir (frame.basisLabel 0) e03
  set b03 := frame.tightDir (frame.basisLabel 3) e03
  set a12 := frame.tightDir (frame.basisLabel 1) e12
  set b12 := frame.tightDir (frame.basisLabel 2) e12
  set a13 := frame.tightDir (frame.basisLabel 1) e13
  set b13 := frame.tightDir (frame.basisLabel 3) e13
  set a23 := frame.tightDir (frame.basisLabel 2) e23
  set b23 := frame.tightDir (frame.basisLabel 3) e23
  -- the off-support coordinate zeros
  have hz0e12 : frame.tightDir (frame.basisLabel 0) e12 = 0 :=
    coordinate_zero_of_support_eq hsupp0
      (by simp [Ne.symm hne0112, Ne.symm hne0212, Ne.symm hne0312])
  have hz0e13 : frame.tightDir (frame.basisLabel 0) e13 = 0 :=
    coordinate_zero_of_support_eq hsupp0
      (by simp [Ne.symm hne0113, Ne.symm hne0213, Ne.symm hne0313])
  have hz0e23 : frame.tightDir (frame.basisLabel 0) e23 = 0 :=
    coordinate_zero_of_support_eq hsupp0
      (by simp [Ne.symm hne0123, Ne.symm hne0223, Ne.symm hne0323])
  have hz1e02 : frame.tightDir (frame.basisLabel 1) e02 = 0 :=
    coordinate_zero_of_support_eq hsupp1
      (by simp [Ne.symm hne0102, hne0212, hne0213])
  have hz1e03 : frame.tightDir (frame.basisLabel 1) e03 = 0 :=
    coordinate_zero_of_support_eq hsupp1
      (by simp [Ne.symm hne0103, hne0312, hne0313])
  have hz1e23 : frame.tightDir (frame.basisLabel 1) e23 = 0 :=
    coordinate_zero_of_support_eq hsupp1
      (by simp [Ne.symm hne0123, Ne.symm hne1223, Ne.symm hne1323])
  have hz2e01 : frame.tightDir (frame.basisLabel 2) e01 = 0 :=
    coordinate_zero_of_support_eq hsupp2
      (by simp [hne0102, hne0112, hne0123])
  have hz2e03 : frame.tightDir (frame.basisLabel 2) e03 = 0 :=
    coordinate_zero_of_support_eq hsupp2
      (by simp [Ne.symm hne0203, hne0312, hne0323])
  have hz2e13 : frame.tightDir (frame.basisLabel 2) e13 = 0 :=
    coordinate_zero_of_support_eq hsupp2
      (by simp [Ne.symm hne0213, Ne.symm hne1213, hne1323])
  have hz3e01 : frame.tightDir (frame.basisLabel 3) e01 = 0 :=
    coordinate_zero_of_support_eq hsupp3
      (by simp [hne0103, hne0113, hne0123])
  have hz3e02 : frame.tightDir (frame.basisLabel 3) e02 = 0 :=
    coordinate_zero_of_support_eq hsupp3
      (by simp [hne0203, hne0213, hne0223])
  have hz3e12 : frame.tightDir (frame.basisLabel 3) e12 = 0 :=
    coordinate_zero_of_support_eq hsupp3
      (by simp [Ne.symm hne0312, hne1213, hne1223])
  -- the corner reads
  have hr01a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 1)
    (frame.hmemAll 0) hs01
  have hr01b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 1)
    (frame.hmemAll 1) hs01
  have hr02a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 2)
    (frame.hmemAll 0) hs02
  have hr02b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 2)
    (frame.hmemAll 2) hs02
  have hr03a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 3)
    (frame.hmemAll 0) hs03
  have hr03b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (0 : Fin 4) ≠ 3)
    (frame.hmemAll 3) hs03
  have hr12a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (1 : Fin 4) ≠ 2)
    (frame.hmemAll 1) hs12
  have hr12b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (1 : Fin 4) ≠ 2)
    (frame.hmemAll 2) hs12
  have hr13a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (1 : Fin 4) ≠ 3)
    (frame.hmemAll 1) hs13
  have hr13b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (1 : Fin 4) ≠ 3)
    (frame.hmemAll 3) hs13
  have hr23a := kfour_corner_read_first frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (2 : Fin 4) ≠ 3)
    (frame.hmemAll 2) hs23
  have hr23b := kfour_corner_read_second frame.hdata frame.basisLabel
    frame.hrepresentation hmult (by decide : (2 : Fin 4) ≠ 3)
    (frame.hmemAll 3) hs23
  -- the unit norms
  have hnorm0 : a01 ^ 2 + a02 ^ 2 + a03 ^ 2 = 1 :=
    kfour_unit_norm_expand frame.hdata frame.basisLabel (frame.hmemAll 0)
      hsupp0 hne0102 hne0103 hne0203
  have hnorm1 : b01 ^ 2 + a12 ^ 2 + a13 ^ 2 = 1 :=
    kfour_unit_norm_expand frame.hdata frame.basisLabel (frame.hmemAll 1)
      hsupp1 hne0112 hne0113 hne1213
  have hnorm2 : b02 ^ 2 + b12 ^ 2 + a23 ^ 2 = 1 :=
    kfour_unit_norm_expand frame.hdata frame.basisLabel (frame.hmemAll 2)
      hsupp2 hne0212 hne0223 hne1223
  have hnorm3 : b03 ^ 2 + b13 ^ 2 + b23 ^ 2 = 1 :=
    kfour_unit_norm_expand frame.hdata frame.basisLabel (frame.hmemAll 3)
      hsupp3 hne0313 hne0323 hne1323
  -- the Gamma matrix in edge coordinates
  have hgram01 := kfour_gram_offdiag frame.basisLabel hs01
  have hgram02 := kfour_gram_offdiag frame.basisLabel hs02
  have hgram03 := kfour_gram_offdiag frame.basisLabel hs03
  have hgram12 := kfour_gram_offdiag frame.basisLabel hs12
  have hgram13 := kfour_gram_offdiag frame.basisLabel hs13
  have hgram23 := kfour_gram_offdiag frame.basisLabel hs23
  have hgramSymm : ∀ slotA slotB : Fin 4,
      basisGram frame.tightDir frame.basisLabel slotA slotB
        = basisGram frame.tightDir frame.basisLabel slotB slotA := by
    intro slotA slotB
    rw [basisGram_apply, basisGram_apply, dotProduct_comm]
  have hΓlit : basisGram frame.tightDir frame.basisLabel
      = !![1, a01 * b01, a02 * b02, a03 * b03;
           a01 * b01, 1, a12 * b12, a13 * b13;
           a02 * b02, a12 * b12, 1, a23 * b23;
           a03 * b03, a13 * b13, a23 * b23, 1] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp
    · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
        (frame.hmemAll 0)
    · exact hgram01
    · exact hgram02
    · exact hgram03
    · rw [hgramSymm 1 0]; exact hgram01
    · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
        (frame.hmemAll 1)
    · exact hgram12
    · exact hgram13
    · rw [hgramSymm 2 0]; exact hgram02
    · rw [hgramSymm 2 1]; exact hgram12
    · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
        (frame.hmemAll 2)
    · exact hgram23
    · rw [hgramSymm 3 0]; exact hgram03
    · rw [hgramSymm 3 1]; exact hgram13
    · rw [hgramSymm 3 2]; exact hgram23
    · exact basisGram_diagonal_of_mem frame.hdata frame.basisLabel
        (frame.hmemAll 3)
  -- the exchange symmetry
  have hsym : (basisGram frame.tightDir frame.basisLabel * frame.coeff)ᵀ
      = basisGram frame.tightDir frame.basisLabel * frame.coeff :=
    gram_exchange_transpose frame.basisLabel frame.hdata.isSymmetric
      frame.hdata.isIdempotent frame.hrepresentation
  -- the diagonal reads
  have hdiag0 : (basisGram frame.tightDir frame.basisLabel * frame.coeff) 0 0
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight e01 * a01 ^ 2
        + (chartPointOfDesign crux.design).weight e02 * a02 ^ 2
        + (chartPointOfDesign crux.design).weight e03 * a03 ^ 2 := by
    have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
      frame.hrepresentation (frame.hmemAll 0)
    rw [sum_six_atoms (fun atomIndex =>
        (chartPointOfDesign crux.design).weight atomIndex
          * frame.tightDir (frame.basisLabel 0) atomIndex ^ 2)
      hne0102 hne0103 hne0112 hne0113 hne0123 hne0203 hne0212 hne0213
      hne0223 hne0312 hne0313 hne0323 hne1213 hne1223 hne1323] at hread
    rw [hz0e12, hz0e13, hz0e23] at hread
    rw [hread]
    ring
  have hdiag1 : (basisGram frame.tightDir frame.basisLabel * frame.coeff) 1 1
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight e01 * b01 ^ 2
        + (chartPointOfDesign crux.design).weight e12 * a12 ^ 2
        + (chartPointOfDesign crux.design).weight e13 * a13 ^ 2 := by
    have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
      frame.hrepresentation (frame.hmemAll 1)
    rw [sum_six_atoms (fun atomIndex =>
        (chartPointOfDesign crux.design).weight atomIndex
          * frame.tightDir (frame.basisLabel 1) atomIndex ^ 2)
      hne0102 hne0103 hne0112 hne0113 hne0123 hne0203 hne0212 hne0213
      hne0223 hne0312 hne0313 hne0323 hne1213 hne1223 hne1323] at hread
    rw [hz1e02, hz1e03, hz1e23] at hread
    rw [hread]
    ring
  have hdiag2 : (basisGram frame.tightDir frame.basisLabel * frame.coeff) 2 2
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight e02 * b02 ^ 2
        + (chartPointOfDesign crux.design).weight e12 * b12 ^ 2
        + (chartPointOfDesign crux.design).weight e23 * a23 ^ 2 := by
    have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
      frame.hrepresentation (frame.hmemAll 2)
    rw [sum_six_atoms (fun atomIndex =>
        (chartPointOfDesign crux.design).weight atomIndex
          * frame.tightDir (frame.basisLabel 2) atomIndex ^ 2)
      hne0102 hne0103 hne0112 hne0113 hne0123 hne0203 hne0212 hne0213
      hne0223 hne0312 hne0313 hne0323 hne1213 hne1223 hne1323] at hread
    rw [hz2e01, hz2e03, hz2e13] at hread
    rw [hread]
    ring
  have hdiag3 : (basisGram frame.tightDir frame.basisLabel * frame.coeff) 3 3
      = chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight e03 * b03 ^ 2
        + (chartPointOfDesign crux.design).weight e13 * b13 ^ 2
        + (chartPointOfDesign crux.design).weight e23 * b23 ^ 2 := by
    have hread := gram_exchange_diag_read frame.hdata frame.basisLabel
      frame.hrepresentation (frame.hmemAll 3)
    rw [sum_six_atoms (fun atomIndex =>
        (chartPointOfDesign crux.design).weight atomIndex
          * frame.tightDir (frame.basisLabel 3) atomIndex ^ 2)
      hne0102 hne0103 hne0112 hne0113 hne0123 hne0203 hne0212 hne0213
      hne0223 hne0312 hne0313 hne0323 hne1213 hne1223 hne1323] at hread
    rw [hz3e01, hz3e02, hz3e12] at hread
    rw [hread]
    ring
  -- the weight sum in edge order
  have hwsum : (chartPointOfDesign crux.design).weight e01
      + (chartPointOfDesign crux.design).weight e02
      + (chartPointOfDesign crux.design).weight e03
      + (chartPointOfDesign crux.design).weight e12
      + (chartPointOfDesign crux.design).weight e13
      + (chartPointOfDesign crux.design).weight e23 = 1 := by
    have hsum := frame.hdata.weight_sum_one
    rw [sum_six_atoms (chartPointOfDesign crux.design).weight
      hne0102 hne0103 hne0112 hne0113 hne0123 hne0203 hne0212 hne0213
      hne0223 hne0312 hne0313 hne0323 hne1213 hne1223 hne1323] at hsum
    exact hsum
  -- the trace
  have htrace : frame.coeff 0 0 + frame.coeff 1 1 + frame.coeff 2 2
      + frame.coeff 3 3 = 2 := by
    have htr := frame.htrace
    rw [trace_eq_four_diag (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (1 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 3)
      (by decide : (2 : Fin 4) ≠ 3)] at htr
    exact htr
  -- feed the certificate
  exact hcert (chartObjective (chartPointOfDesign crux.design))
    ((chartPointOfDesign crux.design).weight e01)
    ((chartPointOfDesign crux.design).weight e02)
    ((chartPointOfDesign crux.design).weight e03)
    ((chartPointOfDesign crux.design).weight e12)
    ((chartPointOfDesign crux.design).weight e13)
    ((chartPointOfDesign crux.design).weight e23)
    a01 b01 a02 b02 a03 b03 a12 b12 a13 b13 a23 b23
    frame.coeff (basisGram frame.tightDir frame.basisLabel)
    frame.hvalueNeg
    (frame.hdata.weight_pos e01) (frame.hdata.weight_pos e02)
    (frame.hdata.weight_pos e03) (frame.hdata.weight_pos e12)
    (frame.hdata.weight_pos e13) (frame.hdata.weight_pos e23)
    hwsum frame.hidempotent htrace
    hr01a hr01b hr02a hr02b hr03a hr03b
    hr12a hr12b hr13a hr13b hr23a hr23b
    hnorm0 hnorm1 hnorm2 hnorm3
    hΓlit hsym hdiag0 hdiag1 hdiag2 hdiag3
    (mem_datumTightSupport.mp hm01L) (mem_datumTightSupport.mp hm01R)
    (mem_datumTightSupport.mp hm02L) (mem_datumTightSupport.mp hm02R)
    (mem_datumTightSupport.mp hm03L) (mem_datumTightSupport.mp hm03R)
    (mem_datumTightSupport.mp hm12L) (mem_datumTightSupport.mp hm12R)
    (mem_datumTightSupport.mp hm13L) (mem_datumTightSupport.mp hm13R)
    (mem_datumTightSupport.mp hm23L) (mem_datumTightSupport.mp hm23R)

end Gtz
