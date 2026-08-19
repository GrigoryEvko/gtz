import Gtz.Wave.CornerSignWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The coplanar matching of a sign-coherent corner

`Gtz.corner_signWord_dichotomy` leaves a corank-two corner two ways to exist:
some inside base carries an opposite-sign pair of outside mixed minors, or
every outside atom is coplanar with an inside pair.  This module works out the
structure of the second horn.

## The matching

On the coherent horn the three corner transports still carry the three nonzero
inside pairings, so each transport owns a nonzero term, and the dichotomy
prunes that term's atom to ONE vanishing bracket.  The result is a system of
three DISTINCT outside atoms, one per inside plane
(`Gtz.corner_matching_of_signCoherent`).  At size six the complement has
exactly three atoms, the matching is perfect, and each transport collapses to
a single term: the co-weighted mixed minor of the matched atom EQUALS the
opposite inside pairing, exactly (`Gtz.corner_matching_quantization`).  No
primitivity is consumed anywhere in the matching.

## The partition

Primitivity enters one level deeper: an outside atom coplanar with TWO inside
pairs is parallel to the shared inside atom.  The Grassmann expansion
`(a × b) × (a × c) = [a b c] · a` (`Gtz.bracketNormal_crossPair`) plus the
double expansion `a × (b × c) = (a·c) b − (a·b) c`
(`Gtz.bracketNormal_triple_expansion`) reduce double coplanarity to a
vanishing cross product, and a vanishing cross product to a parallel pair
(`Gtz.not_double_coplanar_of_primitive`).  So at a primitive corner the
coplanarity classes are disjoint and the matching is a partition.

## Where this points

The complex corner-tie witness satisfies the opposite-sign horn, not the
coherent one, so the coherent horn is invisible to it: every law here is a
theorem about the REAL corner's degenerate stratum.  A closing certificate for
the corner now has two named fronts: beat the opposite-sign floor at every
base against the ten refusals, or beat the quantized matching — three exact
pairing equations on a measure-zero stratum — against the same refusals.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The two Grassmann expansions -/

/-- **The cross of two crosses with a shared base.**  `(a × b) × (a × c) =
[a b c] · a`: the intersection line of two planes through a common vector is
that vector, weighted by the bracket. -/
theorem bracketNormal_crossPair (baseVec firstVec secondVec : Fin 3 → ℝ) :
    bracketNormal (bracketNormal baseVec firstVec) (bracketNormal baseVec secondVec)
      = tripleBracket baseVec firstVec secondVec • baseVec := by
  funext coord
  fin_cases coord <;>
    simp only [bracketNormal, tripleBracket_eq, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

/-- **The Grassmann double expansion.**  `a × (b × c) = (a·c) b − (a·b) c`. -/
theorem bracketNormal_triple_expansion (aVec bVec cVec : Fin 3 → ℝ) :
    bracketNormal aVec (bracketNormal bVec cVec)
      = (aVec ⬝ᵥ cVec) • bVec - (aVec ⬝ᵥ bVec) • cVec := by
  funext coord
  fin_cases coord <;>
    simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

/-! ## 2. Double coplanarity forces a parallel pair -/

/-- **Two coplanarities pin the atom to the shared line.**  An atom whose
bracket vanishes against two pairs with a common base atom, the base triple
spanning, is parallel to the base atom — or zero.  At a primitive design both
are impossible. -/
theorem not_double_coplanar_of_primitive (D : WeightedDesign m 3)
    (hprim : IsPrimitiveDesign D) {x y z dLbl : Fin m} (hdx : dLbl ≠ x)
    (hbase : atomBracket D x y z ≠ 0)
    (hcopXY : atomBracket D x y dLbl = 0) (hcopXZ : atomBracket D x z dLbl = 0) :
    False := by
  have hd1 : D.atom dLbl ⬝ᵥ bracketNormal (D.atom x) (D.atom y) = 0 := by
    rw [dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
    simpa only [atomBracket] using hcopXY
  have hd2 : D.atom dLbl ⬝ᵥ bracketNormal (D.atom x) (D.atom z) = 0 := by
    rw [dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
    simpa only [atomBracket] using hcopXZ
  have hexp := bracketNormal_triple_expansion (D.atom dLbl)
    (bracketNormal (D.atom x) (D.atom y)) (bracketNormal (D.atom x) (D.atom z))
  rw [hd1, hd2, zero_smul, zero_smul, sub_zero] at hexp
  rw [bracketNormal_crossPair, bracketNormal_smul_right] at hexp
  have hcross : bracketNormal (D.atom dLbl) (D.atom x) = 0 := by
    rcases smul_eq_zero.mp hexp with h | h
    · exact absurd h (by simpa only [atomBracket] using hbase)
    · exact h
  have hdt := bracketNormal_double_turn (D.atom dLbl) (D.atom x)
  rw [hcross, bracketNormal_zero_right, eq_comm, sub_eq_zero] at hdt
  by_cases hz : D.atom dLbl ⬝ᵥ D.atom dLbl = 0
  · exact hprim x dLbl 0 (Ne.symm hdx)
      (by rw [dotProduct_self_eq_zero.mp hz, zero_smul])
  · refine hprim dLbl x
      ((D.atom dLbl ⬝ᵥ D.atom x) / (D.atom dLbl ⬝ᵥ D.atom dLbl)) hdx ?_
    calc D.atom x
        = (D.atom dLbl ⬝ᵥ D.atom dLbl)⁻¹ • ((D.atom dLbl ⬝ᵥ D.atom dLbl) • D.atom x) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = (D.atom dLbl ⬝ᵥ D.atom dLbl)⁻¹ • ((D.atom dLbl ⬝ᵥ D.atom x) • D.atom dLbl) := by
          rw [hdt]
      _ = ((D.atom dLbl ⬝ᵥ D.atom x) / (D.atom dLbl ⬝ᵥ D.atom dLbl)) • D.atom dLbl := by
          rw [smul_smul, div_eq_inv_mul]

/-! ## 3. The matching -/

/-- **THE COPLANAR MATCHING.**  On the sign-coherent horn each corner transport
still carries its nonzero pairing, so each inside plane owns an outside atom:
three distinct outside atoms, the first coplanar with `{y,z}`, the second with
`{x,z}`, the third with `{x,y}`, each with its own two base brackets nonzero.
No primitivity and no size hypothesis is consumed. -/
theorem corner_matching_of_signCoherent (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseX : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) :
    ∃ dyz ∈ Cᶜ, ∃ dxz ∈ Cᶜ, ∃ dxy ∈ Cᶜ,
      dyz ≠ dxz ∧ dyz ≠ dxy ∧ dxz ≠ dxy
      ∧ atomBracket D y z dyz = 0
        ∧ atomBracket D x y dyz ≠ 0 ∧ atomBracket D x z dyz ≠ 0
      ∧ atomBracket D x z dxz = 0
        ∧ atomBracket D x y dxz ≠ 0 ∧ atomBracket D y z dxz ≠ 0
      ∧ atomBracket D x y dxy = 0
        ∧ atomBracket D x z dxy ≠ 0 ∧ atomBracket D y z dxy ≠ 0 := by
  have hCy : C = ({y, x, z} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : C = ({z, x, y} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have htX := corner_compl_bracket_transport D C hlam hunit hgap hC hxy hxz hyz
  have htY := corner_compl_bracket_transport D C hlam hunit hgap hCy
    (Ne.symm hxy) hyz hxz
  have htZ := corner_compl_bracket_transport D C hlam hunit hgap hCz
    (Ne.symm hxz) (Ne.symm hyz) hxy
  have hdich : ∀ d ∈ Cᶜ,
      atomBracket D x y d * atomBracket D x z d * atomBracket D y z d = 0 :=
    fun d hd => corner_signWord_dichotomy D C hlam hunit hgap hC hxy hxz hyz
      hPyz hPxz hPxy hbaseX hbaseY hbaseZ hd
  have hwX : ∃ d ∈ Cᶜ, D.weight d * (atomBracket D x y d * atomBracket D x z d) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at htX
    exact hPyz htX.symm
  have hwY : ∃ d ∈ Cᶜ, D.weight d * (atomBracket D y x d * atomBracket D y z d) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at htY
    exact hPxz htY.symm
  have hwZ : ∃ d ∈ Cᶜ, D.weight d * (atomBracket D z x d * atomBracket D z y d) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at htZ
    exact hPxy htZ.symm
  obtain ⟨dyz, hdyzMem, hdyzNe⟩ := hwX
  obtain ⟨dxz, hdxzMem, hdxzNe⟩ := hwY
  obtain ⟨dxy, hdxyMem, hdxyNe⟩ := hwZ
  have hMdyz : atomBracket D x y dyz ≠ 0 ∧ atomBracket D x z dyz ≠ 0 := by
    have hne := right_ne_zero_of_mul hdyzNe
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  have hMdxz : atomBracket D y x dxz ≠ 0 ∧ atomBracket D y z dxz ≠ 0 := by
    have hne := right_ne_zero_of_mul hdxzNe
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  have hMdxy : atomBracket D z x dxy ≠ 0 ∧ atomBracket D z y dxy ≠ 0 := by
    have hne := right_ne_zero_of_mul hdxyNe
    exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩
  have hswapYX : ∀ dLbl : Fin m, atomBracket D y x dLbl = -atomBracket D x y dLbl := by
    intro dLbl
    simp only [atomBracket]
    exact tripleBracket_swapLeft _ _ _
  have hswapZX : ∀ dLbl : Fin m, atomBracket D z x dLbl = -atomBracket D x z dLbl := by
    intro dLbl
    simp only [atomBracket]
    exact tripleBracket_swapLeft _ _ _
  have hswapZY : ∀ dLbl : Fin m, atomBracket D z y dLbl = -atomBracket D y z dLbl := by
    intro dLbl
    simp only [atomBracket]
    exact tripleBracket_swapLeft _ _ _
  have hzeroYZ : atomBracket D y z dyz = 0 := by
    have h := hdich dyz hdyzMem
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hMdyz.1
      · exact absurd h'' hMdyz.2
    · exact h'
  have hzeroXZ : atomBracket D x z dxz = 0 := by
    have h := hdich dxz hdxzMem
    have hxyNe : atomBracket D x y dxz ≠ 0 := by
      intro h'
      exact hMdxz.1 (by rw [hswapYX, h', neg_zero])
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hxyNe
      · exact h''
    · exact absurd h' hMdxz.2
  have hzeroXY : atomBracket D x y dxy = 0 := by
    have h := hdich dxy hdxyMem
    have hxzNe : atomBracket D x z dxy ≠ 0 := by
      intro h'
      exact hMdxy.1 (by rw [hswapZX, h', neg_zero])
    have hyzNe : atomBracket D y z dxy ≠ 0 := by
      intro h'
      exact hMdxy.2 (by rw [hswapZY, h', neg_zero])
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' hxzNe
    · exact absurd h' hyzNe
  have hxyNeDxz : atomBracket D x y dxz ≠ 0 := by
    intro h'
    exact hMdxz.1 (by rw [hswapYX, h', neg_zero])
  have hxzNeDxy : atomBracket D x z dxy ≠ 0 := by
    intro h'
    exact hMdxy.1 (by rw [hswapZX, h', neg_zero])
  have hyzNeDxy : atomBracket D y z dxy ≠ 0 := by
    intro h'
    exact hMdxy.2 (by rw [hswapZY, h', neg_zero])
  refine ⟨dyz, hdyzMem, dxz, hdxzMem, dxy, hdxyMem, ?_, ?_, ?_,
    hzeroYZ, hMdyz.1, hMdyz.2, hzeroXZ, hxyNeDxz, hMdxz.2,
    hzeroXY, hxzNeDxy, hyzNeDxy⟩
  · intro h
    rw [h] at hzeroYZ
    exact hMdxz.2 hzeroYZ
  · intro h
    rw [h] at hzeroYZ
    exact hyzNeDxy hzeroYZ
  · intro h
    rw [h] at hzeroXZ
    exact hxzNeDxy hzeroXZ

/-! ## 4. The quantization at size six -/

/-- **THE MATCHING QUANTIZATION.**  At size six the coherent horn's matching is
perfect and each corner transport collapses to its single matched term: the
co-weighted mixed minor of each matched outside atom EQUALS the opposite
inside pairing, exactly.  Three equations, one per inside plane, on the
degenerate stratum a closing certificate must still empty. -/
theorem corner_matching_quantization (D : WeightedDesign 6 3) (C : Finset (Fin 6))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin 6} (hC : C = ({x, y, z} : Finset (Fin 6)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseX : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) :
    ∃ dyz ∈ Cᶜ, ∃ dxz ∈ Cᶜ, ∃ dxy ∈ Cᶜ,
      dyz ≠ dxz ∧ dyz ≠ dxy ∧ dxz ≠ dxy
      ∧ Cᶜ = ({dyz, dxz, dxy} : Finset (Fin 6))
      ∧ atomBracket D y z dyz = 0 ∧ atomBracket D x z dxz = 0
        ∧ atomBracket D x y dxy = 0
      ∧ D.weight dyz * (atomBracket D x y dyz * atomBracket D x z dyz)
          = atomPairing D y z
      ∧ D.weight dxz * (atomBracket D y x dxz * atomBracket D y z dxz)
          = atomPairing D x z
      ∧ D.weight dxy * (atomBracket D z x dxy * atomBracket D z y dxy)
          = atomPairing D x y := by
  obtain ⟨dyz, hdyzMem, dxz, hdxzMem, dxy, hdxyMem, hne12, hne13, hne23,
    hzYZ, hnYZ1, hnYZ2, hzXZ, hnXZ1, hnXZ2, hzXY, hnXY1, hnXY2⟩ :=
    corner_matching_of_signCoherent D C hlam hunit hgap hC hxy hxz hyz
      hPyz hPxz hPxy hbaseX hbaseY hbaseZ
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hcompl : (Cᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  have hsubset : ({dyz, dxz, dxy} : Finset (Fin 6)) ⊆ Cᶜ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h | h
    · exact h ▸ hdyzMem
    · rcases Finset.mem_insert.mp h with h' | h'
      · exact h' ▸ hdxzMem
      · exact (Finset.mem_singleton.mp h') ▸ hdxyMem
  have hcompl_eq : (Cᶜ : Finset (Fin 6)) = ({dyz, dxz, dxy} : Finset (Fin 6)) := by
    refine (Finset.eq_of_subset_of_card_le hsubset ?_).symm
    rw [hcompl, card_triple_eq hne12 hne13 hne23]
  have hCy : C = ({y, x, z} : Finset (Fin 6)) := by
    rw [hC]
    exact Finset.insert_comm x y {z}
  have hCz : C = ({z, x, y} : Finset (Fin 6)) := by
    rw [hC, Finset.pair_comm y z]
    exact Finset.insert_comm x z {y}
  have hswapYX : atomBracket D y x dxy = -atomBracket D x y dxy := by
    simp only [atomBracket]; exact tripleBracket_swapLeft _ _ _
  have hswapZX : atomBracket D z x dxz = -atomBracket D x z dxz := by
    simp only [atomBracket]; exact tripleBracket_swapLeft _ _ _
  have hswapZY : atomBracket D z y dyz = -atomBracket D y z dyz := by
    simp only [atomBracket]; exact tripleBracket_swapLeft _ _ _
  have htX := corner_compl_bracket_transport D C hlam hunit hgap hC hxy hxz hyz
  have htY := corner_compl_bracket_transport D C hlam hunit hgap hCy
    (Ne.symm hxy) hyz hxz
  have htZ := corner_compl_bracket_transport D C hlam hunit hgap hCz
    (Ne.symm hxz) (Ne.symm hyz) hxy
  rw [hcompl_eq, sum_triple_eq hne12 hne13 hne23] at htX htY htZ
  refine ⟨dyz, hdyzMem, dxz, hdxzMem, dxy, hdxyMem, hne12, hne13, hne23,
    hcompl_eq, hzYZ, hzXZ, hzXY, ?_, ?_, ?_⟩
  · rw [← htX, hzXZ, hzXY]
    ring
  · rw [← htY, hzYZ, hswapYX, hzXY]
    ring
  · rw [← htZ, hswapZX, hzXZ, hswapZY, hzYZ]
    ring

/-! ## 5. The size marker: the coherent horn is empty at size five -/

/-- **THE COHERENT HORN NEEDS THREE OUTSIDE ATOMS.**  At size five the
complement of a corner has two atoms, and the matching demands three distinct
ones: a `(5,3)` corank-two corner with nondegenerate pairings always carries an
opposite-sign pair.  This is where the sign-word chain consumes `6 = 3 + 3` —
the complement must be exactly as large as the set of inside planes. -/
theorem corner_signCoherent_absurd_fiveThree (D : WeightedDesign 5 3)
    (C : Finset (Fin 5)) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin 5} (hC : C = ({x, y, z} : Finset (Fin 5)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseX : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d'))
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) :
    False := by
  obtain ⟨d1, hd1, d2, hd2, d3, hd3, h12, h13, h23, -⟩ :=
    corner_matching_of_signCoherent D C hlam hunit hgap hC hxy hxz hyz
      hPyz hPxz hPxy hbaseX hbaseY hbaseZ
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hcompl : (Cᶜ : Finset (Fin 5)).card = 2 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  have hsub : ({d1, d2, d3} : Finset (Fin 5)) ⊆ Cᶜ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with h | h
    · exact h ▸ hd1
    · rcases Finset.mem_insert.mp h with h' | h'
      · exact h' ▸ hd2
      · exact (Finset.mem_singleton.mp h') ▸ hd3
  have hle : ({d1, d2, d3} : Finset (Fin 5)).card ≤ 2 := by
    rw [← hcompl]
    exact Finset.card_le_card hsub
  rw [card_triple_eq h12 h13 h23] at hle
  omega

end Gtz
