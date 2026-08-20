import Gtz.Wave.CornerSignWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The opposite-horn count: two bases of a corner always disagree

The landed `Gtz.corner_signWord_dichotomy` spends the sign coupling only when
ALL THREE inside bases are coherent.  This module shows that TWO coherent
bases already exhaust the coupling, and reads off the count the opposite horn
needs.

The mechanism is the same squeeze, applied one factor earlier.  At an outside
atom the three base products multiply to minus a square
(`Gtz.atomBracket_baseProduct_cycle`) and the three inside pairings multiply to
a nonnegative number (`Gtz.corner_inside_tripleProduct_nonneg`).  Coherence at
two bases forces those two factors of the product nonnegative, so the third
factor — the free base — is forced STRICTLY NEGATIVE at every
bracket-generic atom:

  `Gtz.corner_twoCoherent_atom_disagree` :
    `P_yz · ([xyd]·[xzd]) < 0`  for every outside `d` with `[xyd][xzd][yzd] ≠ 0`.

But the corner transport (`Gtz.corner_compl_bracket_transport`) sums exactly
those products against positive weights to `P_yz` itself.  Weighting the
pointwise sign by `P_yz` makes every term of a sum with total `P_yz² > 0`
nonpositive:

  `Gtz.corner_twoCoherent_exists_coplanar` :
    two coherent bases force SOME outside atom coplanar with an inside pair.

Contrapositive, at a corner all of whose outside atoms are bracket-generic:

  `Gtz.corner_generic_two_oppositePairs` :
    AT LEAST TWO of the three inside bases carry an opposite-sign pair,

and hence, through the landed floor,

  `Gtz.corner_two_informative_bracket_floors` :
    TWO DISTINCT inside bases each carry an informative triple of strictly
    positive squared bracket.

This doubles the bracket demand of the opposite horn: the landed headline
`Gtz.corner_informative_bracket_floor` produced one such triple, and one is
what the complex corner-tie witness supplies.  The count is sharp — a corner
with exactly one coherent base exists — so the horn splits into the
all-three-disagree stratum and the one-coherent-base stratum, and no further
sign law can close the gap.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The base triple product under a relabelling -/

/-- Swapping the base with its first companion negates the triple product of
anchored brackets. -/
theorem atomBracket_tripleProduct_swapLeft (D : WeightedDesign m 3) (x y z d : Fin m) :
    atomBracket D y x d * atomBracket D y z d * atomBracket D x z d
      = -(atomBracket D x y d * atomBracket D x z d * atomBracket D y z d) := by
  simp only [atomBracket]
  rw [tripleBracket_swapLeft (D.atom y) (D.atom x) (D.atom d)]
  ring

/-- Cycling the base to the third companion fixes the triple product of
anchored brackets. -/
theorem atomBracket_tripleProduct_cycle (D : WeightedDesign m 3) (x y z d : Fin m) :
    atomBracket D z x d * atomBracket D z y d * atomBracket D x y d
      = atomBracket D x y d * atomBracket D x z d * atomBracket D y z d := by
  simp only [atomBracket]
  rw [tripleBracket_swapLeft (D.atom z) (D.atom x) (D.atom d),
    tripleBracket_swapLeft (D.atom z) (D.atom y) (D.atom d)]
  ring

/-! ## 2. Two coherent bases force the third base to disagree -/

/-- **THE DISAGREEMENT LAW.**  At a corank-two corner with nondegenerate inside
pairings, coherence of the two bases `y` and `z` forces the free base `x` to
read every bracket-generic outside atom AGAINST its own pairing:

  `P_yz · ([xyd]·[xzd]) < 0` .

The three inside pairings multiply to a positive number, the three base
products at the atom multiply to minus a square, and the two coherent bases
contribute nonnegative factors — so the free factor carries the whole sign. -/
theorem corner_twoCoherent_atom_disagree (D : WeightedDesign m 3) (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d'))
    {d : Fin m} (hd : d ∈ Cᶜ)
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    atomPairing D y z * (atomBracket D x y d * atomBracket D x z d) < 0 := by
  have hcard : C.card = 3 := by rw [hC]; exact card_triple_eq hxy hxz hyz
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have hCy : C = ({y, x, z} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : C = ({z, x, y} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have htY := corner_compl_bracket_transport D C hlam hunit hgap hCy
    (Ne.symm hxy) hyz hxz
  have htZ := corner_compl_bracket_transport D C hlam hunit hgap hCz
    (Ne.symm hxz) (Ne.symm hyz) hxy
  have hw : ∀ a ∈ Cᶜ, 0 < D.weight a := fun a _ => D.weight_pos a
  have hsY := sum_sign_forced_of_pairwise_nonneg hw hbaseY htY hPxz d hd
  have hsZ := sum_sign_forced_of_pairwise_nonneg hw hbaseZ htZ hPxy d hd
  have hP := corner_inside_tripleProduct_nonneg D C hcard hlam hunit hgap
    hx hy hz hxy hxz hyz
  have hPne : atomPairing D x y * atomPairing D x z * atomPairing D y z ≠ 0 :=
    mul_ne_zero (mul_ne_zero hPxy hPxz) hPyz
  have hPpos : 0 < atomPairing D x y * atomPairing D x z * atomPairing D y z :=
    lt_of_le_of_ne hP (Ne.symm hPne)
  have hTsq : 0 < (atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d) ^ 2 := by
    rcases lt_or_gt_of_ne hT with h | h
    · nlinarith
    · nlinarith
  have hBC : 0 ≤ (atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
      * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)) :=
    mul_nonneg hsY hsZ
  have hprod : (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
      * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
        * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)))
      = -((atomPairing D x y * atomPairing D x z * atomPairing D y z)
        * (atomBracket D x y d * atomBracket D x z d
          * atomBracket D y z d) ^ 2) := by
    have hcyc := atomBracket_baseProduct_cycle D x y z d
    linear_combination (atomPairing D x y * atomPairing D x z
      * atomPairing D y z) * hcyc
  have hneg : (atomPairing D y z * (atomBracket D x y d * atomBracket D x z d))
      * ((atomPairing D x z * (atomBracket D y x d * atomBracket D y z d))
        * (atomPairing D x y * (atomBracket D z x d * atomBracket D z y d)))
      < 0 := by
    rw [hprod]
    nlinarith [hPpos, hTsq]
  by_contra hge
  push Not at hge
  exact absurd (mul_nonneg hge hBC) (not_le.mpr hneg)

/-- **TWO COHERENT BASES FORCE A COPLANARITY.**  If two inside bases of a
corank-two corner see no opposite-sign pair among the outside mixed minors,
then some outside atom is coplanar with an inside pair.

The disagreement law makes every bracket-generic outside atom contribute a
strictly negative term to the corner transport read against its own pairing,
while the transport totals the square of that pairing. -/
theorem corner_twoCoherent_exists_coplanar (D : WeightedDesign m 3)
    (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hbaseY : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D y x d * atomBracket D y z d)
        * (atomBracket D y x d' * atomBracket D y z d'))
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d')) :
    ∃ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d = 0 := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ d ∈ Cᶜ, atomPairing D y z * (D.weight d
      * (atomBracket D x y d * atomBracket D x z d)) ≤ 0 := by
    intro d hd
    have hdis := corner_twoCoherent_atom_disagree D C hlam hunit hgap hC
      hxy hxz hyz hPyz hPxz hPxy hbaseY hbaseZ hd (hcon d hd)
    have hwpos := D.weight_pos d
    nlinarith [hdis, hwpos]
  have hsum0 : ∑ d ∈ Cᶜ, atomPairing D y z * (D.weight d
      * (atomBracket D x y d * atomBracket D x z d)) ≤ 0 :=
    Finset.sum_nonpos hall
  have htX := corner_compl_bracket_transport D C hlam hunit hgap hC hxy hxz hyz
  have hsumeq : ∑ d ∈ Cᶜ, atomPairing D y z * (D.weight d
      * (atomBracket D x y d * atomBracket D x z d))
      = atomPairing D y z ^ 2 := by
    rw [← Finset.mul_sum, htX]
    ring
  rw [hsumeq] at hsum0
  have hpos : 0 < atomPairing D y z ^ 2 := by
    rcases lt_or_gt_of_ne hPyz with h | h
    · nlinarith
    · nlinarith
  linarith

/-! ## 3. The count: two bases of a generic corner disagree -/

/-- **THE OPPOSITE-HORN COUNT.**  At a corank-two corner with nondegenerate
inside pairings all of whose outside atoms are bracket-generic, AT LEAST TWO of
the three inside bases carry an opposite-sign pair of outside mixed minors.

The landed dichotomy produced one such base.  Two coherent bases are already
impossible, so at most one base is coherent. -/
theorem corner_generic_two_oppositePairs (D : WeightedDesign m 3)
    (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0) :
    ((∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D x y d * atomBracket D x z d)
          * (atomBracket D x y d' * atomBracket D x z d') < 0)
        ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d') < 0))
      ∨ ((∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D x y d * atomBracket D x z d)
          * (atomBracket D x y d' * atomBracket D x z d') < 0)
        ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D z x d * atomBracket D z y d)
          * (atomBracket D z x d' * atomBracket D z y d') < 0))
      ∨ ((∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d') < 0)
        ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, (atomBracket D z x d * atomBracket D z y d)
          * (atomBracket D z x d' * atomBracket D z y d') < 0)) := by
  classical
  have hCy : C = ({y, x, z} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hCz : C = ({z, x, y} : Finset (Fin m)) := by
    rw [hC]; ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  by_cases hA : ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
      (atomBracket D x y d * atomBracket D x z d)
        * (atomBracket D x y d' * atomBracket D x z d') < 0
  · by_cases hB : ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
        (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d') < 0
    · exact Or.inl ⟨hA, hB⟩
    · by_cases hZ : ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
          (atomBracket D z x d * atomBracket D z y d)
            * (atomBracket D z x d' * atomBracket D z y d') < 0
      · exact Or.inr (Or.inl ⟨hA, hZ⟩)
      · exfalso
        push Not at hB hZ
        obtain ⟨d, hd, hzero⟩ := corner_twoCoherent_exists_coplanar D C hlam
          hunit hgap hC hxy hxz hyz hPyz hPxz hPxy hB hZ
        exact hgen d hd hzero
  · by_cases hB : ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
        (atomBracket D y x d * atomBracket D y z d)
          * (atomBracket D y x d' * atomBracket D y z d') < 0
    · by_cases hZ : ∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ,
          (atomBracket D z x d * atomBracket D z y d)
            * (atomBracket D z x d' * atomBracket D z y d') < 0
      · exact Or.inr (Or.inr ⟨hB, hZ⟩)
      · exfalso
        push Not at hA hZ
        -- bases `x` and `z` are coherent: the free base is `y`
        have hZ' : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
            0 ≤ (atomBracket D z y d * atomBracket D z x d)
              * (atomBracket D z y d' * atomBracket D z x d') := by
          intro d hd d' hd'
          have h := hZ d hd d' hd'
          have hEq : (atomBracket D z y d * atomBracket D z x d)
              * (atomBracket D z y d' * atomBracket D z x d')
              = (atomBracket D z x d * atomBracket D z y d)
                * (atomBracket D z x d' * atomBracket D z y d') := by ring
          rw [hEq]
          exact h
        obtain ⟨d, hd, hzero⟩ := corner_twoCoherent_exists_coplanar D C hlam
          hunit hgap hCy (Ne.symm hxy) hyz hxz hPxz hPyz
          (by rw [atomPairing_comm]; exact hPxy) hA hZ'
        refine hgen d hd ?_
        have hsw := atomBracket_tripleProduct_swapLeft D x y z d
        linarith [hsw, hzero]
    · exfalso
      push Not at hA hB
      -- bases `x` and `y` are coherent: the free base is `z`
      have hA' : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
          0 ≤ (atomBracket D x z d * atomBracket D x y d)
            * (atomBracket D x z d' * atomBracket D x y d') := by
        intro d hd d' hd'
        have h := hA d hd d' hd'
        have hEq : (atomBracket D x z d * atomBracket D x y d)
            * (atomBracket D x z d' * atomBracket D x y d')
            = (atomBracket D x y d * atomBracket D x z d)
              * (atomBracket D x y d' * atomBracket D x z d') := by ring
        rw [hEq]
        exact h
      have hB' : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
          0 ≤ (atomBracket D y z d * atomBracket D y x d)
            * (atomBracket D y z d' * atomBracket D y x d') := by
        intro d hd d' hd'
        have h := hB d hd d' hd'
        have hEq : (atomBracket D y z d * atomBracket D y x d)
            * (atomBracket D y z d' * atomBracket D y x d')
            = (atomBracket D y x d * atomBracket D y z d)
              * (atomBracket D y x d' * atomBracket D y z d') := by ring
        rw [hEq]
        exact h
      obtain ⟨d, hd, hzero⟩ := corner_twoCoherent_exists_coplanar D C hlam
        hunit hgap hCz (Ne.symm hxz) (Ne.symm hyz) hxy hPxy
        (by rw [atomPairing_comm]; exact hPyz)
        (by rw [atomPairing_comm]; exact hPxz) hA' hB'
      refine hgen d hd ?_
      have hcy := atomBracket_tripleProduct_cycle D x y z d
      linarith [hcy, hzero]

/-! ## 4. The headline: two informative triples -/

/-- **TWO INFORMATIVE BRACKET FLOORS.**  A corank-two corner with nondegenerate
inside pairings and bracket-generic outside atoms carries TWO informative
triples at two DISTINCT inside bases, each of strictly positive squared
bracket.

The landed `Gtz.corner_informative_bracket_floor` produced one, which is what
the complex corner-tie witness supplies at its two floor-respecting bases; the
count law produces a second at a different base. -/
theorem corner_two_informative_bracket_floors (D : WeightedDesign m 3)
    (C : Finset (Fin m))
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x y z : Fin m} (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hPyz : atomPairing D y z ≠ 0) (hPxz : atomPairing D x z ≠ 0)
    (hPxy : atomPairing D x y ≠ 0)
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0) :
    ∃ e ∈ C, ∃ e' ∈ C, e ≠ e'
      ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, d ≠ d' ∧ 0 < (1 + lam) * atomBracket D e d d' ^ 2)
      ∧ (∃ d ∈ Cᶜ, ∃ d' ∈ Cᶜ, d ≠ d'
          ∧ 0 < (1 + lam) * atomBracket D e' d d' ^ 2) := by
  have hx : x ∈ C := by rw [hC]; simp
  have hy : y ∈ C := by rw [hC]; simp
  have hz : z ∈ C := by rw [hC]; simp
  have hgapX : subsetSum D ({x, y, z} : Finset (Fin m)) - 1
      = lam • atomMatrix u := by rw [← hC]; exact hgap
  have hgapY : subsetSum D ({y, x, z} : Finset (Fin m)) - 1
      = lam • atomMatrix u := by
    rw [show ({y, x, z} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgapX
  have hgapZ : subsetSum D ({z, x, y} : Finset (Fin m)) - 1
      = lam • atomMatrix u := by
    rw [show ({z, x, y} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
    exact hgapX
  rcases corner_generic_two_oppositePairs D C hlam hunit hgap hC hxy hxz hyz
      hPyz hPxz hPxy hgen with
    ⟨⟨d1, hd1, d1', hd1', hs1⟩, ⟨d2, hd2, d2', hd2', hs2⟩⟩
    | ⟨⟨d1, hd1, d1', hd1', hs1⟩, ⟨d2, hd2, d2', hd2', hs2⟩⟩
    | ⟨⟨d1, hd1, d1', hd1', hs1⟩, ⟨d2, hd2, d2', hd2', hs2⟩⟩
  · exact ⟨x, hx, y, hy, hxy,
      ⟨d1, hd1, d1', hd1', corner_oppositePair_ne hs1,
        corner_oppositePair_bracket_pos D hxy hxz hyz hlam hunit hgapX hs1⟩,
      ⟨d2, hd2, d2', hd2', corner_oppositePair_ne hs2,
        corner_oppositePair_bracket_pos D (Ne.symm hxy) hyz hxz hlam hunit
          hgapY hs2⟩⟩
  · exact ⟨x, hx, z, hz, hxz,
      ⟨d1, hd1, d1', hd1', corner_oppositePair_ne hs1,
        corner_oppositePair_bracket_pos D hxy hxz hyz hlam hunit hgapX hs1⟩,
      ⟨d2, hd2, d2', hd2', corner_oppositePair_ne hs2,
        corner_oppositePair_bracket_pos D (Ne.symm hxz) (Ne.symm hyz) hxy hlam
          hunit hgapZ hs2⟩⟩
  · exact ⟨y, hy, z, hz, hyz,
      ⟨d1, hd1, d1', hd1', corner_oppositePair_ne hs1,
        corner_oppositePair_bracket_pos D (Ne.symm hxy) hyz hxz hlam hunit
          hgapY hs1⟩,
      ⟨d2, hd2, d2', hd2', corner_oppositePair_ne hs2,
        corner_oppositePair_bracket_pos D (Ne.symm hxz) (Ne.symm hyz) hxy hlam
          hunit hgapZ hs2⟩⟩

end Gtz
