import Gtz.Wave.OppositeHornSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The coherent base sits on the small branch

The count law `Gtz.corner_generic_two_oppositePairs` is SHARP: a corank-two
corner may carry exactly one coherent base, and the census puts that stratum at
about one corner in eight.  This module pins what the coherent base does with
its bracket budget, and the answer is the sharpest real-only statement the horn
owns.

At a coherent base no pair of outside mixed minors disagrees, so — once the
outside atoms are bracket-generic, which makes every mixed minor nonzero —
EVERY pair at that base is a strict SAME-SIGN pair
(`corner_coherentBase_pair_same_sign`).  The two-point form of
`Gtz.OppositeHornSplit` then fires on the other branch at all three pairs:

  `(1+λ)·[z d d']² = (|[zxd][zyd']| − |[zxd'][zyd]|)²`
    (`corner_coherentBase_bracket_difference`)

the DIFFERENCE of the two cross magnitudes, not the sum.  So the coherent base
is pinned to the small branch of the two-point set at every one of its pairs,
while its bracket budget `A_xz·A_yz − e_xe_y` is fixed by the corner scalars
(`Gtz.corner_informative_bracket_budget_closed`).  An opposite base, by
contrast, is pinned to the LARGE branch at its two opposite pairs, where the
landed floor `4|M_d||M_{d'}|` applies.

That is the exact shape of the residual: the horn splits into the stratum where
all three bases sit on the large branch, and the stratum where one base is
forced onto the small branch at every pair.  Over `ℂ` neither branch is forced —
the bracket may take any value between them — which is why the complex
corner-tie witness escapes every law that only reads magnitudes.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- A bracket-generic outside atom has a nonzero mixed minor at the third
base. -/
theorem corner_generic_baseZ_minor_ne_zero (D : WeightedDesign m 3)
    {x y z d : Fin m}
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    atomBracket D z x d * atomBracket D z y d ≠ 0 := by
  intro hzero
  refine hT ?_
  have hzx := atomBracket_swapLeft_neg D x z d
  have hzy := atomBracket_swapLeft_neg D y z d
  rw [hzx, hzy] at hzero
  have hxz : atomBracket D x z d * atomBracket D y z d = 0 := by
    linear_combination hzero
  rcases mul_eq_zero.mp hxz with h | h
  · rw [h]; ring
  · rw [h]; ring

/-- **THE COHERENT BASE HAS ONLY SAME-SIGN PAIRS.**  Coherence gives a
nonnegative product, and bracket-genericity makes both factors nonzero, so the
product is strictly positive at every pair. -/
theorem corner_coherentBase_pair_same_sign (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {x y z : Fin m}
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d'))
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    0 < (atomBracket D z x d * atomBracket D z y d)
      * (atomBracket D z x d' * atomBracket D z y d') := by
  have hnn := hbaseZ d hd d' hd'
  have h1 : atomBracket D z x d * atomBracket D z y d ≠ 0 :=
    corner_generic_baseZ_minor_ne_zero D (hgen d hd)
  have h2 : atomBracket D z x d' * atomBracket D z y d' ≠ 0 :=
    corner_generic_baseZ_minor_ne_zero D (hgen d' hd')
  exact lt_of_le_of_ne hnn (Ne.symm (mul_ne_zero h1 h2))

/-- **THE COHERENT BASE IS ON THE SMALL BRANCH.**  Every informative bracket of
a coherent base is the DIFFERENCE of its two cross magnitudes, at every pair of
outside atoms.  The opposite bases are on the sum branch at their opposite
pairs, where the landed floor applies. -/
theorem corner_coherentBase_bracket_difference (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {x y z : Fin m}
    (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hbaseZ : ∀ d ∈ Cᶜ, ∀ d' ∈ Cᶜ,
      0 ≤ (atomBracket D z x d * atomBracket D z y d)
        * (atomBracket D z x d' * atomBracket D z y d'))
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    (1 + lam) * atomBracket D z d d' ^ 2
      = (|atomBracket D z x d * atomBracket D z y d'|
        - |atomBracket D z x d' * atomBracket D z y d|) ^ 2 := by
  have hsign := corner_coherentBase_pair_same_sign D C hbaseZ hgen hd hd'
  have hgapZ : subsetSum D ({z, x, y} : Finset (Fin m)) - 1
      = lam • atomMatrix u := by
    rw [show ({z, x, y} : Finset (Fin m)) = ({x, y, z} : Finset (Fin m)) from by
      ext a; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto, ← hC]
    exact hgap
  exact corner_samePair_bracket_exact D (Ne.symm hxz) (Ne.symm hyz) hxy hlam
    hunit hgapZ hsign

end Gtz
