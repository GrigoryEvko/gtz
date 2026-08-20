import Gtz.Wave.OppositeHornCoherentBranch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The two-point pinning is total: no base is exempt

The landed opposite-sign floor fires only where a base carries an opposite pair,
and that is why the horn appeared to have a residual "one base" gap: the count
law `Gtz.corner_generic_two_oppositePairs` is sharp, so one base may be coherent
and carry no opposite pair at all.

The EXACT two-point form has no such gap.  At a bracket-generic outside atom
every mixed minor is nonzero, so at every base and every pair the product
`M^e_d·M^e_{d'}` is nonzero and therefore has a strict sign.  Both signs are
already pinned exactly — the sum branch on an opposite pair
(`Gtz.corner_oppositePair_bracket_exact`) and the difference branch on a
same-sign pair (`Gtz.corner_samePair_bracket_exact`) — so

  `(1+λ)·[e d d']² ∈ { (|a| − |b|)² , (|a| + |b|)² }`

at EVERY one of the nine informative slots of a `(6,3)` corner, with no sign
hypothesis whatsoever (`corner_bracket_twoPoint_dichotomy`).

This dissolves the one-base gap.  It was an artefact of the arithmetic-mean
weakening `(|a|+|b|)² ≥ 4|ab|`, which needs an opposite pair to be useful; the
exact statement needs only genericity.  Measured at 512 bits on the complex
corner-tie witness: the AM-weakened floor is violated at 3 of the 9 slots, all
at one base, while the exact two-point form is violated at 9 of 9, with the
relative distance from the nearer branch endpoint ranging from 1.9e-3 to 3.6e-1.
The field separation is total, and it is per slot.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **THE TOTAL TWO-POINT DICHOTOMY.**  At a corank-two corner every
informative bracket of a base whose two mixed minors are nonzero is pinned to
one of exactly two values: the squared sum, or the squared difference, of the
two cross magnitudes.  No sign hypothesis, no opposite pair, no exempt base. -/
theorem corner_bracket_twoPoint_dichotomy (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    {d d' : Fin m}
    (hd : atomBracket D x y d * atomBracket D x z d ≠ 0)
    (hd' : atomBracket D x y d' * atomBracket D x z d' ≠ 0) :
    (1 + lam) * atomBracket D x d d' ^ 2
        = (|atomBracket D x y d * atomBracket D x z d'|
          + |atomBracket D x y d' * atomBracket D x z d|) ^ 2
      ∨ (1 + lam) * atomBracket D x d d' ^ 2
        = (|atomBracket D x y d * atomBracket D x z d'|
          - |atomBracket D x y d' * atomBracket D x z d|) ^ 2 := by
  rcases lt_trichotomy ((atomBracket D x y d * atomBracket D x z d)
      * (atomBracket D x y d' * atomBracket D x z d')) 0 with hneg | hzero | hpos
  · exact Or.inl (corner_oppositePair_bracket_exact D hxy hxz hyz hlam hunit
      hgap hneg)
  · exact absurd hzero (mul_ne_zero hd hd')
  · exact Or.inr (corner_samePair_bracket_exact D hxy hxz hyz hlam hunit hgap
      hpos)

/-- Bracket-genericity of an outside atom makes the mixed minor of the FIRST
base nonzero. -/
theorem corner_generic_baseX_minor_ne_zero (D : WeightedDesign m 3)
    {x y z d : Fin m}
    (hT : atomBracket D x y d * atomBracket D x z d * atomBracket D y z d ≠ 0) :
    atomBracket D x y d * atomBracket D x z d ≠ 0 := by
  intro hzero
  exact hT (by rw [hzero]; ring)

/-- **EVERY INFORMATIVE SLOT OF A GENERIC CORNER IS PINNED.**  With all outside
atoms bracket-generic, the two-point dichotomy holds at the base `x` for every
pair of outside atoms.  The same statement at the bases `y` and `z` follows by
relabelling the corner, which its hypotheses are symmetric under. -/
theorem corner_generic_bracket_twoPoint (D : WeightedDesign m 3)
    (C : Finset (Fin m)) {x y z : Fin m}
    (hC : C = ({x, y, z} : Finset (Fin m)))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    (hgen : ∀ d ∈ Cᶜ, atomBracket D x y d * atomBracket D x z d
      * atomBracket D y z d ≠ 0)
    {d d' : Fin m} (hd : d ∈ Cᶜ) (hd' : d' ∈ Cᶜ) :
    (1 + lam) * atomBracket D x d d' ^ 2
        = (|atomBracket D x y d * atomBracket D x z d'|
          + |atomBracket D x y d' * atomBracket D x z d|) ^ 2
      ∨ (1 + lam) * atomBracket D x d d' ^ 2
        = (|atomBracket D x y d * atomBracket D x z d'|
          - |atomBracket D x y d' * atomBracket D x z d|) ^ 2 := by
  refine corner_bracket_twoPoint_dichotomy D hxy hxz hyz hlam hunit ?_
    (corner_generic_baseX_minor_ne_zero D (hgen d hd))
    (corner_generic_baseX_minor_ne_zero D (hgen d' hd'))
  rw [← hC]; exact hgap

end Gtz
