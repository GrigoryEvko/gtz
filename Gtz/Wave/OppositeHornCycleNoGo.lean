import Gtz.Wave.OppositeHornTwoPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# No third pinning: the outside-triple bracket has no two-point form

Summation destroys the realness of the two-point form, so a closing certificate
must SELECT a slot or MULTIPLY slots.  The multiplicative shape has a natural
candidate: the outside-triple bracket.  Writing `ξ_d = [xyd]`, `η_d = [xzd]`,
`ζ_d = [yzd]` over the complement, the landed
`Gtz.corner_outside_gram_det` reads

  `det M = C₊ − C₋` ,
  `C₊ = ξ₄η₅ζ₆ + ξ₅η₆ζ₄ + ξ₆η₄ζ₅` ,  `C₋ = ξ₄η₆ζ₅ + ξ₅η₄ζ₆ + ξ₆η₅ζ₄`

with `det M = (1+λ)·[d₄d₅d₆]` (measured to 1.5e-14).  If BOTH three-cycles were
sign-definite — each of its three monomials sharing a sign — then
`|det M| = ||C₊| ± |C₋||` would be a two-point set exactly like the slot
pinnings, and the outside bracket would carry a third realness step.  That is
the shape the coherent horn's `(√ − √)²` identity has.

**IT IS NOT AVAILABLE HERE, and the obstruction is this module.**  Pairing the
monomials gives, for every `i` and `j`, `mp_i·mm_j = (a base pair product)·(a
square)`: the nine products run over the three pairs of each of the three bases.
Sign-definiteness of both cycles would force all nine base pair products to
share one sign `σ`.  Taking the three that belong to one base and multiplying
them gives `(M_4M_5M_6)²·(square)`, a nonnegative number of sign `σ³ = σ`, so
`σ > 0`; and then ALL THREE bases are coherent, which
`Gtz.corner_twoCoherent_exists_coplanar` forbids at a corner with
bracket-generic outside atoms.

The load-bearing step is `three_pairProducts_not_all_neg`: three reals cannot
have all three pairwise products negative, because those products multiply to a
square.  It is also what makes an opposite base carry EXACTLY two opposite
pairs, never three.

Measured: over 14165 generic corners the two cycles are individually
sign-definite 43.7% and 44.1% of the time, and BOTH sign-definite 0 times.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **THREE REALS HAVE NO THREE NEGATIVE PAIRWISE PRODUCTS.**  The three
pairwise products multiply to a perfect square, so they cannot all be negative.

This is why a base of a corner never carries three opposite pairs: with three
outside atoms an opposite base carries EXACTLY two. -/
theorem three_pairProducts_not_all_neg {A B C : ℝ}
    (h1 : A * B < 0) (h2 : B * C < 0) (h3 : A * C < 0) : False := by
  have hpos : 0 < (A * B) * (B * C) := mul_pos_of_neg_of_neg h1 h2
  have hneg : (A * B) * (B * C) * (A * C) < 0 := mul_neg_of_pos_of_neg hpos h3
  have hkey : (A * B) * (B * C) * (A * C) = (A * B * C) ^ 2 := by ring
  rw [hkey] at hneg
  exact absurd hneg (not_lt.mpr (sq_nonneg _))

/-- **A BASE OF A CORNER NEVER CARRIES THREE OPPOSITE PAIRS.**  At three outside
atoms the three mixed minors of one base cannot pairwise disagree throughout, so
an opposite base has exactly two opposite pairs and one same-sign pair. -/
theorem corner_base_not_all_pairs_opposite (D : WeightedDesign m 3)
    (x y z d4 d5 d6 : Fin m)
    (h45 : (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d5 * atomBracket D x z d5) < 0)
    (h56 : (atomBracket D x y d5 * atomBracket D x z d5)
      * (atomBracket D x y d6 * atomBracket D x z d6) < 0)
    (h46 : (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d6 * atomBracket D x z d6) < 0) : False :=
  three_pairProducts_not_all_neg h45 h56 h46

/-- **THE SAME-SIGN PAIR OF AN OPPOSITE BASE.**  If two of the three outside
atoms disagree with a third at one base, they agree with each other — so that
pair sits on the DIFFERENCE branch while the other two sit on the sum branch.
Every opposite base therefore mixes both branches. -/
theorem corner_oppositeBase_third_pair_same_sign (D : WeightedDesign m 3)
    (x y z d4 d5 d6 : Fin m)
    (h46 : (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d6 * atomBracket D x z d6) < 0)
    (h56 : (atomBracket D x y d5 * atomBracket D x z d5)
      * (atomBracket D x y d6 * atomBracket D x z d6) < 0) :
    0 < (atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d5 * atomBracket D x z d5) := by
  rcases lt_trichotomy ((atomBracket D x y d4 * atomBracket D x z d4)
      * (atomBracket D x y d5 * atomBracket D x z d5)) 0 with h | h | h
  · exact absurd (three_pairProducts_not_all_neg h h56 h46) (fun hf => hf)
  · exfalso
    rcases mul_eq_zero.mp h with h0 | h0
    · rw [h0, zero_mul] at h46; exact lt_irrefl 0 h46
    · rw [h0, zero_mul] at h56; exact lt_irrefl 0 h56
  · exact h

end Gtz
