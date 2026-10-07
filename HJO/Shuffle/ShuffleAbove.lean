/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.HalfTurnIdes
public import HJO.Shuffle.ShuffleNarrowed
public meta import HJO.Attr

/-! # The below-diagonal shuffle identity from the above-diagonal one

`HJO.External.Shuffle` follows axiom-clean from `HJO.ShuffleNarrowed` by
`HJO.shuffle_of_narrowed`, so `ShuffleNarrowed` is the whole shuffle side of this library.
What Mellit's paper actually supplies is the *above-diagonal* form: Mellit's Section 6 sums over the
above-diagonal parking functions of return composition `α`, with the above-diagonal area, dinv and
inverse descent set. This file is the derivation of the one from the other.

Both quoted inputs are isolated as predicates, in the style of `HJO.Sym.RaiseStableKernel`:

* `HJO.ShuffleAbove` — the above-diagonal identity, `HJO.shuffleAbove`, which is
  Mellit Section 6 and the genuinely deep content.
* `HJO.GesselReverseSum` — `HJO.gessel_reverse_sum`: a fundamental expansion of a
  realised symmetric function stays an expansion of it after every descent set is reflected. It
  follows from the letter reversal (`HJO.ParkingFunctions.letterReverse_gessel`,
  `HJO.Sym.letterReverse_realisation`, `HJO.Sym.ext_letterTrunc`), and it is carried here as a
  hypothesis rather than silently assumed.

`HJO.shuffleNarrowed_of_above` derives `ShuffleNarrowed` from those two. It is conditional on the
two predicates; `HJO.shuffleAbove` and `HJO.gessel_reverse_sum` are the theorems asserting them
outright.

## The derivation

Reindex the finite above-diagonal sum along the half turn
(`HJO.ParkingFunctions.halfTurnPfEquiv`), which matches `PF^{α^rev}` with `PF̂^{α}` — the
*reversal* of the composition is forced here, by `HJO.Paths.hasAboveReturns_halfTurn`, and is not
an adjustment made to fit later uses. The three data in the summand transport by
`HJO.Paths.aboveArea_halfTurn`, `HJO.ParkingFunctions.aboveDinv_halfTurnPf` and
`HJO.ParkingFunctions.aboveIdes_halfTurnPf`; the last of these *complements* the inverse descent
set, and `GesselReverseSum` together with
`HJO.ParkingFunctions.descentReverse_descentReverse` is what undoes the complementation.

## References

This file concerns `HJO.shuffleAbove` and `HJO.External.Shuffle`. The above-diagonal identity is
Section 6 of A. Mellit, *Toric braids and `(m, n)`-parking functions*.
-/

@[expose] public section

open Finset

namespace HJO

open ParkingFunctions Paths

/-! ### The two quoted inputs -/

/-- **BGLX and Mellit, compositional rational shuffle above the diagonal.** This is
`HJO.shuffleAbove`: in any realisation the shuffle element `(-1)^{N(b+1)} Θ(C_α 1) 1` expands
over the *above-diagonal* parking functions of return composition `α` as
`∑ q^{dinv̂(π̂)} u^{âea(P̂_π̂)} F_{bN, ideŝ(π̂)}`. This is the genuinely deep content of the shuffle
side — Mellit, `Toric braids and (m,n)-parking functions`, Section 6 — and it is stated here with
exactly the hypotheses `ShuffleNarrowed` carries, so that the two are comparable clause by
clause. -/
def ShuffleAbove (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → 1 < a → a < b →
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] →
      ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
        ∀ Θ : Sym.Lambda L →ₐ[L] Module.End L (Sym.Lambda L), Sym.IsSlopeHom a b q u Θ →
          ∀ N : ℕ, 0 < N → ∀ α : List ℕ, (∀ x ∈ α, 0 < x) → α.sum = N →
            (-1 : L) ^ (N * (b + 1)) • ι (Θ (Sym.CopComp q α 1) 1) =
              ∑ π ∈ aboveWithReturns α a b N,
                (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) • gessel L (b * N) (aboveIdes π)

/-- **Complementing the descent sets of a symmetric expansion.** This is
`HJO.gessel_reverse_sum`: if a realisation `ι` sends `f` to a combination of degree-`n` Gessel
fundamentals whose descent sets lie in the window `{1, …, n-1}`, then it also sends `f` to the
combination with every descent set reflected. Reversing the first `m` letters of the alphabet fixes
`ι f` and exchanges `F_{n,S}` with the truncation of `F_{n,S^{∨n}}`, so the two combinations have
equal truncations for every `m`, and truncations separate.

The statement rests on the letter reversal (`HJO.ParkingFunctions.letterReverse_gessel`,
`HJO.Sym.letterReverse_realisation`); here it is carried as a hypothesis rather than assumed
silently. -/
def GesselReverseSum (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ (ι : Sym.Lambda L →ₐ[L] Sym.AlphabetSeries L), Sym.IsRealisation ι →
    ∀ (n : ℕ) (I : Type) (s : Finset I) (w : I → L) (S : I → Finset ℕ),
      (∀ i ∈ s, S i ⊆ Ico 1 n) → ∀ f : Sym.Lambda L,
        ι f = ∑ i ∈ s, w i • gessel L n (S i) →
          ι f = ∑ i ∈ s, w i • gessel L n (descentReverse n (S i))

/-! ### The half turn of the sum -/

/-- The above-diagonal sum, reindexed along the half turn. The index set becomes the
below-diagonal parking functions of the **reversed** composition, the area and the dinv become the
below-diagonal ones, and the inverse descent set becomes its reflection `ides(π)^{∨bN}`. -/
theorem sum_aboveWithReturns_eq {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ} (ha : 0 < a)
    (hN : 0 < N) (q u : L) (α : List ℕ) :
    ∑ π ∈ aboveWithReturns α a b N,
        (q ^ aboveDinv π * u ^ aboveArea (abovePath π)) • gessel L (b * N) (aboveIdes π)
      = ∑ π ∈ withReturns α.reverse a b N, (q ^ dinv π * u ^ area (path π)) •
          gessel L (b * N) (descentReverse (b * N) (ides π)) := by
  refine (Finset.sum_equiv halfTurnPfEquiv (fun π => ?_) (fun π _ => ?_)).symm
  · exact (mem_aboveWithReturns_halfTurnPf α π).symm
  · change (q ^ dinv π * u ^ area (path π)) • gessel L (b * N) (descentReverse (b * N) (ides π))
      = (q ^ aboveDinv (halfTurnPf π) * u ^ aboveArea (abovePath (halfTurnPf π))) •
          gessel L (b * N) (aboveIdes (halfTurnPf π))
    rw [aboveDinv_halfTurnPf ha hN, abovePath_halfTurnPf, aboveArea_halfTurn,
      aboveIdes_halfTurnPf ha hN]

/-! ### The derivation -/

/-- **The below-diagonal shuffle identity from the above-diagonal one.** `ShuffleNarrowed` follows
from `ShuffleAbove` together with the Gessel reversal, and from nothing else: reindex the finite sum
along the half turn — which forces the composition to be reversed — and then undo the
complementation of the inverse descent sets with `GesselReverseSum` and
`HJO.ParkingFunctions.descentReverse_descentReverse`.

Composed with `HJO.shuffle_of_narrowed`, this reduces the whole shuffle side of the library to
`ShuffleAbove` and `GesselReverseSum`. -/
theorem shuffleNarrowed_of_above {L : Type*} [Field L] [Algebra ℚ L]
    (hrev : GesselReverseSum L) (h : ShuffleAbove L) : ShuffleNarrowed L := by
  intro a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN
  have ha' : 0 < a := by omega
  have hS : ∀ π ∈ withReturns α.reverse a b N,
      descentReverse (b * N) (ides π) ⊆ Ico 1 (b * N) :=
    fun π _ => descentReverse_subset_Ico (ides_subset π)
  have hf : ι ((-1 : L) ^ (N * (b + 1)) • Θ (Sym.CopComp q α 1) 1)
      = ∑ π ∈ withReturns α.reverse a b N, (q ^ dinv π * u ^ area (path π)) •
          gessel L (b * N) (descentReverse (b * N) (ides π)) := by
    rw [map_smul, h a b hab ha hb q u hqu ι hι Θ hΘ N hN α hαpos hαN]
    exact sum_aboveWithReturns_eq ha' hN q u α
  have hres := hrev ι hι (b * N) (ParkingFunction a b N) (withReturns α.reverse a b N)
    (fun π => q ^ dinv π * u ^ area (path π))
    (fun π => descentReverse (b * N) (ides π)) hS _ hf
  rw [map_smul] at hres
  rw [hres]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [descentReverse_descentReverse ((ides_subset π).trans Finset.Ico_subset_Iic_self)]

/-- **The whole shuffle side of the library, reduced to the two quoted inputs.** Composing the
derivation above with `HJO.shuffle_of_narrowed`, the two-clause assumption `HJO.External.Shuffle`
follows from `ShuffleAbove` and `GesselReverseSum` alone. -/
theorem shuffle_of_above {L : Type*} [Field L] [Algebra ℚ L] (hrev : GesselReverseSum L)
    (h : ShuffleAbove L) : HJO.External.Shuffle L :=
  shuffle_of_narrowed (shuffleNarrowed_of_above hrev h)

end HJO
