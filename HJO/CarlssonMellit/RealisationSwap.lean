/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PartialCharacter
public import HJO.CarlssonMellit.PDeltaDiagonal
public meta import HJO.Attr

/-! # The realisation intertwines the two interchanges of auxiliary variables

There are two interchanges of `y_i` and `y_{i+1}` in the Carlsson--Mellit layer, on the two sides of
the realisation: `s_i` of `HJO.Sweep.swapAux`, a `Λ`-algebra automorphism of the sweep's total
space, and `ŝ_i` of `HJO.Sym.pswap`, which moves the coefficients of a power series in the alphabet.
This file proves that `ι_k` carries the first to the second on `V_k`:
`ι_k(s_i(G)) = ŝ_i(ι_k(G))`.

## Main results

* `HJO.Dyck.realise_rename_swap`: the statement for an arbitrary pair of auxiliary variables, with
  the interchange written as the renaming it is and the coefficients kept polynomial.
* `HJO.Dyck.realise_swapAux`: the same for the adjacent pair `y_i, y_{i+1}`, i.e. for the
  interchange `s_i`, still with polynomial coefficients.
* `HJO.Dyck.auxToFrac_realise_swapAux`: `HJO.Dyck.realise_swapAux`, read in `P°_k`:
  `ι_k(s_i(G)) = ŝ_i(ι_k(G))`.

## Implementation notes

*The proof is the uniqueness of `ι_k`, not a generator induction.* The direct proof compares the
two `𝕜`-algebra homomorphisms `ι_k ∘ s_i` and `ŝ_i ∘ ι_k` on the generators
`y_1, …, y_k, p_1, p_2, …` of `V_k`. That comparison is exactly what
`HJO.Dyck.eq_of_isAuxRealisation` already performs, once the two sides are arranged into a map that
is itself a realisation with auxiliary variables. Neither composite is: `ι_k ∘ s_i` sends `y_i` to
`y_{i+1}` instead of fixing it. But the *conjugate* `HJO.Dyck.conjSwapRealise`, `ŝ_i ∘ ι_k ∘ s_i`,
is — the two interchanges cancel on each `y_l`, and both fix the power sums, whose coefficients are
`0` and `1`. So it agrees with `ι_k` on `V_k`, and applying `ŝ_i` once more to that identity — an
involution — gives the lemma. Nothing here re-derives the generator induction, which lives in
`HJO.Dyck.eq_of_isAuxRealisation`.

*The content is the polynomial-coefficient statement.* `ι_k` lands in `P_k`, whose coefficients are
`𝕂[y_1, …, y_k]`, while `ŝ_i` is an automorphism of `P°_k`, whose coefficients are the fractions.
The interchange of the polynomial coefficients is `HJO.Sym.swapAuxHom`, and
`HJO.Sym.auxToFrac_map_swapAuxHom` — proved for `HJO.Sym.map_numerator_eq_zero` and reused here
rather than re-derived — says that pushing it through the inclusion `HJO.Sym.auxToFrac` is `ŝ_i`.
So `HJO.Dyck.auxToFrac_realise_swapAux` is one rewriting away from
`HJO.Dyck.realise_swapAux`, and the latter is the sharper statement: `auxToFrac` is injective.

*The membership `G ∈ V_k` cannot be dropped.* Off `V_k` the predicate
`HJO.Dyck.IsAuxRealisation` says nothing about the auxiliary variables `y_l` for `l > k`, and
`HJO.Dyck.auxRealise` in fact sends them to `0`; there `s_i` still moves them and the identity
fails. The hypothesis is the membership `G ∈ V_k` itself.

*Index conventions.* The one-based `y_i` for `i ≥ 1` is `MvPolynomial.X (i - 1)` on the sweep side
(`HJO.Sweep.auxVar`) and `MvPolynomial.X (i - 1 : Fin k)` in the coefficients, so the interchange
`s_i` is `HJO.Sweep.swapAux K ((i' : ℕ) + 1)` and its `ŝ_i` is `HJO.Sym.pswap K i' j'` with
`i' = i - 1` and `(j' : ℕ) = (i' : ℕ) + 1`. Both are taken here at an arbitrary pair, the adjacency
entering only through the hypothesis relating the two indices.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4.
-/

@[expose] public section

namespace HJO.Dyck

variable {K : Type*} [CommRing K] {k : ℕ}

/-! ### The transposition read on the two index types -/

/-- The transposition of two auxiliary variables does not depend on whether it is read on `Fin k` or
on the underlying naturals: the auxiliary variables below the level are indexed by `Fin k` in the
coefficients of `P_k` and by `ℕ` in the sweep's total space, and this is the compatibility of the
two readings. -/
theorem val_swap_val (i j l : Fin k) :
    Equiv.swap (i : ℕ) (j : ℕ) (l : ℕ) = ((Equiv.swap i j l : Fin k) : ℕ) := by
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hlj : l = j
    · subst hlj
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj,
        Equiv.swap_apply_of_ne_of_ne (fun h => hli (Fin.val_injective h))
          (fun h => hlj (Fin.val_injective h))]

/-- The coefficientwise interchange of two auxiliary variables is an involution on `P_k`: the
transposition is one. -/
theorem map_swapAuxHom_map_swapAuxHom (i j : Fin k) (F : Sym.AuxAlphabetSeries K k) :
    MvPowerSeries.map (Sym.swapAuxHom K i j) (MvPowerSeries.map (Sym.swapAuxHom K i j) F) = F :=
  MvPowerSeries.ext fun e => by
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, Sym.swapAuxHom_apply,
      Sym.swapAuxHom_apply, MvPolynomial.rename_rename]
    rw [show ((Equiv.swap i j) ∘ (Equiv.swap i j) : Fin k → Fin k) = id from
      funext fun l => Equiv.swap_apply_self i j l, MvPolynomial.rename_id, AlgHom.id_apply]

/-! ### The conjugate of a realisation by the two interchanges -/

/-- The conjugate `ŝ_i ∘ ι_k ∘ s_i` of a realisation with auxiliary variables by the two
interchanges of `y_i` and `y_j`, with the interchange of the coefficients read on the polynomials.
It is again a realisation, by `HJO.Dyck.isAuxRealisation_conjSwapRealise`, which is the whole proof
of `HJO.Dyck.realise_swapAux`: neither factor is one by itself. -/
noncomputable def conjSwapRealise (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k)
    (i j : Fin k) : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k :=
  (MvPowerSeries.mapAlgHom (MvPolynomial.rename (Equiv.swap i j))).comp
    (ι.comp ((MvPolynomial.rename (Equiv.swap (i : ℕ) (j : ℕ)) :
      Sweep.Total K →ₐ[Sym.Lambda K] Sweep.Total K).restrictScalars K))

theorem conjSwapRealise_apply (ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k) (i j : Fin k)
    (G : Sweep.Total K) :
    conjSwapRealise ι i j G = MvPowerSeries.map (Sym.swapAuxHom K i j)
      (ι (MvPolynomial.rename (Equiv.swap (i : ℕ) (j : ℕ)) G)) :=
  rfl

/-- **The conjugate of `ι_k` by the two interchanges is again a realisation with auxiliary
variables.** On the power sums, which `s_i` fixes — they are constants of the total space — the
coefficients are the constants `0` and `1` of `𝕂[y_1, …, y_k]`, which the interchange of the
coefficients fixes too. On the auxiliary variable `y_{l+1}` the two interchanges cancel:
`s_i` renames the index `l` to `Equiv.swap i j l`, `ι_k` carries the result to the corresponding
coefficient variable, and `ŝ_i` renames that index back. -/
theorem isAuxRealisation_conjSwapRealise
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k} (hι : IsAuxRealisation k ι)
    (i j : Fin k) : IsAuxRealisation k (conjSwapRealise ι i j) where
  coeff_pow r m := by
    rw [conjSwapRealise_apply, MvPowerSeries.coeff_map, MvPolynomial.rename_C, hι.coeff_pow r m,
      map_one]
  coeff_of_ne r d hd := by
    rw [conjSwapRealise_apply, MvPowerSeries.coeff_map, MvPolynomial.rename_C,
      hι.coeff_of_ne r d hd, map_zero]
  map_auxVar l := by
    rw [conjSwapRealise_apply, Sweep.auxVar, Nat.add_sub_cancel, MvPolynomial.rename_X,
      val_swap_val,
      show (MvPolynomial.X ((Equiv.swap i j l : Fin k) : ℕ) : Sweep.Total K)
          = Sweep.auxVar (((Equiv.swap i j l : Fin k) : ℕ) + 1) by
        rw [Sweep.auxVar, Nat.add_sub_cancel],
      hι.map_auxVar (Equiv.swap i j l), MvPowerSeries.map_C, Sym.swapAuxHom_apply,
      MvPolynomial.rename_X, Equiv.swap_apply_self]

/-! ### The realisation intertwines the two interchanges -/

/-- **The realisation intertwines the two interchanges of auxiliary variables**, for an arbitrary
pair: on `V_k`, renaming the two auxiliary variables of the sweep's total space into each other and
then realising is realising and then interchanging the two variables in the coefficients.

The conjugate `HJO.Dyck.conjSwapRealise` of `ι_k` by the two interchanges is again a realisation, so
it agrees with `ι_k` on `V_k` by `HJO.Dyck.eq_of_isAuxRealisation`; applying the coefficientwise
interchange, an involution, to that identity gives the claim. -/
theorem realise_rename_swap {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (hι : IsAuxRealisation k ι) (i j : Fin k) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    ι (MvPolynomial.rename (Equiv.swap (i : ℕ) (j : ℕ)) G)
      = MvPowerSeries.map (Sym.swapAuxHom K i j) (ι G) := by
  have h := eq_of_isAuxRealisation (isAuxRealisation_conjSwapRealise hι i j) hι hG
  rw [conjSwapRealise_apply] at h
  rw [← h, map_swapAuxHom_map_swapAuxHom]

/-- **The realisation intertwines the two interchanges**, at the adjacent pair: for
`G ∈ V_k`, `ι_k(s_i(G))` is `ι_k(G)` with `y_i` and `y_{i+1}` interchanged in the coefficients.

This is `HJO.Dyck.realise_swapAux` with the coefficients kept polynomial, which is the sharper
statement — `HJO.Sym.auxToFrac` is injective — and `HJO.Dyck.auxToFrac_realise_swapAux` is the
statement read in `P°_k`. -/
@[hjo "lem_cm_realisation_swap"]
theorem realise_swapAux {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (hι : IsAuxRealisation k ι) (i j : Fin k) (hj : (j : ℕ) = (i : ℕ) + 1)
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    ι (Sweep.swapAux K ((i : ℕ) + 1) G) = MvPowerSeries.map (Sym.swapAuxHom K i j) (ι G) := by
  rw [← realise_rename_swap hι i j hG]
  congr 1
  rw [Sweep.swapAux, hj]
  simp only [MvPolynomial.renameEquiv_apply, Nat.add_sub_cancel]

/-- **The realisation intertwines the two interchanges**, as in
`HJO.Dyck.realise_swapAux`: for `k ≥ 2`, `1 ≤ i ≤ k-1` and `G ∈ V_k`,

`ι_k(s_i(G)) = ŝ_i(ι_k(G))`

inside `P°_k`, where the containment `P_k ⊆ P°_k` is the coefficientwise inclusion
`HJO.Sym.auxToFrac`. The content is `HJO.Dyck.realise_swapAux`; the passage to `P°_k` is
`HJO.Sym.auxToFrac_map_swapAuxHom`, which identifies the coefficientwise interchange of the
polynomials with `ŝ_i`. -/
@[hjo "lem_cm_realisation_swap"]
theorem auxToFrac_realise_swapAux {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k}
    (hι : IsAuxRealisation k ι) (i j : Fin k) (hj : (j : ℕ) = (i : ℕ) + 1)
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k) :
    Sym.auxToFrac K k (ι (Sweep.swapAux K ((i : ℕ) + 1) G))
      = Sym.pswap K i j (Sym.auxToFrac K k (ι G)) := by
  rw [realise_swapAux hι i j hj hG, Sym.auxToFrac_map_swapAuxHom]

end HJO.Dyck
