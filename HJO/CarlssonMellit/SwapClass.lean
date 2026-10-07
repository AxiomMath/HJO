/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.LabelSum
public import HJO.CarlssonMellit.PDelta
public meta import HJO.Attr

/-! # The swapping operator on one class sum

The swapping proposition `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` says
`χ'_{τ_m σ}(π) = Δ_m(χ'_σ(π))`, and its proof has two halves: what `Δ_m` does to the sum over *one*
class, and the passage from the classes to the whole series. This file is the first half, which is
where all the mathematics is.

Let `π ∈ 𝔻_{k,N}`, let `σ` have pairwise distinct entries with `σ a = m` and `σ b = m + 1` for
`a < b` — the hypothesis `σ⁻¹(m) < σ⁻¹(m+1)` — and let `w ∈ U(π,σ)`. By
`HJO.Dyck.finsum_labelClass` the sum over `K_m(π,σ,w)` is

`q^e · g · a_m(l_1, ε_1) · ∏_{t=2}^{r}(a_m(l_t,0) + a_m(l_t,1))`,

and the sum over `K_m(π,τ_mσ,τ_mw)` is the same expression with `ε_1` flipped: the relabelling moves
neither the two-letter support, nor the letters off it, hence neither `e`, nor `g`, nor the runs —
only the letter at the support's first position, which is `m` for `w` (that is what
`σ⁻¹(m) < σ⁻¹(m+1)` buys) and `m + 1` for `τ_m w`. Everything but `a_m(l_1, ε_1)` is fixed by
`ŝ_m`, so `HJO.Sym.pdelta_mul_of_pswap_eq` pulls it out of `Δ_m` and `HJO.Sym.pdelta_runWeight`
flips the remaining factor.

## Main results

* `HJO.Sym.pswap_auxToFrac_zvar_of_ne`: `ŝ_i` fixes a merged variable other than the two it swaps.
* `HJO.Dyck.sortNth_one_eq_of_special`: the first position of the support is the position of `m`.
* `HJO.Dyck.pdelta_auxToFrac_finsum_labelClass`: `Δ_m` carries the class sum of `w` for `σ` to the
  class sum of `τ_m w` for `τ_m σ`.

## Implementation notes

*This is not `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`.* What it leaves out is the
passage from the classes to the series: `χ'_σ(π)` is defined one coefficient at a time
(`HJO.Dyck.unnormalisedCharSeries`), and each coefficient is a *finite* sum over the no-attack
labellings with a prescribed alphabet exponent. Because `m + 1 < k` here — the stated `1 ≤ m ≤ k-1`
— the two letters lie below the level and so contribute nothing to that exponent, which means every
class is entirely inside or entirely outside each of those finite index sets; the remaining work is
therefore to group such a finite sum into classes, apply the lemma below to each, and observe that
`τ_m` matches the classes on the two sides. The grouping key that does it is
`i ↦ if i ∈ S_m(w) then m else w i`, which determines the class exactly (a position is in the
support precisely when the key is `m` there) and which the relabelling `τ_m` leaves alone.

*`Δ_m` acts on `P°_k`, not on `P_k`*, so the statement is about the images of the two class sums
under the containment `HJO.Sym.auxToFrac`, as every statement about `Δ_m` in this library is.

*The hypotheses are weaker than those of the full swapping proposition.*
`HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple` asks `σ` to list `{1, …, k}` without
repetition; what the argument uses is that `σ` is injective and that `m` and `m + 1` occur among its
entries, at positions `a < b`. `k ≥ 2` and `1 ≤ m ≤ k-1` are carried by the existence of
`i j : Fin k` with `(i : ℕ) = m` and `(j : ℕ) = m + 1`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-- The containment `P_k ⊆ P°_k` fixes a letter of the alphabet. -/
@[simp]
theorem auxToFrac_X (k l : ℕ) :
    auxToFrac K k (MvPowerSeries.X l) = MvPowerSeries.X l := by
  rw [auxToFrac]
  simp [MvPowerSeries.mapAlgHom]

/-- At or above the level, the containment `P_k ⊆ P°_k` carries a merged variable to the letter of
the alphabet it is. -/
theorem auxToFrac_zvar_of_le {k l : ℕ} (h : k ≤ l) :
    auxToFrac K k (zvar K k l) = MvPowerSeries.X (l - k) := by
  rw [zvar_of_le h, auxToFrac_X]

/-- **The interchange `ŝ_i` fixes a merged variable other than the two it swaps**: a merged variable
is either an auxiliary variable `y_l`, and then `l` is neither of the two indices, or a letter of
the alphabet, which `ŝ_i` does not touch. -/
theorem pswap_auxToFrac_zvar_of_ne {k l : ℕ} {i j : Fin k} (hi : l ≠ (i : ℕ)) (hj : l ≠ (j : ℕ)) :
    pswap K i j (auxToFrac K k (zvar K k l)) = auxToFrac K k (zvar K k l) := by
  by_cases h : l < k
  · rw [auxToFrac_zvar_of_lt h]
    exact pswap_C_yFrac_of_ne (fun hc => hi (by rw [← hc])) (fun hc => hj (by rw [← hc]))
  · rw [auxToFrac_zvar_of_le (by omega), pswap_X]

end HJO.Sym

namespace HJO.Dyck

open HJO.Sym

variable {N k : ℕ} {x : Fin N → ℕ} {σ : Fin k → ℕ} {m : ℕ} {w : Fin N → ℕ}

/-! ### The relabelling leaves the runs alone -/

@[simp]
theorem labelCutSet_transposeTuple (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) :
    labelCutSet x m (transposeTuple m w) = labelCutSet x m w := by
  simp only [labelCutSet, labelSupport_transposeTuple]

@[simp]
theorem labelRun_transposeTuple (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) (t : ℕ) :
    labelRun x m (transposeTuple m w) t = labelRun x m w t := by
  simp only [labelRun, labelCutSet_transposeTuple, labelSupport_transposeTuple]

@[simp]
theorem labelRunCount_transposeTuple (x : Fin N → ℕ) (m : ℕ) (w : Fin N → ℕ) :
    labelRunCount x m (transposeTuple m w) = labelRunCount x m w := by
  simp only [labelRunCount, labelCutSet_transposeTuple]

/-! ### The first position of the support -/

/-- **The first position of the two-letter support is the position of the letter `m`**, when the
prescription `σ` has pairwise distinct entries and puts `m` before `m + 1`. Below the level the
support consists exactly of the two positions carrying `m` and `m + 1`, and no position of the
support lies below either of them. -/
theorem sortNth_one_eq_of_special (hx : IsPartialDyck k N x) (hw : w ∈ noAttackLabellings x σ)
    (hσ : Function.Injective σ) {a b : Fin k} (ha : σ a = m) (hb : σ b = m + 1)
    (hab : (a : ℕ) < (b : ℕ)) : sortNth (labelSupport m w) 1 = (a : ℕ) := by
  have hak : (a : ℕ) < k := a.isLt
  have hwa : wordOfFin w (a : ℕ) = m := by
    rw [wordOfFin_eq_of_lt_level hx.le_length hw hak]
    simpa using ha
  have haS : (a : ℕ) ∈ labelSupport m w :=
    mem_labelSupport.2 ⟨lt_of_lt_of_le hak hx.le_length, Or.inl hwa⟩
  have hp : 1 ≤ #(labelSupport m w) := Finset.card_pos.2 ⟨_, haS⟩
  have hmem : sortNth (labelSupport m w) 1 ∈ labelSupport m w := sortNth_mem le_rfl hp
  obtain ⟨d, hd1, hdp, hdeq⟩ := exists_sortNth haS
  have hle : sortNth (labelSupport m w) 1 ≤ (a : ℕ) :=
    hdeq ▸ sortNth_le_sortNth le_rfl hdp hd1
  refine le_antisymm hle ?_
  by_contra hcon
  have hck : sortNth (labelSupport m w) 1 < k := lt_trans (by omega) hak
  have hval := wordOfFin_eq_of_lt_level hx.le_length hw hck
  rcases wordOfFin_eq_or_eq_of_mem_labelSupport hmem with h | h
  · rw [hval] at h
    have := congrArg Fin.val (hσ (h.trans ha.symm))
    simp only at this
    omega
  · rw [hval] at h
    have := congrArg Fin.val (hσ (h.trans hb.symm))
    simp only at this
    omega

/-! ### The swapping operator on one class sum -/

variable {K : Type*} [CommRing K]

/-- The algebra of the per-class step: `Δ_m` pulls out a factor its interchange fixes, and moves
the one factor left. -/
theorem pdelta_auxToFrac_mul_mul [IsDomain K] {q : K} {i j : Fin k}
    (Q G P A₀ A₁ : AuxAlphabetSeries K k)
    (hQ : pswap K i j (auxToFrac K k Q) = auxToFrac K k Q)
    (hG : pswap K i j (auxToFrac K k G) = auxToFrac K k G)
    (hP : pswap K i j (auxToFrac K k P) = auxToFrac K k P)
    (hA : pdelta q i j (auxToFrac K k A₀) = auxToFrac K k A₁) :
    pdelta q i j (auxToFrac K k (Q * G * (A₀ * P))) = auxToFrac K k (Q * G * (A₁ * P)) := by
  have hGf : pswap K i j (auxToFrac K k Q * auxToFrac K k G * auxToFrac K k P)
      = auxToFrac K k Q * auxToFrac K k G * auxToFrac K k P := by
    rw [map_mul, map_mul, hQ, hG, hP]
  rw [show auxToFrac K k (Q * G * (A₀ * P))
      = auxToFrac K k Q * auxToFrac K k G * auxToFrac K k P * auxToFrac K k A₀ from by
      rw [map_mul, map_mul, map_mul]; ring,
    show auxToFrac K k (Q * G * (A₁ * P))
      = auxToFrac K k Q * auxToFrac K k G * auxToFrac K k P * auxToFrac K k A₁ from by
      rw [map_mul, map_mul, map_mul]; ring,
    pdelta_mul_of_pswap_eq hGf, hA]

/-- **`Δ_m` carries the class sum of `w` for `σ` to the class sum of `τ_m w` for `τ_m σ`.** Both
class sums are given by `HJO.Dyck.finsum_labelClass`, and they differ in exactly one factor: the
weight of the first run, which `w` starts with `m` — that is the hypothesis `σ⁻¹(m) < σ⁻¹(m+1)` —
and `τ_m w` starts with `m + 1`. Everything else is fixed by `ŝ_m`: the power of `q` is a scalar,
each factor of `g` is a merged variable other than the two `ŝ_m` interchanges, and the later runs
contribute the symmetric sums of `HJO.Sym.pswap_runWeight_add`. So `HJO.Sym.pdelta_mul_of_pswap_eq`
pulls the invariant factor out of `Δ_m`, and `HJO.Sym.pdelta_runWeight` turns `a_m(l_1, 0)` into
`a_m(l_1, 1)`.

This is the per-class step of `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`. What it
does *not* do is sum over the classes, which that proposition does from here. -/
theorem pdelta_auxToFrac_finsum_labelClass [IsDomain K] (q : K) (hx : IsPartialDyck k N x)
    (hσ : Function.Injective σ) {i j : Fin k} (hmi : (i : ℕ) = m) (hmj : (j : ℕ) = m + 1)
    {a b : Fin k} (ha : σ a = m) (hb : σ b = m + 1) (hab : (a : ℕ) < (b : ℕ))
    (hw : w ∈ noAttackLabellings x σ) :
    pdelta q i j (auxToFrac K k (∑ᶠ w' ∈ labelClass x σ m w,
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w'))
      = auxToFrac K k (∑ᶠ w' ∈ labelClass x (transposeTuple m σ) m (transposeTuple m w),
        scalarSeries K k q ^ invNumber (attackSet x) (wordOfFin w') * zmon K k w') := by
  have hij : i ≠ j := fun hc => by rw [hc, hmj] at hmi; omega
  have hmj' : (j : ℕ) = (i : ℕ) + 1 := by rw [hmj, hmi]
  have hak : (a : ℕ) < N := lt_of_lt_of_le a.isLt hx.le_length
  have hτw : transposeTuple m w ∈ noAttackLabellings x (transposeTuple m σ) :=
    (bijOn_transposeTuple x σ m).mapsTo hw
  have hτa : transposeTuple m σ a = m + 1 := by
    simp only [transposeTuple, Function.comp_apply, ha, Equiv.swap_apply_left]
  rw [finsum_labelClass q hx hw (j₀ := a) (Or.inl ha),
    finsum_labelClass q hx hτw (j₀ := a) (Or.inr hτa)]
  simp only [labelSupport_transposeTuple, labelRun_transposeTuple,
    labelRunCount_transposeTuple]
  -- the first run starts with `m` for `w` and with `m + 1` for `τ_m w`
  have hs1 : sortNth (labelSupport m w) 1 = (a : ℕ) :=
    sortNth_one_eq_of_special hx hw hσ ha hb hab
  have hwa : wordOfFin w (a : ℕ) = m := by
    rw [wordOfFin_eq_of_lt_level hx.le_length hw a.isLt]
    simpa using ha
  have hτwa : wordOfFin (transposeTuple m w) (a : ℕ) = m + 1 := by
    rw [wordOfFin_of_lt _ hak, transposeTuple_apply,
      show w ⟨(a : ℕ), hak⟩ = m from by rw [← wordOfFin_of_lt w hak]; exact hwa,
      Equiv.swap_apply_left]
  rw [show decide (wordOfFin w (sortNth (labelSupport m w) 1) = m + 1) = false from by
      rw [hs1, hwa]; simp,
    show decide (wordOfFin (transposeTuple m w) (sortNth (labelSupport m w) 1) = m + 1) = true from
      by rw [hs1, hτwa]; simp]
  -- the exponent `e` and the monomial `g` are the same for both
  have hg : ∏ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) ∉ labelSupport m w),
        zvar K k (transposeTuple m w l)
      = ∏ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) ∉ labelSupport m w),
        zvar K k (w l) :=
    Finset.prod_congr rfl fun l hl => by
      rw [transposeTuple_apply_of_notMem m w (mem_filter.1 hl).2]
  rw [card_filter_invSet_eq_of_labelSupport_eq (x := x) (m := m) (w := w)
      (w' := transposeTuple m w) (labelSupport_transposeTuple m w)
      (fun l hl => transposeTuple_apply_of_notMem m w hl), hg]
  -- the invariant factor, and the one factor `Δ_m` moves
  have hAF : ∀ (l : ℕ) (ε : Bool), auxToFrac K k (runWeightZvar q k m l ε)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l ε := fun l ε => by
    rw [← hmi]
    exact auxToFrac_runWeightZvar q hmj' l ε
  have hp : 1 ≤ #(labelSupport m w) := one_le_card_labelSupport hx hw (Or.inl ha)
  have hCsub : labelCutSet x m w ⊆ Ico 1 #(labelSupport m w) := cutSet_subset_Ico _ _
  have hl1 : 1 ≤ #(labelRun x m w 1) :=
    one_le_card_cutBlock (cutBlock_nonempty hp hCsub le_rfl (by omega))
  have hAF : ∀ (l : ℕ) (ε : Bool), auxToFrac K k (runWeightZvar q k m l ε)
      = runWeight (MvPowerSeries.C (scalarFrac K q)) (MvPowerSeries.C (yFrac K i))
          (MvPowerSeries.C (yFrac K j)) l ε := fun l ε => by
    rw [← hmi]
    exact auxToFrac_runWeightZvar q hmj' l ε
  refine pdelta_auxToFrac_mul_mul _ _ _ _ _ ?_ ?_ ?_ ?_
  · rw [map_pow, map_pow, auxToFrac_scalarSeries, pswap_C_scalarFrac]
  · rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun l hl => ?_
    obtain ⟨h1, h2⟩ := ne_and_ne_of_notMem_twoLetterSupport l.isLt (mem_filter.1 hl).2
    rw [wordOfFin_val] at h1 h2
    exact pswap_auxToFrac_zvar_of_ne (by rw [hmi]; exact h1) (by rw [hmj]; exact h2)
  · rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [map_add, hAF, hAF]
    exact pswap_runWeight_add q i j _
  · rw [hAF, hAF]
    exact pdelta_runWeight q hij hl1

end HJO.Dyck
