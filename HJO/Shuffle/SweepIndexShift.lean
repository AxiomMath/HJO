/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.CornerClosedForm
public import HJO.CMStructure.VmodDminusSection
public meta import HJO.Attr

/-! # The three sweep generators at a shifted index

Appending a part to a composition shifts the width at every event of the base inside the band, by
the number of live north steps the tail contributes there
(`HJO.Paths.sweepWidth_appendHeights_eq`). So comparing the sweep of an extension with the sweep of
its truncation needs `d^♭_-`, `d^♭_+` and `Δ` read at index `k + δ` against the same operators read
at index `k`. This file supplies those three comparisons.

## Main results

* `HJO.Sweep.dminus_eq_of_mem_piece`: **`d^♭_-` does not see the index at all on a lower piece.**
  For `F ∈ V_k` and any `m ≥ k`, `d^♭_-{}^{(m+1)}F = d^♭_-{}^{(k+1)}F`. So the type-`B` half of the
  shift is an *equality*, with no correction term and no hypothesis on `q`.
* `HJO.Sweep.dplus_succ_eq_dplus_add`: **`d^♭_+` at one index higher, with its correction.** For
  `F ∈ V_k`, writing `G = y_{k+1}τ_{k+1,k+1}F`,
  `d^♭_+{}^{(k+1)}F = d^♭_+{}^{(k)}F + T_{[1,k]}((q-1)y_{k+1}∂_{k+1}G)`.
  The two operators therefore differ by one Demazure term read *inside the same ascending word*
  `T_{[1,k]}` — which is the sharpest form available, since `HJO.Sweep.dplus` carries its index both
  in the word and in the variable.
* `HJO.Sweep.dplus_split_prefix`: `d^♭_+` at index `k + δ` factors through the index-`k` word:
  `d^♭_+{}^{(k+δ)}F = -T_{[1,k]}(T_{[k+1,k+δ]}(y_{k+δ+1}τ_{k+δ+1,k+δ+1}F))`.
* `HJO.Sweep.corner_transport_split_prefix`: the same splitting for `Δ` on the transport, on top of
  the closed form `HJO.Sweep.corner_transport_eq`.

## Implementation notes

**Everything rests on one variable interchange.** The substitution `τ^{±}_{m,m}` reads its index
only through the letter `y_m`, so interchanging `y_i` and `y_{i+1}` moves the index by one:
`HJO.Sweep.swapAux_qshift_self` and `HJO.Sweep.swapAux_qshiftNeg_self`. Dually the coefficient
extraction reads its index only through the variable whose exponent it deletes, so the same
interchange moves *its* index by one: `HJO.Sweep.lowerCoeff_swapAux_self`. The existing
`HJO.Sweep.qshiftNeg_swapAux` and `HJO.Sweep.lowerCoeff_swapAux` are the *distant* statements, where
the interchange misses the read index and nothing moves; these are their adjacent counterparts, and
they are what the index shift needs.

`d^♭_-` then comes out index-blind on `V_k` because both of its halves move together and the
interchange fixes `V_k` (`HJO.Sweep.swapAux_of_mem_piece`) as well as the answer
(`HJO.Sweep.lowerCoeff_mem_piece`). `d^♭_+` does not, and the reason is visible in the proof: its
ascending word gains the letter `T_{k+1}`, and `T_{k+1}s_{k+1} = 1 - (q-1)y_{k+1}∂_{k+1}` is not
the identity.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### An adjacent interchange moves the index of the substitution -/

section Substitution

variable {L : Type*} [Field L]

/-- **`s_i` carries `τ_{k,i}` to `τ_{k,i+1}`.** Both sides are ring maps, so it is enough to check
the generators: `τ_{k,i}` reads its index only through the letter `y_i`, which `s_i` renames to
`y_{i+1}`, and it fixes every auxiliary variable, which is where `s_i` acts. -/
theorem swapAux_qshift_self (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    swapAux L i (qshift q i F) = qshift q (i + 1) (swapAux L i F) := by
  have hav : swapAux L i (auxVar i : Total L) = auxVar (i + 1) := swapAux_auxVar_self hi
  have hC : ∀ c : Sym.Lambda L, swapAux L i (qshift q i (MvPolynomial.C c))
      = qshift q (i + 1) (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      rw [hx, qshift_scal, swapAux_scal, qshift_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
    | mul_X p j hp =>
      have hps : (MvPolynomial.C (p * MvPolynomial.X j) : Total L)
          = MvPolynomial.C p * MvPolynomial.C (Sym.powerSum L (j + 1)) := by
        rw [Sym.powerSum, Nat.add_sub_cancel, map_mul]
      have hgen : swapAux L i (qshift q i (MvPolynomial.C (Sym.powerSum L (j + 1)) : Total L))
          = qshift q (i + 1) (MvPolynomial.C (Sym.powerSum L (j + 1))) := by
        rw [qshift_powerSum, qshift_powerSum, map_add, map_mul, map_pow, swapAux_scal, swapAux_C,
          hav]
      rw [hps, map_mul, map_mul, hp, hgen, map_mul]
  induction F using MvPolynomial.induction_on with
  | C c => rw [swapAux_C, hC c]
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
  | mul_X p n hp =>
    rw [map_mul, qshift_auxVar, map_mul, hp, swapAux_X, map_mul, map_mul, swapAux_X,
      qshift_auxVar]

/-- **`s_i` carries `τ^-_{k,i}` to `τ^-_{k,i+1}`**, the same statement for the subtracting
substitution. -/
theorem swapAux_qshiftNeg_self (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    swapAux L i (qshiftNeg q i F) = qshiftNeg q (i + 1) (swapAux L i F) := by
  have hav : swapAux L i (auxVar i : Total L) = auxVar (i + 1) := swapAux_auxVar_self hi
  have hC : ∀ c : Sym.Lambda L, swapAux L i (qshiftNeg q i (MvPolynomial.C c))
      = qshiftNeg q (i + 1) (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      rw [hx, qshiftNeg_scal, swapAux_scal, qshiftNeg_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
    | mul_X p j hp =>
      have hps : (MvPolynomial.C (p * MvPolynomial.X j) : Total L)
          = MvPolynomial.C p * MvPolynomial.C (Sym.powerSum L (j + 1)) := by
        rw [Sym.powerSum, Nat.add_sub_cancel, map_mul]
      have hgen : swapAux L i (qshiftNeg q i (MvPolynomial.C (Sym.powerSum L (j + 1)) : Total L))
          = qshiftNeg q (i + 1) (MvPolynomial.C (Sym.powerSum L (j + 1))) := by
        rw [qshiftNeg_powerSum, qshiftNeg_powerSum, map_sub, map_mul, map_pow, swapAux_scal,
          swapAux_C, hav]
      rw [hps, map_mul, map_mul, hp, hgen, map_mul]
  induction F using MvPolynomial.induction_on with
  | C c => rw [swapAux_C, hC c]
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
  | mul_X p n hp =>
    rw [map_mul, qshiftNeg_auxVar, map_mul, hp, swapAux_X, map_mul, map_mul, swapAux_X,
      qshiftNeg_auxVar]

end Substitution

/-! ### An adjacent interchange moves the index of the extraction -/

section Extraction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- A relabelling moves the exponent it reads along with itself. -/
theorem mapDomain_apply_self (e : ℕ ≃ ℕ) (j : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.mapDomain e d (e j) = d j := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]

/-- A relabelling carries erasure at `j` to erasure at `e j`. -/
theorem erase_mapDomain_self (e : ℕ ≃ ℕ) (j : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.erase (e j) (Finsupp.mapDomain e d) = Finsupp.mapDomain e (Finsupp.erase j d) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_eq_mapDomain]
  refine Finsupp.ext fun a => ?_
  by_cases ha : a = e j
  · subst ha
    rw [Finsupp.erase_same, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
      Finsupp.erase_same]
  · rw [Finsupp.erase_ne ha, Finsupp.equivMapDomain_apply, Finsupp.equivMapDomain_apply,
      Finsupp.erase_ne (fun hc => ha (by rw [← hc, Equiv.apply_symm_apply]))]

/-- **`s_i` moves the index of the coefficient extraction by one**:
`lowerCoeff_i(s_iH) = s_i(lowerCoeff_{i-1}H)`.

The interchange `s_i` renames the variable index `i - 1` to `i`, and the extraction reads exactly
the exponent of one variable and deletes it; so relabelling before extracting at `i` is extracting
at `i - 1` and relabelling after. This is the **adjacent** companion of
`HJO.Sweep.lowerCoeff_swapAux`, which is the distant case `j ∉ {i-1, i}` where the extraction's
index does not move. -/
theorem lowerCoeff_swapAux_self (i : ℕ) (H : Total L) :
    lowerCoeff L i (swapAux L i H) = swapAux L i (lowerCoeff L (i - 1) H) := by
  have he : Equiv.swap (i - 1) i (i - 1) = i := Equiv.swap_apply_left _ _
  have hexp : ∀ d : ℕ →₀ ℕ,
      Finsupp.mapDomain (Equiv.swap (i - 1) i) d i = d (i - 1) := fun d => by
    have h := mapDomain_apply_self (Equiv.swap (i - 1) i) (i - 1) d
    rwa [he] at h
  have hera : ∀ d : ℕ →₀ ℕ, Finsupp.erase i (Finsupp.mapDomain (Equiv.swap (i - 1) i) d)
      = Finsupp.mapDomain (Equiv.swap (i - 1) i) (Finsupp.erase (i - 1) d) := fun d => by
    have h := erase_mapDomain_self (Equiv.swap (i - 1) i) (i - 1) d
    rwa [he] at h
  induction H using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [swapAux_monomial, lowerCoeff_monomial', lowerCoeff_monomial', hexp d, hera d]
    simp only [map_mul, map_pow, map_neg, map_one, swapAux_C, swapAux_monomial]
  | add p r hp hr => rw [map_add, map_add, map_add, map_add, hp, hr]

end Extraction

/-! ### The lowering operator does not see the index -/

section Lowering

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **One step of the index shift for `d^♭_-`, and it is trivial**: for `F ∈ V_k`,
`d^♭_-{}^{(k+2)}F = d^♭_-{}^{(k+1)}F`.

Both halves of `d^♭_-` move their index together under `s_{k+1}`
(`HJO.Sweep.swapAux_qshiftNeg_self`, `HJO.Sweep.lowerCoeff_swapAux_self`), the interchange fixes `F`
because `F ∈ V_k` reads neither `y_{k+1}` nor `y_{k+2}`, and it fixes the answer because
`d^♭_-{}^{(k+1)}F` lies in `V_k` again. -/
theorem dminus_succ_eq_of_mem_piece (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    dminus q (k + 2) F = dminus q (k + 1) F := by
  have hFfix : swapAux L (k + 1) F = F := swapAux_of_mem_piece (by omega) hF
  have hmem : qshiftNeg q (k + 1) F ∈ piece L (k + 1) :=
    qshiftNeg_mem_piece q (by omega) (by omega) hF
  have hval : dminus q (k + 1) F ∈ piece L k := by
    rw [dminus_succ_apply]
    exact lowerCoeff_mem_piece k hmem
  have hshift : qshiftNeg q (k + 2) F = swapAux L (k + 1) (qshiftNeg q (k + 1) F) := by
    rw [swapAux_qshiftNeg_self q (show 1 ≤ k + 1 by omega), hFfix]
  rw [show k + 2 = (k + 1) + 1 from rfl, dminus_succ_apply, hshift, lowerCoeff_swapAux_self,
    Nat.add_sub_cancel, ← dminus_succ_apply, swapAux_of_mem_piece (by omega) hval]

/-- **`d^♭_-` does not see its index on a lower piece.** For `F ∈ V_k` and every `m ≥ k`,
`d^♭_-{}^{(m+1)}F = d^♭_-{}^{(k+1)}F`.

This closes the type-`B` half of the index shift outright: at a type-`B` event of the extension the
width is `k + δ` rather than `k`, and on `V_k` the two lowering operators are the *same map*. No
hypothesis on `q` or `u` is read. -/
theorem dminus_eq_of_mem_piece (q : L) {k m : ℕ} (hkm : k ≤ m) {F : Total L}
    (hF : F ∈ piece L k) : dminus q (m + 1) F = dminus q (k + 1) F := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, dminus_succ_eq_of_mem_piece q (piece_mono hn hF), ih]

end Lowering

/-! ### The raising operator at a shifted index -/

section Raising

variable {L : Type*} [Field L]

/-- **The ascending word of a shifted index factors through the unshifted one**:
`d^♭_+{}^{(k+δ)}F = -T_{[1,k]}(T_{[k+1,k+δ]}(y_{k+δ+1}τ_{k+δ+1,k+δ+1}F))`.

Nothing is assumed on `F`. This is `HJO.Sweep.cmAscWord_split` applied to
`HJO.Sweep.dplus_eq_ascWord`, and it is the statement that makes the comparison with index `k`
possible at all: the outer word is the *same* `T_{[1,k]}` that `d^♭_+{}^{(k)}` carries, so the whole
of the shift sits in the inner factor. -/
theorem dplus_split_prefix (q : L) (k δ : ℕ) (F : Total L) :
    dplus q (k + δ) F
      = -cmAscWord q 1 k (cmAscWord q (k + 1) (k + δ)
          ((auxVar (k + δ + 1) : Total L) * qshift q (k + δ + 1) F)) := by
  rw [dplus_eq_ascWord, cmAscWord_split q (a := 1) (b := k + δ) (c := k) (by omega) (by omega)]
  rfl

/-- **`d^♭_+` one index higher, with its correction term.** For `F ∈ V_k`,

`d^♭_+{}^{(k+1)}F = d^♭_+{}^{(k)}F + T_{[1,k]}((q-1)y_{k+1}∂_{k+1}(y_{k+1}τ_{k+1,k+1}F))`.

The two raising operators differ by a single Demazure term, read inside the **same** ascending word
`T_{[1,k]}` that both of them carry. Three steps, and the first is where the index moves:

* `y_{k+2}τ_{k+2,k+2}F = s_{k+1}(y_{k+1}τ_{k+1,k+1}F)` for `F ∈ V_k`, by
  `HJO.Sweep.swapAux_qshift_self` together with `HJO.Sweep.swapAux_of_mem_piece`;
* the word gains its last letter, `T_{[1,k+1]} = T_{[1,k]}T_{k+1}`
  (`HJO.Sweep.cmAscWord_split`, `HJO.Sweep.cmAscWord_self`);
* `T_{k+1}(s_{k+1}G) = G - (q-1)y_{k+1}∂_{k+1}G`, since `s_{k+1}` is an involution and `∂_{k+1}` is
  antisymmetric under it (`HJO.Sweep.dividedDiff_swapAux`).

**So `d^♭_+` is not index-blind, and this says exactly by how much.** The correction vanishes
precisely when `y_{k+1}τ_{k+1,k+1}F` is `s_{k+1}`-symmetric, and that is not automatic:
`HJO.Sweep.dplus_apply_powerSum_not_mem_piece` shows `d^♭_+{}^{(1)}(p_1) ∉ V_1` while
`d^♭_+{}^{(0)}` carries `V_0` into `V_1`, so no scalar and no grading-preserving conjugation
relates the two.
`HJO.Sweep.dplus_one_one_of_succ` recovers the directly computed value at `F = 1` from this
formula, which pins its sign and scale. -/
theorem dplus_succ_eq_dplus_add (q : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    dplus q (k + 1) F
      = dplus q k F
        + cmAscWord q 1 k (scal (q - 1) * (auxVar (k + 1) : Total L)
            * dividedDiff (k + 1) ((auxVar (k + 1) : Total L) * qshift q (k + 1) F)) := by
  set G : Total L := (auxVar (k + 1) : Total L) * qshift q (k + 1) F with hG
  have hFfix : swapAux L (k + 1) F = F := swapAux_of_mem_piece (by omega) hF
  have hswap : (auxVar (k + 2) : Total L) * qshift q (k + 2) F = swapAux L (k + 1) G := by
    rw [hG, map_mul, swapAux_auxVar_self (show 1 ≤ k + 1 by omega),
      swapAux_qshift_self q (show 1 ≤ k + 1 by omega), hFfix]
  have hword : cmAscWord q 1 (k + 1) = cmAscWord q 1 k * braidEnd q (k + 1) := by
    rw [cmAscWord_split q (a := 1) (b := k + 1) (c := k) (by omega) (by omega), cmAscWord_self]
  have hletter : braid q (k + 1) (swapAux L (k + 1) G)
      = G - scal (q - 1) * (auxVar (k + 1) : Total L) * dividedDiff (k + 1) G := by
    rw [braid_apply, swapAux_swapAux, dividedDiff_swapAux]
    ring
  rw [dplus_eq_ascWord, show k + 1 + 1 = k + 2 from rfl, hswap, hword]
  change -cmAscWord q 1 k (braid q (k + 1) (swapAux L (k + 1) G)) = _
  rw [hletter, map_sub, dplus_eq_ascWord, ← hG]
  abel

/-- `∂_1(y_1) = -1`: the divided difference of the *lower* of the two variables it reads. -/
theorem dividedDiff_one_X_zero : dividedDiff 1 (MvPolynomial.X 0 : Total L) = -1 := by
  refine (dividedDiff_unique (by omega) ?_).symm
  rw [mul_neg, mul_one, swapAux_X]
  simp [Equiv.swap_apply_left]

/-- **Check: the direct value `d^♭_+{}^{(1)}1 = -qy_1` comes back out of the general formula.**

`HJO.Sweep.dplus_one_one` and `HJO.Sweep.dplus_zero_one` were computed directly, from the trains; at
`k = 0` and `F = 1` the correction term of `HJO.Sweep.dplus_succ_eq_dplus_add` is
`-(q-1)y_1`, whose sum with `-y_1` is `-qy_1`. So the general formula's sign and scale are pinned by
a value that does not come from it.

It is also the reason the vacuum is **not** a witness for the obstruction: at `F = 1` the shift
costs only the scalar `q`, as `HJO.Sweep.dplus_one_one`'s own docstring records. The witness that
no scalar and no grading-preserving conjugation will do is
`HJO.Sweep.dplus_apply_powerSum_not_mem_piece` — `d^♭_+{}^{(1)}(p_1) ∉ V_1` while `d^♭_+{}^{(0)}`
carries `V_0` into `V_1`. -/
theorem dplus_one_one_of_succ (q : L) :
    dplus q 1 (1 : Total L) = -(scal q * (MvPolynomial.X 0 : Total L)) := by
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hq1 : qshift q 1 (1 : Total L) = 1 := map_one _
  have h := dplus_succ_eq_dplus_add (k := 0) (F := (1 : Total L)) q (one_mem _)
  rw [dplus_zero_one, cmAscWord_one_zero] at h
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [Module.End.one_apply, hq1, mul_one, hav, dividedDiff_one_X_zero] at h
  rw [h]
  have hs : (scal (q - 1) : Total L) = scal q - 1 := by
    rw [scal, scal, map_sub, map_sub, map_one, map_one]
  rw [hs]
  ring

end Raising

/-! ### The corner operator at a shifted index -/

section Corner

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-- **`Δ` at a shifted index, on the transport, with the index-`k` word split off.** For
`F ∈ V_{k+1+δ}` and `q ≠ 1`,

`Δ^{(k+1+δ)}(Y_{k+1+δ}F) = -Y_{k+1+δ}T_{[1,k]}(T_{[k+1,k+δ]}(y_{k+1+δ}F))`.

This is `HJO.Sweep.corner_transport_eq` — the closed form for `Δ` at *every* width, needing only
`q ≠ 1` — with its ascending word split at `k` by `HJO.Sweep.cmAscWord_split`. At `δ = 0` the inner
word is empty and this is the closed form itself; for `δ ≥ 1` the outer word is the one
`Δ^{(k+1)}` carries, so the whole of the index shift again sits in the inner factor.

Together with `HJO.Sweep.dminus_eq_of_mem_piece` and `HJO.Sweep.dplus_split_prefix` this is the
third of the three comparisons, and it is the reason the corner needs no separate argument: `Δ` is
*not* an independent generator here but a closed-form multiplication-and-word. -/
theorem corner_transport_split_prefix (hq : q ≠ 1) (k δ : ℕ) {F : Total L}
    (hF : F ∈ piece L (k + 1 + δ)) :
    corner q (k + 1 + δ) (transport L (k + 1 + δ) F)
      = -(transportScalar L (k + 1 + δ) *
          cmAscWord q 1 k (cmAscWord q (k + 1) (k + δ) ((auxVar (k + 1 + δ) : Total L) * F))) := by
  have hidx : k + 1 + δ = (k + δ) + 1 := by omega
  rw [hidx] at hF ⊢
  rw [corner_transport_eq hq (k + δ) hF,
    cmAscWord_split q (a := 1) (b := k + δ) (c := k) (by omega) (by omega)]
  rfl

end Corner

end HJO.Sweep

end
