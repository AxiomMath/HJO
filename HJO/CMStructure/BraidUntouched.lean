/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.CMRaising
public meta import HJO.Attr

/-! # The braid operator is linear over the variables it does not touch

The braid operator `T_i` of `HJO.Sweep.braid` moves only the two auxiliary variables `y_i` and
`y_{i+1}`. So it commutes with multiplication by any element built from the symmetric functions
and the *other* auxiliary variables, which is what lets the computations of the Carlsson--Mellit
layer pull such a factor through a word of braid operators.

## Main results

* `HJO.Sweep.braid_mul_mem_supported`.

## Implementation notes

The hypothesis the proof uses is `s_i c = c` and nothing else, which is
`HJO.Sweep.braid_mul_of_swapAux_eq` of `HJO.Shuffle.CMRaising`; the coefficient
algebra `Λ ⊗_𝕜 𝕜[y_j : j ∉ {i, i+1}]` is `MvPolynomial.supported (Sym.Lambda L) s` for a set `s`
of indices avoiding `i - 1` and `i` — the index convention being `y_j = X (j-1)` — and every
element of it is fixed by `s_i`, which is `HJO.Sweep.swapAux_eq_self_of_mem_supported`. The
containment is proved by `Algebra.adjoin_le` into the equalizer of `s_i` and the identity, the
subalgebra `supported` being by definition the one the variables adjoin.

Fixed by `s_i` is strictly weaker than lying in that algebra — `y_i + y_{i+1}` is fixed and does
not lie in it — so the general lemma is a genuine generalisation and not a restatement.

Two of the hypotheses are dropped. It states the lemma for `k ≥ 2` and
`1 ≤ i ≤ k - 1` with `c` built from the `y_j` with `1 ≤ j ≤ k`; in the one-total-space convention
of `HJO.Shuffle.SweepModule` neither the bound `j ≤ k` nor the range of `i` is used, and at
the unread index `i = 0` the statement still holds because `s_0` is the identity and `∂_0` is
zero, so `T_0` is the identity. What the index `i` must avoid is recorded in the set `s` itself.

## References

This file formalises `HJO.Sweep.braid_mul_mem_supported`.
-/

@[expose] public section

namespace HJO.Sweep

section Field

variable {L : Type*} [Field L]

/-- **The elements of `Λ ⊗_𝕜 𝕜[y_j : j ∉ {i, i+1}]` are fixed by `s_i`.** The adjacent
transposition `s_i` fixes `Λ` and every auxiliary variable other than `y_i` and `y_{i+1}`, which
are `X (i-1)` and `X i` in the index convention of `HJO.Sweep.auxVar`, so it fixes the subalgebra
those other variables adjoin. -/
theorem swapAux_eq_self_of_mem_supported {i : ℕ} {s : Set ℕ}
    (hs : ∀ n ∈ s, n ≠ i - 1 ∧ n ≠ i) {c : Total L}
    (hc : c ∈ MvPolynomial.supported (Sym.Lambda L) s) : swapAux L i c = c := by
  have hle : MvPolynomial.supported (Sym.Lambda L) s ≤
      AlgHom.equalizer (swapAux L i).toAlgHom (AlgHom.id (Sym.Lambda L) (Total L)) := by
    rw [MvPolynomial.supported_eq_adjoin_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨hn1, hn2⟩ := hs n hn
    rw [SetLike.mem_coe, AlgHom.mem_equalizer, AlgEquiv.coe_toAlgHom, AlgHom.id_apply, swapAux_X,
      Equiv.swap_apply_of_ne_of_ne hn1 hn2]
  exact hle hc

/-- **The operator is linear over the untouched variables.**
`HJO.Sweep.braid_mul_mem_supported`: for `c` in `Λ ⊗_𝕜 𝕜[y_j : j ∉ {i, i+1}]` and every `F`,
`T_i(cF) = c T_i(F)`. The coefficient algebra is `MvPolynomial.supported` at a set of indices
avoiding `i - 1` and `i`, which are the indices of `y_i` and `y_{i+1}`; the further
restriction to `j ≤ k`, and its range condition on `i`, are not used. -/
@[hjo "lem_cm_braid_linear"]
theorem braid_mul_mem_supported (q : L) {i : ℕ} {s : Set ℕ} (hs : ∀ n ∈ s, n ≠ i - 1 ∧ n ≠ i)
    {c : Total L} (hc : c ∈ MvPolynomial.supported (Sym.Lambda L) s) (F : Total L) :
    braid q i (c * F) = c * braid q i F :=
  braid_mul_of_swapAux_eq q (swapAux_eq_self_of_mem_supported hs hc) F

end Field

end HJO.Sweep
