/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.BopDouble
public meta import HJO.Attr

/-! # The Haglund--Morse--Zabrocki relation between two Hall--Littlewood operators

Two combinations of the operators `B_r` of `HJO.Sym.Bop` collapse, on every `f ∈ Λ`, to a difference
of two of the two-variable coefficients `φ_{a,b}` of `HJO.Sym.bpairCoeff`:

`B_mB_nf - qB_{m+1}B_{n-1}f = φ_{m,n}(f) - φ_{m+1,n-1}(f)`,
`qB_nB_mf - B_{n-1}B_{m+1}f = φ_{n,m}(f) - φ_{n-1,m+1}(f)`.

The symmetry `φ_{a,b} = φ_{b,a}` then identifies the two right-hand sides, and the resulting
identity between the two left-hand sides is Corollary 3.4 of Haglund--Morse--Zabrocki.

## Main results

* `HJO.Sym.bop_bop_sub_smul`, the first combination.
* `HJO.Sym.smul_bop_bop_sub`, the second.
* `HJO.Sym.bop_pair_antisymm_apply` and `HJO.Sym.bop_pair_antisymm`,
  pointwise and as an identity in `Module.End K (Lambda K)`.

## Implementation notes

**The two `κ`-cancellations are one induction and one single-term sum.** Both identities expand the
two products by `HJO.Sym.bop_bop` over the same range and then re-index one of them by one step.
Instead of re-indexing a `Finset.range` — where such proofs go wrong — the combination is read off a
general family `g : ℕ → Λ` with `g s = φ_{m+s, n-s}(f)`, so that the shifted sum is literally
`∑_r κ_r g (r+1)`:

* `HJO.Sym.sum_bkernel_telescope` is the first collapse,
  `∑_{r≤R} κ_r g r - q∑_{r≤R} κ_r g (r+1) = g 0 - g 1 - κ_{R+1} g (R+1)`, proved by induction on
  `R`, the step being exactly `κ_{s+1} = qκ_s` for `s ≥ 1`
  (`HJO.Sym.bkernel_succ_succ`). The textbook proof drops the last term by the support hypothesis;
  here it is carried and discharged once, at the end.
* `HJO.Sym.sum_bkernel_telescope_swap` is the second,
  `q∑_{r≤R} κ_r g r - ∑_{r≤R} κ_{r+1} g r = g 0`, a single sum all of whose terms but the first
  vanish, `qκ_s - κ_{s+1}` being `0` for `s ≥ 1` and
  `1` at `s = 0`. No vanishing hypothesis is needed for this one: the second lemma's longer sum,
  over `0 ≤ r ≤ R+1`, splits off its `r = 0` term exactly and leaves the same range as the first.

**No `q ≠ 1` and no `q ≠ 0`.** The kernel coefficients `κ_r` are polynomials in `q`
(`HJO.Sym.bkernel`), so both collapses are identities over any commutative ring, and neither
identity carries a side condition on `q`. The `N ≥ 0` from `HJO.Sym.exists_bpairCoeff_eq_zero` is
likewise not read: what is used is `n + N ≤ R` for a natural number `R`, and
`R = (max 0 (n+N)).toNat` supplies that with no sign hypothesis.

**The support bound is taken on the second index only.** `HJO.Sym.exists_bpairCoeff_eq_zero`
vanishes as soon as *either* index drops below `-N`; both
lemmas use only the second, which is the half that is stated.

## References

The lemmas `HJO.Sym.bop_bop_sub_smul`, `HJO.Sym.smul_bop_bop_sub` and `HJO.Sym.bop_pair_antisymm`,
on the Haglund--Morse--Zabrocki relations, using
`HJO.Sym.Lambda`, `HJO.Sym.Bop`, `HJO.Sym.bkernel`, `HJO.Sym.bpairCoeff`,
`HJO.Sym.exists_bpairCoeff_eq_zero`, `HJO.Sym.bpairCoeff_comm` and `HJO.Sym.bop_bop`. The last is
Corollary 3.4 of J. Haglund, J. Morse and M. Zabrocki, *A compositional shuffle conjecture
specifying touch points of the Dyck path*, Canad. J. Math.
**64** (2012) 822--844, whose operators are the present ones rescaled by `(-1)^r`, a rescaling the
relation is invariant under; it is consumed by E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, in its Lemma 5.3 and its Proposition 6.3.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The two collapses of the kernel coefficients -/

section Telescope

variable {K : Type*} [CommRing K]

/-- **The first collapse.** For any family `g : ℕ → Λ`,

`∑_{r=0}^{R} κ_r g r - q ∑_{r=0}^{R} κ_r g (r+1) = g 0 - g 1 - κ_{R+1} g (R+1)`.

Only `κ_0 = 1`, `κ_1 - qκ_0 = -1` and `κ_{s+1} = qκ_s` for `s ≥ 1` enter, so the induction step is
a single application of `HJO.Sym.bkernel_succ_succ`. -/
theorem sum_bkernel_telescope (q : K) (g : ℕ → Lambda K) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (bkernel q r) * g r
        - MvPolynomial.C q * ∑ r ∈ Finset.range (R + 1),
            MvPolynomial.C (bkernel q r) * g (r + 1)
      = g 0 - g 1 - MvPolynomial.C (bkernel q (R + 1)) * g (R + 1) := by
  induction R with
  | zero =>
    have h1 : bkernel q 1 = q - 1 := by simp [bkernel]
    simp only [zero_add, Finset.sum_range_one, bkernel_zero, map_one, one_mul, h1, map_sub]
    ring
  | succ R ih =>
    have hk : (MvPolynomial.C (bkernel q (R + 1 + 1)) : Lambda K)
        = MvPolynomial.C q * MvPolynomial.C (bkernel q (R + 1)) := by
      rw [← MvPolynomial.C_mul]
      congr 1
      simp only [bkernel_succ, pow_succ]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ
      (f := fun r => MvPolynomial.C (bkernel q r) * g (r + 1))]
    linear_combination ih + g (R + 1 + 1) * hk

/-- **The second collapse.** For any family `g : ℕ → Λ`,

`q ∑_{r=0}^{R} κ_r g r - ∑_{r=0}^{R} κ_{r+1} g r = g 0`.

Every term but the first vanishes, `qκ_{s+1} = κ_{s+2}`, and the first is `qκ_0 - κ_1 = 1`. -/
theorem sum_bkernel_telescope_swap (q : K) (g : ℕ → Lambda K) (R : ℕ) :
    MvPolynomial.C q * ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (bkernel q r) * g r
        - ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (bkernel q (r + 1)) * g r
      = g 0 := by
  have hzero : ∀ r ∈ Finset.range (R + 1), r ≠ 0 →
      MvPolynomial.C q * (MvPolynomial.C (bkernel q r) * g r)
        - MvPolynomial.C (bkernel q (r + 1)) * g r = 0 := by
    intro r _ hr
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have h0 : (MvPolynomial.C q : Lambda K) * MvPolynomial.C (bkernel q (s + 1))
        = MvPolynomial.C (bkernel q (s + 1 + 1)) := by
      rw [← MvPolynomial.C_mul]
      congr 1
      simp only [bkernel_succ, pow_succ]
      ring
    linear_combination g (s + 1) * h0
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos R)) hzero]
  simp only [bkernel_zero, bkernel_succ, pow_zero, one_mul, map_one, map_sub]
  ring

end Telescope

/-! ### The two combinations -/

section Pair

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The first combination is a difference of two coefficients.** For all
`m, n : ℤ` and every `f ∈ Λ`,

`B_mB_nf - qB_{m+1}B_{n-1}f = φ_{m,n}(f) - φ_{m+1,n-1}(f)`.

Both products are expanded by `HJO.Sym.bop_bop` over `0 ≤ r ≤ R` with `R = max 0 (n+N)`; the
second is the first re-indexed by one step, so `HJO.Sym.sum_bkernel_telescope` applies verbatim, and
its last term `κ_{R+1}φ_{m+R+1, n-R-1}(f)` vanishes because `n - (R+1) ≤ -N-1 < -N`. -/
@[hjo "lem_cm_bop_pair_phi"]
theorem bop_bop_sub_smul (q : K) (m n : ℤ) (f : Lambda K) :
    Bop q m (Bop q n f) - q • Bop q (m + 1) (Bop q (n - 1) f)
      = bpairCoeff q m n f - bpairCoeff q (m + 1) (n - 1) f := by
  obtain ⟨N, -, hN⟩ := exists_bpairCoeff_eq_zero q f
  have hNb : ∀ a b : ℤ, b < -N → bpairCoeff q a b f = 0 := fun a b h => hN a b (Or.inr h)
  set R : ℕ := (max 0 (n + N)).toNat
  have hRcast : ((R : ℤ)) = max 0 (n + N) := Int.toNat_of_nonneg (le_max_left _ _)
  have hRge : n + N ≤ (R : ℤ) := by rw [hRcast]; exact le_max_right _ _
  have hRge' : n - 1 + N ≤ (R : ℤ) := by omega
  set g : ℕ → Lambda K := fun s => bpairCoeff q (m + (s : ℤ)) (n - (s : ℤ)) f with hg
  have hgR : bpairCoeff q (m + ((R + 1 : ℕ) : ℤ)) (n - ((R + 1 : ℕ) : ℤ)) f = 0 := by
    refine hNb _ _ ?_
    push_cast
    omega
  have e1 := bop_bop q f hNb m n hRge
  have e2 : Bop q (m + 1) (Bop q (n - 1) f)
      = ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (bkernel q r) * g (r + 1) := by
    rw [bop_bop q f hNb (m + 1) (n - 1) hRge']
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hg]
    rw [show m + 1 + (r : ℤ) = m + ((r + 1 : ℕ) : ℤ) by push_cast; ring,
      show n - 1 - (r : ℤ) = n - ((r + 1 : ℕ) : ℤ) by push_cast; ring]
  rw [e1, e2, MvPolynomial.smul_eq_C_mul, sum_bkernel_telescope, hgR, mul_zero, sub_zero]
  norm_num

/-- **The second combination is a difference of two coefficients.** For
all `m, n : ℤ` and every `f ∈ Λ`,

`qB_nB_mf - B_{n-1}B_{m+1}f = φ_{n,m}(f) - φ_{n-1,m+1}(f)`.

Here the second product is expanded over the longer range `0 ≤ r ≤ R+1`, with `R = max 0 (m+N)`;
splitting off its `r = 0` term by `Finset.sum_range_succ'` leaves exactly the range of the first,
shifted by one, so `HJO.Sym.sum_bkernel_telescope_swap` applies and nothing has to be shown to
vanish. -/
@[hjo "lem_cm_bop_pair_phi_swap"]
theorem smul_bop_bop_sub (q : K) (m n : ℤ) (f : Lambda K) :
    q • Bop q n (Bop q m f) - Bop q (n - 1) (Bop q (m + 1) f)
      = bpairCoeff q n m f - bpairCoeff q (n - 1) (m + 1) f := by
  obtain ⟨N, -, hN⟩ := exists_bpairCoeff_eq_zero q f
  have hNb : ∀ a b : ℤ, b < -N → bpairCoeff q a b f = 0 := fun a b h => hN a b (Or.inr h)
  set R : ℕ := (max 0 (m + N)).toNat
  have hRcast : ((R : ℤ)) = max 0 (m + N) := Int.toNat_of_nonneg (le_max_left _ _)
  have hRge : m + N ≤ (R : ℤ) := by rw [hRcast]; exact le_max_right _ _
  have hRge' : m + 1 + N ≤ ((R + 1 : ℕ) : ℤ) := by push_cast; omega
  set g : ℕ → Lambda K := fun s => bpairCoeff q (n + (s : ℤ)) (m - (s : ℤ)) f with hg
  have e1 := bop_bop q f hNb n m hRge
  have e2 : Bop q (n - 1) (Bop q (m + 1) f)
      = (∑ r ∈ Finset.range (R + 1), MvPolynomial.C (bkernel q (r + 1)) * g r)
        + bpairCoeff q (n - 1) (m + 1) f := by
    rw [bop_bop q f hNb (n - 1) (m + 1) hRge', Finset.sum_range_succ']
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hg]
      rw [show n - 1 + ((r + 1 : ℕ) : ℤ) = n + (r : ℤ) by push_cast; ring,
        show m + 1 - ((r + 1 : ℕ) : ℤ) = m - (r : ℤ) by push_cast; ring]
    · rw [bkernel_zero, map_one, one_mul, Nat.cast_zero, add_zero, sub_zero]
  have hg0 : g 0 = bpairCoeff q n m f := by
    simp only [hg, Nat.cast_zero, add_zero, sub_zero]
  rw [e1, e2, MvPolynomial.smul_eq_C_mul]
  linear_combination sum_bkernel_telescope_swap q g R + hg0

/-! ### The Haglund--Morse--Zabrocki relation -/

/-- **`HJO.Sym.bop_pair_antisymm`, pointwise**: for all `m, n : ℤ` and every `f ∈ Λ`,

`B_mB_nf - qB_{m+1}B_{n-1}f = qB_nB_mf - B_{n-1}B_{m+1}f`.

The two sides are the two combinations above, and `HJO.Sym.bpairCoeff_comm` identifies their values
`φ_{m,n}(f) - φ_{m+1,n-1}(f)` and `φ_{n,m}(f) - φ_{n-1,m+1}(f)`. -/
theorem bop_pair_antisymm_apply (q : K) (m n : ℤ) (f : Lambda K) :
    Bop q m (Bop q n f) - q • Bop q (m + 1) (Bop q (n - 1) f)
      = q • Bop q n (Bop q m f) - Bop q (n - 1) (Bop q (m + 1) f) := by
  rw [bop_bop_sub_smul, smul_bop_bop_sub, bpairCoeff_comm q n m f,
    bpairCoeff_comm q (n - 1) (m + 1) f]

/-- **The Haglund--Morse--Zabrocki relation** `HJO.Sym.bop_pair_antisymm`: for all integers `m, n`,
`B_mB_n - qB_{m+1}B_{n-1} = qB_nB_m - B_{n-1}B_{m+1}` as endomorphisms of `Λ`.

Equivalently, the combination `E m n = B_mB_n - qB_{m+1}B_{n-1}` is antisymmetric under the
involution `(m,n) ↦ (n-1, m+1)`, which at `m = a+1`, `n = b+2` is the interchange of `a` and `b` —
the form in which the Carlsson--Mellit argument uses it. Both indices range over all of `ℤ`, which
is necessary rather than generous: the shifts `n-1` and `m+1` do not preserve the non-negative half,
and `B_{-1}` is not the zero operator. -/
@[hjo "lem_cm_hmz_cor34"]
theorem bop_pair_antisymm (q : K) (m n : ℤ) :
    Bop q m * Bop q n - q • (Bop q (m + 1) * Bop q (n - 1))
      = q • (Bop q n * Bop q m) - Bop q (n - 1) * Bop q (m + 1) := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
  exact bop_pair_antisymm_apply q m n f

end Pair

end HJO.Sym
