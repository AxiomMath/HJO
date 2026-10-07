/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitDopColumn
public meta import HJO.Attr

/-! # The commutator of two basic operators, at every pair of integer indices

The `(a,1)` column at `b = 0` rests on the single identity
`M·∑_{l ≥ 0}(qu)^lD_{1+l}(D_{-l}f) = D_1(D_0f) - D_0(D_1f)`
(`HJO.Sym.smul_sum_pow_smul_dopInt_dopInt`). This file proves the identity that specialises to it:
**for every pair of integer indices `n ≤ m`,**

`D_m(D_nf) - D_n(D_mf) = M·∑_{i=0}^{m-n-1}∑_{l ≥ 0}(qu)^lD_{n+1+i+l}(D_{m-1-i-l}f)`.

The right-hand side is a sum of `m - n` geometric rows, one for each way of splitting the gap
between the two indices; at `(m,n) = (1,0)` there is a single row and it is the earlier identity
(`HJO.Sym.smul_sum_pow_smul_dopInt_dopInt_of_comm` re-derives that theorem from this one, so the
specialisation is checked by machine and not by eye).

## Why the general pair, and not just `(1,0)`

`M·ψ_{b+1} = ψ_b∘D_0 - D_0∘ψ_b` is an identity among `b + 2` basic operators
(`HJO.Sweep.ColumnCommutes`), and `ψ_b` is the chain

`ψ_b = ∑_{l_1,…,l_b ≥ 0}(qu)^{l_1+⋯+l_b}D_{l_b-l_{b+1}}D_{l_{b-1}-l_b}⋯D_{l_0-l_1}`,
`l_0 = 0`, `l_{b+1} = -1`

(the composition law `HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum` iterated). Commuting
`D_0` past such a word is Leibniz: one term per letter, each carrying the commutator of that letter
with `D_0`, and the letters are `D_{l_p - l_{p+1}}` at every pair. So **the identity below is
exactly the input the general clause needs, and the pairs it needs are not just `(1,0)`.**

## Main definitions

* `HJO.Sym.dopPair` — the two-variable coefficient family `φ_{i,j}` at an arbitrary pair of integer
  indices. `HJO.Sym.dopDiag` is its restriction to the line `i + j = 1`
  (`HJO.Sym.dopDiag_eq_dopPair`), and that restriction is all the `b = 0` clause used.

## Main results

* `HJO.Sym.dopPair_symm` — `φ_{i,j} = φ_{j,i}`, the interchange of the two variables of the double
  displacement. `HJO.Sym.dopDiag_reflect` is its case `i + j = 1`.
* `HJO.Sym.dopInt_dopInt_eq_sum_mkernel_dopPair` — the unfolding
  `D_i(D_jf) = ∑_{r ≥ 0}λ_rφ_{i+r,j-r}` at **every** pair of integer indices.
* `HJO.Sym.smul_sum_sum_of_symm` — the commutator formula as a statement about an arbitrary
  symmetric, eventually-vanishing family, with no symmetric functions in it.
* `HJO.Sym.smul_sum_sum_dopInt_dopInt` — the commutator formula.
* `HJO.Sym.smul_sum_pow_smul_dopInt_dopInt_of_comm` — the `b = 0` identity, re-derived.

## Implementation notes

**No hypothesis on `q` or `u`, and no `M ≠ 0`.** As at `b = 0`, `M` appears because every member of
the displacement's kernel above the zeroth carries it (`HJO.Sym.mkernel_succ`), and the proof
cancels against that factor rather than dividing.

**The proof is the `b = 0` proof with one telescope more.** Write `g(s) = φ_{s,m+n-s}` for the
family on the line `i + j = m + n`. The unfolding reads `D_a(D_{m+n-a}f) = ∑_rλ_rg(a+r)`, so both
sides are functionals on `g`; `HJO.Sym.dopPair_symm` is `g(s) = g(m+n-s)`; each of the `m - n` rows
collapses to `∑_tc_tg(n+1+i+t)` by `HJO.Sym.sum_pow_smul_sum_mkernel_smul` and then to
`∑_jh_j(g(n+1+i+j) - g(n+2+i+j))` by `HJO.Sym.sum_hsym2_smul_sub`; summing the `m - n` rows
telescopes the inner difference to `g(n+1+j) - g(m+1+j)`; and the `r = 0` term of the commutator
vanishes because `g(m) = g(n)` by the symmetry. At `(m,n) = (1,0)` there is one row and this is the
proof of `HJO.Sym.smul_sum_pow_smul_dopInt_dopInt` verbatim.
-/

@[expose] public section

namespace HJO.Sym

/-! ### The combinatorial core, on an arbitrary symmetric family -/

section Core

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **The commutator formula, stripped of symmetric functions.** Let `g : ℤ → M` be symmetric about
`N/2` (`g s = g (N - s)`) and vanish above `N + Dg`, and let `P a = ∑_{r ≥ 0}λ_r g(a+r)` for
`a ≥ n`. Then for every `n ≤ m` with `N = m + n`,

`M·∑_{i=0}^{m-n-1}∑_{l ≥ 0}(qu)^lP(n+1+i+l) = P(m) - P(n)`.

With `g(s) = φ_{s,N-s}` the two-variable coefficient family and `P(a) = D_a(D_{N-a}f)` this is
`HJO.Sym.smul_sum_sum_dopInt_dopInt`. There is no hypothesis on `q` or `u`.

The proof: each row `i` collapses onto the diagonal by `HJO.Sym.sum_pow_smul_sum_mkernel_smul` and
telescopes by `HJO.Sym.sum_hsym2_smul_sub`; summing the `m - n` rows telescopes the inner
difference; the `r = 0` term of `P(m) - P(n)` dies by the symmetry. -/
theorem smul_sum_sum_of_symm (q u : K) (g : ℤ → M) (P : ℤ → M) (N : ℤ) (Dg R : ℕ)
    (m n : ℤ) (hmn : n ≤ m) (hN : N = m + n)
    (hP : ∀ a : ℤ, n ≤ a → P a = ∑ r ∈ Finset.range (R + 1), mkernel q u r • g (a + (r : ℤ)))
    (hsymm : ∀ s : ℤ, g s = g (N - s))
    (hvan : ∀ s : ℤ, N + (Dg : ℤ) < s → g s = 0)
    (hR : m + (Dg : ℤ) < (R : ℤ)) (hR1 : 0 < R) :
    ((1 - q) * (1 - u)) • ∑ i ∈ Finset.range (m - n).toNat, ∑ l ∈ Finset.range (R + 1),
        ((q * u) ^ l) • P (n + 1 + (i : ℤ) + (l : ℤ))
      = P m - P n := by
  classical
  have hθvan : ∀ j : ℕ, (m - 1 + (Dg : ℤ)).toNat < j → g (n + 1 + (j : ℤ)) = 0 := by
    intro j hj
    have hjz : ((m - 1 + (Dg : ℤ)).toNat : ℤ) < (j : ℤ) := by exact_mod_cast hj
    exact hvan _ (by omega)
  have hN0R : (m - 1 + (Dg : ℤ)).toNat ≤ R := by omega
  have hN0R' : (m - 1 + (Dg : ℤ)).toNat + 1 ≤ R := by omega
  -- (A) each row collapses onto the diagonal, and (B) telescopes
  have hrow : ∀ i : ℕ, (∑ l ∈ Finset.range (R + 1),
        ((q * u) ^ l) • P (n + 1 + (i : ℤ) + (l : ℤ)))
      = ∑ j ∈ Finset.range ((m - 1 + (Dg : ℤ)).toNat + 1),
          hsym2 q u j • (g (n + 1 + ((i + j : ℕ) : ℤ)) - g (n + 1 + ((i + j + 1 : ℕ) : ℤ))) := by
    intro i
    have hstep : ∀ l : ℕ, P (n + 1 + (i : ℤ) + (l : ℤ))
        = ∑ r ∈ Finset.range (R + 1), mkernel q u r • g (n + 1 + ((i + l + r : ℕ) : ℤ)) := by
      intro l
      rw [hP (n + 1 + (i : ℤ) + (l : ℤ)) (by omega)]
      exact Finset.sum_congr rfl fun r _ => by
        rw [show n + 1 + ((i + l + r : ℕ) : ℤ) = n + 1 + (i : ℤ) + (l : ℤ) + (r : ℤ) from by
          push_cast; ring]
    rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range (R + 1)) => by rw [hstep l])]
    have hcol := sum_pow_smul_sum_mkernel_smul q u ((m - 1 + (Dg : ℤ)).toNat)
      (fun j => g (n + 1 + ((i + j : ℕ) : ℤ)))
      (fun j hj => hθvan (i + j) (by omega)) R R hN0R hN0R
    have htel := sum_hsym2_smul_sub q u (fun j => g (n + 1 + ((i + j : ℕ) : ℤ)))
      ((m - 1 + (Dg : ℤ)).toNat)
    rw [hθvan (i + ((m - 1 + (Dg : ℤ)).toNat + 1)) (by omega), smul_zero, sub_zero] at htel
    rw [show (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) • ∑ r ∈ Finset.range (R + 1),
          mkernel q u r • g (n + 1 + ((i + l + r : ℕ) : ℤ)))
        = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) • ∑ r ∈ Finset.range (R + 1),
          mkernel q u r • g (n + 1 + ((i + (l + r) : ℕ) : ℤ)) from
      Finset.sum_congr rfl fun l _ => by
        refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
        rw [show i + l + r = i + (l + r) from by omega], hcol, ← htel]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show i + (j + 1) = i + j + 1 from by omega]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (m - n).toNat) => hrow i),
    Finset.sum_comm, Finset.smul_sum]
  -- (C) summing the rows telescopes the inner difference
  have hinner : ∀ j : ℕ, ((1 - q) * (1 - u)) • ∑ i ∈ Finset.range (m - n).toNat,
        hsym2 q u j • (g (n + 1 + ((i + j : ℕ) : ℤ)) - g (n + 1 + ((i + j + 1 : ℕ) : ℤ)))
      = mkernel q u (j + 1) •
          (g (n + 1 + ((j + (m - n).toNat : ℕ) : ℤ)) - g (n + 1 + (j : ℤ))) := by
    intro j
    have htel : (∑ i ∈ Finset.range (m - n).toNat,
          (g (n + 1 + ((i + j : ℕ) : ℤ)) - g (n + 1 + ((i + j + 1 : ℕ) : ℤ))))
        = g (n + 1 + (j : ℤ)) - g (n + 1 + ((j + (m - n).toNat : ℕ) : ℤ)) := by
      have h := Finset.sum_range_sub' (fun i => g (n + 1 + ((j + i : ℕ) : ℤ))) ((m - n).toNat)
      simp only [Nat.add_zero] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by
        rw [show i + j = j + i from by omega, show j + i + 1 = j + (i + 1) from by omega]
    rw [← Finset.smul_sum, htel, smul_smul, mkernel_succ, neg_mul, neg_smul, ← smul_neg, neg_sub]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range ((m - 1 + (Dg : ℤ)).toNat + 1)) =>
    hinner j)]
  -- (E) widen the range, the family having run out
  have hwide : (∑ j ∈ Finset.range ((m - 1 + (Dg : ℤ)).toNat + 1), mkernel q u (j + 1) •
        (g (n + 1 + ((j + (m - n).toNat : ℕ) : ℤ)) - g (n + 1 + (j : ℤ))))
      = ∑ j ∈ Finset.range R, mkernel q u (j + 1) •
        (g (n + 1 + ((j + (m - n).toNat : ℕ) : ℤ)) - g (n + 1 + (j : ℤ))) := by
    refine Finset.sum_subset (fun x hx => Finset.mem_range.2 (by
      have := Finset.mem_range.1 hx
      omega)) ?_
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [hθvan (j + (m - n).toNat) (by omega), hθvan j (by omega), sub_zero, smul_zero]
  rw [hwide]
  -- (F) the right-hand side, whose `r = 0` term dies by the symmetry
  have hzero : mkernel q u 0 • (g (m + ((0 : ℕ) : ℤ)) - g (n + ((0 : ℕ) : ℤ))) = 0 := by
    have h := hsymm n
    rw [show N - n = m from by rw [hN]; ring] at h
    rw [Nat.cast_zero, add_zero, add_zero, ← h, sub_self, smul_zero]
  rw [hP m hmn, hP n le_rfl, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun r (_ : r ∈ Finset.range (R + 1)) =>
      (smul_sub (mkernel q u r) (g (m + (r : ℤ))) (g (n + (r : ℤ)))).symm),
    Finset.sum_range_succ' (fun r => mkernel q u r • (g (m + (r : ℤ)) - g (n + (r : ℤ)))) R,
    hzero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  · rw [show n + 1 + ((j + (m - n).toNat : ℕ) : ℤ) = m + ((j + 1 : ℕ) : ℤ) from by
      push_cast
      omega]
  · rw [show n + 1 + (j : ℤ) = n + ((j + 1 : ℕ) : ℤ) from by push_cast; ring]

end Core

/-! ### The two-variable coefficient family at an arbitrary pair of indices -/

section Pair

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The two-variable coefficient family** `φ_{i,j}` of the object
`f[X + M/y₁ + M/y₂]·Ω(y₁)·Ω(y₂)`, written without ever naming that object:

`φ_{i,j} = ∑_k D_i(δ(f)_k)·c_{j+k}`,

with `δ` the displacement of `HJO.Sym.plethShift`, `D` the integer-indexed basic operator
`HJO.Sym.DopInt` and `c` the alternating elementary family `HJO.Sym.esymmSigned`. The sum runs over
a range covering the degree of `δ(f)`, so it is finite by construction and no Laurent series is
built.

`HJO.Sym.dopDiag` is the restriction to the line `i + j = 1`. -/
noncomputable def dopPair (q u : K) (f : Lambda K) (i j : ℤ) : Lambda K :=
  ∑ k ∈ Finset.range ((plethShift q u f).natDegree + 1),
    DopInt q u i ((plethShift q u f).coeff k) * esymmSigned K (j + (k : ℤ))

/-- The diagonal family of the `b = 0` clause is this family on the line `i + j = 1`. -/
theorem dopDiag_eq_dopPair (q u : K) (f : Lambda K) (s : ℤ) :
    dopDiag q u f s = dopPair q u f (s + 1) (-s) := rfl

/-- Any range covering the degree of `δ(f)` computes the family. -/
theorem dopPair_eq_sum_range (q u : K) (f : Lambda K) (i j : ℤ) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) :
    dopPair q u f i j = ∑ k ∈ Finset.range T,
      DopInt q u i ((plethShift q u f).coeff k) * esymmSigned K (j + (k : ℤ)) := by
  refine Finset.sum_subset (fun x hx => Finset.mem_range.2 (by
    have := Finset.mem_range.1 hx
    omega)) ?_
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero, zero_mul]

/-- **The family vanishes when the second index is far enough below zero**: every term carries
`c_{j+k}` with `k ≤ natDegree δ(f) < -j`, and the alternating elementary family vanishes below
`0`. -/
theorem dopPair_eq_zero_of_lt (q u : K) (f : Lambda K) {i j : ℤ}
    (hj : ((plethShift q u f).natDegree : ℤ) < -j) : dopPair q u f i j = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hkz : (k : ℤ) ≤ ((plethShift q u f).natDegree : ℤ) := by exact_mod_cast hk
  rw [esymmSigned_of_neg (by omega : j + (k : ℤ) < 0), mul_zero]

/-- The family as an explicit double sum over the coefficients of the double displacement. -/
theorem dopPair_eq_double_sum (q u : K) (f : Lambda K) {T : ℕ}
    (hT1 : (plethShift q u f).natDegree < T)
    (hT2 : ∀ k i : ℕ, T ≤ i → (plethShift q u ((plethShift q u f).coeff k)).coeff i = 0)
    (i j : ℤ) :
    dopPair q u f i j
      = ∑ k ∈ Finset.range T, ∑ k' ∈ Finset.range T,
          (plethShift q u ((plethShift q u f).coeff k)).coeff k'
            * esymmSigned K (i + (k' : ℤ)) * esymmSigned K (j + (k : ℤ)) := by
  rw [dopPair_eq_sum_range q u f i j hT1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show DopInt q u i ((plethShift q u f).coeff k)
      = ∑ k' ∈ Finset.range T, (plethShift q u ((plethShift q u f).coeff k)).coeff k'
          * esymmSigned K (i + (k' : ℤ)) from
    coeffPairing_eq_sum_range _ _ (fun k' hk' => hT2 k k' hk'), Finset.sum_mul]

/-- **The family is symmetric in its two indices**: `φ_{i,j} = φ_{j,i}`.

This is the interchange of the two variables of `Λ[y₁][y₂]`
(`HJO.Sym.coeff_plethShift_coeff_plethShift_comm`), and it is the only genuinely two-variable input
the commutator formula needs. `HJO.Sym.dopDiag_reflect` is the case `i + j = 1`. -/
theorem dopPair_symm (q u : K) (f : Lambda K) (i j : ℤ) :
    dopPair q u f i j = dopPair q u f j i := by
  obtain ⟨T, hT1, hT2⟩ := exists_natDegree_bound q u f
  rw [dopPair_eq_double_sum q u f hT1 hT2 i j, dopPair_eq_double_sum q u f hT1 hT2 j i]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  rw [coeff_plethShift_coeff_plethShift_comm q u f k' k]
  ring

/-- **The unfolding of a product of two basic operators, at every pair of integer indices**:

`D_i(D_jf) = ∑_{r ≥ 0}λ_rφ_{i+r,j-r}`,

with `λ` the kernel `HJO.Sym.mkernel`. `HJO.Sym.dopInt_dopInt_eq_sum_mkernel_dopDiag` is the case
`i + j = 1`; the proof is the same, from the single rule `HJO.Sym.dopInt_mul_esymmSigned` applied to
each coefficient of `δ(f)`. -/
theorem dopInt_dopInt_eq_sum_mkernel_dopPair (q u : K) (f : Lambda K) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) (i j : ℤ) {R : ℕ} (hR : j + (T : ℤ) ≤ (R : ℤ)) :
    DopInt q u i (DopInt q u j f)
      = ∑ r ∈ Finset.range (R + 1),
          MvPolynomial.C (mkernel q u r) * dopPair q u f (i + (r : ℤ)) (j - (r : ℤ)) := by
  have hF : ∀ k : ℕ, T ≤ k → (plethShift q u f).coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : DopInt q u j f
      = ∑ k ∈ Finset.range T,
        (plethShift q u f).coeff k * esymmSigned K (j + (k : ℤ)) :=
    coeffPairing_eq_sum_range _ _ hF
  have hterm : ∀ k ∈ Finset.range T,
      DopInt q u i ((plethShift q u f).coeff k * esymmSigned K (j + (k : ℤ)))
        = ∑ r ∈ Finset.range (R + 1), MvPolynomial.C (mkernel q u r)
            * esymmSigned K (j + (k : ℤ) - (r : ℤ))
            * DopInt q u (i + (r : ℤ)) ((plethShift q u f).coeff k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkz : (k : ℤ) < (T : ℤ) := by exact_mod_cast hk
    exact dopInt_mul_esymmSigned q u i (j + (k : ℤ)) R (by omega) _
  rw [h1, map_sum, Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [dopPair_eq_sum_range q u f (i + (r : ℤ)) (j - (r : ℤ)) hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show j + (k : ℤ) - (r : ℤ) = j - (r : ℤ) + (k : ℤ) from by ring]
  ring

end Pair

/-! ### The commutator of two basic operators -/

section Commutator

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The commutator of two basic operators, at every pair of integer indices `n ≤ m`:**

`D_m(D_nf) - D_n(D_mf) = M·∑_{i=0}^{m-n-1}∑_{l ≥ 0}(qu)^lD_{n+1+i+l}(D_{m-1-i-l}f)`,
`M = (1-q)(1-u)`.

**No hypothesis on `q` or `u`, and in particular no `M ≠ 0`**: `M` is a coefficient here, produced
by the factor every member of the displacement's kernel above the zeroth carries
(`HJO.Sym.mkernel_succ`), and the proof cancels against it rather than dividing.

At `(m,n) = (1,0)` the outer sum has one row and this is the earlier identity behind the `b = 0`
clause of the `(a,1)` column (`HJO.Sym.smul_sum_pow_smul_dopInt_dopInt_of_comm` re-derives it). The
general pair is what commuting `D_0` past a longer word needs: see this module's header. -/
@[hjo "lem_mellit_dop_commutator"]
theorem smul_sum_sum_dopInt_dopInt (q u : K) (f : Lambda K) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) (m n : ℤ) (hnm : n ≤ m) {R : ℕ}
    (hR : T ≤ R) (hRm : m + (T : ℤ) ≤ (R : ℤ)) :
    ((1 - q) * (1 - u)) • ∑ i ∈ Finset.range (m - n).toNat, ∑ l ∈ Finset.range (R + 1),
        ((q * u) ^ l) • DopInt q u (n + 1 + (i : ℤ) + (l : ℤ))
          (DopInt q u (m - 1 - (i : ℤ) - (l : ℤ)) f)
      = DopInt q u m (DopInt q u n f) - DopInt q u n (DopInt q u m f) := by
  have hunf : ∀ a : ℤ, n ≤ a →
      DopInt q u a (DopInt q u (m + n - a) f)
        = ∑ r ∈ Finset.range (R + 1),
            mkernel q u r • dopPair q u f (a + (r : ℤ)) (m + n - (a + (r : ℤ))) := by
    intro a ha
    rw [dopInt_dopInt_eq_sum_mkernel_dopPair q u f hT a (m + n - a) (R := R) (by omega)]
    exact Finset.sum_congr rfl fun r _ => by
      rw [MvPolynomial.smul_eq_C_mul, show m + n - (a + (r : ℤ)) = m + n - a - (r : ℤ) from by ring]
  have hcore := smul_sum_sum_of_symm q u
    (fun s => dopPair q u f s (m + n - s))
    (fun a => DopInt q u a (DopInt q u (m + n - a) f))
    (m + n) ((plethShift q u f).natDegree) R m n hnm rfl hunf
    (fun s => by
      rw [dopPair_symm q u f s (m + n - s), show m + n - (m + n - s) = s from by ring])
    (fun s hs => dopPair_eq_zero_of_lt q u f (by omega))
    (by omega) (by omega)
  rw [show m + n - m = n from by ring, show m + n - n = m from by ring] at hcore
  refine Eq.trans (congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_) hcore
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [show m - 1 - (i : ℤ) - (l : ℤ) = m + n - (n + 1 + (i : ℤ) + (l : ℤ)) from by ring]

/-- **The `b = 0` identity, re-derived from the commutator formula** — the check that
the general pair really specialises to `HJO.Sym.smul_sum_pow_smul_dopInt_dopInt` at `(m,n) = (1,0)`,
where the outer sum has the single row `i = 0`. -/
theorem smul_sum_pow_smul_dopInt_dopInt_of_comm (q u : K) (f : Lambda K) {T : ℕ}
    (hT : (plethShift q u f).natDegree < T) {R : ℕ} (hR : T + 1 ≤ R) :
    ((1 - q) * (1 - u)) • (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
        DopInt q u (1 + (l : ℤ)) (DopInt q u (-(l : ℤ)) f))
      = DopInt q u 1 (DopInt q u 0 f) - DopInt q u 0 (DopInt q u 1 f) := by
  have h := smul_sum_sum_dopInt_dopInt q u f hT 1 0 (by omega) (R := R) (by omega) (by omega)
  rw [show ((1 : ℤ) - 0).toNat = 1 from rfl, Finset.sum_range_one, Nat.cast_zero] at h
  refine Eq.trans ?_ h
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (0 : ℤ) + 1 + 0 + (l : ℤ) = 1 + (l : ℤ) from by ring,
    show (1 : ℤ) - 1 - 0 - (l : ℤ) = -(l : ℤ) from by ring]

end Commutator

end HJO.Sym
