/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CreationSeeds.LogDeriv
public import HJO.CarlssonMellit.SweepCM
public meta import HJO.Attr

/-! # The plethysm of a complete homogeneous function

`HJO.Sweep.theta_completeHomog`: `θ₀(h_r) = ∑_{s+t=r} q^s(-1)^t h_s e_t`.

## Main statements

* `HJO.CreationSeeds.completeHomog_scaled`: the identity for an arbitrary pair of ring
  homomorphisms out of `Λ` differing by the factor `c^k - 1` on the power sums.
* `HJO.Sweep.theta_completeHomog`, the instance of it at `θ₀`.

## Implementation notes

The content is a generating-series identity, and it is proved once for an arbitrary scalar `c` and
an arbitrary pair `φ`, `ψ` of ring homomorphisms out of `Λ` with
`ψ(p_k) = (c^k - 1)φ(p_k)` — which is the shape the file `HJO.CreationSeeds.LogDeriv` states
its letter lemmas in, and which makes the cancellation otherwise performed by hand a single
application of `HJO.CreationSeeds.derivative_mul_of_logDeriv`. `θ₀` is the instance at
`φ = MvPolynomial.C` and `c = algebraMap L (Total L) q`, since `HJO.Sweep.theta`'s scalar is
`q^r - 1`.

Two logarithmic derivatives are computed on the way, and both are proved *coefficientwise* from the
corresponding unscaled one rather than through `HJO.CreationSeeds.derivative_eq_of_coeff_scaled`:
for the `h`-series scaled by `c^n` the identity `c^{k+1}c^{n-k} = c^{n+1}` collapses each term, and
for the alternating `e`-series the identity `(-1)^{n-k} = (-1)^n(-1)^k` does. Both use `k ≤ n`,
which the summation range supplies, so no truncated subtraction survives into a statement.

`θ₀` is the restriction of `HJO.Sweep.theta` to `V_0`, whose elements are the images of
`MvPolynomial.C`; the statement is therefore about `theta q (MvPolynomial.C f)`, and the scalar
`q^j` appears as `(algebraMap L (Total L) q)^j` rather than as `algebraMap L (Total L) (q^j)` — the
same element, written so that `ring` can move it.

## References

The file formalises `HJO.Sweep.theta_completeHomog`.
-/

@[expose] public section

open Finset

namespace HJO.CreationSeeds

section Scaled

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Type*} [CommRing R]

/-- **The `h`-series with its `n`-th term scaled by `cⁿ`** has logarithmic derivative
`∑ₖ c^{k+1}φ(p_{k+1})zᵏ`: each term of the convolution carries `c^{k+1}c^{n-k} = c^{n+1}`, so the
scalar factors straight out of the unscaled identity
`HJO.CreationSeeds.derivative_mk_completeHomog`. -/
theorem derivative_mk_scaled_completeHomog (φ : Sym.Lambda K →+* R) (c : R) :
    PowerSeries.derivative R (PowerSeries.mk fun n => c ^ n * φ (Sym.completeHomog K n))
      = (PowerSeries.mk fun k => c ^ (k + 1) * φ (Sym.powerSum K (k + 1)))
        * PowerSeries.mk fun n => c ^ n * φ (Sym.completeHomog K n) := by
  refine PowerSeries.ext fun n => ?_
  have hc := congrArg (PowerSeries.coeff n) (derivative_mk_completeHomog φ)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have key : ∑ k ∈ range (n + 1), c ^ (k + 1) * φ (Sym.powerSum K (k + 1)) *
        (c ^ (n - k) * φ (Sym.completeHomog K (n - k)))
      = c ^ (n + 1) * ∑ k ∈ range (n + 1),
          φ (Sym.powerSum K (k + 1)) * φ (Sym.completeHomog K (n - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    calc c ^ (k + 1) * φ (Sym.powerSum K (k + 1)) *
          (c ^ (n - k) * φ (Sym.completeHomog K (n - k)))
        = c ^ (k + 1) * c ^ (n - k) *
            (φ (Sym.powerSum K (k + 1)) * φ (Sym.completeHomog K (n - k))) := by ring
      _ = c ^ (n + 1) *
            (φ (Sym.powerSum K (k + 1)) * φ (Sym.completeHomog K (n - k))) := by
          rw [← pow_add, show k + 1 + (n - k) = n + 1 by omega]
  rw [key, ← hc]
  ring

/-- **The alternating `e`-series** `∑ₙ(-1)ⁿφ(eₙ)zⁿ` has logarithmic derivative
`-∑ₖφ(p_{k+1})zᵏ`: reading `(-1)^{n-k} = (-1)^n(-1)^k` turns each term of the convolution into the
corresponding term of `HJO.CreationSeeds.derivative_mk_elemSymm`, with one overall sign left
over. -/
theorem derivative_mk_alternating_elemSymm (φ : Sym.Lambda K →+* R) :
    PowerSeries.derivative R (PowerSeries.mk fun n => (-1) ^ n * φ (Sym.elemSymm K n))
      = (-(PowerSeries.mk fun k => φ (Sym.powerSum K (k + 1))))
        * PowerSeries.mk fun n => (-1) ^ n * φ (Sym.elemSymm K n) := by
  refine PowerSeries.ext fun n => ?_
  have hc := congrArg (PowerSeries.coeff n) (derivative_mk_elemSymm φ)
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  rw [PowerSeries.coeff_derivative, neg_mul, map_neg, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  have hsign : ∀ k ≤ n, ((-1 : R)) ^ (n - k) = (-1) ^ n * (-1) ^ k := fun k hk => by
    have h1 : ((-1 : R)) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    calc ((-1 : R)) ^ (n - k) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
      _ = (-1) ^ n * (-1) ^ k := by rw [← mul_assoc, h1]
  have key : ∑ k ∈ range (n + 1), φ (Sym.powerSum K (k + 1)) *
        ((-1) ^ (n - k) * φ (Sym.elemSymm K (n - k)))
      = (-1) ^ n * ∑ k ∈ range (n + 1),
          (-1) ^ k * φ (Sym.powerSum K (k + 1)) * φ (Sym.elemSymm K (n - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [hsign k (by omega)]
    ring
  rw [key, ← hc, pow_succ]
  ring

/-- **The plethysm identity for an arbitrary scaling of the power sums.** If `ψ` scales `φ`'s power
sum `p_k` by `c^k - 1`, then
`ψ(h_r) = ∑_{s+t=r}c^s(-1)^tφ(h_s)φ(e_t)`.

Both sides are read off the `z^r` coefficient of one identity of power series: the two logarithmic
derivatives add to `ψ`'s by hypothesis (`HJO.CreationSeeds.derivative_mul_of_logDeriv`), and both
series have constant term `1`, so `HJO.CreationSeeds.powerSeries_ext_of_logDeriv` identifies
them. -/
theorem completeHomog_scaled [Algebra ℚ R] (φ ψ : Sym.Lambda K →+* R) (c : R)
    (h : ∀ k : ℕ, 0 < k → ψ (Sym.powerSum K k) = (c ^ k - 1) * φ (Sym.powerSum K k)) (r : ℕ) :
    ψ (Sym.completeHomog K r)
      = ∑ j ∈ range (r + 1), c ^ j * (-1) ^ (r - j) *
          (φ (Sym.completeHomog K j) * φ (Sym.elemSymm K (r - j))) := by
  have hQ : (PowerSeries.mk fun k => c ^ (k + 1) * φ (Sym.powerSum K (k + 1)))
      + (-(PowerSeries.mk fun k => φ (Sym.powerSum K (k + 1))))
      = PowerSeries.mk fun k => ψ (Sym.powerSum K (k + 1)) := by
    refine PowerSeries.ext fun k => ?_
    rw [map_add, map_neg, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      h (k + 1) k.succ_pos]
    ring
  have hlog : PowerSeries.derivative R
      ((PowerSeries.mk fun n => c ^ n * φ (Sym.completeHomog K n))
        * PowerSeries.mk fun n => (-1) ^ n * φ (Sym.elemSymm K n))
      = (PowerSeries.mk fun k => ψ (Sym.powerSum K (k + 1)))
        * ((PowerSeries.mk fun n => c ^ n * φ (Sym.completeHomog K n))
          * PowerSeries.mk fun n => (-1) ^ n * φ (Sym.elemSymm K n)) := by
    rw [← hQ]
    exact derivative_mul_of_logDeriv (derivative_mk_scaled_completeHomog φ c)
      (derivative_mk_alternating_elemSymm φ)
  have key : (PowerSeries.mk fun n => ψ (Sym.completeHomog K n))
      = (PowerSeries.mk fun n => c ^ n * φ (Sym.completeHomog K n))
        * PowerSeries.mk fun n => (-1) ^ n * φ (Sym.elemSymm K n) :=
    powerSeries_ext_of_logDeriv (derivative_mk_completeHomog ψ) hlog
      (by simp [PowerSeries.coeff_mul, CopPower.completeHomog_zero, elemSymm_zero])
  have hc := congrArg (PowerSeries.coeff r) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  simp only [PowerSeries.coeff_mk] at hc
  rw [hc]
  exact Finset.sum_congr rfl fun j _ => by ring

end Scaled

end HJO.CreationSeeds

namespace HJO.Sweep

variable {L : Type*} [CommRing L]

/-- `θ₀` as a ring homomorphism out of `Λ`: `V_0` is the image of `MvPolynomial.C`, so `θ₀` is the
composite of `θ` with that inclusion. -/
noncomputable def thetaC (q : L) : Sym.Lambda L →+* Total L :=
  (theta q).toRingHom.comp MvPolynomial.C

theorem thetaC_apply (q : L) (f : Sym.Lambda L) : thetaC q f = theta q (MvPolynomial.C f) := rfl

/-- `θ₀` scales `p_k` by `q^k - 1`, which is `HJO.Sweep.theta` read through the inclusion of
`V_0`. -/
theorem thetaC_powerSum (q : L) {k : ℕ} (hk : 0 < k) :
    thetaC q (Sym.powerSum L k)
      = ((algebraMap L (Total L) q) ^ k - 1) * MvPolynomial.C (Sym.powerSum L k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [thetaC_apply, theta_powerSum, map_sub, map_pow, map_one]

/-- **The plethysm of a complete homogeneous function.**
`θ₀(h_r) = ∑_{s+t=r}q^s(-1)^t h_s e_t`.

`θ₀` scales `p_r` by `q^r - 1`, the difference of the two logarithmic derivatives carried by the
series of the `q`-scaled `h`'s and of the alternating `e`'s; the cancellation the textbook proof
performs by hand is `HJO.CreationSeeds.derivative_mul_of_logDeriv`, and the identification of the
two series is `HJO.CreationSeeds.powerSeries_ext_of_logDeriv`. -/
@[hjo "lem_om_theta_hsymm"]
theorem theta_completeHomog [Algebra ℚ L] (q : L) (r : ℕ) :
    theta q (MvPolynomial.C (Sym.completeHomog L r))
      = ∑ j ∈ range (r + 1), (algebraMap L (Total L) q) ^ j * (-1) ^ (r - j) *
          (MvPolynomial.C (Sym.completeHomog L j) *
            MvPolynomial.C (Sym.elemSymm L (r - j)) : Total L) := by
  rw [← thetaC_apply]
  exact CreationSeeds.completeHomog_scaled (MvPolynomial.C : Sym.Lambda L →+* Total L)
    (thetaC q) (algebraMap L (Total L) q) (fun k hk => thetaC_powerSum q hk) r

end HJO.Sweep
