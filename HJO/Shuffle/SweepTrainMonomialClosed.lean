/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepTrainMonomial
public import Mathlib.Algebra.Order.Antidiag.Finsupp

/-! # The ascending train on a power of the top variable, in closed form

`HJO/Shuffle/SweepTrainMonomial.lean` reduces the ascending train `T_{1↗k+1}` on an arbitrary
monomial to shorter trains, and on the family `y_{k+1}^{n+1}` collapses that reduction to the single
recursion `F_k^{(n+1)} = qF_{k-1}^{(n+1)} + (q-1)∑_{j<n}y_{k+1}^{n-j}F_{k-1}^{(j+1)}`. This file
solves the recursion: it gives `T_{1↗k+1}(y_{k+1}^{n+1})` outright, as an explicit sum of monomials
with explicit weights, at every width and every exponent.

## The formula

**Every monomial of degree `n+1` in `y_1, …, y_{k+1}` whose exponent on `y_1` is positive occurs
exactly once, with weight `(q-1)^rq^{k-r}`, where `r` is the number of variables *other than `y_1`*
that occur in it. No other monomial occurs.**

That is `HJO.Sweep.coeff_cmAscWord_one_auxVar_last_pow_succ` coefficient by coefficient and
`HJO.Sweep.cmAscWord_one_auxVar_last_pow_succ_eq_sum` as one `Finset` sum, over
`Finset.finsuppAntidiag` — the exponent vectors supported on `{y_1, …, y_{k+1}}` of total degree
`n+1` — filtered by the condition that `y_1` occurs. The weight is `HJO.Sweep.trainWeight`.

The exponents themselves are unconstrained beyond their total: the branching of the train does
**not** see how the degree is distributed, only *how many* variables above the bottom carry any of
it. Each such variable costs one factor `q-1` in place of a factor `q`, and there are exactly `k`
letters to pay for, which is why the two exponents always add to `k`.

## Reading the three earlier shapes off it

* `n + 1 = 1`. The only exponent vector of degree `1` with `y_1` occurring is `y_1` itself, `r = 0`,
  weight `q^k` — `HJO.Sweep.cmAscWord_one_auxVar_last_of_closed`, which reproves
  `HJO.Sweep.cmAscWord_one_auxVar_last` from the closed form and nothing else. This is the check
  that the formula is the right one.
* `n + 1 = 2`. Two families: `y_1^2` with `r = 0` and weight `q^k`, and `y_1y_i` for each of the `k`
  indices `2 ≤ i ≤ k+1` with `r = 1` and weight `(q-1)q^{k-1}` — one term per position, all sharing
  one power of `q`. That is exactly `HJO.Sweep.cmAscWord_one_auxVar_last_sq`, and
  `HJO.Sweep.cmAscWord_one_auxVar_last_sq_of_closed` reproves it from the closed form, which is the
  agreement check at the first shape where the train branches.
* `n + 1` arbitrary with the argument symmetric. A symmetric factor rides through the whole train
  (`HJO.Sweep.cmAscWord_mul_of_swapAux_eq`), which is
  `HJO.Sweep.cmAscWord_one_mul_auxVar_last_pow_succ_eq_sum`; at `n + 1 = 0` the train is the
  identity and the formula is not read at all, the sum over an empty condition being the wrong
  object there.

## Why the exponent on `y_1` is positive

The bottom variable is the one the cascade ends at: every branch of every letter leaves a factor
`y_i` behind at the index it branched at and carries the rest down, and the last thing carried down
lands on `y_1`. So `y_1` always occurs, and a monomial of degree `n+1` in `y_2, …, y_{k+1}` alone is
absent from the answer. That is the only constraint on the support, and it is what makes the count
of terms `∑_r\binom{k}{r}\binom{n}{r}` rather than the full number of monomials.

## Genericity

Nothing here reads a hypothesis on `q`, and nothing mentions `u`. `HJO.Sweep.trainWeight` is a
*polynomial* in `q` — `(q-1)^rq^{k-r}` with `r ≤ k` wherever it is read, the bound
`HJO.Sweep.card_erase_zero_le` — so no inverse occurs and every statement holds at `q = 0` and at
`q = 1`. The truncated subtraction `k - r` in the definition is therefore never truncated where it
matters, but the definition is stated without the hypothesis so that it needs none.

## References

Transcribing A. Mellit, *Toric braids and `(m,n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

section Field

variable {L : Type*} [Field L] {q : L}

/-! ### The weight of an exponent vector -/

/-- **The weight the ascending train attaches to an exponent vector.** For `d : ℕ →₀ ℕ` read as the
monomial `∏_iy_{i+1}^{d(i)}`, this is `(q-1)^rq^{k-r}` with `r` the number of variables *other than
`y_1`* occurring in it — the number of letters of `T_{1↗k+1}` at which the cascade branched.

No hypothesis on `q` and no inverse: this is a polynomial in `q`. Wherever the closed form reads it,
`r ≤ k` (`HJO.Sweep.card_erase_zero_le`), so the truncated subtraction is not truncated. -/
noncomputable def trainWeight (q : L) (k : ℕ) (d : ℕ →₀ ℕ) : L :=
  (q - 1) ^ (d.support.erase 0).card * q ^ (k - (d.support.erase 0).card)

/-! ### Degree bookkeeping for exponent vectors -/

/-- The total degree splits off one variable: `|d| = d(i) + |d \ i|`. -/
theorem sum_eq_add_sum_erase (i : ℕ) (d : ℕ →₀ ℕ) :
    (d.sum fun _ e => e) = d i + ((Finsupp.erase i d).sum fun _ e => e) := by
  conv_lhs => rw [← Finsupp.single_add_erase i d]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

/-- No single exponent exceeds the total degree. -/
theorem apply_le_sum (i : ℕ) (d : ℕ →₀ ℕ) : d i ≤ (d.sum fun _ e => e) := by
  rw [sum_eq_add_sum_erase i d]
  exact Nat.le_add_right _ _

/-- Two distinct exponents are together at most the total degree. Used at `i = k+1` to see that a
monomial of the closed form cannot put more than `n` of its `n+1` degrees on the top variable, the
bottom variable needing one. -/
theorem apply_zero_add_apply_le_sum {i : ℕ} (hi : i ≠ 0) (d : ℕ →₀ ℕ) :
    d 0 + d i ≤ (d.sum fun _ e => e) := by
  rw [sum_eq_add_sum_erase 0 d]
  refine Nat.add_le_add_left ?_ _
  rw [← Finsupp.erase_ne hi]
  exact apply_le_sum i _

/-- **`r ≤ k`**: a monomial in `y_1, …, y_{k+1}` has at most `k` variables other than `y_1`. This is
what keeps `HJO.Sweep.trainWeight`'s truncated subtraction honest. -/
theorem card_erase_zero_le {k : ℕ} {d : ℕ →₀ ℕ} (h : d.support ⊆ Finset.range (k + 1)) :
    (d.support.erase 0).card ≤ k := by
  have h1 : d.support.erase 0 ⊆ (Finset.range (k + 1)).erase 0 := Finset.erase_subset_erase 0 h
  have h2 : ((Finset.range (k + 1)).erase 0).card = k := by
    rw [Finset.card_erase_of_mem (by simp), Finset.card_range]
    omega
  exact h2 ▸ Finset.card_le_card h1

/-! ### The closed form, coefficient by coefficient -/

/-- **The closed form of the ascending train on a power of its top variable.** For every width `k`,
every exponent `n+1` and every exponent vector `d`,

`[y^d]T_{1↗k+1}(y_{k+1}^{n+1}) = (q-1)^rq^{k-r}` when `d` uses only `y_1, …, y_{k+1}`, has total
degree `n+1`, and has `y_1` occurring — `r` being the number of its variables other than `y_1` — and
`0` otherwise.

Proved from the branching recursion
`HJO.Sweep.cmAscWord_one_succ_auxVar_last_pow_succ` by induction on the width, all exponents at
once. The induction does exactly two things at each step: a monomial with no `y_{k+1}` in it comes
from the leading branch and picks up one more factor `q`, and a monomial with `y_{k+1}^e` in it
comes from the one term `j = n-e` of the correction sum and picks up one factor `q-1` instead —
every other term of that sum contributing `0` because its residual still carries a power of
`y_{k+1}`, which the shorter train's values never do.

Unconditional in `q`. -/
theorem coeff_cmAscWord_one_X_self_pow (q : L) (k : ℕ) : ∀ (n : ℕ) (d : ℕ →₀ ℕ),
    MvPolynomial.coeff d (cmAscWord q 1 k ((MvPolynomial.X k : Total L) ^ (n + 1)))
      = if d.support ⊆ Finset.range (k + 1) ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0
          then MvPolynomial.C (trainWeight q k d) else 0 := by
  induction k with
  | zero =>
    intro n d
    have h0 : cmAscWord q 1 0 = (1 : Module.End L (Total L)) := cmAscWord_self_pred q 0
    have hiff : (Finsupp.single 0 (n + 1) = d)
        ↔ (d.support ⊆ Finset.range 1 ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0) := by
      constructor
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · rw [Finsupp.support_single 0 (Nat.succ_ne_zero n)]
          simp
        · rw [Finsupp.sum_single_index rfl]
        · rw [Finsupp.single_eq_same]
          omega
      · rintro ⟨hs, hsum, h0'⟩
        have hother : ∀ i, i ≠ 0 → d i = 0 := by
          intro i hi
          by_contra hne
          have := hs (Finsupp.mem_support_iff.2 hne)
          rw [Finset.mem_range] at this
          omega
        have herase : Finsupp.erase 0 d = 0 := by
          ext i
          rw [Finsupp.erase_apply]
          split_ifs with hi
          · rfl
          · rw [hother i hi, Finsupp.coe_zero, Pi.zero_apply]
        have hd0 : d 0 = n + 1 := by
          rw [sum_eq_add_sum_erase 0 d, herase] at hsum
          simpa using hsum
        ext i
        by_cases hi : i = 0
        · subst hi
          rw [Finsupp.single_eq_same, hd0]
        · rw [Finsupp.single_eq_of_ne hi, hother i hi]
    rw [h0, Module.End.one_apply, MvPolynomial.coeff_X_pow]
    by_cases hc : d.support ⊆ Finset.range 1 ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0
    · rw [ite_eq_left hc, ite_eq_left (hiff.2 hc)]
      have hd : d = Finsupp.single 0 (n + 1) := (hiff.2 hc).symm
      rw [trainWeight, hd, Finsupp.support_single 0 (Nat.succ_ne_zero n)]
      simp
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.1 h))]
  | succ m ih =>
    intro n d
    have hX1 : (MvPolynomial.X (m + 1) : Total L) = auxVar (m + 2) := by
      rw [auxVar, show m + 2 - 1 = m + 1 from by omega]
    have hX0 : (MvPolynomial.X m : Total L) = auxVar (m + 1) := by
      rw [auxVar, Nat.add_sub_cancel]
    -- the shorter train never produces a monomial carrying the top variable
    have hvanish : ∀ (e : ℕ) (d' : ℕ →₀ ℕ), d' (m + 1) ≠ 0 →
        MvPolynomial.coeff d' (cmAscWord q 1 m ((MvPolynomial.X m : Total L) ^ (e + 1))) = 0 := by
      intro e d' hd'
      rw [ih e d', ite_eq_right]
      rintro ⟨hs, -, -⟩
      have := hs (Finsupp.mem_support_iff.2 hd')
      rw [Finset.mem_range] at this
      omega
    have hterm : ∀ (f e : ℕ) (d' : ℕ →₀ ℕ),
        MvPolynomial.coeff d' ((MvPolynomial.X (m + 1) : Total L) ^ f
            * cmAscWord q 1 m ((MvPolynomial.X m : Total L) ^ (e + 1)))
          = if f ≤ d' (m + 1)
            then MvPolynomial.coeff (d' - Finsupp.single (m + 1) f)
              (cmAscWord q 1 m ((MvPolynomial.X m : Total L) ^ (e + 1)))
            else 0 := by
      intro f e d'
      simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul',
        Finsupp.single_le_iff, one_mul]
    rw [hX1, cmAscWord_one_succ_auxVar_last_pow_succ q m n, ← hX0, ← hX1, MvPolynomial.coeff_add,
      scal, scal, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum]
    by_cases hd1 : d (m + 1) = 0
    · -- no top variable: the correction sum contributes nothing and one more `q` is emitted
      have hzero : ∀ j ∈ Finset.range n,
          MvPolynomial.coeff d ((MvPolynomial.X (m + 1) : Total L) ^ (n - j)
            * cmAscWord q 1 m ((MvPolynomial.X m : Total L) ^ (j + 1))) = 0 := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hterm (n - j) j d, ite_eq_right (by omega)]
      have hsup : d.support ⊆ Finset.range (m + 2) ↔ d.support ⊆ Finset.range (m + 1) := by
        constructor
        · intro h i hi
          have h1 := h hi
          rw [Finset.mem_range] at h1 ⊢
          have h2 : i ≠ m + 1 := fun hh => (Finsupp.mem_support_iff.1 hi) (hh ▸ hd1)
          omega
        · intro h i hi
          have h1 := h hi
          rw [Finset.mem_range] at h1 ⊢
          omega
      rw [Finset.sum_eq_zero hzero, mul_zero, add_zero, ih n d]
      by_cases hc : d.support ⊆ Finset.range (m + 1) ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0
      · rw [ite_eq_left hc, ite_eq_left ⟨hsup.2 hc.1, hc.2⟩, ← map_mul]
        refine congrArg (fun x : L => (MvPolynomial.C x : Sym.Lambda L)) ?_
        rw [trainWeight, trainWeight,
          show m + 1 - (d.support.erase 0).card = (m - (d.support.erase 0).card) + 1 from by
            have := card_erase_zero_le hc.1
            omega,
          pow_succ]
        ring
      · rw [ite_eq_right hc, ite_eq_right fun h => hc ⟨hsup.1 h.1, h.2⟩, mul_zero]
    · -- the top variable occurs: one term of the correction sum survives, costing a factor `q-1`
      have herase : d - Finsupp.single (m + 1) (d (m + 1)) = Finsupp.erase (m + 1) d := by
        ext i
        rw [Finsupp.tsub_apply, Finsupp.erase_apply]
        by_cases hi : i = m + 1
        · subst hi
          rw [ite_eq_left rfl, Finsupp.single_eq_same, Nat.sub_self]
        · rw [ite_eq_right hi, Finsupp.single_eq_of_ne hi, Nat.sub_zero]
      have hterm0 : ∀ j ∈ Finset.range n, n - j ≠ d (m + 1) →
          MvPolynomial.coeff d ((MvPolynomial.X (m + 1) : Total L) ^ (n - j)
            * cmAscWord q 1 m ((MvPolynomial.X m : Total L) ^ (j + 1))) = 0 := by
        intro j _ hne
        rw [hterm (n - j) j d]
        split_ifs with hle
        · refine hvanish j _ ?_
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        · rfl
      rw [hvanish n d hd1, mul_zero, zero_add]
      by_cases hcn : d (m + 1) ≤ n
      · have hmem : n - d (m + 1) ∈ Finset.range n := by
          rw [Finset.mem_range]
          omega
        rw [Finset.sum_eq_single_of_mem (n - d (m + 1)) hmem
          (fun b hb hne => hterm0 b hb (by rw [Finset.mem_range] at hb; omega)),
          hterm (n - (n - d (m + 1))) (n - d (m + 1)) d,
          ite_eq_left (by omega), show n - (n - d (m + 1)) = d (m + 1) from by omega, herase,
          ih (n - d (m + 1)) (Finsupp.erase (m + 1) d)]
        -- translate the shorter train's condition into this one
        have hz : (Finsupp.erase (m + 1) d) 0 = d 0 := Finsupp.erase_ne (by omega)
        have hsum : (d.sum fun _ e => e)
            = d (m + 1) + ((Finsupp.erase (m + 1) d).sum fun _ e => e) :=
          sum_eq_add_sum_erase (m + 1) d
        have hsupiff : (Finsupp.erase (m + 1) d).support ⊆ Finset.range (m + 1)
            ↔ d.support ⊆ Finset.range (m + 2) := by
          rw [Finsupp.support_erase]
          constructor
          · intro h i hi
            rw [Finset.mem_range]
            by_cases hie : i = m + 1
            · omega
            · have := h (Finset.mem_erase.2 ⟨hie, hi⟩)
              rw [Finset.mem_range] at this
              omega
          · intro h i hi
            obtain ⟨hie, hi'⟩ := Finset.mem_erase.1 hi
            have := h hi'
            rw [Finset.mem_range] at this ⊢
            omega
        have hmemsup : m + 1 ∈ d.support.erase 0 :=
          Finset.mem_erase.2 ⟨by omega, Finsupp.mem_support_iff.2 hd1⟩
        have hpos : 1 ≤ (d.support.erase 0).card := Finset.card_pos.2 ⟨_, hmemsup⟩
        obtain ⟨r, hrs⟩ : ∃ r, (d.support.erase 0).card = r + 1 :=
          ⟨(d.support.erase 0).card - 1, by omega⟩
        have hcomm : ((Finsupp.erase (m + 1) d).support.erase 0)
            = (d.support.erase 0).erase (m + 1) := by
          rw [Finsupp.support_erase]
          ext x
          simp only [Finset.mem_erase]
          tauto
        have hr : ((Finsupp.erase (m + 1) d).support.erase 0).card = r := by
          rw [hcomm, Finset.card_erase_of_mem hmemsup, hrs]
          omega
        by_cases hc : d.support ⊆ Finset.range (m + 2) ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0
        · obtain ⟨hc1, hc2, hc3⟩ := hc
          have hcond : (Finsupp.erase (m + 1) d).support ⊆ Finset.range (m + 1)
              ∧ ((Finsupp.erase (m + 1) d).sum fun _ e => e) = (n - d (m + 1)) + 1
              ∧ (Finsupp.erase (m + 1) d) 0 ≠ 0 := by
            refine ⟨hsupiff.2 hc1, by omega, ?_⟩
            rwa [hz]
          rw [ite_eq_left hcond, ite_eq_left ⟨hc1, hc2, hc3⟩, ← map_mul]
          refine congrArg (fun x : L => (MvPolynomial.C x : Sym.Lambda L)) ?_
          rw [trainWeight, trainWeight, hr, hrs, Nat.succ_sub_succ, pow_succ]
          ring
        · have hcond : ¬ ((Finsupp.erase (m + 1) d).support ⊆ Finset.range (m + 1)
              ∧ ((Finsupp.erase (m + 1) d).sum fun _ e => e) = (n - d (m + 1)) + 1
              ∧ (Finsupp.erase (m + 1) d) 0 ≠ 0) := by
            rintro ⟨h1, h2, h3⟩
            refine hc ⟨hsupiff.1 h1, by omega, ?_⟩
            rwa [hz] at h3
          rw [ite_eq_right hcond, ite_eq_right hc, mul_zero]
      · -- the top variable carries more than the available degree: nothing survives
        rw [Finset.sum_eq_zero fun b hb => hterm0 b hb (by rw [Finset.mem_range] at hb; omega),
          mul_zero]
        refine (ite_eq_right ?_).symm
        rintro ⟨-, hsd, hd0⟩
        have := apply_zero_add_apply_le_sum (i := m + 1) (by omega) d
        omega

/-! ### The closed form as a single sum of monomials -/

/-- The closed form of `HJO.Sweep.coeff_cmAscWord_one_X_self_pow` with the top variable written as
`y_{k+1}` rather than `X k`. -/
theorem coeff_cmAscWord_one_auxVar_last_pow_succ (q : L) (k n : ℕ) (d : ℕ →₀ ℕ) :
    MvPolynomial.coeff d (cmAscWord q 1 k ((auxVar (k + 1) : Total L) ^ (n + 1)))
      = if d.support ⊆ Finset.range (k + 1) ∧ (d.sum fun _ e => e) = n + 1 ∧ d 0 ≠ 0
          then MvPolynomial.C (trainWeight q k d) else 0 := by
  rw [show (auxVar (k + 1) : Total L) = MvPolynomial.X k from by rw [auxVar, Nat.add_sub_cancel],
    coeff_cmAscWord_one_X_self_pow q k n d]

/-- **`T_{1↗k+1}(y_{k+1}^{n+1}) = ∑_d(q-1)^{r(d)}q^{k-r(d)}y^d`**, the sum running over the exponent
vectors of total degree `n+1` supported on `y_1, …, y_{k+1}` in which `y_1` occurs, and `r(d)` being
the number of variables other than `y_1` that occur in `d`.

This is `HJO.Sweep.coeff_cmAscWord_one_auxVar_last_pow_succ` assembled into one polynomial, the
index set being `Finset.finsuppAntidiag` filtered by `d 0 ≠ 0`. Unconditional in `q`.

Exponent `0` is excluded because the statement would be false there: the train is the identity on
`1`, so the value is `1`, whereas the condition `d 0 ≠ 0` makes the sum empty. That case is
`HJO.Sweep.cmAscWord_one_auxVar_last_pow_zero_check`. -/
theorem cmAscWord_one_auxVar_last_pow_succ_eq_sum (q : L) (k n : ℕ) :
    cmAscWord q 1 k ((auxVar (k + 1) : Total L) ^ (n + 1))
      = ∑ d ∈ {d ∈ (Finset.range (k + 1)).finsuppAntidiag (n + 1) | d 0 ≠ 0},
          scal (trainWeight q k d) * MvPolynomial.monomial d (1 : Sym.Lambda L) := by
  refine MvPolynomial.ext _ _ fun e => ?_
  have hcoeff : ∀ d : ℕ →₀ ℕ,
      MvPolynomial.coeff e (scal (trainWeight q k d) * MvPolynomial.monomial d (1 : Sym.Lambda L))
        = if d = e then MvPolynomial.C (trainWeight q k d) else 0 := by
    intro d
    rw [scal, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  have hmem : e ∈ {d ∈ (Finset.range (k + 1)).finsuppAntidiag (n + 1) | d 0 ≠ 0}
      ↔ (e.support ⊆ Finset.range (k + 1) ∧ (e.sum fun _ x => x) = n + 1 ∧ e 0 ≠ 0) := by
    rw [Finset.mem_filter, Finset.mem_finsuppAntidiag']
    tauto
  rw [coeff_cmAscWord_one_auxVar_last_pow_succ, MvPolynomial.coeff_sum,
    Finset.sum_congr rfl fun d _ => hcoeff d,
    Finset.sum_ite_eq' _ e fun d => MvPolynomial.C (trainWeight q k d)]
  by_cases hc : e.support ⊆ Finset.range (k + 1) ∧ (e.sum fun _ x => x) = n + 1 ∧ e 0 ≠ 0
  · rw [ite_eq_left hc, ite_eq_left (hmem.2 hc)]
  · rw [ite_eq_right hc, ite_eq_right fun h => hc (hmem.1 h)]

/-- **The closed form with a symmetric factor riding through.** For `S` symmetric in
`y_1, …, y_{k+1}` the train is linear over `S` (`HJO.Sweep.cmAscWord_mul_of_swapAux_eq`), so
`HJO.Sweep.cmAscWord_one_auxVar_last_pow_succ_eq_sum` applies unchanged. This is the shape
`HJO.Sweep.corner` and `HJO.Sweep.dplus` present whenever the vector they are applied to is
symmetric; at `n + 1 = 1` it is `HJO.Sweep.cmAscWord_one_mul_auxVar_last` and at
`n + 1 = 2` it is `HJO.Sweep.cmAscWord_one_mul_auxVar_last_sq`. -/
theorem cmAscWord_one_mul_auxVar_last_pow_succ_eq_sum (q : L) (k n : ℕ) {S : Total L}
    (hS : ∀ j, 1 ≤ j → j ≤ k → swapAux L j S = S) :
    cmAscWord q 1 k (S * (auxVar (k + 1) : Total L) ^ (n + 1))
      = S * ∑ d ∈ {d ∈ (Finset.range (k + 1)).finsuppAntidiag (n + 1) | d 0 ≠ 0},
          scal (trainWeight q k d) * MvPolynomial.monomial d (1 : Sym.Lambda L) := by
  rw [cmAscWord_mul_of_swapAux_eq q (by omega) hS, cmAscWord_one_auxVar_last_pow_succ_eq_sum]

/-! ### Exponent vectors of small degree, and the agreement checks -/

/-- An exponent vector whose whole degree sits on `y_1` is a power of `y_1`. -/
theorem eq_single_zero_of_apply_zero_eq {d : ℕ →₀ ℕ} {N : ℕ}
    (hsum : (d.sum fun _ e => e) = N) (h0 : d 0 = N) : d = Finsupp.single 0 N := by
  have hrest : ((Finsupp.erase 0 d).sum fun _ e => e) = 0 := by
    rw [sum_eq_add_sum_erase 0 d, h0] at hsum
    omega
  ext i
  by_cases hi : i = 0
  · subst hi
    rw [Finsupp.single_eq_same, h0]
  · have h1 : (Finsupp.erase 0 d) i = 0 := by
      have := apply_le_sum i (Finsupp.erase 0 d)
      omega
    rw [Finsupp.erase_ne hi] at h1
    rw [Finsupp.single_eq_of_ne hi, h1]

/-- Total degree `0` forces the exponent vector to be `0`. -/
theorem eq_zero_of_sum_eq_zero {d : ℕ →₀ ℕ} (h : (d.sum fun _ e => e) = 0) : d = 0 := by
  ext i
  have := apply_le_sum i d
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- Total degree `1` forces the exponent vector to be a single variable. -/
theorem exists_eq_single_of_sum_eq_one {d : ℕ →₀ ℕ} (h : (d.sum fun _ e => e) = 1) :
    ∃ i, d = Finsupp.single i 1 := by
  have hne : d ≠ 0 := by
    intro h0
    rw [h0, Finsupp.sum_zero_index] at h
    exact absurd h (by omega)
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hne
  refine ⟨i, ?_⟩
  have hdi : d i = 1 := by
    have h1 := apply_le_sum i d
    have h2 := Finsupp.mem_support_iff.1 hi
    omega
  have hrest : Finsupp.erase i d = 0 := by
    refine eq_zero_of_sum_eq_zero ?_
    rw [sum_eq_add_sum_erase i d, hdi] at h
    omega
  conv_lhs => rw [← Finsupp.single_add_erase i d]
  rw [hrest, add_zero, hdi]

/-- **Agreement at exponent `1`.** The closed form reproves
`HJO.Sweep.cmAscWord_one_auxVar_last`: `T_{1↗k+1}(y_{k+1}) = q^ky_1`.

The only exponent vector of total degree `1` in which `y_1` occurs is `y_1` itself, whose `r` is
`0`, so the whole sum is the single term `q^ky_1`. Proved from
`HJO.Sweep.coeff_cmAscWord_one_auxVar_last_pow_succ` and nothing else, which is what makes it a
check on the closed form rather than a restatement. -/
theorem cmAscWord_one_auxVar_last_of_closed (q : L) (k : ℕ) :
    cmAscWord q 1 k (auxVar (k + 1) : Total L) = scal (q ^ k) * auxVar 1 := by
  have hX : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [show (auxVar (k + 1) : Total L) = (auxVar (k + 1) : Total L) ^ (0 + 1) from by
      rw [Nat.zero_add, pow_one],
    coeff_cmAscWord_one_auxVar_last_pow_succ q k 0 d, hX, scal, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X]
  by_cases hd : Finsupp.single (0 : ℕ) 1 = d
  · have hsupp : d.support.erase 0 = ∅ := by
      rw [← hd, Finsupp.support_single 0 (by omega)]
      simp
    have h1 : d.support ⊆ Finset.range (k + 1) := by
      rw [← hd, Finsupp.support_single 0 (by omega)]
      intro i hi
      rw [Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    have h2 : (d.sum fun _ e => e) = 0 + 1 := by
      have hs : ((Finsupp.single (0 : ℕ) 1).sum fun _ e => e) = 1 := Finsupp.sum_single_index rfl
      rw [← hd, hs]
    have h3 : d 0 ≠ 0 := by
      rw [← hd, Finsupp.single_eq_same]
      omega
    rw [ite_eq_left hd, mul_one, ite_eq_left ⟨h1, h2, h3⟩, trainWeight, hsupp]
    simp
  · rw [ite_eq_right hd, mul_zero, ite_eq_right]
    rintro ⟨-, hsum, h0⟩
    refine hd ?_
    have hd0 : d 0 = 1 := by
      have := apply_le_sum 0 d
      omega
    exact (eq_single_zero_of_apply_zero_eq hsum hd0).symm

/-! ### The weights of the degree-`≤ 2` exponent vectors -/

/-- The weight of `y_1^N`: its only variable is `y_1`, so `r = 0` and the weight is `q^k`. -/
theorem trainWeight_single_zero (q : L) (k : ℕ) {N : ℕ} (hN : N ≠ 0) :
    trainWeight q k (Finsupp.single 0 N) = q ^ k := by
  rw [trainWeight, Finsupp.support_single 0 hN]
  simp

/-- `y_1y_i` for `i ≠ 0` has exactly one variable other than `y_1`. -/
theorem support_erase_zero_single_add_single {i : ℕ} (hi : i ≠ 0) :
    (Finsupp.single (0 : ℕ) 1 + Finsupp.single i 1 : ℕ →₀ ℕ).support.erase 0 = {i} := by
  ext x
  rw [Finset.mem_erase, Finsupp.mem_support_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hx0, hxv⟩
    by_contra hxi
    refine hxv ?_
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hx0, Finsupp.single_eq_of_ne hxi]
    omega
  · rintro rfl
    refine ⟨hi, ?_⟩
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, Finsupp.single_eq_same]
    omega

/-- The weight of `y_1y_i` for `i ≠ 0`: `r = 1`, so the weight is `(q-1)q^{k-1}`. -/
theorem trainWeight_single_add_single (q : L) (k : ℕ) {i : ℕ} (hi : i ≠ 0) :
    trainWeight q k (Finsupp.single (0 : ℕ) 1 + Finsupp.single i 1 : ℕ →₀ ℕ)
      = (q - 1) * q ^ (k - 1) := by
  rw [trainWeight, support_erase_zero_single_add_single hi]
  simp

/-- `y_1^2` satisfies the closed form's condition at degree `2`, at every width. -/
theorem single_zero_two_mem (k : ℕ) :
    (Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ).support ⊆ Finset.range (k + 1)
      ∧ (((Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ).sum fun _ e => e) = 1 + 1)
      ∧ (Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ) 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finsupp.support_single 0 (by omega)]
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    omega
  · rw [Finsupp.sum_single_index rfl]
  · rw [Finsupp.single_eq_same]
    omega

/-- `y_1y_i` with `1 ≤ i ≤ k` satisfies the closed form's condition at degree `2` and width `k`. -/
theorem single_add_single_mem {i k : ℕ} (hi : i ≠ 0) (hik : i ≤ k) :
    (Finsupp.single (0 : ℕ) 1 + Finsupp.single i 1 : ℕ →₀ ℕ).support ⊆ Finset.range (k + 1)
      ∧ (((Finsupp.single (0 : ℕ) 1 + Finsupp.single i 1 : ℕ →₀ ℕ).sum fun _ e => e) = 1 + 1)
      ∧ (Finsupp.single (0 : ℕ) 1 + Finsupp.single i 1 : ℕ →₀ ℕ) 0 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rw [Finset.mem_range]
    by_cases hx0 : x = 0
    · omega
    · by_cases hxi : x = i
      · omega
      · refine absurd ?_ hx
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hx0, Finsupp.single_eq_of_ne hxi]
        omega
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Finsupp.sum_single_index rfl]
  · rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (0 : ℕ) ≠ i by omega)]
    omega

/-- **An exponent vector of total degree `2` in which `y_1` occurs is `y_1^2` or `y_1y_i`.** The
classification the degree-`2` agreement check runs over. -/
theorem eq_single_or_single_add_single_of_sum_eq_two {d : ℕ →₀ ℕ}
    (hsum : (d.sum fun _ e => e) = 2) (h0 : d 0 ≠ 0) :
    d = Finsupp.single 0 2 ∨ ∃ i, i ≠ 0 ∧ d = Finsupp.single 0 1 + Finsupp.single i 1 := by
  have hle := apply_le_sum 0 d
  by_cases h2 : d 0 = 2
  · exact Or.inl (eq_single_zero_of_apply_zero_eq hsum h2)
  · have hd0 : d 0 = 1 := by omega
    have hrest : ((Finsupp.erase 0 d).sum fun _ e => e) = 1 := by
      rw [sum_eq_add_sum_erase 0 d, hd0] at hsum
      omega
    obtain ⟨i, hi⟩ := exists_eq_single_of_sum_eq_one hrest
    have hi0 : i ≠ 0 := by
      intro h
      subst h
      have hz : (Finsupp.erase 0 d) 0 = 1 := by rw [hi, Finsupp.single_eq_same]
      rw [Finsupp.erase_same] at hz
      exact absurd hz (by omega)
    refine Or.inr ⟨i, hi0, ?_⟩
    conv_lhs => rw [← Finsupp.single_add_erase 0 d]
    rw [hi, hd0]

/-! ### The agreement check at exponent `2`, the first branching shape -/

/-- **Agreement at exponent `2`.** The closed form reproves
`HJO.Sweep.cmAscWord_one_auxVar_last_sq`:
`T_{1↗k+2}(y_{k+2}^2) = q^{k+1}y_1^2 + (q-1)q^ky_1(y_2 + ⋯ + y_{k+2})`.

This is the check the general formula has to pass. The exponent vectors of degree `2` in which `y_1`
occurs are `y_1^2`, with no other variable and so weight `q^{k+1}`, and the `k+1` vectors `y_1y_i`
with `2 ≤ i ≤ k+2`, each with exactly one other variable and so weight `(q-1)q^k` — one term per
position, all sharing one power of `q`, which is exactly what that statement says.

Proved from `HJO.Sweep.coeff_cmAscWord_one_auxVar_last_pow_succ` and the degree-`2` classification
`HJO.Sweep.eq_single_or_single_add_single_of_sum_eq_two`; that statement is not used, which is
what makes this a check on the closed form. -/
theorem cmAscWord_one_auxVar_last_sq_of_closed (q : L) (m : ℕ) :
    cmAscWord q 1 (m + 1) ((auxVar (m + 2) : Total L) ^ 2)
      = scal (q ^ (m + 1)) * (auxVar 1 : Total L) ^ 2
        + scal ((q - 1) * q ^ m) * ((auxVar 1 : Total L)
            * ∑ j ∈ Finset.range (m + 1), (auxVar (j + 2) : Total L)) := by
  have hX1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := by rw [auxVar]
  have hsumX : (∑ j ∈ Finset.range (m + 1), (auxVar (j + 2) : Total L))
      = ∑ j ∈ Finset.range (m + 1), (MvPolynomial.X (j + 1) : Total L) :=
    Finset.sum_congr rfl fun j _ => by rw [auxVar, show j + 2 - 1 = j + 1 from by omega]
  have hmono : ∀ i : ℕ, (MvPolynomial.X 0 : Total L) * MvPolynomial.X i
      = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single i 1) (1 : Sym.Lambda L) := by
    intro i
    have e0 : (MvPolynomial.X 0 : Total L) = MvPolynomial.monomial (Finsupp.single 0 1) 1 := by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    have ei : (MvPolynomial.X i : Total L) = MvPolynomial.monomial (Finsupp.single i 1) 1 := by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    rw [e0, ei, MvPolynomial.monomial_mul, mul_one]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [show (auxVar (m + 2) : Total L) ^ 2 = (auxVar (m + 1 + 1) : Total L) ^ (1 + 1) from by
      norm_num,
    coeff_cmAscWord_one_auxVar_last_pow_succ q (m + 1) 1 d, MvPolynomial.coeff_add, hX1, hsumX,
    scal, scal, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
    Finset.mul_sum, MvPolynomial.coeff_sum]
  by_cases hcond : d.support ⊆ Finset.range (m + 1 + 1) ∧ (d.sum fun _ e => e) = 1 + 1 ∧ d 0 ≠ 0
  · obtain ⟨hs, hsum, h0⟩ := hcond
    rw [ite_eq_left ⟨hs, hsum, h0⟩]
    rcases eq_single_or_single_add_single_of_sum_eq_two (by omega) h0 with hd | ⟨i, hi0, hd⟩
    · have hzero : ∀ j ∈ Finset.range (m + 1),
          MvPolynomial.coeff d ((MvPolynomial.X 0 : Total L) * MvPolynomial.X (j + 1)) = 0 := by
        intro j _
        rw [hmono (j + 1), MvPolynomial.coeff_monomial]
        refine ite_eq_right fun h => ?_
        have hev : (Finsupp.single (0 : ℕ) 1 + Finsupp.single (j + 1) 1 : ℕ →₀ ℕ) (j + 1)
            = d (j + 1) := by rw [h]
        rw [hd, Finsupp.add_apply, Finsupp.single_eq_of_ne (by omega : j + 1 ≠ (0 : ℕ)),
          Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by omega : j + 1 ≠ (0 : ℕ))] at hev
        exact absurd hev (by omega)
      rw [Finset.sum_eq_zero hzero, mul_zero, add_zero, ite_eq_left hd.symm, mul_one, hd,
        trainWeight_single_zero q (m + 1) (by omega)]
    · have hiu : i ≤ m + 1 := by
        have hmi : i ∈ d.support := by
          rw [Finsupp.mem_support_iff, hd, Finsupp.add_apply, Finsupp.single_eq_of_ne hi0,
            Finsupp.single_eq_same]
          omega
        have hr := hs hmi
        rw [Finset.mem_range] at hr
        omega
      have hne2 : ¬ ((Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ) = d) := by
        intro h
        have hev : (Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ) i = d i := by rw [h]
        rw [hd, Finsupp.single_eq_of_ne hi0, Finsupp.add_apply, Finsupp.single_eq_of_ne hi0,
          Finsupp.single_eq_same] at hev
        exact absurd hev (by omega)
      have hmem : i - 1 ∈ Finset.range (m + 1) := by
        rw [Finset.mem_range]
        omega
      have hother : ∀ b ∈ Finset.range (m + 1), b ≠ i - 1 →
          MvPolynomial.coeff d ((MvPolynomial.X 0 : Total L) * MvPolynomial.X (b + 1)) = 0 := by
        intro b _ hb
        rw [hmono (b + 1), MvPolynomial.coeff_monomial]
        refine ite_eq_right fun h => ?_
        have hev : (Finsupp.single (0 : ℕ) 1 + Finsupp.single (b + 1) 1 : ℕ →₀ ℕ) (b + 1)
            = d (b + 1) := by rw [h]
        rw [hd, Finsupp.add_apply, Finsupp.add_apply,
          Finsupp.single_eq_of_ne (by omega : b + 1 ≠ (0 : ℕ)), Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by omega : b + 1 ≠ i)] at hev
        exact absurd hev (by omega)
      have hlive : MvPolynomial.coeff d
          ((MvPolynomial.X 0 : Total L) * MvPolynomial.X (i - 1 + 1)) = 1 := by
        rw [hmono (i - 1 + 1), MvPolynomial.coeff_monomial]
        exact ite_eq_left (by rw [hd, show i - 1 + 1 = i from by omega])
      rw [ite_eq_right hne2, mul_zero, zero_add,
        Finset.sum_eq_single_of_mem (i - 1) hmem hother, hlive, mul_one, hd,
        trainWeight_single_add_single q (m + 1) hi0, Nat.add_sub_cancel]
  · have hne2 : ¬ ((Finsupp.single (0 : ℕ) 2 : ℕ →₀ ℕ) = d) := by
      rintro rfl
      exact hcond (single_zero_two_mem (m + 1))
    have hzero : ∀ j ∈ Finset.range (m + 1),
        MvPolynomial.coeff d ((MvPolynomial.X 0 : Total L) * MvPolynomial.X (j + 1)) = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hmono (j + 1), MvPolynomial.coeff_monomial]
      refine ite_eq_right fun h => ?_
      subst h
      exact hcond (single_add_single_mem (by omega) (by omega))
    rw [Finset.sum_eq_zero hzero, mul_zero, add_zero, ite_eq_right hne2, mul_zero,
      ite_eq_right hcond]

end Field

end HJO.Sweep

end
