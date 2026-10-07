/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.PowerRing
public meta import HJO.Attr

/-! # Insertion shifts the merged variables

The insertion `Φ_k : P_k → P_{k+1}` of `HJO.Sym.insertFront` substitutes the new auxiliary
variable `y_{k+1}` for the first letter `x₁` and pushes every later letter down by one, leaving
the old auxiliary variables alone. The merged variables `z^{(k)}_j` of `HJO.Sym.zvar` are exactly
the family that reads `y_j` below the level `k` and `x_{j-k}` above it, so `Φ_k` carries the family
at the level `k` to the family at the level `k+1`, label by label: below the level nothing moves,
at the level the first letter becomes the new auxiliary variable, and above it the drop of the
letter index is cancelled by the rise of the level.

## Main results

* `HJO.Sym.insertFront_zvar`: `Φ_k(z^{(k)}_j) = z^{(k+1)}_j` for every level `k` and every label
  `j`.

## Implementation notes

Labels are indexed from `0` here, so the range `j ≥ 1` of the `1`-based labelling is the whole of
`ℕ` and the statement carries no hypothesis on `j`; the three cases `j ≤ k`, `j = k+1`, `j > k+1`
of the `1`-based labelling are the three cases `j < k`, `j = k`, `k < j` below.

The proof is coefficientwise, through `HJO.Sym.coeff_insertFront`, and goes through the value of
`Φ_k` on the three kinds of generator the merged variables are: a constant `C p`, the first letter
`X 0`, and a later letter `X (m+1)`. In each case the defining `finsum` has at most one nonzero
term — the letter-monomial index of that term is `Finsupp.single 0 a + e.mapDomain Nat.succ`, whose
value is `a` at the first letter and `e n` at the letter `n+1`, so matching it against a monomial
pins down both `a` and `e` — and the sum is evaluated by `finsum_eq_single` or is identically zero.
Those three values are stated as private lemmas rather than as API: `insertFront` is the total
extension by `0` of the substitution (see `HJO.Sym.insertFront`), and
`HJO.Sym.not_injective_insertFront` records that the extension is not the substitution everywhere.

## References

E. Carlsson and
A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697,
Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K]

/-! ### The letter-monomial index of the defining sum -/

/-- The index `x₁^a` times `e` pushed up one letter, read at the first letter: it is the exponent
`a` of the first letter, the pushed-up monomial being supported away from it. -/
private theorem insertZvar_index_apply_zero (a : ℕ) (e : ℕ →₀ ℕ) :
    (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) 0 = a := by
  have hmap : (e.mapDomain Nat.succ) 0 = 0 :=
    Finsupp.mapDomain_of_notMem_range e 0 (by simp)
  rw [Finsupp.add_apply, Finsupp.single_eq_same, hmap, add_zero]

/-- The index `x₁^a` times `e` pushed up one letter, read at the letter `n+1`: it is `e n`, the
exponent the first letter contributes being carried at the index `0` alone. -/
private theorem insertZvar_index_apply_succ (a : ℕ) (e : ℕ →₀ ℕ) (n : ℕ) :
    (Finsupp.single 0 a + e.mapDomain Nat.succ : ℕ →₀ ℕ) (n + 1) = e n := by
  have hmap : (e.mapDomain Nat.succ) (n + 1) = e n :=
    Finsupp.mapDomain_apply Nat.succ_injective e n
  have hsingle : (Finsupp.single (0 : ℕ) a) (n + 1) = 0 := Finsupp.single_eq_of_ne (by omega)
  rw [Finsupp.add_apply, hsingle, hmap, zero_add]

/-! ### The insertion on the generators the merged variables are -/

/-- `Φ_k` on a constant series: it renames the old auxiliary variables into the first `k` of the
new ones. Only the empty letter-monomial contributes, and there only the term `a = 0`. -/
private theorem insertZvar_insertFront_C (k : ℕ) (p : MvPolynomial (Fin k) K) :
    insertFront K k (MvPowerSeries.C p) =
      MvPowerSeries.C (MvPolynomial.rename Fin.castSucc p) := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront]
  by_cases he : e = 0
  · subst he
    have hzero : ∀ a : ℕ, a ≠ 0 →
        MvPolynomial.X (Fin.last k) ^ a *
            MvPolynomial.rename Fin.castSucc
              (MvPowerSeries.coeff (Finsupp.single 0 a + (0 : ℕ →₀ ℕ).mapDomain Nat.succ)
                (MvPowerSeries.C p)) = 0 := by
      intro a ha
      have hidx : Finsupp.single 0 a + (0 : ℕ →₀ ℕ).mapDomain Nat.succ ≠ 0 := by
        rw [Finsupp.mapDomain_zero, add_zero]
        simpa using ha
      rw [MvPowerSeries.coeff_C_of_ne_zero hidx, map_zero, mul_zero]
    rw [finsum_eq_single _ 0 hzero, Finsupp.mapDomain_zero, add_zero, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_C, pow_zero, one_mul]
  · obtain ⟨n, hn⟩ := Finsupp.ne_iff.1 he
    replace hn : e n ≠ 0 := by simpa using hn
    rw [MvPowerSeries.coeff_C_of_ne_zero he]
    refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
    have hidx : Finsupp.single 0 a + e.mapDomain Nat.succ ≠ 0 := by
      intro hcon
      have h2 := insertZvar_index_apply_succ a e n
      rw [hcon] at h2
      exact hn (by simpa using h2.symm)
    rw [MvPowerSeries.coeff_C_of_ne_zero hidx, map_zero, mul_zero]

/-- `Φ_k` on the first letter: it becomes the new auxiliary variable `y_{k+1}`, a constant of
`P_{k+1}`. Only the empty letter-monomial contributes, and there only the term `a = 1`. -/
private theorem insertZvar_insertFront_X_zero (k : ℕ) :
    insertFront K k (MvPowerSeries.X 0) = MvPowerSeries.C (MvPolynomial.X (Fin.last k)) := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront]
  by_cases he : e = 0
  · subst he
    have hzero : ∀ a : ℕ, a ≠ 1 →
        MvPolynomial.X (Fin.last k) ^ a *
            MvPolynomial.rename Fin.castSucc
              (MvPowerSeries.coeff (Finsupp.single 0 a + (0 : ℕ →₀ ℕ).mapDomain Nat.succ)
                (MvPowerSeries.X 0 : AuxAlphabetSeries K k)) = 0 := by
      intro a ha
      have hidx : Finsupp.single 0 a + (0 : ℕ →₀ ℕ).mapDomain Nat.succ ≠
          Finsupp.single 0 1 := by
        rw [Finsupp.mapDomain_zero, add_zero]
        intro hcon
        exact ha (by simpa using congrArg (fun f => f 0) hcon)
      rw [MvPowerSeries.coeff_X, ite_eq_right hidx, map_zero, mul_zero]
    rw [finsum_eq_single _ 1 hzero, Finsupp.mapDomain_zero, add_zero,
      MvPowerSeries.coeff_index_single_self_X, MvPowerSeries.coeff_zero_C, map_one, pow_one,
      mul_one]
  · obtain ⟨n, hn⟩ := Finsupp.ne_iff.1 he
    replace hn : e n ≠ 0 := by simpa using hn
    rw [MvPowerSeries.coeff_C_of_ne_zero he]
    refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
    have hidx : Finsupp.single 0 a + e.mapDomain Nat.succ ≠ Finsupp.single 0 1 := by
      intro hcon
      have h2 := insertZvar_index_apply_succ a e n
      have h3 : (Finsupp.single (0 : ℕ) (1 : ℕ)) (n + 1) = 0 := Finsupp.single_eq_of_ne (by omega)
      rw [hcon, h3] at h2
      exact hn h2.symm
    rw [MvPowerSeries.coeff_X, ite_eq_right hidx, map_zero, mul_zero]

/-- `Φ_k` on a letter other than the first: it drops down one place. Only the letter-monomial
`e = x_{m+1}` contributes, and there only the term `a = 0`. -/
private theorem insertZvar_insertFront_X_succ (k m : ℕ) :
    insertFront K k (MvPowerSeries.X (m + 1)) = MvPowerSeries.X m := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_insertFront]
  by_cases he : e = Finsupp.single m 1
  · subst he
    have hzero : ∀ a : ℕ, a ≠ 0 →
        MvPolynomial.X (Fin.last k) ^ a *
            MvPolynomial.rename Fin.castSucc
              (MvPowerSeries.coeff
                (Finsupp.single 0 a + (Finsupp.single m 1 : ℕ →₀ ℕ).mapDomain Nat.succ)
                (MvPowerSeries.X (m + 1) : AuxAlphabetSeries K k)) = 0 := by
      intro a ha
      have hidx : Finsupp.single 0 a + (Finsupp.single m 1 : ℕ →₀ ℕ).mapDomain Nat.succ ≠
          Finsupp.single (m + 1) 1 := by
        intro hcon
        have h2 := insertZvar_index_apply_zero a (Finsupp.single m 1)
        have h3 : (Finsupp.single (m + 1) (1 : ℕ)) (0 : ℕ) = 0 :=
          Finsupp.single_eq_of_ne (by omega)
        rw [hcon, h3] at h2
        exact ha h2.symm
      rw [MvPowerSeries.coeff_X, ite_eq_right hidx, map_zero, mul_zero]
    have hidx : Finsupp.single 0 0 + (Finsupp.single m 1 : ℕ →₀ ℕ).mapDomain Nat.succ =
        Finsupp.single (m + 1) 1 := by
      rw [Finsupp.single_zero, zero_add, Finsupp.mapDomain_single]
    rw [finsum_eq_single _ 0 hzero, hidx, MvPowerSeries.coeff_index_single_self_X,
      MvPowerSeries.coeff_index_single_self_X, map_one, pow_zero, one_mul]
  · rw [MvPowerSeries.coeff_X, ite_eq_right he]
    refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
    have hidx : Finsupp.single 0 a + e.mapDomain Nat.succ ≠ Finsupp.single (m + 1) 1 := by
      intro hcon
      refine he (Finsupp.ext fun n => ?_)
      have h2 := insertZvar_index_apply_succ a e n
      rw [hcon] at h2
      rw [← h2, Finsupp.single_apply, Finsupp.single_apply]
      simp
    rw [MvPowerSeries.coeff_X, ite_eq_right hidx, map_zero, mul_zero]

/-! ### Insertion shifts the merged variables -/

/-- **Insertion shifts the merged variables**: `Φ_k(z^{(k)}_j) = z^{(k+1)}_j` for every level `k`
and every label `j`. Below the level both sides are the auxiliary variable `y_{j+1}`, which the
insertion renames into the new alphabet of auxiliary variables without moving it; at the level the
variable `z^{(k)}_{k+1} = x_1` of the `1`-based labelling becomes the new auxiliary variable
`y_{k+1} = z^{(k+1)}_{k+1}`; and above the level the drop of the letter index under `Φ_k` cancels
the rise of the level. The hypothesis `j ≥ 1` of the `1`-based labelling is vacuous here, labels
being indexed from `0`, so no hypothesis on `j` is carried. -/
@[hjo "lem_cm_insert_zvar"]
theorem insertFront_zvar (k j : ℕ) : insertFront K k (zvar K k j) = zvar K (k + 1) j := by
  rcases lt_trichotomy j k with h | h | h
  · rw [zvar_of_lt h, zvar_of_lt (show j < k + 1 by omega), insertZvar_insertFront_C,
      MvPolynomial.rename_X]
    rfl
  · subst h
    rw [zvar_self, zvar_of_lt (Nat.lt_succ_self j), insertZvar_insertFront_X_zero]
    rfl
  · rw [zvar_of_le h.le, zvar_of_le (show k + 1 ≤ j by omega),
      show j - k = (j - (k + 1)) + 1 by omega, insertZvar_insertFront_X_succ]

end HJO.Sym
