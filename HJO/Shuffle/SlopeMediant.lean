/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SlopeWord
public meta import HJO.Attr

/-! # The Stern–Brocot recursion for Mellit's slope word

Mellit's Section 6 asserts, with "it is easy to see" and no computation, that the slope word
`β_{m,n}` "can be computed recursively using the extended Euclidean algorithm". The two lemmas that
make that precise are `HJO.Mellit.slopeWord_mediant` and
`HJO.Mellit.slopeWord_mediant_rev`: if `(m₁, n₁)` and `(m₂, n₂)` are coprime pairs with
`m₂ n₁ - m₁ n₂ = 1` — the two Stern–Brocot parents of their mediant — then

* `β_{m₁+m₂,\,n₁+n₂} = β_{m₂,n₂}\, 𝗒 𝗓\, β_{m₁,n₁}`, and
* `β_{m₁+m₂,\,n₁+n₂} = β_{m₁,n₁}\, 𝗓 𝗒\, β_{m₂,n₂}`.

Both orders are needed: `HJO.Mellit.euclid` uses the first for the third of its three operators and
the second for the other two, and its induction does not close from either alone.

## Main results

* `HJO.Mellit.slopeWord_mediant`.
* `HJO.Mellit.slopeWord_mediant_rev`.

## Implementation notes

The proof is a fractional-part computation over `ℚ`: it writes `im/M` as
`im₁/M₁ + i/(MM₁)`, reads off the fractional part, and multiplies back by `M`. Over `ℕ` the same
content is the pair of *exact* identities

* `M₁ · ϱ_{m,n}(i) = M · ϱ_{m₁,n₁}(i) + i` for `1 ≤ i ≤ M₁ - 2` (`slopeResidue_left_eq`), and
* `M₂ · ϱ_{m,n}(i) + i = M · ϱ_{m₂,n₂}(i)` for `1 ≤ i ≤ M₂ - 2` (`slopeResidue_right_eq`),

each proved by exhibiting the right-hand side's quotient and identifying it with the residue
through `HJO.Mellit.eq_slopeResidue_iff`. Both are stated with *abstract* `M`, `M₁`, `M₂` and the
one Bézout identity they consume, rather than at `M₁ = m₁ + n₁`: the same two lemmas then serve
both mediant orders, which swap the roles of the two parents. That is why the arithmetic below
takes `m * M₁ = m₁ * M + 1` and `m * M₂ + 1 = m₂ * M` as hypotheses instead of deriving them —
they are derived once, in `slopeWord_mediant`, and fed to both.

No division and no subtraction of residues occurs. Every inequality is put in the
`x + 1 ≤ y` form, because truncated `ℕ` subtraction makes `x ≤ y - 1` *true* at `y = 0`, where the
condition `x + 1 ≤ y` is false.

The two index shifts `ϱ_{m,n}(M₁ + i) = ϱ_{m,n}(i) + 1` and `ϱ_{m,n}(M₂ + i) + 1 = ϱ_{m,n}(i)`
are `slopeResidue_shift_up` and `slopeResidue_shift_down`. Each needs a bound saying the shifted
value stays inside `{1, …, M-1}`, and those bounds are `slopeResidue_add_two_le` and
`two_le_slopeResidue` — they are *not* automatic, and the second of them is exactly the step one
argues informally by "that value is an integer greater than `M/M₂ > 1`, hence at least `2`".

`slopeWord_eq_append` isolates the list combinatorics from the arithmetic and is stated with the
two middle letters left as `λ(P)` and `λ(P-1)`, so that one lemma serves both orders: the mediant
reads it with `(p, q) = (m₁, n₁)` and the reversed mediant with `(p, q) = (m₂, n₂)`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 6: the recursive computation of
the slope word, made precise as `HJO.Mellit.slopeWord_mediant` and
`HJO.Mellit.slopeWord_mediant_rev`. The slope word itself is defined in
`HJO/Shuffle/SlopeWord.lean`.
-/

@[expose] public section

namespace HJO.Mellit

/-! ### The residue of a mediant, computed from the residue at a parent -/

/-- **The residue at the mediant, from the residue at the first parent.** If `M = M₁ + M₂` is the
denominator sum, `m + n = M`, and `m M₁ = m₁ M + 1`, then for `1 ≤ i ≤ M₁ - 2` and `r` any
representative of `i m₁` modulo `M₁` in `{1, …, M₁ - 1}`,
`M₁ · ϱ_{m,n}(i) = M · r + i`.

This is the `ϱ_{m,n}(i) = (Mr + i)/M₁` of part (1) of the proof of
`HJO.Mellit.slopeWord_mediant`, in a form with no division: the quotient
`s := (Mr + i)/M₁` exists because `m M₁ = m₁ M + 1` makes `Mr + i ≡ M₁(im) (mod M₁)`, it lies in
`{1, …, M-1}` because `r ≤ M₁ - 1` and `i < M`, and it is congruent to `im` modulo `M` because
`m M₁ ≡ 1 (mod M)`. `eq_slopeResidue_iff` then identifies it with the residue. -/
theorem slopeResidue_left_eq {m n m₁ M M₁ M₂ i r : ℕ}
    (hM : M = M₁ + M₂) (hM₂ : 2 ≤ M₂) (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hB : m * M₁ = m₁ * M + 1)
    (hr2 : r + 1 ≤ M₁) (hrmod : r ≡ i * m₁ [MOD M₁]) (hi1 : 1 ≤ i) (hi2 : i + 2 ≤ M₁) :
    M₁ * slopeResidue m n i = M * r + i := by
  have hdvd : M₁ ∣ M * r + i := by
    have e : M * r + i ≡ M₁ * (i * m) [MOD M₁] := by
      calc M * r + i ≡ M * (i * m₁) + i [MOD M₁] := (Nat.ModEq.mul_left M hrmod).add_right i
        _ = i * (m₁ * M + 1) := by ring
        _ = i * (m * M₁) := by rw [← hB]
        _ = M₁ * (i * m) := by ring
    have h0 : (M * r + i) % M₁ = 0 := by
      rw [Nat.ModEq] at e
      rw [e, Nat.mul_mod_right]
    exact Nat.dvd_of_mod_eq_zero h0
  obtain ⟨s, hs⟩ := hdvd
  have h1 : M * r + M ≤ M₁ * M := by
    calc M * r + M = M * (r + 1) := by ring
      _ ≤ M * M₁ := Nat.mul_le_mul_left M hr2
      _ = M₁ * M := by ring
  have hslt : s < M := Nat.lt_of_mul_lt_mul_left (show M₁ * s < M₁ * M by omega)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, Nat.mul_zero] at hs
      omega
    · exact h
  have hcong : s ≡ i * m [MOD M] := by
    have e1 : m * M₁ * s = M * (m₁ * s) + s := by rw [hB]; ring
    have e2 : m * (M * r + i) = M * (m * r) + m * i := by ring
    change s % M = (i * m) % M
    calc s % M = (M * (m₁ * s) + s) % M := (Nat.mul_add_mod _ _ _).symm
      _ = (m * M₁ * s) % M := by rw [e1]
      _ = (m * (M₁ * s)) % M := by rw [Nat.mul_assoc]
      _ = (m * (M * r + i)) % M := by rw [← hs]
      _ = (M * (m * r) + m * i) % M := by rw [e2]
      _ = (m * i) % M := Nat.mul_add_mod _ _ _
      _ = (i * m) % M := by rw [Nat.mul_comm]
  have heq : s = slopeResidue m n i := by
    rw [eq_slopeResidue_iff hcop hm hn hi1 (by omega)]
    refine ⟨hs1, by omega, ?_⟩
    rw [hmn]
    exact hcong
  rw [← heq, hs]

/-- **The residue at the mediant, from the residue at the second parent.** If `M = M₁ + M₂`,
`m + n = M`, and `m M₂ + 1 = m₂ M`, then for `1 ≤ i ≤ M₂ - 2` and `r` a representative of `i m₂`
modulo `M₂` in `{1, …, M₂ - 1}`, `M₂ · ϱ_{m,n}(i) + i = M · r`.

This is the `ϱ_{m,n}(i) = (Mr - i)/M₂` of part (3), again with no division: the
quotient is `(Mr)/M₂`, and `m M₂ + 1 = m₂ M` is what makes `Mr` leave remainder exactly `i`. -/
theorem slopeResidue_right_eq {m n m₂ M M₁ M₂ i r : ℕ}
    (hM : M = M₁ + M₂) (hM₁ : 2 ≤ M₁) (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hC : m * M₂ + 1 = m₂ * M)
    (hr1 : 1 ≤ r) (hr2 : r + 1 ≤ M₂) (hrmod : r ≡ i * m₂ [MOD M₂]) (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ M₂) :
    M₂ * slopeResidue m n i + i = M * r := by
  have hmod : (M * r) % M₂ = i := by
    have e : M * r ≡ M₂ * (i * m) + i [MOD M₂] := by
      calc M * r ≡ M * (i * m₂) [MOD M₂] := Nat.ModEq.mul_left M hrmod
        _ = i * (m₂ * M) := by ring
        _ = i * (m * M₂ + 1) := by rw [hC]
        _ = M₂ * (i * m) + i := by ring
    rw [Nat.ModEq] at e
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hsplit : M₂ * (M * r / M₂) + i = M * r := by
    have h := Nat.div_add_mod (M * r) M₂
    rw [hmod] at h
    exact h
  set t := M * r / M₂ with ht
  have hMr : M * r + M ≤ M₂ * M := by
    calc M * r + M = M * (r + 1) := by ring
      _ ≤ M * M₂ := Nat.mul_le_mul_left M hr2
      _ = M₂ * M := by ring
  have htlt : t < M := Nat.lt_of_mul_lt_mul_left (show M₂ * t < M₂ * M by omega)
  have hMone : M ≤ M * r := Nat.le_mul_of_pos_right M hr1
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero] at hsplit
      omega
    · exact h
  have key : M * (m * r) + t = M * (m₂ * t) + m * i := by
    have e : m * (M₂ * t + i) + t = M * (m₂ * t) + m * i := by
      calc m * (M₂ * t + i) + t = (m * M₂ + 1) * t + m * i := by ring
        _ = m₂ * M * t + m * i := by rw [hC]
        _ = M * (m₂ * t) + m * i := by ring
    rw [hsplit] at e
    calc M * (m * r) + t = m * (M * r) + t := by ring
      _ = _ := e
  have hcong : t ≡ i * m [MOD M] := by
    change t % M = (i * m) % M
    calc t % M = (M * (m * r) + t) % M := (Nat.mul_add_mod _ _ _).symm
      _ = (M * (m₂ * t) + m * i) % M := by rw [key]
      _ = (m * i) % M := Nat.mul_add_mod _ _ _
      _ = (i * m) % M := by rw [Nat.mul_comm]
  have heq : t = slopeResidue m n i := by
    rw [eq_slopeResidue_iff hcop hm hn hi1 (by omega)]
    refine ⟨ht1, by omega, ?_⟩
    rw [hmn]
    exact hcong
  rw [← heq]
  exact hsplit

/-- **The residue at the mediant is at least `2` on the first parent's range.** From
`M₁ s = M r + i` with `r ≥ 1`, `i ≥ 1` and `M₁ < M` one gets `M₁ s > M₁`, hence `s ≥ 2`. The
reversed mediant needs this: it reads `ϱ_{m,n}(M₂ + i)` as `ϱ_{m,n}(i) - 1`, which is only in
range because `ϱ_{m,n}(i) ≥ 2`. -/
theorem two_le_slopeResidue {M M₁ i r s : ℕ} (hlt : M₁ < M) (hr1 : 1 ≤ r) (hi1 : 1 ≤ i)
    (h : M₁ * s = M * r + i) : 2 ≤ s := by
  have hMone : M ≤ M * r := Nat.le_mul_of_pos_right M hr1
  exact Nat.lt_of_mul_lt_mul_left (show M₁ * 1 < M₁ * s by rw [Nat.mul_one]; omega)

/-- **The residue at the mediant is at most `M - 2` on the second parent's range.** From
`M₂ t + i = M r` with `1 ≤ r ≤ M₂ - 1`, `i ≥ 1`, `M₂ < M` and `t < M` the value `t = M - 1` is
impossible: it would give `M (M₂ - r) = M₂ - i`, whose left side is at least `M` and whose right
side is less than `M₂ < M`. This is the "the sum being at most `M-1`", and it is what
lets `ϱ_{m,n}(M₁ + i) = ϱ_{m,n}(i) + 1` stay inside the residue range. -/
theorem slopeResidue_add_two_le {M M₂ i r t : ℕ} (hlt : M₂ < M) (hr2 : r + 1 ≤ M₂) (hi1 : 1 ≤ i)
    (htlt : t < M) (h : M₂ * t + i = M * r) : t + 2 ≤ M := by
  by_contra hcon
  have htM : t + 1 = M := by omega
  obtain ⟨d, hd, hd1⟩ : ∃ d, M₂ = r + d ∧ 1 ≤ d := ⟨M₂ - r, by omega, by omega⟩
  have e1 : M * M₂ = M * r + M * d := by rw [hd]; ring
  have e2 : M₂ * M = M₂ * t + M₂ := by rw [← htM]; ring
  have e3 : M * M₂ = M₂ * M := by ring
  have hMd : M ≤ M * d := Nat.le_mul_of_pos_right M hd1
  omega

/-! ### The two index shifts -/

/-- **Shifting the index up by `M₁` adds one to the residue.** If `m M₁ = m₁ M + 1` then
`M₁ m ≡ 1 (mod M)`, so `ϱ_{m,n}(M₁ + i) = ϱ_{m,n}(i) + 1` as soon as both indices are in range.
The part (3) uses this after computing `ϱ_{m,n}(i)` itself. -/
theorem slopeResidue_shift_up {m n m₁ M M₁ i : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hB : m * M₁ = m₁ * M + 1)
    (hi1 : 1 ≤ i) (hidx : M₁ + i + 1 ≤ M) (hbd : slopeResidue m n i + 2 ≤ M) :
    slopeResidue m n (M₁ + i) = slopeResidue m n i + 1 := by
  have ht : slopeResidue m n i ≡ i * m [MOD M] := by
    have h := slopeResidue_modEq m n i
    rwa [hmn] at h
  have e : (M₁ + i) * m = M * m₁ + (1 + i * m) := by
    calc (M₁ + i) * m = m * M₁ + i * m := by ring
      _ = m₁ * M + 1 + i * m := by rw [hB]
      _ = M * m₁ + (1 + i * m) := by ring
  have heq : slopeResidue m n i + 1 = slopeResidue m n (M₁ + i) := by
    rw [eq_slopeResidue_iff hcop hm hn (by omega) (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmn]
    change (slopeResidue m n i + 1) % M = ((M₁ + i) * m) % M
    calc (slopeResidue m n i + 1) % M = (1 + slopeResidue m n i) % M := by rw [Nat.add_comm]
      _ = (1 + i * m) % M := Nat.ModEq.add_left 1 ht
      _ = (M * m₁ + (1 + i * m)) % M := (Nat.mul_add_mod _ _ _).symm
      _ = ((M₁ + i) * m) % M := by rw [e]
  exact heq.symm

/-- **Shifting the index up by `M₂` subtracts one from the residue.** If `m M₂ + 1 = m₂ M` then
`M₂ m ≡ -1 (mod M)`, so `ϱ_{m,n}(M₂ + i) + 1 = ϱ_{m,n}(i)` as soon as both indices are in range
and the residue at `i` is at least `2`. The statement is an addition rather than a subtraction
because truncated `ℕ` subtraction would make it hold vacuously at `ϱ_{m,n}(i) = 0`. -/
theorem slopeResidue_shift_down {m n m₂ M M₂ i s : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hC : m * M₂ + 1 = m₂ * M)
    (hi1 : 1 ≤ i) (hidx : M₂ + i + 1 ≤ M) (hs : slopeResidue m n i = s + 1) (hs1 : 1 ≤ s) :
    slopeResidue m n (M₂ + i) = s := by
  have ht : slopeResidue m n i ≡ i * m [MOD M] := by
    have h := slopeResidue_modEq m n i
    rwa [hmn] at h
  have hslt : slopeResidue m n i < M := by
    have h := slopeResidue_lt (show 0 < m + n by omega) i
    omega
  have e : (M₂ + i) * m + 1 = M * m₂ + i * m := by
    calc (M₂ + i) * m + 1 = m * M₂ + 1 + i * m := by ring
      _ = m₂ * M + i * m := by rw [hC]
      _ = M * m₂ + i * m := by ring
  have hA : s + 1 ≡ i * m [MOD M] := by rw [← hs]; exact ht
  have hB2 : (M₂ + i) * m + 1 ≡ i * m [MOD M] := by
    change ((M₂ + i) * m + 1) % M = (i * m) % M
    calc ((M₂ + i) * m + 1) % M = (M * m₂ + i * m) % M := by rw [e]
      _ = (i * m) % M := Nat.mul_add_mod _ _ _
  have heq : s = slopeResidue m n (M₂ + i) := by
    rw [eq_slopeResidue_iff hcop hm hn (by omega) (by omega)]
    refine ⟨hs1, by omega, ?_⟩
    rw [hmn]
    exact Nat.ModEq.add_right_cancel' 1 (hA.trans hB2.symm)
  exact heq.symm

/-! ### The four residues at the two junction indices -/

/-- **`ϱ_{m,n}(M₁) = 1`.** Immediate from `m M₁ = m₁ M + 1`, which says `M₁ m ≡ 1 (mod M)`. -/
theorem slopeResidue_at_junction {m n m₁ M M₁ : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hB : m * M₁ = m₁ * M + 1)
    (hM₁ : 1 ≤ M₁) (hidx : M₁ + 1 ≤ M) : slopeResidue m n M₁ = 1 := by
  have e : M * m₁ + 1 = M₁ * m := by
    calc M * m₁ + 1 = m₁ * M + 1 := by ring
      _ = m * M₁ := hB.symm
      _ = M₁ * m := by ring
  have heq : 1 = slopeResidue m n M₁ := by
    rw [eq_slopeResidue_iff hcop hm hn hM₁ (by omega)]
    refine ⟨le_rfl, by omega, ?_⟩
    rw [hmn]
    change 1 % M = (M₁ * m) % M
    calc 1 % M = (M * m₁ + 1) % M := (Nat.mul_add_mod _ _ _).symm
      _ = (M₁ * m) % M := by rw [e]
  exact heq.symm

/-- **`ϱ_{m,n}(M₁ - 1) = n + 1`.** Here `(M₁ - 1)m ≡ 1 - m (mod M)` and `n + 1 + m = M + 1`, so
the two agree modulo `M`; the value is in range because `m ≥ 2`. -/
theorem slopeResidue_at_junction_pred {m n m₁ M M₁ i : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 2 ≤ m) (hn : 1 ≤ n) (hB : m * M₁ = m₁ * M + 1)
    (hi : M₁ = i + 1) (hi1 : 1 ≤ i) (hidx : M₁ + 1 ≤ M) : slopeResidue m n i = n + 1 := by
  have e1 : i * m + m = M * m₁ + 1 := by
    calc i * m + m = m * (i + 1) := by ring
      _ = m * M₁ := by rw [hi]
      _ = m₁ * M + 1 := hB
      _ = M * m₁ + 1 := by ring
  have e2 : n + 1 + m = M + 1 := by omega
  have hA : i * m + m ≡ 1 [MOD M] := by
    change (i * m + m) % M = 1 % M
    rw [e1]
    exact Nat.mul_add_mod _ _ _
  have hB2 : n + 1 + m ≡ 1 [MOD M] := by
    change (n + 1 + m) % M = 1 % M
    rw [e2, Nat.add_comm M 1, Nat.add_mod_right]
  have heq : n + 1 = slopeResidue m n i := by
    rw [eq_slopeResidue_iff hcop (by omega) hn hi1 (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmn]
    exact (Nat.ModEq.add_right_cancel' m (hB2.trans hA.symm))
  exact heq.symm

/-- **`ϱ_{m,n}(M₂) = M - 1`.** Here `m M₂ + 1 = m₂ M` says `M₂ m ≡ -1 (mod M)`, and `M - 1` is the
representative of `-1` in `{1, …, M-1}`. -/
theorem slopeResidue_at_junction' {m n m₂ M M₂ v : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) (hC : m * M₂ + 1 = m₂ * M)
    (hM₂ : 1 ≤ M₂) (hidx : M₂ + 1 ≤ M) (hMv : M = v + 1) : slopeResidue m n M₂ = v := by
  have e1 : M₂ * m + 1 = M * m₂ := by
    calc M₂ * m + 1 = m * M₂ + 1 := by ring
      _ = m₂ * M := hC
      _ = M * m₂ := by ring
  have hA : M₂ * m + 1 ≡ 0 [MOD M] := by
    change (M₂ * m + 1) % M = 0 % M
    rw [e1, Nat.mul_mod_right, Nat.zero_mod]
  have hB2 : v + 1 ≡ 0 [MOD M] := by
    change (v + 1) % M = 0 % M
    rw [← hMv, Nat.mod_self, Nat.zero_mod]
  have heq : v = slopeResidue m n M₂ := by
    rw [eq_slopeResidue_iff hcop hm hn hM₂ (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmn]
    exact (Nat.ModEq.add_right_cancel' 1 (hB2.trans hA.symm))
  exact heq.symm

/-- **`ϱ_{m,n}(M₂ - 1) = n - 1`.** Here `(M₂ - 1)m + m + 1 = m₂ M ≡ 0` and
`(n - 1) + m + 1 = M ≡ 0`; the value is in range because `n ≥ 2`. -/
theorem slopeResidue_at_junction_pred' {m n m₂ M M₂ i v : ℕ} (hmn : m + n = M)
    (hcop : Nat.Coprime m n) (hm : 1 ≤ m) (hn : 2 ≤ n) (hC : m * M₂ + 1 = m₂ * M)
    (hi : M₂ = i + 1) (hi1 : 1 ≤ i) (hidx : M₂ + 1 ≤ M) (hnv : n = v + 1) :
    slopeResidue m n i = v := by
  have e1 : i * m + (m + 1) = M * m₂ := by
    calc i * m + (m + 1) = m * (i + 1) + 1 := by ring
      _ = m * M₂ + 1 := by rw [hi]
      _ = m₂ * M := hC
      _ = M * m₂ := by ring
  have e2 : v + (m + 1) = M := by omega
  have hA : i * m + (m + 1) ≡ 0 [MOD M] := by
    change (i * m + (m + 1)) % M = 0 % M
    rw [e1, Nat.mul_mod_right, Nat.zero_mod]
  have hB2 : v + (m + 1) ≡ 0 [MOD M] := by
    change (v + (m + 1)) % M = 0 % M
    rw [e2, Nat.mod_self, Nat.zero_mod]
  have heq : v = slopeResidue m n i := by
    rw [eq_slopeResidue_iff hcop hm (by omega) hi1 (by omega)]
    refine ⟨by omega, by omega, ?_⟩
    rw [hmn]
    exact (Nat.ModEq.add_right_cancel' (m + 1) (hB2.trans hA.symm))
  exact heq.symm

/-! ### Which side of the threshold the mediant's residue falls on -/

/-- **The threshold test transfers to the first parent.** With `M₁ s = M r + i`, `r ≠ n₁` and
`M n₁ = n M₁ + 1`, the test `s < n` is the test `r < n₁`. This is the conjunction of the two
displayed estimates in part (1) of the proof. -/
theorem lt_iff_left {n n₁ M M₁ M₂ i r s : ℕ} (hM : M = M₁ + M₂) (hM₂ : 1 ≤ M₂)
    (hD : M * n₁ = n * M₁ + 1) (hr2 : r + 1 ≤ M₁) (hrne : r ≠ n₁) (hi2 : i + 2 ≤ M₁)
    (hs : M₁ * s = M * r + i) : s < n ↔ r < n₁ := by
  have hcomm : n * M₁ = M₁ * n := by ring
  constructor
  · intro h
    by_contra hcon
    have hge : n₁ + 1 ≤ r := by omega
    have hup : M * n₁ + M ≤ M * r := by
      calc M * n₁ + M = M * (n₁ + 1) := by ring
        _ ≤ M * r := Nat.mul_le_mul_left M hge
    exact absurd (Nat.lt_of_mul_lt_mul_left (show M₁ * n < M₁ * s by omega)) (by omega)
  · intro h
    have hup : M * r + M ≤ M * n₁ := by
      calc M * r + M = M * (r + 1) := by ring
        _ ≤ M * n₁ := Nat.mul_le_mul_left M h
    exact Nat.lt_of_mul_lt_mul_left (show M₁ * s < M₁ * n by omega)

/-- **The threshold test transfers to the first parent, after a downward shift.** With
`M₁ (s + 1) = M r + i` and the same Bézout data, the test `s < n` is again the test `r < n₁`.
This is part (3′) of the proof of `HJO.Mellit.slopeWord_mediant_rev`. -/
theorem lt_iff_left_pred {n n₁ M M₁ M₂ i r s : ℕ} (hM : M = M₁ + M₂) (hM₂ : 1 ≤ M₂)
    (hD : M * n₁ = n * M₁ + 1) (hr2 : r + 1 ≤ M₁) (hrne : r ≠ n₁) (hi2 : i + 2 ≤ M₁)
    (hs : M₁ * (s + 1) = M * r + i) : s < n ↔ r < n₁ := by
  have hcomm : n * M₁ = M₁ * n := by ring
  have hexp : M₁ * (s + 1) = M₁ * s + M₁ := by ring
  constructor
  · intro h
    by_contra hcon
    have hge : n₁ + 1 ≤ r := by omega
    have hup : M * n₁ + M ≤ M * r := by
      calc M * n₁ + M = M * (n₁ + 1) := by ring
        _ ≤ M * r := Nat.mul_le_mul_left M hge
    exact absurd (Nat.lt_of_mul_lt_mul_left (show M₁ * n < M₁ * s by omega)) (by omega)
  · intro h
    have hup : M * r + M ≤ M * n₁ := by
      calc M * r + M = M * (r + 1) := by ring
        _ ≤ M * n₁ := Nat.mul_le_mul_left M h
    exact Nat.lt_of_mul_lt_mul_left (show M₁ * s < M₁ * n by omega)

/-- **The threshold test transfers to the second parent.** With `M₂ t + i = M r`, `r ≠ n₂` and
`M n₂ + 1 = n M₂`, the test `t < n` is the test `r < n₂`. This is part (1′) of the
proof of `HJO.Mellit.slopeWord_mediant_rev`. -/
theorem lt_iff_right {n n₂ M M₁ M₂ i r t : ℕ} (hM : M = M₁ + M₂) (hM₁ : 1 ≤ M₁)
    (hE : M * n₂ + 1 = n * M₂) (hrne : r ≠ n₂) (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ M₂) (ht : M₂ * t + i = M * r) : t < n ↔ r < n₂ := by
  have hcomm : n * M₂ = M₂ * n := by ring
  constructor
  · intro h
    by_contra hcon
    have hge : n₂ + 1 ≤ r := by omega
    have hup : M * n₂ + M ≤ M * r := by
      calc M * n₂ + M = M * (n₂ + 1) := by ring
        _ ≤ M * r := Nat.mul_le_mul_left M hge
    exact absurd (Nat.lt_of_mul_lt_mul_left (show M₂ * n < M₂ * t by omega)) (by omega)
  · intro h
    have hup : M * r + M ≤ M * n₂ := by
      calc M * r + M = M * (r + 1) := by ring
        _ ≤ M * n₂ := Nat.mul_le_mul_left M h
    exact Nat.lt_of_mul_lt_mul_left (show M₂ * t < M₂ * n by omega)

/-- **The threshold test transfers to the second parent, after an upward shift.** With
`M₂ t + i = M r` the test `t + 1 < n` is the test `r < n₂`. This is part (3) of the
proof of `HJO.Mellit.slopeWord_mediant`. -/
theorem lt_iff_right_succ {n n₂ M M₁ M₂ i r t : ℕ} (hM : M = M₁ + M₂) (hM₁ : 1 ≤ M₁)
    (hE : M * n₂ + 1 = n * M₂) (hrne : r ≠ n₂) (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ M₂) (ht : M₂ * t + i = M * r) : t + 1 < n ↔ r < n₂ := by
  have hcomm : n * M₂ = M₂ * n := by ring
  have hexp : M₂ * (t + 1) = M₂ * t + M₂ := by ring
  constructor
  · intro h
    by_contra hcon
    have hge : n₂ + 1 ≤ r := by omega
    have hup : M * n₂ + M ≤ M * r := by
      calc M * n₂ + M = M * (n₂ + 1) := by ring
        _ ≤ M * r := Nat.mul_le_mul_left M hge
    exact absurd (Nat.lt_of_mul_lt_mul_left (show M₂ * n < M₂ * (t + 1) by omega)) (by omega)
  · intro h
    have hup : M * r + M ≤ M * n₂ := by
      calc M * r + M = M * (r + 1) := by ring
        _ ≤ M * n₂ := Nat.mul_le_mul_left M h
    exact Nat.lt_of_mul_lt_mul_left (show M₂ * (t + 1) < M₂ * n by omega)

/-! ### The list combinatorics -/

/-- **Splitting the slope word at a denominator.** If the letters of `β_{m,n}` at the indices
`1 ≤ i ≤ P - 2` are those of `β_{p,q}`, and the letters at the shifted indices `P + i` for
`1 ≤ i ≤ P' - 2` are those of `β_{p',q'}`, then
`β_{m,n} = β_{p',q'}\, λ(P)\, λ(P-1)\, β_{p,q}`, where `P = p + q` and `P' = p' + q'`.

The two middle letters are left as the values of `λ` at the two junction indices, so that this one
lemma serves both mediant orders: they differ exactly in which of `𝗒𝗓`, `𝗓𝗒` those two values
are. Only the index bookkeeping happens here — `β_{m,n}` lists its letters in decreasing order of
the index, so position `j` of the concatenation must be matched with index `M - 2 - j`. -/
theorem slopeWord_eq_append {m n p q p' q' : ℕ}
    (hMM : m + n = p + q + (p' + q')) (hP : 2 ≤ p + q) (hP' : 2 ≤ p' + q')
    (hlow : ∀ i, 1 ≤ i → i + 2 ≤ p + q → slopeLetter m n i = slopeLetter p q i)
    (hhigh : ∀ i, 1 ≤ i → i + 2 ≤ p' + q' → slopeLetter m n (p + q + i) = slopeLetter p' q' i) :
    slopeWord m n = slopeWord p' q' ++ slopeLetter m n (p + q) ::
      slopeLetter m n (p + q - 1) :: slopeWord p q := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_cons, length_slopeWord]
    omega
  · intro j hj1 hj2
    rw [length_slopeWord] at hj1
    rw [getElem_slopeWord]
    rcases lt_or_ge j (p' + q' - 2) with hj | hj
    · rw [List.getElem_append_left (by rw [length_slopeWord]; omega), getElem_slopeWord,
        ← hhigh (p' + q' - 2 - j) (by omega) (by omega)]
      congr 1
      omega
    · rw [List.getElem_append_right (by rw [length_slopeWord]; omega)]
      simp only [length_slopeWord]
      obtain ⟨k, hk⟩ : ∃ k, j = p' + q' - 2 + k := ⟨j - (p' + q' - 2), by omega⟩
      subst hk
      simp only [Nat.add_sub_cancel_left]
      match k with
      | 0 =>
        rw [List.getElem_cons_zero]
        congr 1
        omega
      | 1 =>
        rw [List.getElem_cons_succ, List.getElem_cons_zero]
        congr 1
        omega
      | (k + 2) =>
        rw [List.getElem_cons_succ, List.getElem_cons_succ, getElem_slopeWord,
          ← hlow (p + q - 2 - k) (by omega) (by omega)]
        congr 1
        omega

/-! ### The two mediant identities -/

section Mediant

variable {m₁ n₁ m₂ n₂ : ℕ}

/-- The mediant of two coprime pairs with `m₂ n₁ - m₁ n₂ = 1` is coprime. Any common divisor of
`m₁ + m₂` and `n₁ + n₂` divides `m₂(n₁ + n₂) - n₂(m₁ + m₂) = m₂ n₁ - m₁ n₂ = 1`.

Both mediant lemmas are commonly stated with `gcd(m₁,n₁) = gcd(m₂,n₂) = 1` as hypotheses. They are
**redundant**: the determinant identity alone forces each pair to be coprime, by the same one-line
argument. They are kept in the statements below, to match the form in which they are commonly
stated. -/
theorem coprime_mediant (hdet : m₂ * n₁ = m₁ * n₂ + 1) :
    Nat.Coprime (m₁ + m₂) (n₁ + n₂) := by
  have key : m₂ * (n₁ + n₂) = n₂ * (m₁ + m₂) + 1 := by
    calc m₂ * (n₁ + n₂) = m₂ * n₂ + m₂ * n₁ := by ring
      _ = m₂ * n₂ + (m₁ * n₂ + 1) := by rw [hdet]
      _ = n₂ * (m₁ + m₂) + 1 := by ring
  have hd := Nat.gcd_dvd_left (m₁ + m₂) (n₁ + n₂)
  have hd' := Nat.gcd_dvd_right (m₁ + m₂) (n₁ + n₂)
  have hdd : Nat.gcd (m₁ + m₂) (n₁ + n₂) ∣ m₂ * (n₁ + n₂) - n₂ * (m₁ + m₂) :=
    Nat.dvd_sub (hd'.mul_left m₂) (hd.mul_left n₂)
  have hsub : m₂ * (n₁ + n₂) - n₂ * (m₁ + m₂) = 1 := by omega
  rw [hsub] at hdd
  exact Nat.eq_one_of_dvd_one hdd

/-- `m M₁ = m₁ M + 1` at the mediant: the first of the three identities the proof of
`HJO.Mellit.slopeWord_mediant` isolates. -/
theorem mediant_bezout_left (hdet : m₂ * n₁ = m₁ * n₂ + 1) :
    (m₁ + m₂) * (m₁ + n₁) = m₁ * (m₁ + n₁ + (m₂ + n₂)) + 1 := by
  calc (m₁ + m₂) * (m₁ + n₁) = m₁ * m₁ + m₁ * n₁ + m₂ * m₁ + m₂ * n₁ := by ring
    _ = m₁ * m₁ + m₁ * n₁ + m₂ * m₁ + (m₁ * n₂ + 1) := by rw [hdet]
    _ = m₁ * (m₁ + n₁ + (m₂ + n₂)) + 1 := by ring

/-- `m M₂ + 1 = m₂ M` at the mediant. -/
theorem mediant_bezout_right (hdet : m₂ * n₁ = m₁ * n₂ + 1) :
    (m₁ + m₂) * (m₂ + n₂) + 1 = m₂ * (m₁ + n₁ + (m₂ + n₂)) := by
  calc (m₁ + m₂) * (m₂ + n₂) + 1 = m₁ * m₂ + m₂ * m₂ + m₂ * n₂ + (m₁ * n₂ + 1) := by ring
    _ = m₁ * m₂ + m₂ * m₂ + m₂ * n₂ + m₂ * n₁ := by rw [← hdet]
    _ = m₂ * (m₁ + n₁ + (m₂ + n₂)) := by ring

/-- `M n₁ = n M₁ + 1` at the mediant: the second of the three identities. -/
theorem mediant_num_left (hdet : m₂ * n₁ = m₁ * n₂ + 1) :
    (m₁ + n₁ + (m₂ + n₂)) * n₁ = (n₁ + n₂) * (m₁ + n₁) + 1 := by
  calc (m₁ + n₁ + (m₂ + n₂)) * n₁ = m₁ * n₁ + n₁ * n₁ + n₂ * n₁ + m₂ * n₁ := by ring
    _ = m₁ * n₁ + n₁ * n₁ + n₂ * n₁ + (m₁ * n₂ + 1) := by rw [hdet]
    _ = (n₁ + n₂) * (m₁ + n₁) + 1 := by ring

/-- `M n₂ + 1 = n M₂` at the mediant: the third of the three identities. -/
theorem mediant_num_right (hdet : m₂ * n₁ = m₁ * n₂ + 1) :
    (m₁ + n₁ + (m₂ + n₂)) * n₂ + 1 = (n₁ + n₂) * (m₂ + n₂) := by
  calc (m₁ + n₁ + (m₂ + n₂)) * n₂ + 1 = m₁ * n₂ + n₁ * n₂ + m₂ * n₂ + n₂ * n₂ + 1 := by ring
    _ = n₁ * n₂ + m₂ * n₂ + n₂ * n₂ + (m₁ * n₂ + 1) := by ring
    _ = n₁ * n₂ + m₂ * n₂ + n₂ * n₂ + m₂ * n₁ := by rw [← hdet]
    _ = (n₁ + n₂) * (m₂ + n₂) := by ring

variable (hm₁ : 1 ≤ m₁) (hn₁ : 1 ≤ n₁) (hm₂ : 1 ≤ m₂) (hn₂ : 1 ≤ n₂)
  (hdet : m₂ * n₁ = m₁ * n₂ + 1)

include hm₁ hn₁ hm₂ hn₂ hdet

/-- **Below the first junction the mediant reads its first parent.** Part (1) of the
proof of `HJO.Mellit.slopeWord_mediant`: for `1 ≤ i ≤ M₁ - 2` the letter of `β_{m,n}` at index `i`
is the letter of `β_{m₁,n₁}` at the same index. -/
theorem slopeLetter_mediant_low (hc₁ : Nat.Coprime m₁ n₁) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ m₁ + n₁) :
    slopeLetter (m₁ + m₂) (n₁ + n₂) i = slopeLetter m₁ n₁ i := by
  have hr2 : slopeResidue m₁ n₁ i + 1 ≤ m₁ + n₁ := by
    have h := slopeResidue_lt (show 0 < m₁ + n₁ by omega) i
    omega
  have hrne : slopeResidue m₁ n₁ i ≠ n₁ :=
    slopeResidue_ne hc₁ hm₁ hn₁ hi1 (by omega)
  have hs : (m₁ + n₁) * slopeResidue (m₁ + m₂) (n₁ + n₂) i
      = (m₁ + n₁ + (m₂ + n₂)) * slopeResidue m₁ n₁ i + i :=
    slopeResidue_left_eq rfl (by omega) (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_left hdet) hr2 (slopeResidue_modEq m₁ n₁ i) hi1 hi2
  have hiff := lt_iff_left (M₂ := m₂ + n₂) rfl (by omega) (mediant_num_left hdet) hr2 hrne hi2 hs
  rw [slopeLetter, slopeLetter]
  exact if_congr hiff rfl rfl

/-- **Above the first junction the mediant reads its second parent.** Part (3) of the
proof of `HJO.Mellit.slopeWord_mediant`: for `1 ≤ i ≤ M₂ - 2` the letter of `β_{m,n}` at index
`M₁ + i` is the letter of `β_{m₂,n₂}` at index `i`. The residue itself is shifted by one, which is
why the threshold test has to be run at `ϱ_{m,n}(i) + 1`. -/
theorem slopeLetter_mediant_high (hc₂ : Nat.Coprime m₂ n₂) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ m₂ + n₂) :
    slopeLetter (m₁ + m₂) (n₁ + n₂) (m₁ + n₁ + i) = slopeLetter m₂ n₂ i := by
  have hr1 : 1 ≤ slopeResidue m₂ n₂ i :=
    one_le_slopeResidue hc₂ hm₂ hn₂ hi1 (by omega)
  have hr2 : slopeResidue m₂ n₂ i + 1 ≤ m₂ + n₂ := by
    have h := slopeResidue_lt (show 0 < m₂ + n₂ by omega) i
    omega
  have hrne : slopeResidue m₂ n₂ i ≠ n₂ :=
    slopeResidue_ne hc₂ hm₂ hn₂ hi1 (by omega)
  have ht : (m₂ + n₂) * slopeResidue (m₁ + m₂) (n₁ + n₂) i + i
      = (m₁ + n₁ + (m₂ + n₂)) * slopeResidue m₂ n₂ i :=
    slopeResidue_right_eq rfl (by omega) (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_right hdet) hr1 hr2 (slopeResidue_modEq m₂ n₂ i) hi1 hi2
  have hlt : slopeResidue (m₁ + m₂) (n₁ + n₂) i < m₁ + n₁ + (m₂ + n₂) := by
    have h := slopeResidue_lt (show 0 < m₁ + m₂ + (n₁ + n₂) by omega) i
    omega
  have hbd : slopeResidue (m₁ + m₂) (n₁ + n₂) i + 2 ≤ m₁ + n₁ + (m₂ + n₂) :=
    slopeResidue_add_two_le (by omega) hr2 hi1 hlt ht
  have hshift : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₁ + n₁ + i)
      = slopeResidue (m₁ + m₂) (n₁ + n₂) i + 1 :=
    slopeResidue_shift_up (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_left hdet) hi1 (by omega) hbd
  have hiff := lt_iff_right_succ (M₁ := m₁ + n₁) rfl (by omega) (mediant_num_right hdet) hrne hi1
    hi2 ht
  rw [slopeLetter, slopeLetter, hshift]
  exact if_congr hiff rfl rfl

/-- **Below the second junction the mediant reads its second parent.** Part (1′) of the
proof of `HJO.Mellit.slopeWord_mediant_rev`: the same residue computation as
`slopeLetter_mediant_high`, with the threshold test run at `ϱ_{m,n}(i)` itself rather than at
`ϱ_{m,n}(i) + 1`. -/
theorem slopeLetter_mediant_low' (hc₂ : Nat.Coprime m₂ n₂) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ m₂ + n₂) :
    slopeLetter (m₁ + m₂) (n₁ + n₂) i = slopeLetter m₂ n₂ i := by
  have hr1 : 1 ≤ slopeResidue m₂ n₂ i :=
    one_le_slopeResidue hc₂ hm₂ hn₂ hi1 (by omega)
  have hr2 : slopeResidue m₂ n₂ i + 1 ≤ m₂ + n₂ := by
    have h := slopeResidue_lt (show 0 < m₂ + n₂ by omega) i
    omega
  have hrne : slopeResidue m₂ n₂ i ≠ n₂ :=
    slopeResidue_ne hc₂ hm₂ hn₂ hi1 (by omega)
  have ht : (m₂ + n₂) * slopeResidue (m₁ + m₂) (n₁ + n₂) i + i
      = (m₁ + n₁ + (m₂ + n₂)) * slopeResidue m₂ n₂ i :=
    slopeResidue_right_eq rfl (by omega) (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_right hdet) hr1 hr2 (slopeResidue_modEq m₂ n₂ i) hi1 hi2
  have hiff := lt_iff_right (M₁ := m₁ + n₁) rfl (by omega) (mediant_num_right hdet) hrne hi1 hi2 ht
  rw [slopeLetter, slopeLetter]
  exact if_congr hiff rfl rfl

/-- **Above the second junction the mediant reads its first parent.** Part (3′) of the
proof of `HJO.Mellit.slopeWord_mediant_rev`: the residue drops by one across the shift, so the
threshold test is run at `ϱ_{m,n}(i) - 1` — which is in range only because `ϱ_{m,n}(i) ≥ 2`, the
step argued informally by "that value exceeds `M/M₁ > 1`, hence is at least `2`". -/
theorem slopeLetter_mediant_high' (hc₁ : Nat.Coprime m₁ n₁) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i + 2 ≤ m₁ + n₁) :
    slopeLetter (m₁ + m₂) (n₁ + n₂) (m₂ + n₂ + i) = slopeLetter m₁ n₁ i := by
  have hr1 : 1 ≤ slopeResidue m₁ n₁ i :=
    one_le_slopeResidue hc₁ hm₁ hn₁ hi1 (by omega)
  have hr2 : slopeResidue m₁ n₁ i + 1 ≤ m₁ + n₁ := by
    have h := slopeResidue_lt (show 0 < m₁ + n₁ by omega) i
    omega
  have hrne : slopeResidue m₁ n₁ i ≠ n₁ :=
    slopeResidue_ne hc₁ hm₁ hn₁ hi1 (by omega)
  have hs : (m₁ + n₁) * slopeResidue (m₁ + m₂) (n₁ + n₂) i
      = (m₁ + n₁ + (m₂ + n₂)) * slopeResidue m₁ n₁ i + i :=
    slopeResidue_left_eq rfl (by omega) (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_left hdet) hr2 (slopeResidue_modEq m₁ n₁ i) hi1 hi2
  have h2 : 2 ≤ slopeResidue (m₁ + m₂) (n₁ + n₂) i :=
    two_le_slopeResidue (by omega) hr1 hi1 hs
  obtain ⟨s, hsv⟩ : ∃ s, slopeResidue (m₁ + m₂) (n₁ + n₂) i = s + 1 :=
    ⟨slopeResidue (m₁ + m₂) (n₁ + n₂) i - 1, by omega⟩
  have hshift : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₂ + n₂ + i) = s :=
    slopeResidue_shift_down (by omega) (coprime_mediant hdet) (by omega) (by omega)
      (mediant_bezout_right hdet) hi1 (by omega) hsv (by omega)
  have hs' : (m₁ + n₁) * (s + 1) = (m₁ + n₁ + (m₂ + n₂)) * slopeResidue m₁ n₁ i + i := by
    rw [← hsv]; exact hs
  have hiff := lt_iff_left_pred (M₂ := m₂ + n₂) rfl (by omega) (mediant_num_left hdet) hr2 hrne
    hi2 hs'
  rw [slopeLetter, slopeLetter, hshift]
  exact if_congr hiff rfl rfl

/-- **The slope word of a mediant.** `HJO.Mellit.slopeWord_mediant`: for coprime
pairs `(m₁, n₁)` and `(m₂, n₂)` of positive integers with `m₂ n₁ - m₁ n₂ = 1`, the mediant
`(m₁+m₂, n₁+n₂)` is coprime and
`β_{m₁+m₂,\,n₁+n₂} = β_{m₂,n₂}\, 𝗒 𝗓\, β_{m₁,n₁}`.

The two junction letters are `λ(M₁) = 𝗒` — because `ϱ_{m,n}(M₁) = 1` and `n = n₁ + n₂ ≥ 2` — and
`λ(M₁ - 1) = 𝗓`, because `ϱ_{m,n}(M₁ - 1) = n + 1`; the first uses `m M₁ ≡ 1 (mod M)` and the
second needs `m = m₁ + m₂ ≥ 2` to put `n + 1` inside the residue range. -/
@[hjo "lem_mellit_slope_word_mediant"]
theorem slopeWord_mediant (hc₁ : Nat.Coprime m₁ n₁) (hc₂ : Nat.Coprime m₂ n₂) :
    Nat.Coprime (m₁ + m₂) (n₁ + n₂) ∧
      slopeWord (m₁ + m₂) (n₁ + n₂)
        = slopeWord m₂ n₂ ++ SlopeLetter.y :: SlopeLetter.z :: slopeWord m₁ n₁ := by
  refine ⟨coprime_mediant hdet, ?_⟩
  have hjy : slopeLetter (m₁ + m₂) (n₁ + n₂) (m₁ + n₁) = SlopeLetter.y := by
    have h : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₁ + n₁) = 1 :=
      slopeResidue_at_junction (by omega) (coprime_mediant hdet) (by omega) (by omega)
        (mediant_bezout_left hdet) (by omega) (by omega)
    rw [slopeLetter, h]
    exact ite_eq_left (by omega)
  have hjz : slopeLetter (m₁ + m₂) (n₁ + n₂) (m₁ + n₁ - 1) = SlopeLetter.z := by
    have h : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₁ + n₁ - 1) = n₁ + n₂ + 1 :=
      slopeResidue_at_junction_pred (M₁ := m₁ + n₁) (by omega) (coprime_mediant hdet) (by omega)
        (by omega) (mediant_bezout_left hdet) (by omega) (by omega) (by omega)
    rw [slopeLetter, h]
    exact ite_eq_right (by omega)
  rw [slopeWord_eq_append (p := m₁) (q := n₁) (p' := m₂) (q' := n₂) (by omega) (by omega)
    (by omega) (fun i hi1 hi2 => slopeLetter_mediant_low hm₁ hn₁ hm₂ hn₂ hdet hc₁ hi1 hi2)
    (fun i hi1 hi2 => slopeLetter_mediant_high hm₁ hn₁ hm₂ hn₂ hdet hc₂ hi1 hi2), hjy, hjz]

/-- **The slope word of a mediant, the other order.** `HJO.Mellit.slopeWord_mediant_rev`: under the
same hypotheses,
`β_{m₁+m₂,\,n₁+n₂} = β_{m₁,n₁}\, 𝗓 𝗒\, β_{m₂,n₂}`.

Here the junction letters are `λ(M₂) = 𝗓` — because `ϱ_{m,n}(M₂) = M - 1`, which exceeds `n` as
soon as `m = m₁ + m₂ ≥ 2` — and `λ(M₂ - 1) = 𝗒`, because `ϱ_{m,n}(M₂ - 1) = n - 1`, in range
because `n = n₁ + n₂ ≥ 2`. Both orders are needed downstream: the induction of `HJO.Mellit.euclid`
uses this one for `Ω(1; ·)` and `Ω(2; ·)` and the other for `Ω(3; ·)`, and closes from neither
alone. -/
@[hjo "lem_mellit_slope_word_mediant_rev"]
theorem slopeWord_mediant_rev (hc₁ : Nat.Coprime m₁ n₁) (hc₂ : Nat.Coprime m₂ n₂) :
    slopeWord (m₁ + m₂) (n₁ + n₂)
      = slopeWord m₁ n₁ ++ SlopeLetter.z :: SlopeLetter.y :: slopeWord m₂ n₂ := by
  have hjz : slopeLetter (m₁ + m₂) (n₁ + n₂) (m₂ + n₂) = SlopeLetter.z := by
    have h : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₂ + n₂) = m₁ + m₂ + (n₁ + n₂) - 1 :=
      slopeResidue_at_junction' (by omega) (coprime_mediant hdet) (by omega) (by omega)
        (mediant_bezout_right hdet) (by omega) (by omega) (by omega)
    rw [slopeLetter, h]
    exact ite_eq_right (by omega)
  have hjy : slopeLetter (m₁ + m₂) (n₁ + n₂) (m₂ + n₂ - 1) = SlopeLetter.y := by
    have h : slopeResidue (m₁ + m₂) (n₁ + n₂) (m₂ + n₂ - 1) = n₁ + n₂ - 1 :=
      slopeResidue_at_junction_pred' (M₂ := m₂ + n₂) (by omega) (coprime_mediant hdet) (by omega)
        (by omega) (mediant_bezout_right hdet) (by omega) (by omega) (by omega) (by omega)
    rw [slopeLetter, h]
    exact ite_eq_left (by omega)
  rw [slopeWord_eq_append (p := m₂) (q := n₂) (p' := m₁) (q' := n₁) (by omega) (by omega)
    (by omega) (fun i hi1 hi2 => slopeLetter_mediant_low' hm₁ hn₁ hm₂ hn₂ hdet hc₂ hi1 hi2)
    (fun i hi1 hi2 => slopeLetter_mediant_high' hm₁ hn₁ hm₂ hn₂ hdet hc₁ hi1 hi2), hjy, hjz]

end Mediant

/-! ### The two identities, checked outright

Both mediant lemmas are hypothesis-heavy, and a transcription slip in the *statement* — the two
junction letters in the wrong order, or the two parents swapped — would leave every proof above
intact. These four computations pin the statements from the satisfiable side. The first pair is the
smallest non-degenerate mediant and is already visible in `HJO.Mellit.slopeWord_three_two`; the
second pair is `(m₁, n₁) = (2, 3)`, `(m₂, n₂) = (3, 4)`, the smallest case in which **both** parents
have both entries at least `2`, so that neither `HJO.Mellit.slopeWord_one_left` nor
`HJO.Mellit.slopeWord_one_right` could be substituted for the mediant recursion. -/

/-- `β_{3,2} = β_{2,1}\,𝗒𝗓\,β_{1,1}`: `HJO.Mellit.slopeWord_mediant` at
`(m₁, n₁) = (1, 1)`, `(m₂, n₂) = (2, 1)`. -/
theorem slopeWord_mediant_check_three_two :
    slopeWord 3 2 = slopeWord 2 1 ++ SlopeLetter.y :: SlopeLetter.z :: slopeWord 1 1 := by decide

/-- `β_{3,2} = β_{1,1}\,𝗓𝗒\,β_{2,1}`: `HJO.Mellit.slopeWord_mediant_rev` at the same pair. -/
theorem slopeWord_mediant_rev_check_three_two :
    slopeWord 3 2 = slopeWord 1 1 ++ SlopeLetter.z :: SlopeLetter.y :: slopeWord 2 1 := by decide

/-- `β_{5,7} = β_{3,4}\,𝗒𝗓\,β_{2,3}`: `HJO.Mellit.slopeWord_mediant` at
`(m₁, n₁) = (2, 3)`, `(m₂, n₂) = (3, 4)`, where `3·3 - 2·4 = 1` and both parents are nontrivial in
both coordinates. Both sides are `𝗒𝗓𝗒𝗓𝗒𝗒𝗓𝗒𝗓𝗒`. -/
theorem slopeWord_mediant_check_five_seven :
    slopeWord 5 7 = slopeWord 3 4 ++ SlopeLetter.y :: SlopeLetter.z :: slopeWord 2 3 := by decide

/-- `β_{5,7} = β_{2,3}\,𝗓𝗒\,β_{3,4}`: `HJO.Mellit.slopeWord_mediant_rev` at the same pair. The two
junction letters are exchanged and the two blocks swapped, and the result is the same word — which
is the only reason the induction of `HJO.Mellit.euclid` can use whichever order it needs. -/
theorem slopeWord_mediant_rev_check_five_seven :
    slopeWord 5 7 = slopeWord 2 3 ++ SlopeLetter.z :: SlopeLetter.y :: slopeWord 3 4 := by decide

end HJO.Mellit
