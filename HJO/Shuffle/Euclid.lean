/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Mellit
public import HJO.Shuffle.SlopeMediant
public import HJO.Shuffle.SweepModule
public meta import HJO.Attr

/-! # The extended Euclidean identities of Mellit's Section 6

`HJO.Mellit.euclid` is the arithmetic heart of Mellit's Section 6: the slope operator `Ξ_{m,n}`,
read off the slope word `β_{m,n}`, carries the three replicated operators at `(1,1)` to the three
replicated operators at `(m,n)` up to the sign `(-1)^{m-1}`:
`Ξ_{m,n}\,Ω(j;1,1) = (-1)^{m-1}\,Ω(j;m,n)` for `j ∈ {1,2,3}`.

Mellit asserts the cases `j = 1` and `j = 2` with "it is easy to see"; the case `j = 3` is not
asserted there and is what makes the induction close, since the recursion for `ρ_{m,n}(y_1)` feeds
the recursions for the two starred operators.

## Main definitions

* `HJO.Mellit.slopeEval`: the evaluation of `β_{m,n}` in an arbitrary monoid, one generator per
  letter. `HJO.Sweep.slopeOperator` is this
  applied to `-y_1` and `(qu)^{-1} z_1` in `Module.End L (Total L)`
  (`HJO.Sweep.slopeOperator_eq_slopeEval`), and the statement below is the same evaluation on a
  `SweepSystem`, which is the substrate `HJO.Mellit.IsReplicationFamily` is stated over.

## Main results

* `HJO.Mellit.slopeEval_mediant`, `HJO.Mellit.slopeEval_mediant_rev`: the two mediant
  factorisations of `Ξ_{m,n}`, transported from the two slope-word identities.
* `HJO.Mellit.euclid`.

## Implementation notes

**Where genericity is spent: nowhere.** The proof passes through the two identities
`(-y_1)\,(qu)^{-1}z_1 = (qu)^{-1}Ω(2;1,1)` and `(qu)^{-1}z_1\,(-y_1) = Ω(3;1,1)`, and reading the
first of them from right to left would need `(qu)(qu)^{-1} = 1`, i.e. `q u ≠ 0`. It is never needed
in that direction: every occurrence of `(qu)^{-1}` below is a scalar that sits in the same place on
both sides of the identity being proved, so the identity is an identity of composites with matching
scalars and holds over **any** field, at any `q` and `u` — including `q = 0`, `u = 0`, `qu = 1` and
`u` a root of unity. There is no hypothesis on the parameters here and none is missing; see the
degenerate-corner note below.

The identity is proved as an equality of *global* endomorphisms of the total space, not of their
restrictions to `V_k`. That is stronger than the statement, which reads the two sides
as maps `V_k → V_{k+1}` for `j = 1` and as endomorphisms of `V_k` for `j ∈ {2,3}`: the gradings are
already recorded in `HJO.Mellit.IsReplicationFamily` and in `HJO.Mellit.SweepSystem`, and the
graded reading follows from this one by restriction. Nothing in the proof looks at a graded
piece.

The induction is on `m + n`, with the conclusion quantified over `j` *inside* the induction: the
three recursions of `HJO.Mellit.IsReplicationFamily` mix the three indices, so the hypothesis has to
be available at every `j` at each smaller index sum. It is *not* quantified over a rank `k`, as a
graded statement would be, for the reason in the previous paragraph.

Three of the four cases of the induction use a Stern–Brocot parent pair that is written down
explicitly — `(0,1)` at `(1,n)`, `(m-1,1)` at `(m,1)` — rather than obtained from
`HJO.Mellit.existsUnique_isSBParent`; only the case `m, n ≥ 2` calls that lemma, and what it needs
beyond the lemma is that **both entries of both parents are positive** there
(`HJO.Mellit.isSBParent_pos`), which is what lets `HJO.Mellit.slopeWord_mediant` be applied at
all. So the mediant induction needs one fact more than `existsUnique_isSBParent`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 6. `HJO.Mellit.euclid` is consumed
inside the proof of `HJO.Mellit.braidRep_specialBraid_dplusIter` rather than by the residual
interface. -/

@[expose] public section

namespace HJO.Mellit

/-! ### The slope word evaluated in a monoid -/

/-- **The slope word read in a monoid.** `slopeEval Y Z m n` replaces each letter `𝗒` of
`β_{m,n}` by `Y` and each letter `𝗓` by `Z`, and multiplies the factors in the order in which they
are written — so the head of `β_{m,n}`, which is `λ(m+n-2)`, is the leftmost factor.

This is `HJO.Sweep.slopeOperator` with its two substituted operators left as
parameters. `HJO.Sweep.slopeOperator` lives on the concrete total
space; `HJO.Sweep.slopeOperator_eq_slopeEval` identifies the two, and `HJO.Mellit.euclid` below is
stated with the same evaluation on a `SweepSystem`, because that is the substrate a replication
family lives on. -/
def slopeEval {A : Type*} [Monoid A] (Y Z : A) (m n : ℕ) : A :=
  ((slopeWord m n).map fun l =>
    match l with
    | SlopeLetter.y => Y
    | SlopeLetter.z => Z).prod

section Eval

variable {A : Type*} [Monoid A] (Y Z : A)

/-- At `(1,1)` the slope word is empty, so the slope operator is the identity. -/
@[simp] theorem slopeEval_one_one : slopeEval Y Z 1 1 = 1 := by
  rw [slopeEval, show slopeWord 1 1 = [] from rfl, List.map_nil, List.prod_nil]

/-- `Ξ_{1,n} = Y^{n-1}`, from `HJO.Mellit.slopeWord_one_left`. -/
theorem slopeEval_one_left {n : ℕ} (hn : 1 ≤ n) : slopeEval Y Z 1 n = Y ^ (n - 1) := by
  rw [slopeEval, slopeWord_one_left hn, List.map_replicate, List.prod_replicate]

/-- `Ξ_{m,1} = Z^{m-1}`, from `HJO.Mellit.slopeWord_one_right`. -/
theorem slopeEval_one_right {m : ℕ} (hm : 1 ≤ m) : slopeEval Y Z m 1 = Z ^ (m - 1) := by
  rw [slopeEval, slopeWord_one_right hm, List.map_replicate, List.prod_replicate]

/-- `Ξ_{1,n} = Y · Ξ_{1,n-1}`: one step of the unit-denominator recursion. -/
theorem slopeEval_succ_left {n : ℕ} (hn : 2 ≤ n) :
    slopeEval Y Z 1 n = Y * slopeEval Y Z 1 (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [slopeEval_one_left Y Z (by omega), slopeEval_one_left Y Z (by omega)]
  change Y ^ (k + 1) = Y * Y ^ k
  exact pow_succ' Y k

/-- `Ξ_{m,1} = Z · Ξ_{m-1,1}`: one step of the unit-numerator recursion. -/
theorem slopeEval_succ_right {m : ℕ} (hm : 2 ≤ m) :
    slopeEval Y Z m 1 = Z * slopeEval Y Z (m - 1) 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [slopeEval_one_right Y Z (by omega), slopeEval_one_right Y Z (by omega)]
  change Z ^ (k + 1) = Z * Z ^ k
  exact pow_succ' Z k

/-- **The mediant factorisation of the slope operator.** From
`HJO.Mellit.slopeWord_mediant`: `Ξ_{m₁+m₂,\,n₁+n₂} = Ξ_{m₂,n₂}\, Y\, Z\, Ξ_{m₁,n₁}`. -/
theorem slopeEval_mediant {m₁ n₁ m₂ n₂ : ℕ} (hm₁ : 1 ≤ m₁) (hn₁ : 1 ≤ n₁) (hm₂ : 1 ≤ m₂)
    (hn₂ : 1 ≤ n₂) (hdet : m₂ * n₁ = m₁ * n₂ + 1) (hc₁ : Nat.Coprime m₁ n₁)
    (hc₂ : Nat.Coprime m₂ n₂) :
    slopeEval Y Z (m₁ + m₂) (n₁ + n₂)
      = slopeEval Y Z m₂ n₂ * (Y * (Z * slopeEval Y Z m₁ n₁)) := by
  rw [slopeEval, (slopeWord_mediant hm₁ hn₁ hm₂ hn₂ hdet hc₁ hc₂).2, List.map_append,
    List.prod_append, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
  rfl

/-- **The reversed mediant factorisation of the slope operator.** From
`HJO.Mellit.slopeWord_mediant_rev`: `Ξ_{m₁+m₂,\,n₁+n₂} = Ξ_{m₁,n₁}\, Z\, Y\, Ξ_{m₂,n₂}`. -/
theorem slopeEval_mediant_rev {m₁ n₁ m₂ n₂ : ℕ} (hm₁ : 1 ≤ m₁) (hn₁ : 1 ≤ n₁) (hm₂ : 1 ≤ m₂)
    (hn₂ : 1 ≤ n₂) (hdet : m₂ * n₁ = m₁ * n₂ + 1) (hc₁ : Nat.Coprime m₁ n₁)
    (hc₂ : Nat.Coprime m₂ n₂) :
    slopeEval Y Z (m₁ + m₂) (n₁ + n₂)
      = slopeEval Y Z m₁ n₁ * (Z * (Y * slopeEval Y Z m₂ n₂)) := by
  rw [slopeEval, slopeWord_mediant_rev hm₁ hn₁ hm₂ hn₂ hdet hc₁ hc₂, List.map_append,
    List.prod_append, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
  rfl

/-- `Ξ_{1,n} = Ξ_{1,n-1} · Y`: the unit-denominator recursion with the new letter on the right. Both
groupings are used, because the slope operator at `(1,n)` is a power of `Y` and the induction needs
it split on either side. -/
theorem slopeEval_succ_left' {n : ℕ} (hn : 2 ≤ n) :
    slopeEval Y Z 1 n = slopeEval Y Z 1 (n - 1) * Y := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [slopeEval_one_left Y Z (by omega), slopeEval_one_left Y Z (by omega)]
  change Y ^ (k + 1) = Y ^ k * Y
  exact pow_succ Y k

/-- `Ξ_{m,1} = Ξ_{m-1,1} · Z`: the unit-numerator recursion with the new letter on the right. Both
groupings are used, because the slope operator at `(m,1)` is a power of `Z` and the induction needs
it split on either side. -/
theorem slopeEval_succ_right' {m : ℕ} (hm : 2 ≤ m) :
    slopeEval Y Z m 1 = slopeEval Y Z (m - 1) 1 * Z := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [slopeEval_one_right Y Z (by omega), slopeEval_one_right Y Z (by omega)]
  change Z ^ (k + 1) = Z ^ k * Z
  exact pow_succ Z k

end Eval

/-! ### Signs -/

/-- `(-1)^{m-2} = -(-1)^{m-1}` for `m ≥ 2`: the sign bookkeeping of the unit-numerator case. -/
private theorem neg_one_pow_sub_two {R : Type*} [CommRing R] {m : ℕ} (hm : 2 ≤ m) :
    (-1 : R) ^ (m - 2) = -((-1 : R) ^ (m - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [show k + 2 - 2 = k from by omega, show k + 2 - 1 = k + 1 from by omega]
  ring

/-- `(-1)^{m₁-1}·(-1)^{m₂-1} = -(-1)^{m₁+m₂-1}` for `m₁, m₂ ≥ 1`: the sign bookkeeping of the
mediant case, and the reason the extra `-1` in each of the three recursions of
`HJO.Mellit.IsReplicationFamily` is exactly what the factor `(-1)^{m-1}` absorbs. -/
private theorem neg_one_pow_add_sub_one {R : Type*} [CommRing R] {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (-1 : R) ^ (a - 1) * (-1 : R) ^ (b - 1) = -((-1 : R) ^ (a + b - 1)) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  rw [show c + 1 - 1 = c from by omega, show d + 1 - 1 = d from by omega,
    show c + 1 + (d + 1) - 1 = c + d + 1 from by omega]
  ring

/-! ### The Stern–Brocot parents at a doubly nontrivial pair -/

/-- **Both Stern–Brocot parents have both entries positive when `m, n ≥ 2`.** This is the fact
`HJO.Mellit.euclid` needs beyond `HJO.Mellit.existsUnique_isSBParent`:
`HJO.Mellit.slopeWord_mediant` is stated for two *positive* coprime pairs, so without this the
mediant case of the induction cannot even be started.

Each of the four is a two-line consequence of `m n₁ - n m₁ = 1`. `n₁ ≥ 1` needs nothing:
`n₁ = 0` would make the left side non-positive. `m₁ ≥ 1` needs `m ≥ 2`, since `m₁ = 0` forces
`m = 1`. `m₁ < m` needs nothing beyond `n₁ ≤ n`: at `m₁ = m` the left side is `m(n₁ - n) ≤ 0`. And
`n₁ < n` needs `n ≥ 2`, since `n₁ = n` forces `n(m - m₁) = 1`. -/
theorem isSBParent_pos {m n m₁ n₁ : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (h : IsSBParent m n m₁ n₁) :
    1 ≤ m₁ ∧ 1 ≤ n₁ ∧ m₁ + 1 ≤ m ∧ n₁ + 1 ≤ n := by
  obtain ⟨hm1, hn1, he⟩ := h
  have hmz : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hnz : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hm1z : (m₁ : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
  have hn1z : (n₁ : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn1
  have hm1n : (0 : ℤ) ≤ (m₁ : ℤ) := Int.natCast_nonneg _
  have hn1n : (0 : ℤ) ≤ (n₁ : ℤ) := Int.natCast_nonneg _
  have hn1pos : 1 ≤ n₁ := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · exfalso
      have hz : (n₁ : ℤ) = 0 := by rw [h0]; norm_num
      rw [hz, mul_zero] at he
      linarith [mul_nonneg (show (0 : ℤ) ≤ (n : ℤ) by linarith) hm1n]
    · exact h0
  have hm1pos : 1 ≤ m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h0 | h0
    · exfalso
      have hz : (m₁ : ℤ) = 0 := by rw [h0]; norm_num
      rw [hz, mul_zero, sub_zero] at he
      have := Int.le_of_dvd one_pos (⟨(n₁ : ℤ), he.symm⟩ : (m : ℤ) ∣ 1)
      linarith
    · exact h0
  have hm1lt : m₁ + 1 ≤ m := by
    by_contra hcon
    have hmm : (m₁ : ℤ) = (m : ℤ) := by
      have he' : m₁ = m := by omega
      exact_mod_cast he'
    rw [hmm] at he
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) by linarith)
      (show (0 : ℤ) ≤ (n : ℤ) - (n₁ : ℤ) by linarith)]
  have hn1lt : n₁ + 1 ≤ n := by
    by_contra hcon
    have hnn : (n₁ : ℤ) = (n : ℤ) := by
      have he' : n₁ = n := by omega
      exact_mod_cast he'
    rw [hnn] at he
    have hone : (n : ℤ) * ((m : ℤ) - (m₁ : ℤ)) = 1 := by ring_nf; linarith
    have := Int.le_of_dvd one_pos (⟨(m : ℤ) - (m₁ : ℤ), hone.symm⟩ : (n : ℤ) ∣ 1)
    linarith
  exact ⟨hm1pos, hn1pos, hm1lt, hn1lt⟩

/-- **The determinant identity at a Stern–Brocot parent pair.** `m n₁ - n m₁ = 1` rearranges to
`m₂ n₁ = m₁ n₂ + 1` with `(m₂, n₂) = (m - m₁, n - n₁)`, which is the shape
`HJO.Mellit.slopeWord_mediant` is stated in. -/
theorem isSBParent_det {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) :
    (m - m₁) * n₁ = m₁ * (n - n₁) + 1 := by
  obtain ⟨hm1, hn1, he⟩ := h
  zify [hm1, hn1]
  linarith

/-- **Both Stern–Brocot parents are coprime.** Any common divisor of `m₁` and `n₁` divides
`m n₁ - n m₁ = 1`, and any common divisor of `m₂` and `n₂` divides `m₂ n₁ - m₁ n₂ = 1`. -/
theorem isSBParent_coprime {m n m₁ n₁ : ℕ} (h : IsSBParent m n m₁ n₁) :
    Nat.Coprime m₁ n₁ ∧ Nat.Coprime (m - m₁) (n - n₁) := by
  have hdet := isSBParent_det h
  obtain ⟨hm1, hn1, he⟩ := h
  have key : m * n₁ = n * m₁ + 1 := by zify; linarith
  refine ⟨?_, ?_⟩
  · have hd := Nat.gcd_dvd_left m₁ n₁
    have hd' := Nat.gcd_dvd_right m₁ n₁
    have hdd : Nat.gcd m₁ n₁ ∣ m * n₁ - n * m₁ := Nat.dvd_sub (hd'.mul_left m) (hd.mul_left n)
    rw [show m * n₁ - n * m₁ = 1 from by omega] at hdd
    exact Nat.eq_one_of_dvd_one hdd
  · have hd := Nat.gcd_dvd_left (m - m₁) (n - n₁)
    have hd' := Nat.gcd_dvd_right (m - m₁) (n - n₁)
    have hdd : Nat.gcd (m - m₁) (n - n₁) ∣ (m - m₁) * n₁ - m₁ * (n - n₁) :=
      Nat.dvd_sub (hd.mul_right n₁) (hd'.mul_left m₁)
    rw [show (m - m₁) * n₁ - m₁ * (n - n₁) = 1 from by omega] at hdd
    exact Nat.eq_one_of_dvd_one hdd

/-! ### The induction -/

section Euclid

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}
  {S : SweepSystem L q u} {Ω : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}

/-- The induction behind `HJO.Mellit.euclid`, on the index sum `m + n`, with the conclusion
quantified over `j` at every smaller value: the three recursions of `HJO.Mellit.IsReplicationFamily`
mix the three indices, so the hypothesis has to be available at each of them.

`Y` and `Z` are the two substituted operators of `HJO.Sweep.slopeOperator`, and the only things
the induction knows about them are the two identities of the `(∗)` —
`Y Z = (qu)^{-1}Ω(2;1,1)` and `Z Y = Ω(3;1,1)` — both of which are derived below from the three
base values of the family. -/
private theorem euclid_aux (hΩ : IsReplicationFamily S Ω) (Y Z : S.W →ₗ[L] S.W)
    (hY : Y = -S.y1) (hZ : Z = (q * u)⁻¹ • S.z1) (N : ℕ) :
    ∀ m n : ℕ, m + n ≤ N → Nat.Coprime m n → 1 ≤ m → 1 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      slopeEval Y Z m n * Ω j 1 1 = (-1 : L) ^ (m - 1) • Ω j m n := by
  have hp11 : IsSBParent 1 1 0 1 := ⟨by omega, by omega, by norm_num⟩
  have hΩ211 : Ω 2 1 1 = -(S.y1 * S.z1) := by
    have h := hΩ.rule_two 1 1 0 1 (Nat.coprime_one_left 1) le_rfl le_rfl hp11
    simpa [hΩ.base_three, hΩ.base_two, Module.End.mul_eq_comp] using h
  have hΩ311 : Ω 3 1 1 = -((q * u)⁻¹ • (S.z1 * S.y1)) := by
    have h := hΩ.rule_three 1 1 0 1 (Nat.coprime_one_left 1) le_rfl le_rfl hp11
    simpa [hΩ.base_three, hΩ.base_two, Module.End.mul_eq_comp] using h
  have hZY : Z * Y = Ω 3 1 1 := by
    rw [hY, hZ, hΩ311, smul_mul_assoc, mul_neg, smul_neg]
  have hYZ : Y * Z = (q * u)⁻¹ • Ω 2 1 1 := by
    rw [hY, hZ, hΩ211, mul_smul_comm, neg_mul, smul_neg]
  have hΩ211' : Ω 2 1 1 = Y * S.z1 := by rw [hΩ211, hY, neg_mul]
  induction N with
  | zero =>
    intro m n hle _ hm hn j _ _
    exfalso
    omega
  | succ N ih =>
    intro m n hle hcop hm hn j hj1 hj3
    rcases (show (j = 1 ∨ j = 2) ∨ j = 3 by omega) with hj12 | hjj
    · -- the two starred operators, `j ∈ {1, 2}`
      have hrule : ∀ a b a₁ b₁ : ℕ, Nat.Coprime a b → 1 ≤ a → 1 ≤ b → IsSBParent a b a₁ b₁ →
          Ω j a b = -(Ω 3 a₁ b₁ * Ω j (a - a₁) (b - b₁)) := by
        rcases hj12 with rfl | rfl
        · exact hΩ.rule_one
        · exact hΩ.rule_two
      have hbase : Ω j 1 1 = Y * Ω j 1 0 := by
        have h := hrule 1 1 0 1 (Nat.coprime_one_left 1) le_rfl le_rfl hp11
        rw [hY]
        simpa [hΩ.base_three, neg_mul] using h
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have hme : m = 1 := by omega
        subst hme
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have hne : n = 1 := by omega
          subst hne
          simp
        · -- `m = 1`, `n ≥ 2`: the parents are `(0,1)` and `(1,n-1)`
          have hp : IsSBParent 1 n 0 1 := ⟨by omega, by omega, by norm_num⟩
          have hih : slopeEval Y Z 1 (n - 1) * Ω j 1 1 = Ω j 1 (n - 1) := by
            have h := ih 1 (n - 1) (by omega) (Nat.coprime_one_left _) le_rfl (by omega) j hj1 hj3
            simpa using h
          have hr : Ω j 1 n = -(S.y1 * Ω j 1 (n - 1)) := by
            have h := hrule 1 n 0 1 hcop le_rfl (by omega) hp
            simpa [hΩ.base_three] using h
          rw [slopeEval_succ_left Y Z hn2, mul_assoc, hih, hr, hY]
          simp
      · rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · -- `n = 1`, `m ≥ 2`: the parents are `(m-1,1)` and `(1,0)`
          have hne : n = 1 := by omega
          subst hne
          have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
            have h1 : (1 : ℕ) ≤ m := by omega
            rw [Nat.cast_sub h1, Nat.cast_one]
          have hp : IsSBParent m 1 (m - 1) 1 := ⟨by omega, le_rfl, by push_cast [hcast]; ring⟩
          have hsub : m - (m - 1) = 1 := by omega
          have hih3 : slopeEval Y Z (m - 1) 1 * Ω 3 1 1
              = (-1 : L) ^ (m - 2) • Ω 3 (m - 1) 1 := by
            have h := ih (m - 1) 1 (by omega) (Nat.coprime_one_right _) (by omega) le_rfl 3
              (by omega) le_rfl
            rwa [show m - 1 - 1 = m - 2 from by omega] at h
          have hr : Ω j m 1 = -(Ω 3 (m - 1) 1 * Ω j 1 0) := by
            have h := hrule m 1 (m - 1) 1 hcop (by omega) le_rfl hp
            rwa [hsub, Nat.sub_self] at h
          rw [slopeEval_succ_right' Y Z hm2, hbase, ← mul_assoc,
            mul_assoc (slopeEval Y Z (m - 1) 1), hZY, hih3, hr, smul_mul_assoc,
            neg_one_pow_sub_two hm2, neg_smul, smul_neg]
        · -- `m, n ≥ 2`: both parents have both entries positive
          obtain ⟨m₁, n₁, hp⟩ := exists_isSBParent hcop (by omega) (by omega)
          obtain ⟨hm₁, hn₁, hm₁lt, hn₁lt⟩ := isSBParent_pos hm2 hn2 hp
          obtain ⟨hc₁, hc₂⟩ := isSBParent_coprime hp
          have hdet := isSBParent_det hp
          obtain ⟨m₂, hm₂e⟩ : ∃ m₂, m = m₁ + m₂ := ⟨m - m₁, by omega⟩
          obtain ⟨n₂, hn₂e⟩ : ∃ n₂, n = n₁ + n₂ := ⟨n - n₁, by omega⟩
          subst hm₂e
          subst hn₂e
          simp only [Nat.add_sub_cancel_left] at hdet hc₂
          have hm₂ : 1 ≤ m₂ := by omega
          have hn₂ : 1 ≤ n₂ := by omega
          have hr : Ω j (m₁ + m₂) (n₁ + n₂) = -(Ω 3 m₁ n₁ * Ω j m₂ n₂) := by
            have h := hrule (m₁ + m₂) (n₁ + n₂) m₁ n₁ hcop (by omega) (by omega) hp
            rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h
          have hih1 := ih m₁ n₁ (by omega) hc₁ hm₁ hn₁ 3 (by omega) le_rfl
          have hih2 := ih m₂ n₂ (by omega) hc₂ hm₂ hn₂ j hj1 hj3
          rw [slopeEval_mediant_rev Y Z hm₁ hn₁ hm₂ hn₂ hdet hc₁ hc₂, hr]
          calc slopeEval Y Z m₁ n₁ * (Z * (Y * slopeEval Y Z m₂ n₂)) * Ω j 1 1
              = slopeEval Y Z m₁ n₁ * (Z * Y) * (slopeEval Y Z m₂ n₂ * Ω j 1 1) := by
                simp only [mul_assoc]
            _ = ((-1 : L) ^ (m₁ - 1) • Ω 3 m₁ n₁) * ((-1 : L) ^ (m₂ - 1) • Ω j m₂ n₂) := by
                rw [hZY, hih1, hih2]
            _ = ((-1 : L) ^ (m₁ - 1) * (-1 : L) ^ (m₂ - 1)) • (Ω 3 m₁ n₁ * Ω j m₂ n₂) := by
                rw [smul_mul_assoc, mul_smul_comm, smul_smul]
            _ = (-1 : L) ^ (m₁ + m₂ - 1) • -(Ω 3 m₁ n₁ * Ω j m₂ n₂) := by
                rw [neg_one_pow_add_sub_one hm₁ hm₂, neg_smul, smul_neg]
    · -- the third operator, `j = 3`
      subst hjj
      rcases Nat.lt_or_ge m 2 with hm2 | hm2
      · have hme : m = 1 := by omega
        subst hme
        rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · have hne : n = 1 := by omega
          subst hne
          simp
        · -- `m = 1`, `n ≥ 2`
          have hp : IsSBParent 1 n 0 1 := ⟨by omega, by omega, by norm_num⟩
          have hih2 : slopeEval Y Z 1 (n - 1) * Ω 2 1 1 = Ω 2 1 (n - 1) := by
            have h := ih 1 (n - 1) (by omega) (Nat.coprime_one_left _) le_rfl (by omega) 2
              (by omega) (by omega)
            simpa using h
          have hr3 : Ω 3 1 n = -((q * u)⁻¹ • (Ω 2 1 (n - 1) * S.y1)) := by
            have h := hΩ.rule_three 1 n 0 1 hcop le_rfl (by omega) hp
            simpa [hΩ.base_three, Module.End.mul_eq_comp] using h
          have h2 : Ω 2 1 (n - 1) = slopeEval Y Z 1 (n - 1) * (Y * S.z1) := by
            rw [← hΩ211', hih2]
          rw [slopeEval_succ_left' Y Z hn2, hr3, h2, hΩ311]
          simp only [Nat.sub_self, pow_zero, one_smul, mul_neg, mul_smul_comm, mul_assoc]
      · rcases Nat.lt_or_ge n 2 with hn2 | hn2
        · -- `n = 1`, `m ≥ 2`
          have hne : n = 1 := by omega
          subst hne
          have hcast : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
            have h1 : (1 : ℕ) ≤ m := by omega
            rw [Nat.cast_sub h1, Nat.cast_one]
          have hp : IsSBParent m 1 (m - 1) 1 := ⟨by omega, le_rfl, by push_cast [hcast]; ring⟩
          have hsub : m - (m - 1) = 1 := by omega
          have hih3 : slopeEval Y Z (m - 1) 1 * Ω 3 1 1
              = (-1 : L) ^ (m - 2) • Ω 3 (m - 1) 1 := by
            have h := ih (m - 1) 1 (by omega) (Nat.coprime_one_right _) (by omega) le_rfl 3
              (by omega) le_rfl
            rwa [show m - 1 - 1 = m - 2 from by omega] at h
          have hr3 : Ω 3 m 1 = -((q * u)⁻¹ • (S.z1 * Ω 3 (m - 1) 1)) := by
            have h := hΩ.rule_three m 1 (m - 1) 1 hcop (by omega) le_rfl hp
            rwa [hsub, Nat.sub_self, hΩ.base_two] at h
          rw [slopeEval_succ_right Y Z hm2, mul_assoc, hih3, hr3, hZ, mul_smul_comm,
            smul_mul_assoc, neg_one_pow_sub_two hm2, neg_smul, smul_neg]
        · -- `m, n ≥ 2`
          obtain ⟨m₁, n₁, hp⟩ := exists_isSBParent hcop (by omega) (by omega)
          obtain ⟨hm₁, hn₁, hm₁lt, hn₁lt⟩ := isSBParent_pos hm2 hn2 hp
          obtain ⟨hc₁, hc₂⟩ := isSBParent_coprime hp
          have hdet := isSBParent_det hp
          obtain ⟨m₂, hm₂e⟩ : ∃ m₂, m = m₁ + m₂ := ⟨m - m₁, by omega⟩
          obtain ⟨n₂, hn₂e⟩ : ∃ n₂, n = n₁ + n₂ := ⟨n - n₁, by omega⟩
          subst hm₂e
          subst hn₂e
          simp only [Nat.add_sub_cancel_left] at hdet hc₂
          have hm₂ : 1 ≤ m₂ := by omega
          have hn₂ : 1 ≤ n₂ := by omega
          have hr3 : Ω 3 (m₁ + m₂) (n₁ + n₂) = -((q * u)⁻¹ • (Ω 2 m₂ n₂ * Ω 3 m₁ n₁)) := by
            have h := hΩ.rule_three (m₁ + m₂) (n₁ + n₂) m₁ n₁ hcop (by omega) (by omega) hp
            rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h
          have hih1 := ih m₁ n₁ (by omega) hc₁ hm₁ hn₁ 3 (by omega) le_rfl
          have hih2 := ih m₂ n₂ (by omega) hc₂ hm₂ hn₂ 2 (by omega) (by omega)
          have hscal : (q * u)⁻¹ * (-1 : L) ^ (m₂ - 1) * (-1 : L) ^ (m₁ - 1)
              = -((-1 : L) ^ (m₁ + m₂ - 1) * (q * u)⁻¹) := by
            calc (q * u)⁻¹ * (-1 : L) ^ (m₂ - 1) * (-1 : L) ^ (m₁ - 1)
                = (q * u)⁻¹ * ((-1 : L) ^ (m₁ - 1) * (-1 : L) ^ (m₂ - 1)) := by ring
              _ = (q * u)⁻¹ * -((-1 : L) ^ (m₁ + m₂ - 1)) := by
                  rw [neg_one_pow_add_sub_one hm₁ hm₂]
              _ = -((-1 : L) ^ (m₁ + m₂ - 1) * (q * u)⁻¹) := by ring
          rw [slopeEval_mediant Y Z hm₁ hn₁ hm₂ hn₂ hdet hc₁ hc₂, hr3]
          calc slopeEval Y Z m₂ n₂ * (Y * (Z * slopeEval Y Z m₁ n₁)) * Ω 3 1 1
              = slopeEval Y Z m₂ n₂ * (Y * Z) * (slopeEval Y Z m₁ n₁ * Ω 3 1 1) := by
                simp only [mul_assoc]
            _ = ((q * u)⁻¹ • ((-1 : L) ^ (m₂ - 1) • Ω 2 m₂ n₂))
                  * ((-1 : L) ^ (m₁ - 1) • Ω 3 m₁ n₁) := by
                rw [hYZ, mul_smul_comm, hih2, hih1]
            _ = ((q * u)⁻¹ * (-1 : L) ^ (m₂ - 1) * (-1 : L) ^ (m₁ - 1))
                  • (Ω 2 m₂ n₂ * Ω 3 m₁ n₁) := by
                rw [smul_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
            _ = (-1 : L) ^ (m₁ + m₂ - 1) • -((q * u)⁻¹ • (Ω 2 m₂ n₂ * Ω 3 m₁ n₁)) := by
                rw [smul_neg, smul_smul, ← neg_smul, hscal]

/-- **The extended Euclidean identities.** `HJO.Mellit.euclid`: for coprime
`m, n ≥ 1`, a replication family `Ω` on a Carlsson–Mellit sweep system, and `j ∈ {1,2,3}`,
`Ξ_{m,n}\,Ω(j;1,1) = (-1)^{m-1}\,Ω(j;m,n)`.

The slope operator is `HJO.Mellit.slopeEval` at `Y = -y_1` and `Z = (qu)^{-1}z_1`, which is
`HJO.Sweep.slopeOperator` — see `HJO.Sweep.slopeOperator_eq_slopeEval`. The identity is an
equality of endomorphisms of the whole space, which is stronger than the reading as maps
`V_k → V_{k+1}` for `j = 1` and as endomorphisms of `V_k` for `j ∈ {2,3}`; the gradings are carried
by `HJO.Mellit.IsReplicationFamily` and the reading follows by restriction.

There is **no hypothesis on `q` and `u`** and none is missing. Every occurrence of `(qu)^{-1}` is a
scalar sitting in the same place on both sides, so the identity never asks for `(qu)(qu)^{-1} = 1`;
it holds at `q = 0`, at `u = 0`, at `qu = 1` and at `u` a root of unity. -/
@[hjo "lem_mellit_euclid"]
theorem euclid (hΩ : IsReplicationFamily S Ω) {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 1 ≤ m)
    (hn : 1 ≤ n) {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    slopeEval (-S.y1) ((q * u)⁻¹ • S.z1) m n * Ω j 1 1 = (-1 : L) ^ (m - 1) • Ω j m n :=
  euclid_aux hΩ _ _ rfl rfl (m + n) m n le_rfl hmn hm hn j hj1 hj3

end Euclid

end HJO.Mellit

namespace HJO.Sweep

/-- **The slope operator is the monoid evaluation.** `HJO.Sweep.slopeOperator`, which carries
`HJO.Sweep.slopeOperator`, is `HJO.Mellit.slopeEval` at `Y = -y_1` and `Z = (qu)^{-1}z_1` in
`Module.End L (Total L)`. Recorded so that the abstract evaluation used by `HJO.Mellit.euclid` is
not a second, unattributed reading of the definition. -/
theorem slopeOperator_eq_slopeEval {L : Type*} [Field L] [Algebra ℚ L] (q u : L) (k m n : ℕ) :
    slopeOperator q u k m n
      = Mellit.slopeEval (-LinearMap.mulLeft L (auxVar 1 : Total L))
          ((q * u)⁻¹ • zop q u k 1) m n :=
  rfl

end HJO.Sweep
