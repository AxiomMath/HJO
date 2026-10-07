/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitStageInduction
public meta import HJO.Attr

/-! # Mellit's Section 6: the Stern–Brocot parent, and the rigidity of a replication family

Two arithmetic statements open Mellit's Section 6, and both are about the *extended Euclidean
algorithm* that the section's identities run on.

The first is that a coprime pair `(m, n)` of positive integers has exactly one **Stern–Brocot
parent**: exactly one pair of integers `(m₁, n₁)` inside the box `0 ≤ m₁ ≤ m`, `0 ≤ n₁ ≤ n`
with `m n₁ - n m₁ = 1`. Existence is Bézout with the solution normalised into the box; uniqueness
is that two solutions differ by an integer multiple of `(m, n)`, and the box admits no nonzero
multiple. Its complement `(m₂, n₂) = (m - m₁, n - n₁)` is the other parent, `(m, n)` being their
mediant, and the recursion of `HJO.Mellit.IsReplicationFamily` descends the Stern–Brocot tree along
them.

The second is that the recursion leaves nothing free. A **replication family** `Ω` is pinned at
the three base values `Ω(1;1,0) = d^*_+`, `Ω(2;1,0) = z_1`, `Ω(3;0,1) = y_1` and by the three
Stern–Brocot rules; the rules never read the remaining three triples `(1;0,1)`, `(2;0,1)` and
`(3;1,0)`, and off those three any two families agree. So "let `Ω` be a replication family" names
an essentially unique object rather than a choice, and the extended Euclidean identities of the
section are statements about *the* replicated operators.

## Main results

* `HJO.Mellit.existsUnique_int_sbParent`: the Stern–Brocot parent of a coprime pair of positive
  integers exists and is unique, among pairs of **integers** in the box.
* `HJO.Mellit.IsReplicationFamily.eq_index_one`,
  `HJO.Mellit.IsReplicationFamily.eq_index_two`,
  `HJO.Mellit.IsReplicationFamily.eq_index_three`: two replication families on one sweep system
  agree at each index, off the one unpinned pair for that index.

## Implementation notes

Both results are the Section 6 readings of mathematics the shuffle layer already carries, and each
is deduced from it rather than reproved.

`existsUnique_int_sbParent` quantifies over `ℤ × ℤ`, and its moduli `m, n` over `ℤ`, because that
is the generality the statement is made at: the box conditions force nonnegativity, so the
`ℕ`-valued form `HJO.Mellit.existsUnique_isSBParent` — the same statement in the vocabulary
`HJO.Mellit.IsSBParent` that `HJO.Mellit.IsReplicationFamily` is written in — is the special case
`m, n : ℕ`, and it is what the proof here reduces to.

The rigidity statement is split into one lemma per index rather than carried as a single claim
quantified over `j ∈ {1, 2, 3}`, because the excepted pair depends on the index: `(0, 1)` for
`j ∈ {1, 2}` and `(1, 0)` for `j = 3`. Each is then a hypothesis-free rewrite at a use site,
where the packed form `HJO.Mellit.ReplUnique` needs the index bounds discharged first. The three
are the three cases of `HJO.Mellit.replUnique`, which proves the packed form by strong induction on
the index sum.

The side condition `m + n ≥ 1` on the pair is not a hypothesis of the three: it is implied by
coprimality, `Nat.Coprime 0 0` being `Nat.gcd 0 0 = 1` and so false. The pairs quantified over are
therefore exactly the intended ones.

Like every statement of the Mellit layer these are read relative to a `HJO.Mellit.SweepSystem`
rather than on one fixed module; `HJO.Mellit.sweepWitness` is a system whose operators are the
actual `d^*_+`, `z_1` and `y_1`, so reading them there gives the statements on the actual objects.

## References

Mellit's Section 6, the extended Euclidean identities: `HJO.Mellit.existsUnique_int_sbParent`,
`HJO.Mellit.IsReplicationFamily.eq_index_one`, and the definition they are about,
`HJO.Mellit.IsReplicationFamily`. The first is `HJO.Mellit.existsUnique_isSBParent` restated in the
section that uses it. A. Mellit, *Toric braids and `(m, n)`-parking functions*, §6.
-/

@[expose] public section

namespace HJO.Mellit

universe w

/-! ### The Stern–Brocot parent -/

/-- **The Stern–Brocot parent.** `HJO.Mellit.existsUnique_int_sbParent`: for coprime integers
`m, n ≥ 1` there is exactly one pair of integers `(m₁, n₁)` with `0 ≤ m₁ ≤ m`, `0 ≤ n₁ ≤ n` and
`m n₁ - n m₁ = 1`.

Both hypotheses are spent on existence, and in the same place: at `n = 0` the equation reads
`m n₁ = 1` with `n₁ = 0` forced by the box, and at `m = 0` it reads `-n m₁ = 1` with `m₁ = 0`
forced, so neither degenerate pair has a parent even though both are coprime. Uniqueness needs
only `1 ≤ m`.

The pair is the one `HJO.Mellit.IsReplicationFamily` recurses on: the complement
`(m₂, n₂) = (m - m₁, n - n₁)` satisfies `m₂ n₁ - m₁ n₂ = 1` as well, so both parents are coprime,
both have smaller index sum, and the two-parent recursion descends. -/
@[hjo "lem_mellit_sb_exists"]
theorem existsUnique_int_sbParent {m n : ℤ} (hmn : IsCoprime m n) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃! p : ℤ × ℤ, 0 ≤ p.1 ∧ p.1 ≤ m ∧ 0 ≤ p.2 ∧ p.2 ≤ n ∧ m * p.2 - n * p.1 = 1 := by
  have hM : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hN : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
  have hcop : Nat.Coprime m.toNat n.toNat := Nat.isCoprime_iff_coprime.1 (by rwa [hM, hN])
  have hM1 : 1 ≤ m.toNat := by omega
  have hN1 : 1 ≤ n.toNat := by omega
  -- Every integer pair in the box is a `IsSBParent` pair of the truncations, and conversely.
  have key : ∀ p : ℤ × ℤ, 0 ≤ p.1 → p.1 ≤ m → 0 ≤ p.2 → p.2 ≤ n → m * p.2 - n * p.1 = 1 →
      IsSBParent m.toNat n.toNat p.1.toNat p.2.toNat := by
    intro p ha0 ham hb0 hbn he
    refine ⟨by omega, by omega, ?_⟩
    rw [hM, hN, Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0]
    exact he
  obtain ⟨⟨m₁, n₁⟩, h, -⟩ := existsUnique_isSBParent hcop hM1 hN1
  obtain ⟨hm1, hn1, he⟩ := h
  refine ⟨((m₁ : ℤ), (n₁ : ℤ)), ⟨by positivity, by omega, by positivity, by omega, ?_⟩, ?_⟩
  · rw [← hM, ← hN]; exact he
  · rintro ⟨a, b⟩ ⟨ha0, ham, hb0, hbn, hab⟩
    obtain ⟨e1, e2⟩ :=
      isSBParent_unique hcop hM1 (key (a, b) ha0 ham hb0 hbn hab) ⟨hm1, hn1, he⟩
    simp only at e1 e2
    exact Prod.ext (by omega) (by omega)

/-! ### A replication family is rigid

`HJO.Mellit.IsReplicationFamily` pins `Ω(1;1,0)`, `Ω(2;1,0)` and `Ω(3;0,1)` outright, and its three
Stern–Brocot rules pin every value at a coprime pair with both entries positive. The three
remaining triples `(1;0,1)`, `(2;0,1)` and `(3;1,0)` it never mentions — and never reads, since a
Stern–Brocot parent of `(m, n)` with `n ≥ 1` is not `(1, 0)` and a complement with `m ≥ 1` is not
`(0, 1)`. Off those three, then, two families agree. -/

/-- A coprime pair of natural numbers has positive index sum, `Nat.Coprime 0 0` being false. This
is why the side condition `m + n ≥ 1` is not carried as a hypothesis below. -/
private theorem one_le_add_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) : 1 ≤ m + n := by
  by_contra h
  obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
  exact Nat.not_coprime_zero_zero hmn

variable {L : Type w} [Field L] [Algebra ℚ L] {q u : L} {S : SweepSystem L q u}
  {Ω Ω' : ℕ → ℕ → ℕ → (S.W →ₗ[L] S.W)}

/-- **`HJO.Mellit.IsReplicationFamily.eq_index_one` at index `1`.** Two replication families agree
at `Ω(1; m, n)` for every coprime `(m, n)` other than `(0, 1)`, where
`HJO.Mellit.IsReplicationFamily` pins nothing. -/
@[hjo "lem_mellit_repl_unique"]
theorem IsReplicationFamily.eq_index_one (hΩ : IsReplicationFamily S Ω)
    (hΩ' : IsReplicationFamily S Ω') {m n : ℕ} (hmn : Nat.Coprime m n)
    (hne : (m, n) ≠ (0, 1)) : Ω 1 m n = Ω' 1 m n :=
  replUnique S Ω Ω' hΩ hΩ' 1 m n le_rfl (by norm_num) hmn (one_le_add_of_coprime hmn)
    (fun h => hne (by simp_all)) (by simp) (by simp)

/-- **`HJO.Mellit.IsReplicationFamily.eq_index_one` at index `2`.** Two replication families agree
at `Ω(2; m, n)` for every coprime `(m, n)` other than `(0, 1)`, where
`HJO.Mellit.IsReplicationFamily` pins nothing. -/
@[hjo "lem_mellit_repl_unique"]
theorem IsReplicationFamily.eq_index_two (hΩ : IsReplicationFamily S Ω)
    (hΩ' : IsReplicationFamily S Ω') {m n : ℕ} (hmn : Nat.Coprime m n)
    (hne : (m, n) ≠ (0, 1)) : Ω 2 m n = Ω' 2 m n :=
  replUnique S Ω Ω' hΩ hΩ' 2 m n (by norm_num) (by norm_num) hmn (one_le_add_of_coprime hmn)
    (by simp) (fun h => hne (by simp_all)) (by simp)

/-- **`HJO.Mellit.IsReplicationFamily.eq_index_one` at index `3`.** Two replication families agree
at `Ω(3; m, n)` for every coprime `(m, n)` other than `(1, 0)`, where
`HJO.Mellit.IsReplicationFamily` pins nothing. -/
@[hjo "lem_mellit_repl_unique"]
theorem IsReplicationFamily.eq_index_three (hΩ : IsReplicationFamily S Ω)
    (hΩ' : IsReplicationFamily S Ω') {m n : ℕ} (hmn : Nat.Coprime m n)
    (hne : (m, n) ≠ (1, 0)) : Ω 3 m n = Ω' 3 m n :=
  replUnique S Ω Ω' hΩ hΩ' 3 m n (by norm_num) le_rfl hmn (one_le_add_of_coprime hmn)
    (by simp) (by simp) (fun h => hne (by simp_all))

end HJO.Mellit

end
