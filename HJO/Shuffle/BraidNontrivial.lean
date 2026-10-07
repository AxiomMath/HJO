/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidRotation
public meta import HJO.Attr

/-! # The braid monoid is not trivial

Every identity of the braid layer — `HJO.Braid.braidWord_pair_comm`, the train identities, the
relations for the commuting lifts — is an equation in `HJO.Braid.BraidMonoid`, and each of them
would hold for free if that monoid had one element. This file proves that it has more than one, in
one line, from the `z`-counting homomorphism.

## Main results

* `HJO.Braid.braidGenZ_ne_one` — `z_a ≠ 1` in `𝔹_k^+(𝕋_0)` for `1 ≤ a` and `1 ≤ k`.
* `HJO.Braid.braidMonoid_nontrivial` — `𝔹_k^+(𝕋_0)` has at least two elements, for every `k ≥ 1`.

## Implementation notes

The witness is the `z`-counting homomorphism `HJO.Braid.zCount`: it sends `z_a` to `1` and the
identity to `0`, so the two are different elements. That homomorphism is the one
`HJO.Braid.zCount_mul` builds, and it exists precisely because no relation family of
`HJO.Braid.BraidMonoid` changes the number of `𝗓_1` letters of a word — the one family mixing `𝗓_1`
with `𝗒_1` has one of each on both sides.

Stated as a theorem and not an instance: nothing here needs `Nontrivial` by typeclass
search, and an instance would start firing in the side conditions of unrelated lemmas.

At `k = 0` the monoid **is** trivial — every letter is out of rank — which is why `1 ≤ k` is a
hypothesis here and in `HJO.Braid.zCount`.

## References

Uses the homomorphism of `HJO.Braid.zCount_mul` and the definition `HJO.Braid.BraidMonoid`. -/

@[expose] public section

namespace HJO.Braid

/-- **`z_a ≠ 1`**: the `z`-counting homomorphism of `HJO.Braid.zCount_mul` separates them, one
having `z`-count `1` and the other `0`. -/
theorem braidGenZ_ne_one {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : 1 ≤ a) :
    braidGenZ k a ≠ 1 := fun h => by
  simpa [zCount_braidGenZ hk ha] using congrArg (zCount k hk) h

/-- **The braid monoid of the punctured torus is not trivial** for `k ≥ 1`. So the identities the
braid layer proves — every one of them an equation in `HJO.Braid.BraidMonoid` — are not vacuously
true of a one-element monoid. -/
theorem braidMonoid_nontrivial {k : ℕ} (hk : 1 ≤ k) : Nontrivial (BraidMonoid k) :=
  ⟨braidGenZ k 1, 1, braidGenZ_ne_one hk le_rfl⟩

end HJO.Braid
