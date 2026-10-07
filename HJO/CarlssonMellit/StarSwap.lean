/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DPATwoSided
public meta import HJO.Attr

/-! # The star swap, and the starred corner elements of `𝔹`

`HJO.Dyck.IsStarSwap`: let `A` be a quotient of `𝔹` of `HJO.Dyck.TwoSided.Bq` and write `e_k`,
`T_i`, `d₋`, `d₊`, `d₊^*` for the images in `A` of the generators of the same name. An additive map
`σ : A → A` is a *star swap* if `σ(cx) = c̄σ(x)`, `σ(xy) = σ(x)σ(y)`, `σ(σ(x)) = x`,
`σ(e_k) = e_k`, `σ(d₋) = d₋`, `σ(d₊) = d₊^*`, `σ(d₊^*) = d₊`, and `σ(T_i) = T̂_i` for `k ≥ 2` and
`1 ≤ i ≤ k-1`.

`HJO.Dyck.TwoSided.Bq.zElt`: for `k ≥ 1` the starred corner elements `z_1, …, z_k` of `e_k𝔹e_k` are
`z_k = (q⁻¹-1)⁻¹T_{k-1}⋯T_1(d₊^*d₋ - d₋d₊^*)e_k` and `z_i = qT̂_iz_{i+1}T̂_i` walking down.

## The star swap is conjugate-linear, so it is not an `AlgHom`

The bar of `HJO.Sym.paramInvLambda` is `q ↦ q⁻¹` on the coefficients, and `σ(cx) = c̄σ(x)`; so `σ`
is `K`-linear only where the bar is the identity, and an `A →ₐ[K] A` cannot state it. Two further
shapes are also wrong: a `RingHom` over the involuted base is a map between two *different* types
here (`𝔹` is built from the relation list at the scalar `q`, and the involuted base would rebuild
it at `q⁻¹`), and a `LinearMap` over a `RingHom`-semilinear `SMul` would have to be set up against
the canonical `Algebra K (RingQuot _)` instance already in scope.

What is used instead is the shape this library already uses for the *same* conjugate-linear
involution one level up, `HJO.Sweep.IsConjugationOperator`:
the bar is carried as an argument `bar : K ≃+* K`, the map is an `A →+ A`, and the
conjugate-linearity `σ(cx) = bar c • σ(x)` is a field of the predicate rather than part of the
bundling. Nothing is lost: `σ(1) = 1` is *derivable* from the clauses below — `σ` is multiplicative
and involutive, hence surjective, and `σ(1)σ(x) = σ(x)` for every `x` — so bundling `σ` as a
`RingHom` would state the same predicate, and bundling it as an `AddMonoidHom` keeps the clause list
exactly as listed above.

**The range on `σ(T_i) = T̂_i` is not decoration.** At `i + 2 > k` the quiver has no loop `T_i` at
the vertex `k`, so `T_i = 0` and `σ(T_i) = 0`, while `T̂_i = q⁻¹(0 + (q-1)e_k)` is `q⁻¹(q-1)e_k`.
Dropping the range would therefore force `(q-1)e_k = 0`, killing every idempotent as soon as
`q ≠ 1`; the clause is stated on `i + 2 ≤ k`, which is the range `k ≥ 2`, `1 ≤ i ≤ k-1` in
the shifted indexing of `HJO.Dyck.TwoSided.Bq.Tg`.

## `z_i` speaks the Carlsson--Mellit `d₋`, and the prefactor hides no division by zero

`d₋` here is the lowering *arrow of the quiver* of `HJO.Dyck.Aq`, a formal generator; the
convention question (`HJO.Sweep.dminus` pairing `F_j` with `e_j` against `HJO.Sweep.dminusCM`
pairing it with `e_{j+1}`) is a question about the *representation*, and the representation the
star swaps are transported along is `HJO.Sweep.dminusVstar`, assembled from
`HJO.Sweep.dminusCM`, the Carlsson--Mellit operator. So `z_i` speaks Carlsson--Mellit's `d₋`, and
agrees with the starred action built from it.

The prefactor `(q⁻¹-1)⁻¹` is written here as the ring element `-(q(q-1)⁻¹)`, whose
product with `q⁻¹-1` is `1` by `HJO.Dyck.Tilde.neg_mul_invOf_sub_one_mul`. That is deliberate: a
Lean `(q⁻¹ - 1)⁻¹` in a field would be `0` at `q = 1` and the definition would silently degenerate
rather than fail to typecheck. Written as above the two side conditions `q ≠ 0` and `q ≠ 1` are
carried as the instances `[Invertible q]` and `[Invertible (q - 1)]`, and there is no division.

## The word of loops in `z_k` is unstarred

The formula for `z_k` has `T_{k-1}⋯T_1` and not `T̂_{k-1}⋯T̂_1`, and that is not a slip: `z` is `y`
after the substitution `T_i ↦ T_i⁻¹`, so the descending word of *inverses* in `y_k` becomes a
descending word of inverses-of-inverses, which is the word of loops again. Inside the formula that
is `HJO.Dyck.Tilde.tinvOf_tinvOf`, and `HJO.Dyck.tinvWordOf_tinvOf_eq_braidWordOf` is the statement
that the substituted word collapses. `HJO.Dyck.TwoSided.Bq.zElt_self` is therefore stated with the
unstarred word, exactly as in the formula above.

## Main definitions

* `HJO.Dyck.braidWordOf`: the descending word `T_n ⋯ T_1` of loops at a vertex.
* `HJO.Dyck.IsStarSwap`: the star swaps of a quotient of `𝔹`.
* `HJO.Dyck.TwoSided.Bq.yElt`, `HJO.Dyck.TwoSided.Bq.zElt`: the corner elements of `e_k𝔹e_k`, the
  second being the starred family `z_1, …, z_k`.

## Main results

* `HJO.Dyck.map_cornerOf_bar`: a conjugate-linear multiplicative map carries the corner element
  built from one family to the corner element built from the images, with each scalar barred.
* `HJO.Dyck.IsStarSwap.map_cornerOf`, that `σ(y_i) = z_i`.
* `HJO.Dyck.IsStarSwap.map_cornerOf_symm`, that `σ(z_i) = y_i`.

## References

Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The descending word of loops -/

section BraidWord

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]

/-- The descending word `T_n ⋯ T_1` of loops at the vertex `k`, the empty word being the
idempotent `E k`. This is `HJO.Dyck.tinvWordOf` with the loops themselves in place of their
polynomial inverses, and it is the word appearing in the formula for `z_k`. -/
def braidWordOf (E : ℕ → A) (T : ℕ → ℕ → A) (k : ℕ) : ℕ → A
  | 0 => E k
  | n + 1 => T k n * braidWordOf E T k n

@[simp] theorem braidWordOf_zero (E : ℕ → A) (T : ℕ → ℕ → A) (k : ℕ) :
    braidWordOf E T k 0 = E k := rfl

theorem braidWordOf_succ (E : ℕ → A) (T : ℕ → ℕ → A) (k n : ℕ) :
    braidWordOf E T k (n + 1) = T k n * braidWordOf E T k n := rfl

variable {q : K} [Invertible q]

/-- **The substituted word of inverses is the word of loops.** Reading
`HJO.Dyck.tinvWordOf` at the substituted scalars `q⁻¹`, `q` and at the family of polynomial
inverses returns the descending word of the loops themselves, each factor collapsing by
`HJO.Dyck.Tilde.tinvOf_tinvOf`. This is why `HJO.Dyck.TwoSided.Bq.zElt` displays `T_{k-1} ⋯ T_1` and
not `T̂_{k-1} ⋯ T̂_1`. -/
theorem tinvWordOf_tinvOf_eq_braidWordOf (E : ℕ → A) (T : ℕ → ℕ → A) (k n : ℕ) :
    tinvWordOf (⅟q) q E (fun m j => tinvOf q ⅟q (T m j) (E m)) k n = braidWordOf E T k n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tinvWordOf, braidWordOf_succ, ih, Tilde.tinvOf_tinvOf]

end BraidWord

/-! ### Transport along a conjugate-linear multiplicative map -/

section Semilinear

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A] {B : Type*} [Ring B]
  [Algebra K B] {bar : K ≃+* K} {f : A →+ B}
variable {E U D : ℕ → A} {E' U' D' : ℕ → B} {T : ℕ → ℕ → A} {T' : ℕ → ℕ → B}

/-- A conjugate-linear multiplicative map carries the commutator of one raising and one lowering
family to the commutator of the images. -/
theorem map_commOf_bar (hmul : ∀ x y : A, f (x * y) = f x * f y) (hU : ∀ n, f (U n) = U' n)
    (hD : ∀ n, f (D n) = D' n) (k : ℕ) : f (commOf U D k) = commOf U' D' k := by
  rw [commOf, commOf, map_sub, hmul, hmul, hU, hD, hU, hD]

/-- A conjugate-linear multiplicative map carries a polynomial inverse to the polynomial inverse
of the image at the barred scalars. -/
theorem map_tinvOf_bar (hsmul : ∀ (c : K) (x : A), f (c • x) = bar c • f x) (a b : K)
    {t e : A} {t' e' : B} (ht : f t = t') (he : f e = e') :
    f (tinvOf a b t e) = tinvOf (bar a) (bar b) t' e' := by
  rw [tinvOf, tinvOf, hsmul, map_add, hsmul, ht, he, map_sub, map_one]

/-- A conjugate-linear multiplicative map carries the descending word of polynomial inverses to
the descending word of the images at the barred scalars, provided every loop it reads lies in the
range at which the map is known on loops. -/
theorem map_tinvWordOf_bar (hmul : ∀ x y : A, f (x * y) = f x * f y)
    (hsmul : ∀ (c : K) (x : A), f (c • x) = bar c • f x) (a b : K) (hE : ∀ n, f (E n) = E' n)
    {k : ℕ} (hT : ∀ i, i + 2 ≤ k → f (T k i) = T' k i) :
    ∀ n, n + 1 ≤ k → f (tinvWordOf a b E T k n) = tinvWordOf (bar a) (bar b) E' T' k n := by
  intro n
  induction n with
  | zero => intro _; exact hE k
  | succ n ih =>
    intro hn
    rw [tinvWordOf, tinvWordOf, hmul, map_tinvOf_bar hsmul a b (hT n (by omega)) (hE k),
      ih (by omega)]

/-- A conjugate-linear multiplicative map carries the corner elements of one family to those of
the images, each of the three scalars barred, for as many steps down as the loops it reads stay in
range. -/
theorem map_cornerAux_bar (hmul : ∀ x y : A, f (x * y) = f x * f y)
    (hsmul : ∀ (c : K) (x : A), f (c • x) = bar c • f x) (a b c : K) (hE : ∀ n, f (E n) = E' n)
    (hU : ∀ n, f (U n) = U' n) (hD : ∀ n, f (D n) = D' n) {k : ℕ}
    (hT : ∀ i, i + 2 ≤ k → f (T k i) = T' k i) :
    ∀ j, j + 1 ≤ k → f (cornerAux a b c E U D T k j)
      = cornerAux (bar a) (bar b) (bar c) E' U' D' T' k j := by
  intro j
  induction j with
  | zero =>
    intro hk
    rw [cornerAux, cornerAux, hsmul, hmul, hmul,
      map_tinvWordOf_bar hmul hsmul a b hE hT (k - 1) (by omega),
      map_commOf_bar hmul hU hD, hE]
  | succ j ih =>
    intro hj
    rw [cornerAux, cornerAux, hsmul, hmul, hmul, ih (by omega), hT (k - j - 2) (by omega)]

/-- **A conjugate-linear multiplicative map carries corner elements to corner elements.** The
three scalars of `HJO.Dyck.cornerOf` are barred, the four families are replaced by their images,
and the index range is `1 ≤ i ≤ k`, which is exactly the range in which every
loop the formula reads is a loop the quiver has. -/
theorem map_cornerOf_bar (hmul : ∀ x y : A, f (x * y) = f x * f y)
    (hsmul : ∀ (c : K) (x : A), f (c • x) = bar c • f x) (a b c : K) (hE : ∀ n, f (E n) = E' n)
    (hU : ∀ n, f (U n) = U' n) (hD : ∀ n, f (D n) = D' n) {k i : ℕ}
    (hT : ∀ j, j + 2 ≤ k → f (T k j) = T' k j) (hi : 1 ≤ i) (hik : i ≤ k) :
    f (cornerOf a b c E U D T k i) = cornerOf (bar a) (bar b) (bar c) E' U' D' T' k i :=
  map_cornerAux_bar hmul hsmul a b c hE hU hD hT (k - i) (by omega)

end Semilinear

/-! ### What the bar does to the three scalars -/

section Bar

variable {K : Type*} [CommRing K] (bar : K ≃+* K) {q : K} [Invertible q]

/-- The bar inverts `q`, hence also `q⁻¹`: `q̄⁻¹ = q`. Only `bar q = q⁻¹` is used, not that the
bar is an involution. -/
theorem bar_invOf (hbar : bar q = ⅟q) : bar ⅟q = q := by
  have h0 : bar ⅟q * bar q = 1 := by rw [← map_mul, invOf_mul_self, map_one]
  have h : bar ⅟q * ⅟q = 1 := by rwa [hbar] at h0
  calc bar ⅟q = bar ⅟q * (⅟q * q) := by rw [invOf_mul_self, mul_one]
    _ = bar ⅟q * ⅟q * q := by rw [mul_assoc]
    _ = q := by rw [h, one_mul]

variable [Invertible (q - 1)]

/-- **The bar of the prefactor of `y_k` is the prefactor of `z_k`**: `(q-1)⁻¹` goes to
`-(q(q-1)⁻¹)`, which is the ring element standing for `(q⁻¹-1)⁻¹` in `HJO.Dyck.TwoSided.Bq.zElt`.
Both are inverses of `q⁻¹-1` — the second by `HJO.Dyck.Tilde.neg_mul_invOf_sub_one_mul` — and an
inverse in a commutative ring is unique. -/
theorem bar_invOf_sub_one (hbar : bar q = ⅟q) : bar ⅟(q - 1) = -(q * ⅟(q - 1)) := by
  have hb1 : bar (q - 1) = ⅟q - 1 := by rw [map_sub, hbar, map_one]
  have h : bar ⅟(q - 1) * (⅟q - 1) = 1 := by
    rw [← hb1, ← map_mul, invOf_mul_self, map_one]
  have hx : (⅟q - 1) * -(q * ⅟(q - 1)) = 1 := by
    rw [mul_comm]; exact Tilde.neg_mul_invOf_sub_one_mul
  calc bar ⅟(q - 1) = bar ⅟(q - 1) * ((⅟q - 1) * -(q * ⅟(q - 1))) := by rw [hx, mul_one]
    _ = bar ⅟(q - 1) * (⅟q - 1) * -(q * ⅟(q - 1)) := by rw [mul_assoc]
    _ = -(q * ⅟(q - 1)) := by rw [h, one_mul]

end Bar

/-! ### The star swap -/

/-- **A star swap.** Let `A` be a quotient of `𝔹` and let `E`, `U`, `Ustar`,
`D`, `T` be the images in `A` of `e_k`, `d₊`, `d₊^*`, `d₋` and the loops. An additive map
`σ : A → A` is a *star swap* if

* it is conjugate-linear over the bar of `HJO.Sym.paramInvLambda`: `σ(cx) = c̄σ(x)`;
* it is multiplicative: `σ(xy) = σ(x)σ(y)`;
* it is an involution: `σ(σ(x)) = x`;
* it fixes every idempotent and the lowering arrow;
* it exchanges the two raising arrows;
* it carries each loop the quiver has to the polynomial inverse of `HJO.Dyck.braidInvGen`.

Nothing here asserts that a star swap exists; that is `HJO.Dyck.TwoSided.exists_isStarSwap` for `𝔹`
and `HJO.Dyck.Tilde.Atilde.exists_isStarSwap` for `Ã`, and this predicate is what their consumers
spend.

The predicate reads the generator families rather than a quotient map, so it applies verbatim to
`𝔹`, to `Ã`, and to any further quotient — which is what "let `A` be a quotient of `𝔹` and write
`e_k`, `T_i`, `d₋`, `d₊`, `d₊^*` for the images in `A`" in the module documentation asks for. None
of the relations of `𝔹` is required of the families: every clause is a statement about `σ` alone, so
the predicate is available before any relation is checked, and every consequence below holds in that
generality.

`bar` is carried as an argument and is not assumed to invert `q`; the lemmas that need
`bar q = q⁻¹` take it as a hypothesis, as `HJO.Sym.paramInvLambda` does for the same reason — over
a general base ring `q ↦ q⁻¹` is not an automorphism at all. -/
@[hjo "def_cm_star_swap"]
structure IsStarSwap {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A] (q : K)
    [Invertible q] (bar : K ≃+* K) (E U Ustar D : ℕ → A) (T : ℕ → ℕ → A) (σ : A →+ A) : Prop where
  /-- `σ(cx) = c̄σ(x)`: `σ` is conjugate-linear over the bar. -/
  map_smul : ∀ (c : K) (x : A), σ (c • x) = bar c • σ x
  /-- `σ(xy) = σ(x)σ(y)`. -/
  map_mul : ∀ x y : A, σ (x * y) = σ x * σ y
  /-- `σ(σ(x)) = x`. -/
  involutive : ∀ x : A, σ (σ x) = x
  /-- `σ(e_k) = e_k` for every `k ≥ 0`. -/
  map_e : ∀ k, σ (E k) = E k
  /-- `σ(d₋) = d₋`. -/
  map_dMinus : ∀ k, σ (D k) = D k
  /-- `σ(d₊) = d₊^*`. -/
  map_dPlus : ∀ k, σ (U k) = Ustar k
  /-- `σ(d₊^*) = d₊`. -/
  map_dPlusStar : ∀ k, σ (Ustar k) = U k
  /-- `σ(T_i) = T̂_i` for every `k ≥ 2` and every `1 ≤ i ≤ k-1`, which is `i + 2 ≤ k` in the
  shifted indexing of the loops. Outside that range the quiver has no loop and the clause would be
  false: `σ(0) = 0` while `T̂_i` is `q⁻¹(q-1)e_k`. -/
  map_T : ∀ {k i : ℕ}, i + 2 ≤ k → σ (T k i) = tinvOf q ⅟q (T k i) (E k)

namespace IsStarSwap

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A] {q : K} [Invertible q]
variable {bar : K ≃+* K} {E U Ustar D : ℕ → A} {T : ℕ → ℕ → A} {σ : A →+ A}
variable (h : IsStarSwap q bar E U Ustar D T σ)

include h

/-- A star swap is surjective, being an involution. -/
theorem surjective : Function.Surjective σ := fun x => ⟨σ x, h.involutive x⟩

/-- A star swap fixes the unit. It is *derived* and not assumed: `σ` is multiplicative and
surjective, so `σ(1)y = y` for every `y`, and `y = 1` gives the claim. -/
theorem map_one : σ 1 = 1 := by
  obtain ⟨y, hy⟩ := h.surjective 1
  calc σ 1 = σ 1 * 1 := (mul_one _).symm
    _ = σ 1 * σ y := by rw [hy]
    _ = σ (1 * y) := (h.map_mul 1 y).symm
    _ = σ y := by rw [one_mul]
    _ = 1 := hy

variable [Invertible (q - 1)]

/-- **A star swap carries a corner element to the starred one.** For every
`k ≥ 1` and every `1 ≤ i ≤ k`, `σ(y_i) = z_i`, where `y_i` is `HJO.Dyck.cornerOf` at the unstarred
family and `z_i` is the same formula at the starred one — the scalars `q`, `q⁻¹`, `(q-1)⁻¹` of
`HJO.Dyck.Aq.yElt` becoming `q⁻¹`, `q`, `-(q(q-1)⁻¹)`, the raising arrow becoming the starred one,
and each loop becoming its polynomial inverse.

The proof is a single transport: `HJO.Dyck.map_cornerOf_bar` carries the formula,
`HJO.Dyck.bar_invOf` and `HJO.Dyck.bar_invOf_sub_one` identify the three barred scalars, and the
range `1 ≤ i ≤ k` is what keeps every loop the formula reads inside the range of `map_T`.

One may reach `σ(T_j^{-1}) = T_j` from the uniqueness of inverses in the quotient; here
`T̂_j` is the *polynomial* of `HJO.Dyck.braidInvGen` and no relation of `𝔹` is read, so the claim
holds for an arbitrary family. -/
@[hjo "lem_cm_star_swap_yz"]
theorem map_cornerOf (hbar : bar q = ⅟q) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    σ (cornerOf q ⅟q ⅟(q - 1) E U D T k i)
      = cornerOf ⅟q q (-(q * ⅟(q - 1))) E Ustar D
          (fun m j => tinvOf q ⅟q (T m j) (E m)) k i := by
  have hmain := map_cornerOf_bar (bar := bar) (f := σ) h.map_mul h.map_smul q ⅟q ⅟(q - 1)
    h.map_e h.map_dPlus h.map_dMinus (T' := fun m j => tinvOf q ⅟q (T m j) (E m))
    (fun j hj => h.map_T hj) hi hik
  rwa [hbar, bar_invOf bar hbar, bar_invOf_sub_one bar hbar] at hmain

/-- **A star swap carries a starred corner element back.** For every
`k ≥ 1` and every `1 ≤ i ≤ k`, `σ(z_i) = y_i`. This is `HJO.Dyck.IsStarSwap.map_cornerOf` read
through `σ(σ(x)) = x`. -/
@[hjo "lem_cm_star_swap_zy"]
theorem map_cornerOf_symm (hbar : bar q = ⅟q) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    σ (cornerOf ⅟q q (-(q * ⅟(q - 1))) E Ustar D (fun m j => tinvOf q ⅟q (T m j) (E m)) k i)
      = cornerOf q ⅟q ⅟(q - 1) E U D T k i := by
  rw [← h.map_cornerOf hbar hi hik, h.involutive]

end IsStarSwap

/-! ### The corner elements of `𝔹` -/

namespace TwoSided.Bq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-- **The corner element `y_i`** at the vertex `k`, inside `𝔹`: the image of the element of
`HJO.Dyck.Aq.yElt` under the homomorphism from `𝔸_q` to `𝔹` carrying each generator to the
generator of the same name, which is the reading fixed for `y_1, …, y_k` in every
quotient of `𝔹`. -/
noncomputable def yElt (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Bq K q :=
  cornerOf q ⅟q ⅟(q - 1) (e K q) (dPlus K q) (dMinus K q) (Tg K q) k i

/-- **The starred corner elements `z_1, …, z_k` of `e_k𝔹e_k`.** The two formulas
of `HJO.Dyck.Aq.yElt` read in the starred generators: the scalars `q`, `q⁻¹`, `(q-1)⁻¹` become
`q⁻¹`, `q` and `-(q(q-1)⁻¹)` — the last being the ring element standing for
`(q⁻¹-1)⁻¹` — the raising arrow becomes `d₊^*`, and each loop becomes its polynomial inverse
`T̂_i` of `HJO.Dyck.braidInvGen`.

Only the values at `1 ≤ i ≤ k` are meaningful; outside that range the definition is a
totalization no statement reads, as for `HJO.Dyck.Aq.yElt`. -/
@[hjo "def_cm_zelement"]
noncomputable def zElt (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k i : ℕ) : Bq K q :=
  cornerOf ⅟q q (-(q * ⅟(q - 1))) (e K q) (dPlusStar K q) (dMinus K q) (Tinv K q) k i

omit [Invertible (q - 1)] in
/-- The family of polynomial inverses inside `𝔹` is the substituted loop family that
`HJO.Dyck.IsStarSwap` produces, so the corner element of the starred family is `zElt` on the
nose. -/
theorem tinvOf_Tg_eq_Tinv :
    (fun m j => tinvOf q ⅟q (Tg K q m j) (e K q m)) = Tinv K q := rfl

omit [Invertible (q - 1)] in
/-- The polynomial inverse is a loop at its vertex, absorbed by the idempotent on the left. -/
@[simp]
theorem e_mul_Tinv (k i : ℕ) : e K q k * Tinv K q k i = Tinv K q k i := by
  rw [Tinv_eq_braidInvGen, braidInvGen, mul_smul_comm, mul_add, mul_smul_comm, e_mul_Tg,
    e_mul_self]

omit [Invertible (q - 1)] in
/-- The polynomial inverse is a loop at its vertex, absorbed by the idempotent on the right. -/
@[simp]
theorem Tinv_mul_e (k i : ℕ) : Tinv K q k i * e K q k = Tinv K q k i := by
  rw [Tinv_eq_braidInvGen, braidInvGen, smul_mul_assoc, add_mul, smul_mul_assoc, Tg_mul_e,
    e_mul_self]

/-- **The top starred corner element**, in the form `HJO.Dyck.TwoSided.Bq.zElt` displays:
`z_k = (q⁻¹-1)⁻¹T_{k-1}⋯T_1(d₊^*d₋ - d₋d₊^*)e_k`, with the word of loops *unstarred* — the
substitution having turned the word of inverses of `y_k` into a word of inverses of inverses — and
the prefactor the ring element `-(q(q-1)⁻¹)`, whose product with `q⁻¹-1` is `1`. -/
@[hjo "def_cm_zelement"]
theorem zElt_self (k : ℕ) :
    zElt K q k k = -(q * ⅟(q - 1)) • (braidWordOf (e K q) (Tg K q) k (k - 1) *
      commOf (dPlusStar K q) (dMinus K q) (k - 1) * e K q k) := by
  rw [zElt, cornerOf, Nat.sub_self, cornerAux, ← tinvOf_Tg_eq_Tinv,
    tinvWordOf_tinvOf_eq_braidWordOf]

/-- The prefactor of `z_k` is an inverse of `q⁻¹-1`, written `(q⁻¹-1)⁻¹` in the formula for `z_k`.
Stated so that the two side conditions that formula needs — `q ≠ 0` and `q ≠ 1`, carried here as
`[Invertible q]` and `[Invertible (q-1)]` — are visible at the definition rather than hidden inside
a division. -/
theorem zElt_prefactor : -(q * ⅟(q - 1)) * (⅟q - 1) = (1 : K) :=
  Tilde.neg_mul_invOf_sub_one_mul

/-- **The downward recursion for the starred corner elements**, the second formula of
`HJO.Dyck.TwoSided.Bq.zElt`: `z_i = qT̂_iz_{i+1}T̂_i` for `1 ≤ i ≤ k-1`, the loop being `T̂_{i}` at
the index `i - 1` in the shifted indexing of `HJO.Dyck.TwoSided.Bq.Tg`. -/
@[hjo "def_cm_zelement"]
theorem zElt_recursion {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    zElt K q k i = q • (Tinv K q k (i - 1) * zElt K q k (i + 1) * Tinv K q k (i - 1)) := by
  have hj : k - i = k - i - 1 + 1 := by omega
  have hidx : k - (k - i - 1) - 2 = i - 1 := by omega
  have hnext : k - (i + 1) = k - i - 1 := by omega
  rw [zElt, cornerOf, hj, cornerAux, hidx, zElt, cornerOf, hnext]

/-- Every starred corner element is a loop at the vertex `k`, absorbed by the idempotent on the
left: `z_i` lies in `e_k𝔹e_k`, where `HJO.Dyck.TwoSided.Bq.zElt` places the family. -/
theorem e_mul_zAux (k j : ℕ) :
    e K q k * cornerAux ⅟q q (-(q * ⅟(q - 1))) (e K q) (dPlusStar K q) (dMinus K q) (Tinv K q) k j
      = cornerAux ⅟q q (-(q * ⅟(q - 1))) (e K q) (dPlusStar K q) (dMinus K q) (Tinv K q) k j := by
  induction j with
  | zero =>
    rw [cornerAux, mul_smul_comm, ← mul_assoc, ← mul_assoc, ← tinvOf_Tg_eq_Tinv,
      tinvWordOf_tinvOf_eq_braidWordOf]
    congr 3
    cases k - 1 with
    | zero => exact e_mul_self k
    | succ n => rw [braidWordOf_succ, ← mul_assoc, e_mul_Tg]
  | succ j _ => rw [cornerAux, mul_smul_comm, ← mul_assoc, ← mul_assoc, e_mul_Tinv]

/-- Every starred corner element is a loop at the vertex `k`, absorbed on the right. -/
theorem zAux_mul_e (k j : ℕ) :
    cornerAux ⅟q q (-(q * ⅟(q - 1))) (e K q) (dPlusStar K q) (dMinus K q) (Tinv K q) k j *
        e K q k
      = cornerAux ⅟q q (-(q * ⅟(q - 1))) (e K q) (dPlusStar K q) (dMinus K q) (Tinv K q) k j := by
  induction j with
  | zero => rw [cornerAux, smul_mul_assoc, mul_assoc, e_mul_self]
  | succ j _ => rw [cornerAux, smul_mul_assoc, mul_assoc, Tinv_mul_e]

/-- **The starred corner elements lie in `e_k𝔹e_k`**: the idempotent at the vertex `k` is a
two-sided identity on each `z_i`, which is where `HJO.Dyck.TwoSided.Bq.zElt` places the family. -/
@[hjo "def_cm_zelement"]
theorem e_mul_zElt_mul_e (k i : ℕ) :
    e K q k * zElt K q k i * e K q k = zElt K q k i := by
  rw [zElt, cornerOf, e_mul_zAux, zAux_mul_e]

/-- **`HJO.Dyck.IsStarSwap.map_cornerOf` inside `𝔹`**: a star swap of `𝔹` carries `y_i` to `z_i`. -/
theorem IsStarSwap.map_yElt {bar : K ≃+* K} {σ : Bq K q →+ Bq K q}
    (h : IsStarSwap q bar (e K q) (dPlus K q) (dPlusStar K q) (dMinus K q) (Tg K q) σ)
    (hbar : bar q = ⅟q) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    σ (yElt K q k i) = zElt K q k i := by
  rw [yElt, zElt, ← tinvOf_Tg_eq_Tinv]
  exact h.map_cornerOf hbar hi hik

/-- **`HJO.Dyck.IsStarSwap.map_cornerOf_symm` inside `𝔹`**: a star swap of `𝔹` carries `z_i` back to
`y_i`. -/
theorem IsStarSwap.map_zElt {bar : K ≃+* K} {σ : Bq K q →+ Bq K q}
    (h : IsStarSwap q bar (e K q) (dPlus K q) (dPlusStar K q) (dMinus K q) (Tg K q) σ)
    (hbar : bar q = ⅟q) {k i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    σ (zElt K q k i) = yElt K q k i := by
  rw [← IsStarSwap.map_yElt h hbar hi hik, h.involutive]

end TwoSided.Bq

end HJO.Dyck
