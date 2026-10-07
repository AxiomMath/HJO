/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.CutRestrict
public import HJO.Macdonald.OperatorStable
public meta import HJO.Attr

/-! # Erasing a variable in Macdonald's operator

`HJO.Mac.killComplComp_macOpComp`, the one piece of real work in the alphabet descent: for
`f ∈ 𝒮_{n+1,d}`, `cut_n(D^{(n+1)}_1 f) = u D^{(n)}_1(cut_n f) + cut_n f`. Setting `x_{n+1} = 0` in
the coefficient `A_i = ∏_{j ≠ i}(u x_i - x_j)/(x_i - x_j)` leaves the `j = n+1` factor
`(u x_i - 0)/(x_i - 0) = u` for `i ≤ n`, and collapses `A_{n+1}` to
`∏_{j ≤ n}(u·0 - x_j)/(0 - x_j) = 1`.

## The route: clear the denominators instead of extending `cut_n`

The usual proof builds the subring `R ⊆ 𝕜(x_1,…,x_{n+1})` of fractions whose
denominator is a product of the `x_k - x_l`, observes that `cut_n` carries each such factor to a
nonzero polynomial, and extends `cut_n` to `R`. That localisation is not built here. Instead the
whole identity is proved **in the polynomial ring**, against the Vandermonde product: the library
already has `HJO.Mac.macOpNum`, the polynomial `𝒱_N D^{(n)}_1 f` of
`HJO.Mac.vandermondeProd_mul_macOp`, and

* `HJO.Mac.killCompl_macOpNum` computes `cut_n(macOpNum^{(n+1)} f)` factor by factor -- one
  Vandermonde product, one numerator product, one parameter shift per summand -- and finds
  `(∏_{k ≤ n} x_k)·(u·macOpNum^{(n)}(cut_n f) + 𝒱_{N'} cut_n f)`, the extra `∏ x_k` being exactly
  what `cut_n 𝒱_N = (∏_{k ≤ n} x_k)·𝒱_{N'}` contributes;
* `macOpNum^{(n+1)} f = 𝒱_N·D^{(n+1)}_1 f` and `macOpNum^{(n)} g = 𝒱_{N'}·D^{(n)}_1 g` turn that
  into the claim after cancelling `∏_{k ≤ n} x_k` and `𝒱_{N'}`, both nonzero in a domain.

Two sign computations that cancel are the only bookkeeping: the summand at the erased letter carries
`(-1)^{#σ}` from `HJO.Mac.vandermondeProd_mul_macOp` and another `(-1)^{#σ}` from
`cut_n ∏_{j ≤ n}(u x_{n+1} - x_j) = ∏_{j ≤ n}(-x_j)`.

## Generality: one new largest letter

`MvPolynomial.killCompl` is stated in this library for an arbitrary injection `f : σ → τ`
(`HJO/Macdonald/CutAlphabet.lean`), but this lemma genuinely needs `τ` to be `σ` with **one**
new letter, and needs it to be the **largest** one: the `A_i` are indexed by letters, the erased
letter contributes the summand that becomes the `+ cut_n f`, and the signs of
`HJO.Mac.vandermondeProd_mul_macOp` are read off the order. `HJO.Mac.IsTopExtension` is that datum,
and `Fin.isTopExtension_castSucc` is the instance `σ = Fin n`, `τ = Fin (n+1)`,
`e = Fin.castSucc`, `t = Fin.last n`. The hypothesis `n ≥ 1` is absent: `σ` may be empty, where the
identity reads `cut_0(D^{(1)}_1 f) = cut_0 f` and is true.

## Genericity: none, and the two corners checked

**Nothing is spent.** The only hypotheses are `q : Kˣ` -- which `HJO.Mac.qShift` needs to have a
shift at all, and which is usually left implicit -- and `[Algebra ℚ K]`, which comes in only
through `HJO.Mac.macOpComp`, i.e. through `HJO.Mac.exists_eq_macOp_algebraMap`, whose proof
makes the same char-zero appeal. No `u ≠ 0`, no `u ≠ 1`, no `qu ≠ 1`, no algebraic independence.

`u` sits in the statement as a coefficient, so the two degenerate corners deserve a check, against
the pattern of `HJO.Mac.one_sub_mul_sum_macCoeff`,
`HJO.Mac.sub_one_mul_sum_macCoeff_mul_pow` and `HJO.Mac.dop_pleth`, which do omit a needed `u ≠ 0`:

* at `u = 0` the identity reads `cut_n(D^{(n+1)}_1 f) = cut_n f`, and it holds: `A_i` at `u = 0` has
  `j = n+1` factor `-x_{n+1}/(x_i - x_{n+1})`, which vanishes at `x_{n+1} = 0`, matching the `u` on
  the right; `A_{n+1}` still collapses to `1`. At `n = 1`, `f = x_1 + x_2` both sides are `x_1`;
* at `u = 1` every `A_i` is `1`, so `D^{(m)}_1 = ∑_i T_{q,x_i}`; at `n = 1`, `f = x_1 + x_2` both
  sides are `(1 + q)x_1`.

In general at `n = 1`, `f = x_1 + x_2`: `D^{(2)}_1 f = (1 + qu)(x_1 + x_2)`, cut to
`(1 + qu)x_1 = u·q x_1 + x_1`. The proof below confirms this: no step divides by `u`.

This matches the rest of the descent -- `HJO.Sym.killCompl_restrictAlphabet` spends only
injectivity, `MvPolynomial.killComplComp_bijective` only `d ≤ #σ`, `HJO.Mac.macOp_comm` only
`[Algebra ℚ K]`. The hypothesis `u ≠ 0` of this branch appears one step later, in the *proof* of
`HJO.Mac.killComplComp_macPpoly`, which cancels `u` from `u D^{(n)}_1 g = u E_n(μ)g`.

## Main definitions

* `HJO.Mac.IsTopExtension`: `τ` is `σ` with one new largest letter `t` adjoined.

## Main results

* `HJO.Mac.killCompl_macOpNum`: the numerator computation, the heart of the proof.
* `HJO.Mac.killComplComp_macOpComp`, `HJO.Mac.killCompl_macOpComp`: **erasing the last variable
  turns Macdonald's operator into `u D^{(n)}_1 + 1`**, on the graded piece and on the underlying
  polynomials.
* `HJO.Mac.killComplComp_macOpComp_castSucc`: the same at `σ = Fin n`, `τ = Fin (n + 1)`, which is
  the statement in its usual form.

## References

The lemma `HJO.Mac.killComplComp_macOpComp` on Macdonald's polynomials, on the definitions
`MvPolynomial.symmetricHomogeneousSubmodule`, `HJO.Mac.qShift`, `HJO.Mac.macOp` and
`MvPolynomial.eq_killCompl_castSucc_iff`. Its one consumer is `HJO.Mac.killComplComp_macPpoly`, and
through it `HJO.Mac.restrictAlphabet_macPfun_partDiagram` and
`HJO.Mac.restrictAlphabet_macPfun_partDiagram_of_pos`.

The *statement* of `HJO.Mac.killComplComp_macOpComp` depends on
`HJO.Mac.exists_eq_macOp_algebraMap`, not just its proof: without it `D^{(n+1)}_1 f` is a rational
function and `cut_n` does not apply to it. By that lemma it is a polynomial, so the two readings of
`cut_n(D^{(n+1)}_1 f)` agree.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### Reindexing a Vandermonde product along an order embedding -/

namespace Finset

variable {ι κ R : Type*} [LinearOrder ι] [LinearOrder κ] [CommRing R]

/-- **A Vandermonde product over the image of an order embedding is the Vandermonde product of the
reindexed family.** An order embedding matches the pairs `k < l` of `S` with the pairs of
`S.image e` one for one, so the two products have the same factors. This is what lets the
Vandermonde products of the two alphabets of an alphabet descent be compared. -/
theorem vandermondeProd_image {e : ι → κ} (he : StrictMono e) (S : Finset ι) (v : κ → R) :
    (S.image e).vandermondeProd v = S.vandermondeProd (v ∘ e) := by
  classical
  rw [vandermondeProd, vandermondeProd, Finset.prod_image fun x _ y _ h => he.injective h]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hfilt : {l ∈ S.image e | e k < l} = (S.filter (k < ·)).image e := by
    refine Finset.ext fun b => ?_
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
      exact ⟨a, ⟨ha, he.lt_iff_lt.1 hlt⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hak⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, he.lt_iff_lt.2 hak⟩
  rw [hfilt, Finset.prod_image fun x _ y _ h => he.injective h]
  rfl

end Finset

namespace HJO.Mac

/-! ### One new largest letter

The datum an alphabet descent runs on: `e` embeds the small alphabet in the large one in an
order-preserving way, `t` is the one letter of the large alphabet outside the image, and it is
larger than every letter of the image. The instance is
`Fin.isTopExtension_castSucc`.
-/

/-- **`τ` is `σ` with one new largest letter `t` adjoined**: `e` is an order embedding, every `e a`
is below `t`, and every letter other than `t` is an `e a`. This is the passage from the
alphabet `x_1, …, x_n` to `x_1, …, x_{n+1}`, and `MvPolynomial.killCompl hd.injective` is its
`cut_n`. -/
structure IsTopExtension {σ τ : Type*} [LinearOrder σ] [LinearOrder τ] (e : σ → τ) (t : τ) :
    Prop where
  /-- `e` is order preserving, which is what makes the Vandermonde products and the signs of
  `HJO.Mac.vandermondeProd_mul_macOp` comparable across the two alphabets. -/
  strictMono : StrictMono e
  /-- the new letter is above every old one. -/
  lt_top (a : σ) : e a < t
  /-- the new letter is the only one outside the image. -/
  exists_eq {b : τ} (hb : b ≠ t) : ∃ a, e a = b

namespace IsTopExtension

variable {σ τ : Type*} [LinearOrder σ] [LinearOrder τ] {e : σ → τ} {t : τ}
  (hd : IsTopExtension e t)

include hd

/-- An order embedding is injective, which is what `MvPolynomial.killCompl` asks for. -/
theorem injective : Function.Injective e := hd.strictMono.injective

/-- The new letter is in no image of a set of old letters. -/
theorem notMem_image (S : Finset σ) : t ∉ S.image e := by
  simp only [Finset.mem_image, not_exists]
  exact fun a ha => absurd ha.2 (hd.lt_top a).ne

/-- The new letter is outside the range of `e`, so `cut_n` kills its variable. -/
theorem notMem_range : t ∉ Set.range e := by
  rintro ⟨a, rfl⟩
  exact absurd (hd.lt_top a) (lt_irrefl _)

variable [Fintype σ] [Fintype τ]

/-- Deleting the new letter from the large alphabet leaves the old alphabet. -/
theorem erase_top : (univ : Finset τ).erase t = univ.image e := by
  refine Finset.ext fun b => ?_
  rw [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hb, -⟩
    obtain ⟨a, ha⟩ := hd.exists_eq hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · rintro ⟨a, -, rfl⟩
    exact ⟨(hd.lt_top a).ne, Finset.mem_univ _⟩

/-- The large alphabet is the old one together with the new letter. -/
theorem univ_eq : (univ : Finset τ) = insert t (univ.image e) := by
  rw [← hd.erase_top, Finset.insert_erase (Finset.mem_univ t)]

/-- Deleting an old letter from the large alphabet leaves the new letter together with the old
alphabet less that letter. This is the index set of the `i`-th coefficient `A_i` of Macdonald's
operator in the large alphabet, split at the erased variable. -/
theorem erase_image (i : σ) :
    (univ : Finset τ).erase (e i) = insert t ((univ.erase i).image e) := by
  classical
  refine Finset.ext fun b => ?_
  rw [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hb, -⟩
    rcases eq_or_ne b t with rfl | hbt
    · exact Or.inl rfl
    · obtain ⟨a, rfl⟩ := hd.exists_eq hbt
      exact Or.inr ⟨a, Finset.mem_erase.2 ⟨fun h => hb (congrArg e h), Finset.mem_univ a⟩, rfl⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨(hd.lt_top i).ne', Finset.mem_univ _⟩
    · exact ⟨fun h => Finset.ne_of_mem_erase ha (hd.injective h), Finset.mem_univ _⟩

/-- An old letter has the same letters below it in either alphabet, the new one being above it.
This is what makes the sign `(-1)^{c_i}` of `HJO.Mac.vandermondeProd_mul_macOp` the same in both. -/
theorem card_filter_lt (i : σ) :
    #{k ∈ (univ : Finset τ) | k < e i} = #{k ∈ (univ : Finset σ) | k < i} := by
  classical
  have hset : {k ∈ (univ : Finset τ) | k < e i} = {k ∈ (univ : Finset σ) | k < i}.image e := by
    refine Finset.ext fun b => ?_
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨a, rfl⟩ := hd.exists_eq fun h => absurd (h ▸ hb) (hd.lt_top i).asymm
      exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, hd.strictMono.lt_iff_lt.1 hb⟩, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Finset.mem_univ _, hd.strictMono.lt_iff_lt.2 (Finset.mem_filter.1 ha).2⟩
  rw [hset, Finset.card_image_of_injective _ hd.injective]

/-- Every old letter is below the new one, so the sign the new letter carries in
`HJO.Mac.vandermondeProd_mul_macOp` is `(-1)^{#σ}`. -/
theorem card_filter_lt_top : #{k ∈ (univ : Finset τ) | k < t} = Fintype.card σ := by
  classical
  have hset : {k ∈ (univ : Finset τ) | k < t} = (univ : Finset σ).image e := by
    refine Finset.ext fun b => ?_
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨a, rfl⟩ := hd.exists_eq hb.ne
      exact ⟨a, Finset.mem_univ a, rfl⟩
    · rintro ⟨a, -, rfl⟩
      exact ⟨Finset.mem_univ _, hd.lt_top a⟩
  rw [hset, Finset.card_image_of_injective _ hd.injective, Finset.card_univ]

end IsTopExtension

/-! ### What erasing the new variable does to the pieces of Macdonald's operator

One lemma for each factor of a summand of `HJO.Mac.vandermondeProd_mul_macOp`: the Vandermonde
product, the numerator product `∏_{j ≠ i}(u x_i - x_j)`, and the parameter shift.
-/

section Cut

variable {σ τ K : Type*} [CommRing K] [LinearOrder σ] [LinearOrder τ]
  {e : σ → τ} {t : τ} (hd : IsTopExtension e t)

include hd

/-- `cut_n` kills the new variable. -/
theorem killCompl_X_top : killCompl (R := K) hd.injective (X t) = 0 :=
  killCompl_X_eq_zero hd.injective hd.notMem_range

/-- **`cut_n` carries a Vandermonde product over old letters to the Vandermonde product of the old
alphabet**: no factor mentions the new variable. -/
theorem killCompl_vandermondeProd_image (S : Finset σ) :
    killCompl (R := K) hd.injective ((S.image e).vandermondeProd X) = S.vandermondeProd X := by
  rw [Finset.map_vandermondeProd, Finset.vandermondeProd_image hd.strictMono]
  exact congrArg _ (funext fun a => killCompl_X hd.injective a)

/-- **`cut_n` carries a Vandermonde product that includes the new letter to `∏_{k ∈ S} x_k` times
the Vandermonde product of the old letters**: the new letter is the largest, so it contributes one
factor `x_k - x_t` for each `k ∈ S`, and `cut_n(x_k - x_t) = x_k`. At `S = univ` this is
`cut_n 𝒱_N = (∏_{k ≤ n} x_k)·𝒱_{N'}`, the whole discrepancy the proof below has to cancel. -/
theorem killCompl_vandermondeProd_insert (S : Finset σ) :
    killCompl (R := K) hd.injective ((insert t (S.image e)).vandermondeProd X)
      = (∏ k ∈ S, X k) * S.vandermondeProd X := by
  classical
  have h1 : {l ∈ S.image e | t < l} = ∅ := Finset.filter_eq_empty_iff.2 fun {l} hl => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hl
    exact (hd.lt_top a).asymm
  have h2 : {k ∈ S.image e | k < t} = S.image e := Finset.filter_true_of_mem fun k hk => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hk
    exact hd.lt_top a
  rw [Finset.vandermondeProd_insert (hd.notMem_image S), h1, h2, Finset.prod_empty, one_mul,
    map_mul, map_prod, killCompl_vandermondeProd_image hd,
    Finset.prod_image fun x _ y _ h => hd.injective h]
  refine congrArg (· * _) (Finset.prod_congr rfl fun a _ => ?_)
  rw [map_sub, killCompl_X hd.injective, killCompl_X_top hd, sub_zero]

/-- **The shift of an old variable commutes with `cut_n`**: both composites are algebra maps
sending `x_{e a}` to `q^{[a = i]} x_a` and the new variable to `0`. This is
`cut_n ∘ T_{q,x_i} = T_{q,x_i} ∘ cut_n` for `i ≤ n`. -/
theorem killCompl_rescaleEquiv (q : Kˣ) (i : σ) (p : MvPolynomial τ K) :
    killCompl (R := K) hd.injective (rescaleEquiv (Pi.mulSingle (e i) q) p)
      = rescaleEquiv (Pi.mulSingle i q) (killCompl hd.injective p) := by
  have hcomp : (killCompl (R := K) hd.injective).comp
      (rescaleEquiv (Pi.mulSingle (e i) q)).toAlgHom =
      (rescaleEquiv (Pi.mulSingle i q)).toAlgHom.comp (killCompl hd.injective) := by
    refine MvPolynomial.algHom_ext fun b => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, rescaleEquiv_X, map_smul]
    rcases eq_or_ne b t with rfl | hb
    · rw [killCompl_X_top hd, smul_zero, map_zero]
    · obtain ⟨a, rfl⟩ := hd.exists_eq hb
      rw [killCompl_X hd.injective, rescaleEquiv_X]
      rcases eq_or_ne a i with rfl | hai
      · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hai, Pi.mulSingle_eq_of_ne fun h => hai (hd.injective h)]
  exact AlgHom.congr_fun hcomp p

/-- **The shift of the new variable is invisible to `cut_n`**: both sides fix every old variable
and kill the new one. This is the identity `cut_n ∘ T_{q,x_{n+1}} = cut_n`. -/
theorem killCompl_rescaleEquiv_top (q : Kˣ) (p : MvPolynomial τ K) :
    killCompl (R := K) hd.injective (rescaleEquiv (Pi.mulSingle t q) p)
      = killCompl hd.injective p := by
  have hcomp : (killCompl (R := K) hd.injective).comp
      (rescaleEquiv (Pi.mulSingle t q)).toAlgHom = killCompl hd.injective := by
    refine MvPolynomial.algHom_ext fun b => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, rescaleEquiv_X, map_smul]
    rcases eq_or_ne b t with rfl | hb
    · rw [killCompl_X_top hd, smul_zero]
    · rw [Pi.mulSingle_eq_of_ne hb, Units.val_one, one_smul]
  exact AlgHom.congr_fun hcomp p

variable [Fintype σ] [Fintype τ]

/-- **The numerator of `A_i` at an old letter, with the new variable erased**: the `j = t` factor of
`∏_{j ≠ i}(u x_i - x_j)` becomes `u x_i`, and the rest is the numerator of `A_i` in the old
alphabet. This is where the `u` of the statement comes from. -/
theorem killCompl_prod_numFactor (u : K) (i : σ) :
    killCompl (R := K) hd.injective (∏ j ∈ (univ : Finset τ).erase (e i), (C u * X (e i) - X j))
      = C u * X i * ∏ j ∈ (univ : Finset σ).erase i, (C u * X i - X j) := by
  classical
  rw [hd.erase_image i, Finset.prod_insert (hd.notMem_image _), map_mul, map_prod,
    Finset.prod_image fun x _ y _ h => hd.injective h, map_sub, map_mul, algHom_C,
    killCompl_X hd.injective, killCompl_X_top hd, sub_zero]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by
    rw [map_sub, map_mul, algHom_C, killCompl_X hd.injective, killCompl_X hd.injective,
      MvPolynomial.algebraMap_eq])

/-- **The numerator of `A_i` at the new letter, with the new variable erased**: every factor
`u x_t - x_{e a}` becomes `-x_a`, so the product is `(-1)^{#σ} ∏_a x_a`. Together with the sign
`(-1)^{#σ}` that `HJO.Mac.vandermondeProd_mul_macOp` attaches to the largest letter this is
`cut_n(A_{n+1}) = 1`. -/
theorem killCompl_prod_numFactor_top (u : K) :
    killCompl (R := K) hd.injective (∏ j ∈ (univ : Finset τ).erase t, (C u * X t - X j))
      = (-1) ^ Fintype.card σ * ∏ j : σ, X j := by
  classical
  rw [hd.erase_top, map_prod, Finset.prod_image fun x _ y _ h => hd.injective h]
  have hstep : ∀ a : σ, killCompl (R := K) hd.injective (C u * X t - X (e a))
      = (-1 : MvPolynomial σ K) * X a := fun a => by
    rw [map_sub, map_mul, algHom_C, killCompl_X hd.injective, killCompl_X_top hd, mul_zero,
      zero_sub, neg_eq_neg_one_mul]
  rw [Finset.prod_congr rfl fun a _ => hstep a, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

end Cut

/-! ### Erasing the new variable in the numerator

`HJO.Mac.macOpNum` is `𝒱_N D^{(n)}_1 f` read as a polynomial (`HJO.Mac.vandermondeProd_mul_macOp`).
Its summand at the new letter becomes `𝒱_{N'} (∏_k x_k) cut_n f`, and its summand at an old letter
`i` becomes `(∏_k x_k) u` times the summand of the old alphabet at `i`.
-/

section Num

variable {σ τ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] [LinearOrder τ] [Fintype τ]
  {e : σ → τ} {t : τ}

/-- The `i`-th summand of `HJO.Mac.macOpNum`, named so that the two computations below can be
stated one summand at a time. -/
private noncomputable def macOpNumTerm (q : Kˣ) (u : K) (f : MvPolynomial σ K) (i : σ) :
    MvPolynomial σ K :=
  (-1) ^ #{k ∈ (univ : Finset σ) | k < i} * (univ.erase i).vandermondeProd X *
    (∏ j ∈ univ.erase i, (C u * X i - X j)) * rescaleEquiv (Pi.mulSingle i q) f

private theorem macOpNum_eq_sum (q : Kˣ) (u : K) (f : MvPolynomial σ K) :
    macOpNum q u f = ∑ i : σ, macOpNumTerm q u f i := rfl

/-- The summand at the new letter: the two signs `(-1)^{#σ}` cancel and what is left is
`𝒱_{N'} (∏_k x_k) cut_n f`, the `+ cut_n f` of the statement waiting for its `𝒱_{N'}` to be
cancelled. -/
private theorem killCompl_macOpNumTerm_top (hd : IsTopExtension e t) (q : Kˣ) (u : K)
    (f : MvPolynomial τ K) :
    killCompl (R := K) hd.injective (macOpNumTerm q u f t)
      = (univ : Finset σ).vandermondeProd X * (∏ k : σ, X k) * killCompl hd.injective f := by
  have hsq : ((-1 : MvPolynomial σ K)) ^ Fintype.card σ * (-1) ^ Fintype.card σ = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  rw [macOpNumTerm, map_mul, map_mul, map_mul, map_pow, map_neg, map_one,
    killCompl_prod_numFactor_top hd, killCompl_rescaleEquiv_top hd, hd.card_filter_lt_top,
    hd.erase_top, killCompl_vandermondeProd_image hd]
  linear_combination ((univ : Finset σ).vandermondeProd (X : σ → MvPolynomial σ K) *
    (∏ k : σ, X k) * killCompl hd.injective f) * hsq

/-- The summand at an old letter `i`: the Vandermonde product contributes `∏_{k ≠ i} x_k`, the
numerator contributes `u x_i`, and `(∏_{k ≠ i} x_k)·x_i = ∏_k x_k`, so what is left is
`(∏_k x_k) u` times the old alphabet's summand at `i`. -/
private theorem killCompl_macOpNumTerm (hd : IsTopExtension e t) (q : Kˣ) (u : K)
    (f : MvPolynomial τ K) (i : σ) :
    killCompl (R := K) hd.injective (macOpNumTerm q u f (e i))
      = (∏ k : σ, X k) * C u * macOpNumTerm q u (killCompl hd.injective f) i := by
  have hprod : (∏ k ∈ (univ : Finset σ).erase i, X k) * X i
      = ∏ k : σ, (X k : MvPolynomial σ K) := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  rw [macOpNumTerm, macOpNumTerm, map_mul, map_mul, map_mul, map_pow, map_neg, map_one,
    killCompl_prod_numFactor hd, killCompl_rescaleEquiv hd, hd.card_filter_lt i,
    hd.erase_image i, killCompl_vandermondeProd_insert hd, ← hprod]
  ring

/-- **Erasing the new variable in the numerator of Macdonald's operator.**
`cut_n(𝒱_N D^{(n+1)}_1 f) = (∏_{k ≤ n} x_k)·(u·𝒱_{N'} D^{(n)}_1(cut_n f) + 𝒱_{N'} cut_n f)`, with
both sides read as polynomials through `HJO.Mac.macOpNum`.

This is `HJO.Mac.killComplComp_macOpComp` with the denominators cleared, and it is the whole content
of the lemma: what remains is to cancel `∏_{k ≤ n} x_k` and `𝒱_{N'}`. The sum over the large
alphabet is split at the new letter, and the two summands are `killCompl_macOpNumTerm_top` and
`killCompl_macOpNumTerm`. -/
theorem killCompl_macOpNum (hd : IsTopExtension e t) (q : Kˣ) (u : K) (f : MvPolynomial τ K) :
    killCompl (R := K) hd.injective (macOpNum q u f)
      = (∏ k : σ, X k) * (C u * macOpNum q u (killCompl hd.injective f)
          + (univ : Finset σ).vandermondeProd X * killCompl hd.injective f) := by
  classical
  rw [macOpNum_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ t), hd.erase_top,
    Finset.sum_image fun x _ y _ h => hd.injective h, map_add, map_sum,
    killCompl_macOpNumTerm_top hd,
    Finset.sum_congr rfl fun i _ => killCompl_macOpNumTerm hd q u f i,
    ← Finset.mul_sum, ← macOpNum_eq_sum]
  ring

end Num

/-! ### `HJO.Mac.killComplComp_macOpComp` -/

section Main

variable {σ τ K : Type*} [Field K] [LinearOrder σ] [Fintype σ] [LinearOrder τ] [Fintype τ]
  [Algebra ℚ K] {e : σ → τ} {t : τ}

/-- `HJO.Mac.vandermondeProd_mul_macOp` and `HJO.Mac.exists_eq_macOp_algebraMap` together, in the
polynomial ring: `macOpNum q u f = 𝒱_N · D^{(n)}_1 f` with the right-hand side a polynomial.

This is the *only* step that leaves `FractionRing (MvPolynomial σ K)`; everything downstream of it
is an identity between polynomials, which is what makes `killCompl` — and, in
`HJO/Macdonald/SplitVandermonde.lean`, `HJO.Mac.splitAt` — applicable at all. It is public for
that reason: consumers outside this file need it.

`HJO/Macdonald/Triangular.lean` carries a `private` copy of this same statement, specialised to
`msymm`. -/
theorem macOpNum_eq_vandermondeProd_mul (q : Kˣ) (u : K) (d : ℕ)
    (v : symmetricHomogeneousSubmodule σ K d) :
    macOpNum q u (v : MvPolynomial σ K)
      = (univ : Finset σ).vandermondeProd X * (macOpComp q u d v : MvPolynomial σ K) :=
  IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
    (by rw [algebraMap_macOpNum, map_mul, algebraMap_macOpComp])

omit [LinearOrder σ] [Algebra ℚ K] in
/-- The product of all the variables is not zero: a polynomial ring over a field is a domain. -/
private theorem prod_X_ne_zero : (∏ k : σ, X k : MvPolynomial σ K) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => MvPolynomial.X_ne_zero k

/-- **`HJO.Mac.killComplComp_macOpComp` on the underlying polynomials**:
`cut_n(D^{(n+1)}_1 f) = u·D^{(n)}_1(cut_n f) + cut_n f`, with both operators read through
`HJO.Mac.macOpComp`, i.e. as the endomorphisms of the graded pieces that
`HJO.Mac.exists_eq_macOp_algebraMap` provides.

`killCompl_macOpNum` gives the identity multiplied by `(∏_{k ≤ n} x_k)·𝒱_{N'}`, and that factor is
nonzero in the domain `𝕜[x_1, …, x_n]`. -/
theorem killCompl_macOpComp (hd : IsTopExtension e t) (q : Kˣ) (u : K) (d : ℕ)
    (v : symmetricHomogeneousSubmodule τ K d) :
    killCompl (R := K) hd.injective ((macOpComp q u d v : MvPolynomial τ K))
      = C u * (macOpComp q u d (killComplComp hd.injective K d v) : MvPolynomial σ K)
        + killCompl hd.injective (v : MvPolynomial τ K) := by
  have hw : killCompl (R := K) hd.injective (v : MvPolynomial τ K)
      = ((killComplComp hd.injective K d v : symmetricHomogeneousSubmodule σ K d) :
          MvPolynomial σ K) := rfl
  refine mul_left_cancel₀ (mul_ne_zero (prod_X_ne_zero (σ := σ) (K := K))
    (vandermondeProd_univ_ne_zero (σ := σ) (K := K))) ?_
  have hkey := killCompl_macOpNum hd q u (v : MvPolynomial τ K)
  rw [macOpNum_eq_vandermondeProd_mul q u d v, map_mul, hd.univ_eq,
    killCompl_vandermondeProd_insert hd, hw,
    macOpNum_eq_vandermondeProd_mul q u d (killComplComp hd.injective K d v)] at hkey
  rw [hw]
  linear_combination hkey

/-- **Erasing the last variable turns Macdonald's operator into
`u D^{(n)}_1 + 1`.** For `f ∈ 𝒮_{n+1,d}`,
`cut_n(D^{(n+1)}_1 f) = u D^{(n)}_1(cut_n f) + cut_n f`, an identity in `𝒮_{n,d}`.

Evaluating the coefficient `A_i = ∏_{j ≠ i}(u x_i - x_j)/(x_i - x_j)` at `x_{n+1} = 0` leaves the
`j = n+1` factor `(u x_i - 0)/(x_i - 0) = u` for `i ≤ n`, and `A_{n+1}` becomes
`∏_{j ≤ n}(-x_j)/(-x_j) = 1`; the shift of `x_{n+1}` is invisible after the erasure, and the shifts
of the surviving variables commute with it.

Nothing is assumed on `u`: the identity holds at `u = 0`, where it reads
`cut_n(D^{(n+1)}_1 f) = cut_n f`, and at `u = 1`, where both operators are `∑_i T_{q,x_i}`. The
`u ≠ 0` of this branch is spent one step later, in `HJO.Mac.killComplComp_macPpoly`. -/
@[hjo "lem_mac_dop_cut"]
theorem killComplComp_macOpComp (hd : IsTopExtension e t) (q : Kˣ) (u : K) (d : ℕ)
    (v : symmetricHomogeneousSubmodule τ K d) :
    killComplComp hd.injective K d (macOpComp q u d v)
      = u • macOpComp q u d (killComplComp hd.injective K d v)
        + killComplComp hd.injective K d v :=
  Subtype.ext (by
    rw [coe_killComplComp, Submodule.coe_add, SetLike.val_smul, coe_killComplComp,
      smul_eq_C_mul, killCompl_macOpComp hd])

end Main

/-! ### The alphabets -/

/-- `Fin (n + 1)` is `Fin n` with the new largest letter `Fin.last n` adjoined, along
`Fin.castSucc`. This is the alphabet descent, and `MvPolynomial.killCompl` of its
injection is the `cut_n`. -/
theorem isTopExtension_castSucc (n : ℕ) :
    IsTopExtension (Fin.castSucc : Fin n → Fin (n + 1)) (Fin.last n) where
  strictMono _ _ h := Fin.castSucc_lt_castSucc_iff.2 h
  lt_top a := Fin.castSucc_lt_last a
  exists_eq hb := Fin.exists_castSucc_eq.2 hb

/-- **`HJO.Mac.killComplComp_macOpComp` at the alphabets**: with `cut_n` the erasure of `x_{n+1}`
from `𝕜[x_1, …, x_{n+1}]` and `D^{(m)}_1` Macdonald's operator on `𝒮_{m,d}`,
`cut_n ∘ D^{(n+1)}_1 = u D^{(n)}_1 ∘ cut_n + cut_n`. -/
theorem killComplComp_macOpComp_castSucc {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ} (q : Kˣ)
    (u : K) (d : ℕ) (v : symmetricHomogeneousSubmodule (Fin (n + 1)) K d) :
    killComplComp (Fin.castSucc_injective n) K d (macOpComp q u d v)
      = u • macOpComp q u d (killComplComp (Fin.castSucc_injective n) K d v)
        + killComplComp (Fin.castSucc_injective n) K d v :=
  killComplComp_macOpComp (isTopExtension_castSucc n) q u d v

end HJO.Mac
