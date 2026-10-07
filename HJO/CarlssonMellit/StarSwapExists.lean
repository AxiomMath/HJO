/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import HJO.CarlssonMellit.StarSwap
public meta import HJO.Attr

/-! # A star swap of the two-sided Dyck path algebra exists

`HJO.Dyck.TwoSided.exists_isStarSwap`: `𝔹` of `HJO.Dyck.TwoSided.Bq` admits a star swap of
`HJO.Dyck.IsStarSwap`.

## The construction, and where it differs from the path-algebra one

The map lives naturally on the path algebra `P` of the enlarged quiver: an assignment of an
element of `e_lPe_k` to each arrow from `k` to `l` determines a unique additive, multiplicative,
conjugate-linear `σ_P`, and the assignment is `d₊ ↦ d₊^*`, `d₊^* ↦ d₊`, `d₋ ↦ d₋`, `T_i ↦ T̂_i`.

Here `P` is the *free* algebra on `HJO.Dyck.Tilde.Gen` and the quiver's own structure is imposed as
relations, so two things must be supplied that the path algebra carries for free.

**The conjugate-linear map on the free algebra.** `FreeAlgebra.lift` produces `K`-algebra maps only,
and `σ_P` is conjugate-linear. It is therefore built as a composite: `HJO.Dyck.coeffBar`, the bar
applied to the coefficients, which is a ring automorphism fixing every generator and moving a
scalar by `bar`; followed by the honest `K`-algebra map `FreeAlgebra.lift` at the assignment. The
first factor is `MonoidAlgebra.mapRingEquiv` read through
`FreeAlgebra.equivMonoidAlgebraFreeMonoid`, and is the only place a presentation of the free algebra
is opened.

**The loops the quiver does not have.** At `i + 2 > k` the enlarged quiver has no loop `T_i` at the
vertex `k` and `HJO.Dyck.TwoSided.Rel.braid_eq_zero` kills the generator, but `T̂_i` is the
*polynomial* `q⁻¹(T_i + (q-1)e_k)`, which at `T_i = 0` is `q⁻¹(q-1)e_k` and is *not* zero. So the
assignment on `Gen.braid k i` must be `T̂_i` in range and `0` outside, or the map would not descend:
it would force `(q-1)e_k = 0`, killing every idempotent. That is the same asymmetry
`HJO.Dyck.Tilde.Rel` records for the starred group, seen from the other side.

One consequence: `σ_P` is **not** an involution on the free algebra — out of range it sends `T_i`
to `0` and `0` back to `0`, not to `T_i`. It is an involution on `𝔹`, where `T_i` is itself `0`, and
`HJO.Dyck.TwoSided.mk_starSwapFree_starSwapFree` is where that is proved. On `P` one would prove
involutivity directly; that step is genuinely unavailable in this presentation, and moving it to the
quotient is the one divergence in the proof.

Everything else is the path-algebra argument verbatim: `σ_P` carries the unstarred group of
relations onto the starred group and back, by `HJO.Dyck.SourceRel.mapBar`, so it preserves the ideal
and descends.

## The hypotheses on the bar

`bar q = q⁻¹` and `bar (bar c) = c` are hypotheses, not consequences: over a general commutative
ring `q ↦ q⁻¹` is not an automorphism at all, which is why `HJO.Sym.paramInvLambda` carries the
automorphism of the base as an argument too. Both are part of `HJO.Sym.paramInvLambda` — it is *the
involution* `c ↦ c̄` of `𝕜` inverting the parameters — so assuming them is reading that definition,
not weakening this one.

## Main definitions

* `HJO.Dyck.coeffBar`: the bar on the coefficients of a free algebra.
* `HJO.Dyck.swapGen`, `HJO.Dyck.starSwapFree`, `HJO.Dyck.starSwapFreeAdd`: the assignment on the
  generators of the enlarged quiver, and the conjugate-linear multiplicative map of the free algebra
  it determines.
* `HJO.Dyck.TwoSided.starSwapBq`: the induced map on `𝔹`.

## Main results

* `HJO.Dyck.SourceRel.mapBar`: Carlsson and Mellit's relations transport along a conjugate-linear
  multiplicative map, the scalar being barred — the range hypothesis on the loops being the one
  `HJO.Dyck.SourceRel` never violates.
* `HJO.Dyck.TwoSided.isStarSwap_starSwapBq` and
  `HJO.Dyck.TwoSided.exists_isStarSwap`: the induced map is a star swap of `𝔹`, so `𝔹` admits one.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*,
J. Amer. Math. Soc.
**31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The paper's relations transport along a conjugate-linear map -/

section MapBar

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A] {B : Type*} [Ring B]
  [Algebra K B] {bar : K ≃+* K} {f : A →+ B} {E U D : ℕ → A} {T : ℕ → ℕ → A} {E' U' D' : ℕ → B}
  {T' : ℕ → ℕ → B} {q : K}

/-- **The paper's relations transport along a conjugate-linear multiplicative map**, the scalar
being barred: if `f` carries each family to the corresponding one — the loops only where the quiver
has them — then every instance of `HJO.Dyck.SourceRel` at the scalar `q` is an instance at `bar q`
in the image families.

The range hypothesis on the loops is the point. `HJO.Dyck.SourceRel` never reads a loop the quiver
does not have: each of its six clauses mentioning a loop carries the bound that puts every index it
reads inside `i + 2 ≤ k`, including `braid_down`, `up_braid`, `braid_up_up`, `down_down_braid`,
`down_delta` and `braid_delta`, where the index and the vertex move together. So a map known on the
loops only in range still transports the whole list — which is exactly what
`HJO.Dyck.starSwapFree` is, its value on an absent loop being `0` rather than the polynomial
inverse. -/
theorem SourceRel.mapBar (hmul : ∀ x y : A, f (x * y) = f x * f y)
    (hsmul : ∀ (c : K) (x : A), f (c • x) = bar c • f x) (hE : ∀ n, f (E n) = E' n)
    (hU : ∀ n, f (U n) = U' n) (hD : ∀ n, f (D n) = D' n)
    (hT : ∀ n i, i + 2 ≤ n → f (T n i) = T' n i) {x y : A}
    (h : SourceRel q E U D T x y) : SourceRel (bar q) E' U' D' T' (f x) (f y) := by
  induction h with
  | vertex_mul_up k =>
    simp only [hmul, hE, hU]
    exact SourceRel.vertex_mul_up k
  | up_mul_vertex k =>
    simp only [hmul, hU, hE]
    exact SourceRel.up_mul_vertex k
  | @quadratic k i h =>
    simp only [hmul, map_sub, map_add, hsmul, hT _ _ h, hE, map_zero]
    exact SourceRel.quadratic h
  | @braid_braid k i h =>
    simp only [hmul, hT _ _ (show i + 2 ≤ k by omega), hT _ _ (show i + 1 + 2 ≤ k by omega)]
    exact SourceRel.braid_braid h
  | @braid_comm k i j hi hj hij =>
    simp only [hmul, hT _ _ hi, hT _ _ hj]
    exact SourceRel.braid_comm hi hj hij
  | @braid_down m i h =>
    simp only [hmul, hT _ _ h, hT _ _ (show i + 2 ≤ m + 1 by omega), hD]
    exact SourceRel.braid_down h
  | @up_braid k i h =>
    simp only [hmul, hT _ _ h, hT _ _ (show i + 1 + 2 ≤ k + 1 by omega), hU]
    exact SourceRel.up_braid h
  | braid_up_up k =>
    simp only [hmul, hT _ _ (show 0 + 2 ≤ k + 2 by omega), hU]
    exact SourceRel.braid_up_up k
  | down_down_braid m =>
    simp only [hmul, hT _ _ (show m + 2 ≤ m + 2 by omega), hD]
    exact SourceRel.down_down_braid m
  | down_delta j =>
    simp only [hmul, hsmul, hD, hT _ _ (show j + 2 ≤ j + 2 by omega),
      map_commOf_bar hmul hU hD]
    exact SourceRel.down_delta j
  | braid_delta m =>
    simp only [hmul, hsmul, hU, hT _ _ (show 0 + 2 ≤ m + 2 by omega),
      map_commOf_bar hmul hU hD]
    exact SourceRel.braid_delta m

end MapBar

/-! ### The bar on the coefficients of a free algebra -/

section CoeffBar

variable {K : Type*} [CommRing K] (X : Type*) (bar : K ≃+* K)

/-- **The bar on the coefficients of a free algebra**: the ring automorphism of `FreeAlgebra K X`
fixing every generator and moving a scalar by `bar`. It is `MonoidAlgebra.mapRingEquiv` read
through `FreeAlgebra.equivMonoidAlgebraFreeMonoid`, which is the one presentation of the free
algebra this library opens; `FreeAlgebra.lift` cannot produce it, being restricted to
`K`-algebra maps. -/
noncomputable def coeffBar : FreeAlgebra K X ≃+* FreeAlgebra K X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toRingEquiv.trans
      (MonoidAlgebra.mapRingEquiv (FreeMonoid X) bar)).trans
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toRingEquiv.symm

@[simp]
theorem coeffBar_ι (x : X) : coeffBar X bar (FreeAlgebra.ι K x) = FreeAlgebra.ι K x := by
  have h : (MonoidAlgebra.mapRingEquiv (FreeMonoid X) bar)
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι K x))
        = FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι K x) := by
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapRingEquiv_single]
  simp only [coeffBar, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
  rw [h]
  simp

@[simp]
theorem coeffBar_algebraMap (c : K) :
    coeffBar X bar (algebraMap K (FreeAlgebra K X) c) = algebraMap K (FreeAlgebra K X) (bar c) := by
  simp only [coeffBar, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    RingEquiv.symm_apply_eq]
  have h : (algebraMap K (MonoidAlgebra K (FreeMonoid X))) c = MonoidAlgebra.single 1 c := rfl
  have h2 : (algebraMap K (MonoidAlgebra K (FreeMonoid X))) (bar c)
      = MonoidAlgebra.single 1 (bar c) := rfl
  rw [h, h2, MonoidAlgebra.mapRingEquiv_single]

theorem coeffBar_smul (c : K) (x : FreeAlgebra K X) :
    coeffBar X bar (c • x) = bar c • coeffBar X bar x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, coeffBar_algebraMap]

end CoeffBar

/-! ### The conjugate-linear map on the free algebra of the enlarged quiver -/

section Free

variable (K : Type*) [CommRing K] (q : K) [Invertible q]

/-- **The assignment on the generators of the enlarged quiver**: the two raising arrows are
exchanged, the idempotents and the lowering arrow are fixed, and a loop the quiver has goes to its
polynomial inverse of `HJO.Dyck.braidInvGen`.

A loop the quiver does *not* have — `T_i` at the vertex `k` with `i + 2 > k` — goes to `0` and not
to the polynomial `T̂_i`. That is forced: the generator is killed in `𝔹`, while `T̂_i` at `T_i = 0`
is `q⁻¹(q-1)e_k`, so the other reading would not descend. -/
noncomputable def swapGen : Tilde.Gen → FreeAlgebra K Tilde.Gen
  | .vertex k => Tilde.freeE K k
  | .up k => Tilde.freeUpStar K k
  | .upStar k => Tilde.freeUp K k
  | .down k => Tilde.freeDown K k
  | .braid k i => if i + 2 ≤ k then Tilde.freeTinv K q k i else 0

variable (bar : K ≃+* K)


/-- **The conjugate-linear multiplicative map of the free algebra** determined by the assignment:
the bar on the coefficients followed by the `K`-algebra map lifting `HJO.Dyck.swapGen`. It is the
path-algebra map `σ_P`, up to the two differences the module docstring records. -/
noncomputable def starSwapFree : FreeAlgebra K Tilde.Gen →+* FreeAlgebra K Tilde.Gen :=
  (FreeAlgebra.lift K (swapGen K q)).toRingHom.comp (coeffBar Tilde.Gen bar).toRingHom

variable {K q bar}

theorem starSwapFree_apply (x : FreeAlgebra K Tilde.Gen) :
    starSwapFree K q bar x = FreeAlgebra.lift K (swapGen K q) (coeffBar Tilde.Gen bar x) := rfl

theorem starSwapFree_ι (g : Tilde.Gen) :
    starSwapFree K q bar (FreeAlgebra.ι K g) = swapGen K q g := by
  rw [starSwapFree_apply, coeffBar_ι, FreeAlgebra.lift_ι_apply]

@[simp] theorem starSwapFree_freeE (k : ℕ) :
    starSwapFree K q bar (Tilde.freeE K k) = Tilde.freeE K k := starSwapFree_ι _

@[simp] theorem starSwapFree_freeUp (k : ℕ) :
    starSwapFree K q bar (Tilde.freeUp K k) = Tilde.freeUpStar K k := starSwapFree_ι _

@[simp] theorem starSwapFree_freeUpStar (k : ℕ) :
    starSwapFree K q bar (Tilde.freeUpStar K k) = Tilde.freeUp K k := starSwapFree_ι _

@[simp] theorem starSwapFree_freeDown (k : ℕ) :
    starSwapFree K q bar (Tilde.freeDown K k) = Tilde.freeDown K k := starSwapFree_ι _

theorem starSwapFree_freeT (k i : ℕ) :
    starSwapFree K q bar (Tilde.freeT K k i)
      = if i + 2 ≤ k then Tilde.freeTinv K q k i else 0 := starSwapFree_ι _

/-- On a loop the quiver has, the map is the polynomial inverse. -/
theorem starSwapFree_freeT_of_le {k i : ℕ} (h : i + 2 ≤ k) :
    starSwapFree K q bar (Tilde.freeT K k i) = Tilde.freeTinv K q k i := by
  simp [starSwapFree_freeT, h]

/-- On a loop the quiver does not have, the map is `0`, and not the polynomial inverse: that is
what makes the map descend to `𝔹`, where the loop is itself `0`. -/
theorem starSwapFree_freeT_of_lt {k i : ℕ} (h : k ≤ i + 1) :
    starSwapFree K q bar (Tilde.freeT K k i) = 0 := by
  have hn : ¬ i + 2 ≤ k := by omega
  simp [starSwapFree_freeT, hn]

theorem starSwapFree_algebraMap (c : K) :
    starSwapFree K q bar (algebraMap K (FreeAlgebra K Tilde.Gen) c)
      = algebraMap K (FreeAlgebra K Tilde.Gen) (bar c) := by
  rw [starSwapFree_apply, coeffBar_algebraMap, AlgHom.commutes]

theorem starSwapFree_smul (c : K) (x : FreeAlgebra K Tilde.Gen) :
    starSwapFree K q bar (c • x) = bar c • starSwapFree K q bar x := by
  rw [starSwapFree_apply, starSwapFree_apply, coeffBar_smul, map_smul]

/-- The map bundled as an additive map, which is the shape the transport lemmas of
`HJO.CarlssonMellit.StarSwap` read. -/
noncomputable def starSwapFreeAdd (K : Type*) [CommRing K] (q : K) [Invertible q] (bar : K ≃+* K) :
    FreeAlgebra K Tilde.Gen →+ FreeAlgebra K Tilde.Gen :=
  (starSwapFree K q bar).toAddMonoidHom

@[simp] theorem starSwapFreeAdd_apply (x : FreeAlgebra K Tilde.Gen) :
    starSwapFreeAdd K q bar x = starSwapFree K q bar x := rfl

/-- The map carries a polynomial inverse to the polynomial inverse of the image at the barred
scalars. -/
theorem starSwapFree_tinvOf (a b : K) (t e : FreeAlgebra K Tilde.Gen) :
    starSwapFree K q bar (tinvOf a b t e)
      = tinvOf (bar a) (bar b) (starSwapFree K q bar t) (starSwapFree K q bar e) := by
  rw [tinvOf, tinvOf, starSwapFree_smul, map_add, starSwapFree_smul, map_sub, map_one]

/-- **The map sends the polynomial inverse of a loop the quiver has back to that loop.** This is
`HJO.Dyck.Tilde.tinvOf_tinvOf`: the substitution `T_i ↦ T_i⁻¹` is an involution on the loops, which
is what makes the starred group of relations the paper's own list. -/
theorem starSwapFree_freeTinv_of_le (hbar : bar q = ⅟q) {k i : ℕ} (h : i + 2 ≤ k) :
    starSwapFree K q bar (Tilde.freeTinv K q k i) = Tilde.freeT K k i := by
  change starSwapFree K q bar (tinvOf q ⅟q (Tilde.freeT K k i) (Tilde.freeE K k))
    = Tilde.freeT K k i
  rw [starSwapFree_tinvOf, starSwapFree_freeT_of_le h, starSwapFree_freeE, hbar,
    bar_invOf bar hbar]
  exact Tilde.tinvOf_tinvOf _ _

end Free

/-! ### The induced map on `𝔹` -/

namespace TwoSided

open Bq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] {bar : K ≃+* K}

theorem mk_eq_mkRingHom (x : FreeAlgebra K Tilde.Gen) :
    mk K q x = RingQuot.mkRingHom (Rel K q) x := by
  rw [← RingQuot.mkAlgHom_coe K (Rel K q)]
  rfl

/-- The map of `HJO.Dyck.starSwapFree` followed by the quotient map onto `𝔹`, bundled as an
additive map: the shape `HJO.Dyck.SourceRel.mapBar` reads. -/
noncomputable def mkStarSwap (K : Type*) [CommRing K] (q : K) [Invertible q] (bar : K ≃+* K) :
    FreeAlgebra K Tilde.Gen →+ Bq K q :=
  ((mk K q).toRingHom.comp (starSwapFree K q bar)).toAddMonoidHom

theorem mkStarSwap_apply (x : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q bar x = mk K q (starSwapFree K q bar x) := rfl

theorem mkStarSwap_mul (x y : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q bar (x * y) = mkStarSwap K q bar x * mkStarSwap K q bar y := by
  rw [mkStarSwap_apply, mkStarSwap_apply, mkStarSwap_apply, map_mul, map_mul]

theorem mkStarSwap_smul (c : K) (x : FreeAlgebra K Tilde.Gen) :
    mkStarSwap K q bar (c • x) = bar c • mkStarSwap K q bar x := by
  rw [mkStarSwap_apply, mkStarSwap_apply, starSwapFree_smul, map_smul]

variable (hbar : bar q = ⅟q)

include hbar

/-- **The map respects the relations of `𝔹`.** The quiver's own relations are carried to themselves
— a loop the quiver does not have going to `0`, which is what it is in `𝔹` — and the unstarred group
is carried onto the starred group and back, by `HJO.Dyck.SourceRel.mapBar`. This is the step of the
path-algebra argument that `σ_P` preserves the ideal of relations. -/
theorem mk_starSwapFree_rel {x y : FreeAlgebra K Tilde.Gen} (h : Rel K q x y) :
    mk K q (starSwapFree K q bar x) = mk K q (starSwapFree K q bar y) := by
  induction h with
  | vertex_mul_self k =>
    simp only [map_mul, starSwapFree_freeE, mk_freeE]
    exact e_mul_self k
  | vertex_mul_vertex h =>
    simp only [map_mul, starSwapFree_freeE, mk_freeE, map_zero]
    exact e_mul_e_of_ne h
  | vertex_mul_down k =>
    simp only [map_mul, starSwapFree_freeE, starSwapFree_freeDown, mk_freeE, mk_freeDown]
    exact e_mul_dMinus k
  | down_mul_vertex k =>
    simp only [map_mul, starSwapFree_freeE, starSwapFree_freeDown, mk_freeE, mk_freeDown]
    exact dMinus_mul_e k
  | vertex_mul_braid k i =>
    rcases le_or_gt (i + 2) k with hk | hk
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_le hk, mk_freeE, mk_freeTinv]
      exact e_mul_Tinv k i
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_lt (by omega : k ≤ i + 1),
        mul_zero, map_zero]
  | braid_mul_vertex k i =>
    rcases le_or_gt (i + 2) k with hk | hk
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_le hk, mk_freeE, mk_freeTinv]
      exact Tinv_mul_e k i
    · simp only [map_mul, starSwapFree_freeE, starSwapFree_freeT_of_lt (by omega : k ≤ i + 1),
        zero_mul, map_zero]
  | braid_eq_zero h => simp only [starSwapFree_freeT_of_lt h, map_zero]
  | source h =>
    refine eq_of_sourceRelStar ?_
    have hmain := SourceRel.mapBar (bar := bar) (f := mkStarSwap K q bar) (E' := e K q)
      (U' := dPlusStar K q) (D' := dMinus K q) (T' := Tinv K q) mkStarSwap_mul mkStarSwap_smul
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeE]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeUp]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeDown]; rfl)
      (fun n i hni => by rw [mkStarSwap_apply, starSwapFree_freeT_of_le hni]; exact mk_freeTinv n i)
      h
    rwa [hbar] at hmain
  | sourceStar h =>
    refine eq_of_sourceRel ?_
    have hmain := SourceRel.mapBar (bar := bar) (f := mkStarSwap K q bar) (E' := e K q)
      (U' := dPlus K q) (D' := dMinus K q) (T' := Tg K q) mkStarSwap_mul mkStarSwap_smul
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeE]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeUpStar]; rfl)
      (fun n => by rw [mkStarSwap_apply, starSwapFree_freeDown]; rfl)
      (fun n i hni => by rw [mkStarSwap_apply, starSwapFree_freeTinv_of_le hbar hni]; rfl) h
    rwa [bar_invOf bar hbar] at hmain

/-- **The star swap of `𝔹`**: the map of `HJO.Dyck.starSwapFree` descended to the quotient. -/
noncomputable def starSwapBq : Bq K q →+* Bq K q :=
  RingQuot.lift ⟨(RingQuot.mkRingHom (Rel K q)).comp (starSwapFree K q bar), fun _ _ h => by
    simp only [RingHom.comp_apply, ← mk_eq_mkRingHom]
    exact mk_starSwapFree_rel hbar h⟩

theorem starSwapBq_mk (x : FreeAlgebra K Tilde.Gen) :
    starSwapBq hbar (mk K q x) = mk K q (starSwapFree K q bar x) := by
  rw [mk_eq_mkRingHom, starSwapBq, RingQuot.lift_mkRingHom_apply, RingHom.comp_apply,
    ← mk_eq_mkRingHom]

variable (hbb : ∀ c : K, bar (bar c) = c)

include hbb

/-- **The descended map is an involution.** This is where the construction departs from the
path-algebra argument, which proves involutivity there: on the *free* algebra the map is not an
involution, sending a loop the quiver does not have to `0` and `0` back to `0` rather than to the
loop. In `𝔹` that loop is itself `0`, by `HJO.Dyck.TwoSided.Bq.Tg_eq_zero`, and the identity
holds. On a loop the quiver has it is `HJO.Dyck.Tilde.tinvOf_tinvOf`, and on a scalar it is the
involutivity of the bar. -/
theorem mk_starSwapFree_starSwapFree (x : FreeAlgebra K Tilde.Gen) :
    mk K q (starSwapFree K q bar (starSwapFree K q bar x)) = mk K q x := by
  induction x with
  | grade0 c => rw [starSwapFree_algebraMap, starSwapFree_algebraMap, hbb]
  | grade1 g =>
    match g with
    | .vertex k => rw [starSwapFree_freeE, starSwapFree_freeE]
    | .up k => rw [starSwapFree_freeUp, starSwapFree_freeUpStar]
    | .upStar k => rw [starSwapFree_freeUpStar, starSwapFree_freeUp]
    | .down k => rw [starSwapFree_freeDown, starSwapFree_freeDown]
    | .braid k i =>
      rcases le_or_gt (i + 2) k with hk | hk
      · rw [starSwapFree_freeT_of_le hk, starSwapFree_freeTinv_of_le hbar hk]
      · simp only [starSwapFree_freeT_of_lt (by omega : k ≤ i + 1), map_zero]
        exact (Tg_eq_zero (by omega : k ≤ i + 1)).symm
  | mul a b iha ihb => rw [map_mul, map_mul, map_mul, iha, ihb, map_mul]
  | add a b iha ihb => rw [map_add, map_add, map_add, iha, ihb, map_add]

/-- **`HJO.Dyck.TwoSided.exists_isStarSwap`: the map is a star swap of `𝔹`.** Every clause of
`HJO.Dyck.IsStarSwap` is read off the construction: conjugate-linearity and multiplicativity from
`HJO.Dyck.starSwapFree`, involutivity from
`HJO.Dyck.TwoSided.mk_starSwapFree_starSwapFree`, and the values on the generators from
`HJO.Dyck.swapGen`. -/
theorem isStarSwap_starSwapBq :
    IsStarSwap q bar (e K q) (dPlus K q) (dPlusStar K q) (dMinus K q) (Tg K q)
      (starSwapBq hbar).toAddMonoidHom where
  map_smul c x := by
    change starSwapBq hbar (c • x) = bar c • starSwapBq hbar x
    obtain ⟨w, rfl⟩ := RingQuot.mkRingHom_surjective (Rel K q) x
    rw [← mk_eq_mkRingHom, ← map_smul (mk K q), starSwapBq_mk, starSwapBq_mk, starSwapFree_smul,
      map_smul]
  map_mul x y := by
    change starSwapBq hbar (x * y) = starSwapBq hbar x * starSwapBq hbar y
    exact map_mul _ x y
  involutive x := by
    change starSwapBq hbar (starSwapBq hbar x) = x
    obtain ⟨w, rfl⟩ := RingQuot.mkRingHom_surjective (Rel K q) x
    rw [← mk_eq_mkRingHom, starSwapBq_mk, starSwapBq_mk]
    exact mk_starSwapFree_starSwapFree hbar hbb w
  map_e k := by
    change starSwapBq hbar (e K q k) = e K q k
    rw [show e K q k = mk K q (Tilde.freeE K k) from rfl, starSwapBq_mk, starSwapFree_freeE]
  map_dMinus k := by
    change starSwapBq hbar (dMinus K q k) = dMinus K q k
    rw [show dMinus K q k = mk K q (Tilde.freeDown K k) from rfl, starSwapBq_mk,
      starSwapFree_freeDown]
  map_dPlus k := by
    change starSwapBq hbar (dPlus K q k) = dPlusStar K q k
    rw [show dPlus K q k = mk K q (Tilde.freeUp K k) from rfl, starSwapBq_mk, starSwapFree_freeUp,
      mk_freeUpStar]
  map_dPlusStar k := by
    change starSwapBq hbar (dPlusStar K q k) = dPlus K q k
    rw [show dPlusStar K q k = mk K q (Tilde.freeUpStar K k) from rfl, starSwapBq_mk,
      starSwapFree_freeUpStar, mk_freeUp]
  map_T {k i} h := by
    change starSwapBq hbar (Tg K q k i) = tinvOf q ⅟q (Tg K q k i) (e K q k)
    rw [show Tg K q k i = mk K q (Tilde.freeT K k i) from rfl, starSwapBq_mk,
      starSwapFree_freeT_of_le h]
    exact mk_freeTinv k i

/-- **`HJO.Dyck.TwoSided.exists_isStarSwap`: `𝔹` admits a star swap.** The two hypotheses are the
content of `HJO.Sym.paramInvLambda`: the bar inverts `q`, and it is an involution. -/
@[hjo "lem_cm_star_swap_exists"]
theorem exists_isStarSwap :
    ∃ σ : Bq K q →+ Bq K q,
      IsStarSwap q bar (e K q) (dPlus K q) (dPlusStar K q) (dMinus K q) (Tg K q) σ :=
  ⟨_, isStarSwap_starSwapBq hbar hbb⟩

end TwoSided

end HJO.Dyck
