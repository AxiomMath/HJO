/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import HJO.Collinear.Vocabulary
public meta import HJO.Attr

/-! # The free algebra on the basic operators, and the descent of the index raise

`HJO.Sym.IsIndexShift` of `HJO/Collinear/Vocabulary.lean` is a *predicate*: an index shift is
an `L`-algebra endomorphism `𝖲` of the operator algebra `𝖠 = Algebra.adjoin L (range (Dop q u))`
with `𝖲(D_k) = D_{k+1}` for every `k`, and nothing there asserts one exists. The collinear
commutation argument takes its existence as a hypothesis — it is the `hshift` argument of
`HJO.CollinearNarrowed.collinearCommute_of_diag` — so constructing one discharges that hypothesis.

BGLX construct it as a descent. Let `F` be the free `L`-algebra on symbols `x_0, x_1, x_2, …`, let
`π : F → End_L(Λ)` be the unique algebra homomorphism with `π(x_k) = D_k`, and let `σ` be the
unique algebra endomorphism of `F` with `σ(x_k) = x_{k+1}`. The image of `π` is exactly `𝖠`, so
`π` corestricts to a surjection onto `𝖠`; if `ker π` is stable under `σ` then `σ` descends along
that surjection to an endomorphism `𝖲` of `𝖠`, and `𝖲(D_k) = 𝖲(π(x_k)) = π(x_{k+1}) = D_{k+1}`
makes it an index shift.

This file is that descent, in full, with `σ`-stability of `ker π` carried as the single explicit
hypothesis `HJO.Sym.RaiseStableKernel`. The free-algebra half of BGLX's argument is therefore
complete and reusable; the one place the vanishing criterion (BGLX Theorem 2.1) enters is
`RaiseStableKernel`.

**`RaiseStableKernel` is proved.** It is discharged by
`HJO.Bglx.raiseStableKernel_of_criterionNecessary` (`HJO/Collinear/CriterionSufficient.lean`),
and an index shift exists unconditionally at the standing field by
`HJO.Bglx.exists_isIndexShift_param` (`HJO/Collinear/IndexShiftStanding.lean`). The theorem below
is the conditional form, from which that one follows.

## Main definitions

* `HJO.Sym.dopFreeHom`: `π`, the unique `L`-algebra homomorphism `FreeAlgebra L ℕ → End_L(Λ)`
  sending the `k`-th generator to `Dop q u k`.
* `HJO.Sym.dopFreeGen`: the same map corestricted to the operator algebra `𝖠`, where it is
  surjective.
* `HJO.Sym.freeIndexRaise`: `σ`, the unique `L`-algebra endomorphism of `FreeAlgebra L ℕ` raising
  every generator.
* `HJO.Sym.RaiseStableKernel`: the predicate `ker π` is stable under `σ`.
* `HJO.Sym.indexShift`: the descent `𝖲` of `σ` to `𝖠`, given that predicate.

## Main statements

* `HJO.Sym.range_dopFreeHom`: the image of `π` is `𝖠` on the nose.
* `HJO.Sym.indexShiftFun_dopFreeGen`: `𝖲(π V) = π(σ V)`, the equation the descent is defined by.
* `HJO.Sym.exists_isIndexShift`: an index shift exists as soon as `ker π` is `σ`-stable.

## Implementation notes

**`F` is `FreeAlgebra L ℕ`, not a monoid algebra.** The construction takes `F` to be the `L`-algebra
of the free monoid on `ℕ` and identifies its length-`k` homogeneous piece `F_k` with the finitely
supported functions `ℕ^k → L`. Mathlib's `FreeAlgebra L ℕ` is that algebra (`FreeAlgebra` is
`MonoidAlgebra` of `FreeMonoid` up to `FreeAlgebra.equivMonoidAlgebra`), and it is the spelling
that carries the two universal properties the argument is made of: `FreeAlgebra.lift` gives both
`π` and `σ` with no construction, and `Algebra.adjoin_range_eq_range_freeAlgebra_lift` gives
`range π = 𝖠` with no computation. The grading by word length is *not* built here, because the
descent does not need it: `RaiseStableKernel` is a statement about arbitrary elements of `F`, and
the route through the homogeneous pieces (`HJO.Sym.sum_dopWordOperator_eq_zero_iff` and
`HJO.Sym.dopWordOperator_dopWordRaise_eq_zero_iff`) is one way to establish it and not the only one.

**The descent is hand-rolled rather than routed through a quotient.** Mathlib's
`AlgHom.liftOfSurjective` is the statement wanted, but it requires all four algebras to be
commutative and `End_L(Λ)` is not; `Ideal.quotientKerAlgEquivOfSurjective` does apply, but the
resulting term carries the quotient and its kernel ideal through every subsequent rewrite. So
`indexShift` is built from `Function.surjInv` and `indexShiftFun_dopFreeGen`, which is the
well-definedness step of the descent verbatim: if `π V = π W` then `V - W ∈ ker π`, so
`σ(V - W) ∈ ker π` and `π(σ V) = π(σ W)`. Every algebra-homomorphism field of `indexShift` is then
discharged by pulling both arguments back along the surjection and citing that one equation, which
is also the reason that the descent is an algebra map.

`dopFreeGen` is `π` corestricted by `AlgHom.codRestrict` rather than `AlgHom.rangeRestrict`
followed by a transport: `range π` and `𝖠` are equal subalgebras but not the same term, and
corestricting directly to `DopAlgebra q u` keeps `𝖠` — the subalgebra named everywhere else in the
library — as the domain and codomain of `indexShift`, so no `Subalgebra.equivOfEq` appears in the
statement of `exists_isIndexShift`.

Hypotheses. `Field L` and `Algebra ℚ L` are what `Dop` and `DopAlgebra` require, and no further
condition on `q` or `u` is used: the descent is formal and holds for every pair of parameters.
Every parameter condition the construction of an index shift genuinely needs is hidden inside
`RaiseStableKernel`, which is where the criterion — and with it any condition on `q` and `u` —
belongs.

Faithfulness. (1) `dopFreeHom` and `freeIndexRaise` are pinned to the `π` and `σ` by
`dopFreeHom_ι` and `freeIndexRaise_ι`, so they are those maps and not merely maps with the right
domain. (2) `range_dopFreeHom` is the statement "the image of `π` is the subalgebra generated by
`D_0, D_1, …`, which is `𝖠`", proved and not assumed. (3) Nothing is weakened: `indexShift` is a
genuine `AlgHom` of `𝖠` into itself and `isIndexShift_indexShift` gives
`𝖲(D_k) = D_{k+1}` for every `k ≥ 0`, so `exists_isIndexShift` produces exactly the datum
`HJO.Sym.IsIndexShift` asks for. (4) The hypothesis is not vacuous and not secretly everything:
`RaiseStableKernel` is an implication about `ker π`, which is a proper ideal of `F` (`π` is not
injective), so it is a real condition; and it is the *only* hypothesis, so a proof of it closes
`HJO.Bglx.exists_isIndexShift_param` immediately.

## References

F. Bergeron, A. M. Garsia, E. Leven and G. Xin, *Some remarkable new plethystic operators in the
theory of Macdonald polynomials*, arXiv:1405.0316v1, J. Comb. **7** (2016) 671--714, Theorem 2.2.
Their Theorem 2.3, that the substitutions
generate an `SL_2(ℤ)` action, is false as stated per Mellit's footnote; only the single
endomorphism constructed here is used.
-/

@[expose] public section

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The free algebra on the basic operators -/

/-- `π`: the unique `L`-algebra homomorphism from the free `L`-algebra on `ℕ` to `End_L(Λ)`
sending the `k`-th generator to the basic operator `D_k`. -/
noncomputable def dopFreeHom (q u : L) : FreeAlgebra L ℕ →ₐ[L] Module.End L (Lambda L) :=
  FreeAlgebra.lift L (Dop q u)

@[simp] theorem dopFreeHom_ι (q u : L) (k : ℕ) :
    dopFreeHom q u (FreeAlgebra.ι L k) = Dop q u k := by
  simp [dopFreeHom]

/-- The image of `π` is the operator algebra `𝖠`: the image of a lift out of a free algebra is the
subalgebra generated by the images of the generators. -/
theorem range_dopFreeHom (q u : L) : (dopFreeHom q u).range = DopAlgebra q u :=
  (Algebra.adjoin_range_eq_range_freeAlgebra_lift (R := L) (f := Dop q u)).symm

theorem dopFreeHom_mem (q u : L) (V : FreeAlgebra L ℕ) :
    dopFreeHom q u V ∈ DopAlgebra q u := by
  rw [← range_dopFreeHom]
  exact ⟨V, rfl⟩

/-- `π` corestricted to the operator algebra `𝖠`, where it is surjective. -/
noncomputable def dopFreeGen (q u : L) : FreeAlgebra L ℕ →ₐ[L] DopAlgebra q u :=
  (dopFreeHom q u).codRestrict (DopAlgebra q u) (dopFreeHom_mem q u)

@[simp] theorem coe_dopFreeGen (q u : L) (V : FreeAlgebra L ℕ) :
    (dopFreeGen q u V : Module.End L (Lambda L)) = dopFreeHom q u V := rfl

theorem dopFreeGen_eq_zero_iff (q u : L) (V : FreeAlgebra L ℕ) :
    dopFreeGen q u V = 0 ↔ dopFreeHom q u V = 0 := by
  rw [← Subtype.coe_inj]
  simp

theorem dopFreeGen_surjective (q u : L) : Function.Surjective (dopFreeGen q u) := by
  intro y
  obtain ⟨V, hV⟩ : (y : Module.End L (Lambda L)) ∈ (dopFreeHom q u).range := by
    rw [range_dopFreeHom]
    exact y.2
  exact ⟨V, Subtype.ext hV⟩

@[simp] theorem dopFreeGen_ι (q u : L) (k : ℕ) :
    dopFreeGen q u (FreeAlgebra.ι L k) = dopGen q u k :=
  Subtype.ext (by simp [dopGen])

/-! ### Raising every index on the free algebra -/

/-- `σ`: the unique `L`-algebra endomorphism of the free `L`-algebra on `ℕ` carrying the `k`-th
generator to the `(k+1)`-st, so that on words it raises every index. -/
noncomputable def freeIndexRaise (L : Type*) [Field L] :
    FreeAlgebra L ℕ →ₐ[L] FreeAlgebra L ℕ :=
  FreeAlgebra.lift L fun k => FreeAlgebra.ι L (k + 1)

@[simp] theorem freeIndexRaise_ι (L : Type*) [Field L] (k : ℕ) :
    freeIndexRaise L (FreeAlgebra.ι L k) = FreeAlgebra.ι L (k + 1) := by
  simp [freeIndexRaise]

/-- `ker π` is stable under `σ`: an element of the free algebra that acts by zero on `Λ` still
acts by zero after every index is raised. This is the single input the construction of an index
shift needs beyond formal algebra, and it is the content of BGLX's Theorem 2.2 — in this
library the one place the vanishing criterion `HJO.Bglx.isVanishingCriterion` is used. -/
def RaiseStableKernel (q u : L) : Prop :=
  ∀ V : FreeAlgebra L ℕ, dopFreeHom q u V = 0 → dopFreeHom q u (freeIndexRaise L V) = 0

/-! ### The descent -/

/-- The underlying function of the descent, defined through a choice of preimage; `π` being
surjective onto `𝖠`, `indexShiftFun_dopFreeGen` shows the choice does not matter. -/
noncomputable def indexShiftFun (q u : L) (a : DopAlgebra q u) : DopAlgebra q u :=
  dopFreeGen q u (freeIndexRaise L (Function.surjInv (dopFreeGen_surjective q u) a))

/-- The equation the descent is defined by: `𝖲(π V) = π(σ V)`. This is the
well-definedness step — if `π V = π W` then `V - W ∈ ker π`, so `σ(V - W) ∈ ker π` and
`π(σ V) = π(σ W)`. -/
theorem indexShiftFun_dopFreeGen {q u : L} (h : RaiseStableKernel q u) (V : FreeAlgebra L ℕ) :
    indexShiftFun q u (dopFreeGen q u V) = dopFreeGen q u (freeIndexRaise L V) := by
  set W := Function.surjInv (dopFreeGen_surjective q u) (dopFreeGen q u V) with hW
  have hWV : dopFreeGen q u W = dopFreeGen q u V :=
    Function.surjInv_eq (dopFreeGen_surjective q u) _
  have h0 : dopFreeHom q u (W - V) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg (fun x : DopAlgebra q u => (x : Module.End L (Lambda L))) hWV
  have h1 := h _ h0
  rw [map_sub, map_sub, sub_eq_zero] at h1
  change dopFreeGen q u (freeIndexRaise L W) = _
  exact Subtype.ext h1

/-- **`σ` descends to `𝖠`.** Given that `ker π` is stable under `σ`, the `L`-algebra endomorphism
`𝖲` of the operator algebra `𝖠` with `𝖲(π V) = π(σ V)`. -/
noncomputable def indexShift {q u : L} (h : RaiseStableKernel q u) :
    DopAlgebra q u →ₐ[L] DopAlgebra q u where
  toFun := indexShiftFun q u
  map_one' := by
    rw [show (1 : DopAlgebra q u) = dopFreeGen q u 1 from (map_one _).symm,
      indexShiftFun_dopFreeGen h, map_one, map_one]
  map_mul' a b := by
    obtain ⟨V, rfl⟩ := dopFreeGen_surjective q u a
    obtain ⟨W, rfl⟩ := dopFreeGen_surjective q u b
    rw [← map_mul, indexShiftFun_dopFreeGen h, indexShiftFun_dopFreeGen h,
      indexShiftFun_dopFreeGen h, map_mul, map_mul]
  map_zero' := by
    rw [show (0 : DopAlgebra q u) = dopFreeGen q u 0 from (map_zero _).symm,
      indexShiftFun_dopFreeGen h, map_zero, map_zero]
  map_add' a b := by
    obtain ⟨V, rfl⟩ := dopFreeGen_surjective q u a
    obtain ⟨W, rfl⟩ := dopFreeGen_surjective q u b
    rw [← map_add, indexShiftFun_dopFreeGen h, indexShiftFun_dopFreeGen h,
      indexShiftFun_dopFreeGen h, map_add, map_add]
  commutes' r := by
    rw [show algebraMap L (DopAlgebra q u) r = dopFreeGen q u (algebraMap L _ r) from
      (AlgHom.commutes _ r).symm, indexShiftFun_dopFreeGen h, AlgHom.commutes, AlgHom.commutes]

@[simp] theorem indexShift_apply {q u : L} (h : RaiseStableKernel q u) (a : DopAlgebra q u) :
    indexShift h a = indexShiftFun q u a := rfl

/-- The descent is an index shift: it sends `D_k` to `D_{k+1}` for every `k ≥ 0`. -/
theorem isIndexShift_indexShift {q u : L} (h : RaiseStableKernel q u) :
    IsIndexShift q u (indexShift h) := by
  intro k
  rw [indexShift_apply, ← dopFreeGen_ι, indexShiftFun_dopFreeGen h, freeIndexRaise_ι,
    dopFreeGen_ι]

/-- **An index shift exists as soon as `ker π` is stable under `σ`.** The free-algebra half of
BGLX's Theorem 2.2, complete: what a proof of `HJO.Bglx.exists_isIndexShift_param` still owes is
exactly `RaiseStableKernel q u`, and no condition on `q` or `u` is needed for anything else. -/
theorem exists_isIndexShift {q u : L} (h : RaiseStableKernel q u) :
    ∃ S : DopAlgebra q u →ₐ[L] DopAlgebra q u, IsIndexShift q u S :=
  ⟨indexShift h, isIndexShift_indexShift h⟩

end HJO.Sym
