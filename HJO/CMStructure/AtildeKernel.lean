/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.KernelStarStep
public import HJO.CarlssonMellit.StarFlipExists
public import HJO.CMStructure.AtildeMixed
public meta import HJO.Attr

/-! # The evaluation map `Ã𝟏_0 → V_*`, and the kernel half of
`HJO.Standing.exists_action_atilde_ker_eq_param`

`HJO.Standing.exists_action_atilde_ker_eq_param` has two conclusions. The first — that `T_i`, `d_-`,
`d_+`, `d^*_+` and the projections define an action of `Ã` on `V_*` — is
`HJO.Sweep.exists_action_atilde`. The second is `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`:
the kernel of the map `Ãe_0 → V_*` sending `fe_0` to `f(1)` is `Ie_0`. That map is
`HJO.Sweep.evalOne`, defined in this file.

## What is proved and what is not

The `⊇` half of `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` is proved **unconditionally**:
`HJO.Sweep.kernelIdealE0_le_ker`. This is also the "vanishes on `Ie_0`" clause of
`HJO.Sweep.exists_quotient_linearMap_evalOne`. It is exactly where
`HJO.Dyck.Tilde.Atilde.kernelIdeal`'s insistence that `I` be a
*left* ideal is spent: `HJO.Sweep.annOne`, the annihilator of `1 ∈ V_0`, is a left ideal and nothing
more, and the counterexample at `HJO.Dyck.Tilde.Atilde.kernelIdeal` is the
statement that it is not a two-sided one.

The `⊆` half is proved **modulo one hypothesis**, `HJO.Sweep.atildeE0_inf_ker_eq_kernelIdealE0`,
and the hypothesis is
`aqE0 ⊓ ker (evalOne ρ) ≤ kernelIdealE0` — the statement that the map is injective on the image of
`𝔸_q𝟏_0` up to `I𝟏_0`. That is the injectivity half of `HJO.Sweep.exists_linearEquiv_e0Ideal`, which
is proved as `HJO.Sweep.exists_linearEquiv_e0Ideal` (`HJO/CMStructure/Thm52Injective.lean`). The
hypothesis is discharged, and `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`
and `HJO.Standing.exists_action_atilde_ker_eq_param` are proved, in
`HJO/CMStructure/Thm73Closed.lean` (`HJO.Sweep.aqE0_inf_ker_evalOne_eq_bot`,
`HJO.Sweep.atildeE0_inf_ker_evalOne_eq` and `HJO.Sweep.exists_action_atilde_ker_eq`); this file
states the reduction.

Everything else the proof of `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` asks for is now
discharged and needs no hypothesis:

* the algebra-level exhaustion `Ã𝟏_0 = 𝔸_q𝟏_0 + I𝟏_0`, which is
  `HJO.Dyck.Tilde.Atilde.atildeE0_eq_aqE0_sup_kernelIdealE0` — and note that its arrow-degree
  induction is gone, so `HJO.Dyck.Tilde.Atilde.isInternal_grade` is not consulted;
* the two unit computations of `HJO.Sweep.cmDPlusPow_map_one`, which enter as
  `HJO.Sweep.evalOne_dPlusPow_zero` and `HJO.Sweep.evalOne_dPlusStar_mul_dPlusPow`.

The proof of `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` runs its induction on the arrow
degree; no induction of any kind appears below. What replaces it is the exhaustion statement above,
which the `d^*_+`-stability lemma proves directly.

## Implementation notes

**The generators of `I` are read at every vertex, and away from the vertex `0` both of their words
already evaluate to `0`.** `HJO.Dyck.Tilde.Atilde.kernelIdeal` is spanned by
`d^*_+d_+^m - d_+^{m+1}` read at each starting vertex `v`, not only at `v = 0`. On `1 ∈ V_0` the
words starting at `v ≠ 0` are annihilated by the leading projection, so
`HJO.Sweep.evalOne_dPlusPow_of_ne` disposes of them; only `v = 0` carries content, and there the two
words agree because both send `1` to `1`.

**`evalOne` is defined on all of `Ã` rather than on `Ãe_0`.** The map has domain
`Ãe_0`; since `ρ(e_0)` is the projection onto `V_0` and fixes `1`, the map `x ↦ ρ(x)(1)` on all of
`Ã` restricts to it on the nose — `HJO.Sweep.evalOne_mul` with
`HJO.Sweep.evalOne_e_zero`. Stating the kernel as `atildeE0 ⊓ LinearMap.ker (evalOne ρ)` keeps the
submodule `Ãe_0` visible where the statement puts it.

**The star swap is not a hypothesis on the action, it is a hypothesis on the coefficients.** The
exhaustion statement needs `HJO.Sym.paramInvLambda`: a ring involution of `𝕜` inverting `q` and `u`,
with `u` invertible. `HJO.Dyck.Tilde.Atilde.exists_isStarSwap` turns exactly that data into the
`IsStarSwap` the exhaustion theorem consumes, so the theorems below carry `bar`, not `σ`. The same
hypothesis appears at `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`.

## Main results

* `HJO.Sweep.evalOne` — the map `fe_0 ↦ f(1)` of `HJO.Sweep.exists_quotient_linearMap_evalOne`.
* `HJO.Sweep.annOne` — the annihilator of `1 ∈ V_0`, as a left ideal of `Ã`.
* `HJO.Sweep.kernelIdealE0_le_ker` — `I𝟏_0` is contained in the kernel; the `⊇` half of
  `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` and the second clause of
  `HJO.Sweep.exists_quotient_linearMap_evalOne`.
* `HJO.Sweep.exists_action_atilde_ker_ge` — the action of
  `HJO.Standing.exists_action_atilde_ker_eq_param` together with that containment, with no
  hypothesis beyond the ones the action already carries.
* `HJO.Sweep.atildeE0_inf_ker_eq_kernelIdealE0` — `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`
  given the injectivity of `HJO.Sweep.exists_linearEquiv_e0Ideal`, and
  `HJO.Sweep.atildeE0_inf_ker_eq_kernelIdealE0_of_injOn` the same from injectivity stated on the
  nose.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, §7, and A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The unit of each summand -/

section Unit

variable {L : Type*} [Field L]

/-- **`1 ∈ V_k`, read in the `k`-th summand of `V_*`.** The value of the `d_+^m(1)`, by
`HJO.Sweep.cmDPlusPow_map_one` says that word fixes `1`, and the vertex it
lands at is `m`. -/
noncomputable def oneAt (L : Type*) [Field L] (k : ℕ) : Vstar L :=
  ofPiece L k ⟨1, one_mem (piece L k)⟩

theorem oneAt_eq (k : ℕ) : oneAt L k = ofPiece L k ⟨1, one_mem (piece L k)⟩ := rfl

theorem oneAt_zero : oneAt L 0 = oneVstar L := rfl

end Unit

/-! ### The evaluation map -/

section Eval

variable {L : Type*} [Field L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))

/-- **The map `fe_0 ↦ f(1)` of `HJO.Sweep.exists_quotient_linearMap_evalOne`**, read on all of `Ã`
rather than on `Ãe_0`: since `ρ(e_0)` fixes `1 ∈ V_0`, the two agree on `Ãe_0`, and having it on `Ã`
is what lets the annihilator below be an ideal of `Ã`. -/
noncomputable def evalOne : Dyck.Tilde.Atilde L q u →ₗ[L] Vstar L where
  toFun x := ρ x (oneVstar L)
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

@[simp]
theorem evalOne_apply (x : Dyck.Tilde.Atilde L q u) : evalOne ρ x = ρ x (oneVstar L) := rfl

/-- The map is `ρ`-equivariant for left multiplication, which is the whole reason a *left* ideal is
the right notion in `HJO.Dyck.Tilde.Atilde.kernelIdeal`. -/
theorem evalOne_mul (x y : Dyck.Tilde.Atilde L q u) :
    evalOne ρ (x * y) = ρ x (evalOne ρ y) := by
  rw [evalOne_apply, map_mul, Module.End.mul_apply, evalOne_apply]

variable (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)

include hρe

/-- The base point: `e_0` acts as the projection onto `V_0`, which fixes `1`. -/
theorem evalOne_e_zero : evalOne ρ (Dyck.Tilde.Atilde.e L q u 0) = oneVstar L := by
  rw [evalOne_apply, hρe]
  exact pieceProj_ofPiece 0 _

/-- A word of raising arrows that does not start at the vertex `0` is annihilated: its leading
projection kills `1 ∈ V_0`. This is what disposes of the generators of `I` read at the vertices
`v ≠ 0`. -/
theorem evalOne_dPlusPow_of_ne {v : ℕ} (hv : v ≠ 0) (m : ℕ) :
    evalOne ρ (Dyck.Tilde.Atilde.dPlusPow L q u v m) = 0 := by
  induction m with
  | zero =>
    rw [show Dyck.Tilde.Atilde.dPlusPow L q u v 0 = Dyck.Tilde.Atilde.e L q u v from rfl,
      evalOne_apply, hρe]
    exact pieceProj_ofPiece_of_ne (Ne.symm hv) _
  | succ m ih =>
    rw [Dyck.Tilde.Atilde.dPlusPow_succ, evalOne_mul, ih, map_zero]

variable (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)

include hρup

/-- **`d_+^m(1) = 1 ∈ V_m`**, the first clause of `HJO.Sweep.cmDPlusPow_map_one`, read through the
action: induction on `m` from `HJO.Sweep.cmDPlus_map_one`. -/
theorem evalOne_dPlusPow_zero (m : ℕ) :
    evalOne ρ (Dyck.Tilde.Atilde.dPlusPow L q u 0 m) = oneAt L m := by
  induction m with
  | zero => exact evalOne_e_zero ρ hρe
  | succ m ih =>
    rw [Dyck.Tilde.Atilde.dPlusPow_succ, evalOne_mul, ih, zero_add, hρup, oneAt_eq,
      raiseVstar_ofPiece, oneAt_eq]
    refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
    rw [coe_cmDPlusPiece]
    exact cmDPlus_map_one q m

variable (hρupStar : ∀ k : ℕ,
  ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

include hρupStar

/-- **`d^*_+d_+^m` and `d_+^{m+1}` have the same value on `1`**, at every starting vertex: the
second clause of `HJO.Sweep.cmDPlusPow_map_one` at the vertex `0`, and `0 = 0` away from it. -/
theorem evalOne_dPlusStar_mul_dPlusPow (v m : ℕ) :
    evalOne ρ (Dyck.Tilde.Atilde.dPlusStar L q u (v + m) * Dyck.Tilde.Atilde.dPlusPow L q u v m)
      = evalOne ρ (Dyck.Tilde.Atilde.dPlusPow L q u v (m + 1)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [evalOne_mul, evalOne_dPlusPow_zero ρ hρe hρup m, zero_add, hρupStar, oneAt_eq,
      raiseVstar_ofPiece, evalOne_dPlusPow_zero ρ hρe hρup (m + 1), oneAt_eq]
    refine congrArg (ofPiece L (m + 1)) (Subtype.ext ?_)
    rw [coe_dplusStarPiece]
    exact dplusStar_map_one q u m
  · rw [evalOne_mul, evalOne_dPlusPow_of_ne ρ hρe hv m, map_zero,
      evalOne_dPlusPow_of_ne ρ hρe hv (m + 1)]

/-- Each generator of `HJO.Dyck.Tilde.Atilde.kernelIdeal`'s `I` evaluates to `0` on `1`. -/
theorem evalOne_kernelIdeal_gen (v m : ℕ) :
    evalOne ρ (Dyck.Tilde.Atilde.dPlusStar L q u (v + m) * Dyck.Tilde.Atilde.dPlusPow L q u v m
      - Dyck.Tilde.Atilde.dPlusPow L q u v (m + 1)) = 0 := by
  rw [map_sub, evalOne_dPlusStar_mul_dPlusPow ρ hρe hρup hρupStar v m, sub_self]

end Eval

/-! ### The annihilator of the unit, and `I𝟏_0` inside it -/

section Ann

variable {L : Type*} [Field L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))

/-- **The annihilator of `1 ∈ V_0`**, as a *left* ideal of `Ã`. Left is all it is, and that is
exactly the reason `HJO.Dyck.Tilde.Atilde.kernelIdeal` makes `I` a left ideal: the remark there
exhibits an element of the two-sided ideal generated by the same elements whose value on `1` is
`My_1 ≠ 0`. -/
noncomputable def annOne : Ideal (Dyck.Tilde.Atilde L q u) where
  carrier := {x | evalOne ρ x = 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy, add_zero]
  zero_mem' := map_zero _
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul, evalOne_mul, hx, map_zero]

theorem mem_annOne {x : Dyck.Tilde.Atilde L q u} : x ∈ annOne ρ ↔ evalOne ρ x = 0 := Iff.rfl

variable (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
  (hρupStar : ∀ k : ℕ,
    ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

include hρe hρup hρupStar

/-- **`I` annihilates `1`.** `I` is generated as a left ideal, and the annihilator is a left ideal,
so it is enough to check the generators. -/
theorem kernelIdeal_le_annOne : Dyck.Tilde.Atilde.kernelIdeal L q u ≤ annOne ρ := by
  rw [Dyck.Tilde.Atilde.kernelIdeal]
  refine Ideal.span_le.2 ?_
  rintro x ⟨v, m, rfl⟩
  exact evalOne_kernelIdeal_gen ρ hρe hρup hρupStar v m

/-- **`I𝟏_0` is contained in the kernel of `fe_0 ↦ f(1)`**: the `⊇` half of
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`, and the clause of
`HJO.Sweep.exists_quotient_linearMap_evalOne` that says the map descends to `Ãe_0/Ie_0`. No
hypothesis beyond the action's own. -/
theorem kernelIdealE0_le_ker :
    Dyck.Tilde.Atilde.kernelIdealE0 L q u ≤ LinearMap.ker (evalOne ρ) := by
  rw [Dyck.Tilde.Atilde.kernelIdealE0]
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  rw [LinearMap.mem_ker, Dyck.Tilde.Atilde.rightE0_apply, evalOne_mul, evalOne_e_zero ρ hρe]
  exact kernelIdeal_le_annOne ρ hρe hρup hρupStar hy

end Ann

/-! ### The kernel half of `HJO.Standing.exists_action_atilde_ker_eq_param` -/

section KernelGe

variable {L : Type*} [Field L] [Algebra ℚ L] (q u : L) [Invertible q] [Invertible (q - 1)]

/-- **The action of `HJO.Standing.exists_action_atilde_ker_eq_param` together with the containment
`I𝟏_0 ⊆ ker`.** This is everything `HJO.Standing.exists_action_atilde_ker_eq_param` asserts except
the reverse containment, which is where `HJO.Sweep.exists_linearEquiv_e0Ideal` enters (proved, with
the full statement, in `HJO/CMStructure/Thm73Closed.lean`); and it carries no hypothesis the action
half did not already carry. -/
theorem exists_action_atilde_ker_ge (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k)
      ∧ Dyck.Tilde.Atilde.kernelIdealE0 L q u ≤ LinearMap.ker (evalOne ρ) := by
  obtain ⟨ρ, hρe, hρT, hρdown, hρup, hρupStar⟩ := exists_action_atilde q u hq1
  exact ⟨ρ, hρe, hρT, hρdown, hρup, hρupStar,
    kernelIdealE0_le_ker ρ hρe hρup hρupStar⟩

end KernelGe

section KernelExact

variable {L : Type*} [Field L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
  (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
  (hρupStar : ∀ k : ℕ,
    ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)
  [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)
  (hbb : ∀ c : L, bar (bar c) = c)

include hρe hρup hρupStar hbar hbaru hbb

/-- **`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`, modulo the injectivity of
`HJO.Sweep.exists_linearEquiv_e0Ideal`.** The kernel of `Ãe_0 → V_*` is `Ie_0`, given `haq`.

The `⊇` half is `HJO.Sweep.kernelIdealE0_le_ker` and is unconditional. For `⊆`, the exhaustion
statement `HJO.Dyck.Tilde.Atilde.atildeE0_eq_aqE0_sup_kernelIdealE0` splits an element of `Ãe_0` as
`a + r` with `a ∈ 𝔸_q𝟏_0` and `r ∈ I𝟏_0`; `r` is already in the kernel, so `a` is too, and `haq`
places it.

`haq` is the injectivity half of `HJO.Sweep.exists_linearEquiv_e0Ideal` in the weakest form this
argument uses, and it is the only input `HJO.Standing.exists_action_atilde_ker_eq_param`'s kernel
conclusion takes beyond this file: no normal form, no arrow-degree induction and no termination
measure appears anywhere below or in the exhaustion statement. It is discharged as
`HJO.Sweep.aqE0_inf_ker_evalOne_eq_bot` in `HJO/CMStructure/Thm73Closed.lean`, from
`HJO.Sweep.exists_linearEquiv_e0Ideal` (`HJO.Sweep.exists_linearEquiv_e0Ideal`,
`HJO/CMStructure/Thm52Injective.lean`).

`bar` is `HJO.Sym.paramInvLambda`, which the exhaustion statement needs and
`HJO.Dyck.Tilde.Atilde.exists_isStarSwap` consumes. -/
theorem atildeE0_inf_ker_eq_kernelIdealE0
    (haq : Dyck.Tilde.Atilde.aqE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      ≤ Dyck.Tilde.Atilde.kernelIdealE0 L q u) :
    Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      = Dyck.Tilde.Atilde.kernelIdealE0 L q u := by
  obtain ⟨σ, hσ⟩ := Dyck.Tilde.Atilde.exists_isStarSwap (K := L) (q := q) (u := u) hbar hbaru hbb
  refine le_antisymm ?_ (le_inf ?_ (kernelIdealE0_le_ker ρ hρe hρup hρupStar))
  · rintro x ⟨hx1, hx2⟩
    rw [Dyck.Tilde.Atilde.atildeE0_eq_aqE0_sup_kernelIdealE0 hσ hbar] at hx1
    obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.1 hx1
    have hr0 : evalOne ρ r = 0 :=
      kernelIdealE0_le_ker ρ hρe hρup hρupStar hr
    have ha0 : evalOne ρ a = 0 := by
      have hx2' : evalOne ρ (a + r) = 0 := hx2
      rwa [map_add, hr0, add_zero] at hx2'
    exact add_mem (haq ⟨ha, ha0⟩) hr
  · rw [Dyck.Tilde.Atilde.atildeE0, Dyck.Tilde.Atilde.kernelIdealE0]
    rintro x hx
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 hx
    exact LinearMap.mem_range_self _ y

/-- **`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` from the injectivity of
`HJO.Sweep.exists_linearEquiv_e0Ideal` stated on the nose.** -/
theorem atildeE0_inf_ker_eq_kernelIdealE0_of_injOn
    (hinj : ∀ x ∈ Dyck.Tilde.Atilde.aqE0 L q u, evalOne ρ x = 0 → x = 0) :
    Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      = Dyck.Tilde.Atilde.kernelIdealE0 L q u :=
  atildeE0_inf_ker_eq_kernelIdealE0 ρ hρe hρup hρupStar hbar hbaru hbb
    (fun x hx => by
      rw [hinj x hx.1 (LinearMap.mem_ker.1 hx.2)]
      exact zero_mem _)

end KernelExact

end HJO.Sweep

end
