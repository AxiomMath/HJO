/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ArrowGraded
public import HJO.CarlssonMellit.DpaMellitWords
public meta import HJO.Attr

/-! # The starred arrow on a raising block, modulo `I𝟏_0`

The two steps of `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` that are internal
to `Ã` and need nothing but the relations of `HJO.Dyck.Tilde.Atilde` and the generators of `I`:

* the starred raising arrow on a *terminal* block of unstarred raising arrows is the unstarred
  block one longer, modulo `I𝟏_0` — this is the `F = d₊^m(1)` case of the lemma, and it is where
  the generators of `I` are used;
* the starred corner element `z_i` on a terminal raising block descends through the block by the
  first mixed relation until the last arrow, where the third mixed relation turns it into `y_1`
  times a starred arrow, which the first step then unstars — so `z_id₊^n𝟏_0` lies in the
  *unstarred* part of `Ã𝟏_0` modulo `I𝟏_0`. This is the step of the lemma's proof that places
  `z_kG`, in the only case its recursion bottoms out in.

Neither statement is the lemma. What the lemma needs beyond them is recorded in the note below.

## What the lemma still needs, and why it is not here

The lemma asserts that the image of `𝔸_q𝟏_0` in `Ã𝟏_0/I𝟏_0` is carried into itself by `d₊^*`. Its
proof pushes `d₊^*` rightwards through a word in the unstarred generators: past a loop by the
starred `up_braid` relation, past a corner element by the second mixed relation
`HJO.Dyck.Tilde.Atilde.mixed_y`, past `d₋` by the starred commutator — and *there is no relation of
`Ã` that moves `d₊^*` past `d₊`*. The generators of `I` retire `d₊^*` only against a block `d₊^m`
that is terminal, i.e. applied to `𝟏_0`, which is what this file proves; `I` is a *left* ideal, so
`d₊^*d₊^m - d₊^{m+1}` may not be multiplied on the right by anything.

So the proof needs its word in a normal form in which every `d₊` sits in one terminal block. That
normal form is not `HJO.Sweep.exists_basis_vstar_prod_bop`, which one might cite for it: that lemma
is a basis of the *module* `V_*`, not a normal form in the algebra. The natural normal form is the
four-move reduction inside the proof of `HJO.Sweep.exists_linearEquiv_e0Ideal`, and
`HJO.Dyck.straightenMeasure_lt_moveTwo` records that the measure of
`HJO.Dyck.straightenMeasure_lt_of_step` *increases* under the second of those moves, so that
reduction comes with no termination measure for the joint iteration. The lemma is proved instead
in `HJO.CarlssonMellit.KernelStarStep`, through the weaker normal form of
`HJO.CarlssonMellit.KernelSpanRoute`, which needs no termination measure.

## Main results

* `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_dPlusPow_sub_mem_kernelIdealE0`.
* `HJO.Dyck.Tilde.Atilde.zElt_mul_dPlusPow`: the descent of `z_i` through the block.
* `HJO.Dyck.Tilde.Atilde.zElt_mul_dPlusPow_sub_mem_kernelIdealE0`: the two combined — `z_i` on a
  terminal raising block is unstarred modulo `I𝟏_0`.

## References

The lemma `HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`, on the kernel of the
extended action, with `HJO.Dyck.Tilde.Atilde`, `HJO.Dyck.Tilde.Atilde.kernelIdeal` and
`HJO.Dyck.Tilde.arrowDeg`; and E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J.
Amer. Math. Soc. **31** (2018) 661--697, Section 7.
-/

@[expose] public section

namespace HJO.Dyck.Tilde.Atilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### The unstarred generators are a corner family -/

theorem e_mul_commOf (n : ℕ) :
    e K q u (n + 1) * commOf (dPlus K q u) (dMinus K q u) n
      = commOf (dPlus K q u) (dMinus K q u) n := by
  rw [commOf, mul_sub, ← mul_assoc, ← mul_assoc, e_mul_dPlus, e_mul_dMinus]

theorem commOf_mul_e (n : ℕ) :
    commOf (dPlus K q u) (dMinus K q u) n * e K q u (n + 1)
      = commOf (dPlus K q u) (dMinus K q u) n := by
  rw [commOf, sub_mul, mul_assoc, mul_assoc, dMinus_mul_e, dPlus_mul_e]

/-- **The unstarred generators of `Ã` are a corner family**, the starred twin of
`HJO.Dyck.Tilde.Atilde.starFamily`; this is what gives `y_i` its idempotent absorptions inside `Ã`.
-/
theorem unstarredFamily :
    CornerFamily q ⅟q (e K q u) (dPlus K q u) (dMinus K q u) (Tg K q u) where
  e_mul_e := e_mul_self
  e_mul_T := e_mul_Tg
  T_mul_e := Tg_mul_e
  T_mul_Tinv _ _ h := Tg_mul_Tinv h
  e_mul_comm := e_mul_commOf
  comm_mul_e := commOf_mul_e

@[simp]
theorem e_mul_yElt (k i : ℕ) : e K q u k * yElt K q u k i = yElt K q u k i :=
  CornerFamily.e_mul_cornerOf (di := ⅟(q - 1)) unstarredFamily k i

@[simp]
theorem yElt_mul_e (k i : ℕ) : yElt K q u k i * e K q u k = yElt K q u k i :=
  CornerFamily.cornerOf_mul_e (di := ⅟(q - 1)) unstarredFamily k i

/-! ### `I𝟏_0` absorbs on the left -/

/-- An element of `I` fixed by `𝟏_0` on the right lies in `I𝟏_0`. -/
theorem mem_kernelIdealE0_of_mem {x : Atilde K q u} (hx : x ∈ kernelIdeal K q u)
    (hx0 : x * e K q u 0 = x) : x ∈ kernelIdealE0 K q u := by
  refine ⟨x, hx, ?_⟩
  simpa using hx0

/-- `I𝟏_0` is stable under left multiplication, `I` being a left ideal. -/
theorem mul_mem_kernelIdealE0 (a : Atilde K q u) {x : Atilde K q u}
    (hx : x ∈ kernelIdealE0 K q u) : a * x ∈ kernelIdealE0 K q u := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨a * y, Ideal.mul_mem_left _ _ hy, by simp [mul_assoc]⟩

theorem smul_mem_kernelIdealE0 (c : K) {x : Atilde K q u}
    (hx : x ∈ kernelIdealE0 K q u) : c • x ∈ kernelIdealE0 K q u :=
  Submodule.smul_mem _ c hx

/-! ### The starred arrow on a terminal raising block -/

/-- **The starred raising arrow retires against a terminal block of unstarred ones.** For every
`n ≥ 0`,

    `d₊^*d₊^{n}𝟏_0 - d₊^{n+1}𝟏_0 ∈ I𝟏_0`,

which is the `m`-th generator of `HJO.Dyck.Tilde.Atilde.kernelIdeal` read at the vertex `0` and
multiplied by `𝟏_0` on the right — an operation that costs nothing because both of its terms
already absorb `𝟏_0` there, by `HJO.Dyck.Tilde.Atilde.dPlusPow_mul_e`.

This is the only place in the lemma's proof where the generators of `I` are used, and the only shape
of raising block they reach: `I` is a *left* ideal, so nothing may be multiplied onto the right of
the generator, and a `d₊` block that is not terminal is out of reach. -/
theorem dPlusStar_mul_dPlusPow_sub_mem_kernelIdealE0 (n : ℕ) :
    dPlusStar K q u n * dPlusPow K q u 0 n - dPlusPow K q u 0 (n + 1)
      ∈ kernelIdealE0 K q u := by
  have hmem : dPlusStar K q u n * dPlusPow K q u 0 n - dPlusPow K q u 0 (n + 1)
      ∈ kernelIdeal K q u := by
    refine Ideal.subset_span ⟨0, n, ?_⟩
    rw [Nat.zero_add]
  refine mem_kernelIdealE0_of_mem hmem ?_
  rw [sub_mul, mul_assoc, dPlusPow_mul_e, dPlusPow_mul_e]

/-- The same, as an equation with an explicit error term in `I𝟏_0`. -/
theorem dPlusStar_mul_dPlusPow_eq (n : ℕ) :
    dPlusStar K q u n * dPlusPow K q u 0 n
      = dPlusPow K q u 0 (n + 1) +
        (dPlusStar K q u n * dPlusPow K q u 0 n - dPlusPow K q u 0 (n + 1)) := by
  abel

/-! ### The starred corner element on a terminal raising block -/

/-- **`z_i` descends through a terminal raising block.** For all `j, m ≥ 0`,

    `z_{j+1}𝟏_{m+1+j}·d₊^{m+1+j}𝟏_0 = -uq^{m+1}·d₊^{j}y_1𝟏_{m+1}d₊^*d₊^{m}𝟏_0`.

Induction on `j`. The step is the first mixed relation
`HJO.Dyck.Tilde.Atilde.mixed_z`, `z_{i+1}d₊ = d₊z_i`, which moves one arrow out of the block and
drops the corner index by one; it is applicable at every step because the index `j+1` never exceeds
the vertex `m+1+j`. The base case `j = 0` is the third mixed relation
`HJO.Dyck.Tilde.Atilde.mixed_top`, `z_1d₊ + uq^{k+1}y_1d₊^* = 0`, read at the vertex `k = m`.

The right-hand side is unstarred apart from the single `d₊^*` at its right end, which
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_dPlusPow_sub_mem_kernelIdealE0` retires; that is
`HJO.Dyck.Tilde.Atilde.zElt_mul_dPlusPow_sub_mem_kernelIdealE0`. -/
theorem zElt_mul_dPlusPow (m : ℕ) : ∀ j : ℕ,
    zElt K q u (m + 1 + j) (j + 1) * dPlusPow K q u 0 (m + 1 + j)
      = -(u * q ^ (m + 1)) •
          (dPlusPow K q u (m + 1) j *
            (yElt K q u (m + 1) 1 * (dPlusStar K q u m * dPlusPow K q u 0 m))) := by
  intro j
  induction j with
  | zero =>
    have hz : zElt K q u (m + 1) 1 * dPlus K q u m
        = (-(u * q ^ (m + 1))) • (yElt K q u (m + 1) 1 * dPlusStar K q u m) :=
      (eq_neg_of_add_eq_zero_left (mixed_top (K := K) (q := q) (u := u) m)).trans
        (neg_smul (u * q ^ (m + 1)) _).symm
    have hey : e K q u (m + 1) *
          (yElt K q u (m + 1) 1 * (dPlusStar K q u m * dPlusPow K q u 0 m))
        = yElt K q u (m + 1) 1 * (dPlusStar K q u m * dPlusPow K q u 0 m) :=
      (mul_assoc _ _ _).symm.trans
        (congrArg (fun t => t * (dPlusStar K q u m * dPlusPow K q u 0 m))
          (e_mul_yElt (m + 1) 1))
    calc zElt K q u (m + 1 + 0) (0 + 1) * dPlusPow K q u 0 (m + 1 + 0)
        = zElt K q u (m + 1) 1 * dPlus K q u m * dPlusPow K q u 0 m := by
          rw [Nat.add_zero, Nat.zero_add,
            show dPlusPow K q u 0 (m + 1) = dPlus K q u m * dPlusPow K q u 0 m from by
              rw [dPlusPow_succ, Nat.zero_add], ← mul_assoc]
      _ = (-(u * q ^ (m + 1))) • (yElt K q u (m + 1) 1 * dPlusStar K q u m)
            * dPlusPow K q u 0 m := by rw [hz]
      _ = (-(u * q ^ (m + 1))) • (yElt K q u (m + 1) 1 * dPlusStar K q u m
            * dPlusPow K q u 0 m) := smul_mul_assoc _ _ _
      _ = (-(u * q ^ (m + 1))) • (yElt K q u (m + 1) 1 *
            (dPlusStar K q u m * dPlusPow K q u 0 m)) := by rw [mul_assoc]
      _ = (-(u * q ^ (m + 1))) • (dPlusPow K q u (m + 1) 0 *
            (yElt K q u (m + 1) 1 * (dPlusStar K q u m * dPlusPow K q u 0 m))) :=
          congrArg (fun t => (-(u * q ^ (m + 1))) • t) hey.symm
  | succ j ih =>
    have hz : zElt K q u (m + 1 + j + 1) (j + 1 + 1) * dPlus K q u (m + 1 + j)
        = dPlus K q u (m + 1 + j) * zElt K q u (m + 1 + j) (j + 1) :=
      mixed_z (by omega) (by omega)
    rw [show m + 1 + (j + 1) = m + 1 + j + 1 from by omega,
      show dPlusPow K q u 0 (m + 1 + j + 1)
          = dPlus K q u (m + 1 + j) * dPlusPow K q u 0 (m + 1 + j) from by
        rw [dPlusPow_succ, Nat.zero_add], ← mul_assoc, hz, mul_assoc, ih,
      show dPlusPow K q u (m + 1) (j + 1)
          = dPlus K q u (m + 1 + j) * dPlusPow K q u (m + 1) j from dPlusPow_succ _ _,
      mul_smul_comm, mul_assoc]

/-- **`z_i` on a terminal raising block is unstarred modulo `I𝟏_0`.** For all `j, m ≥ 0`,

    `z_{j+1}𝟏_{m+1+j}·d₊^{m+1+j}𝟏_0 + uq^{m+1}·d₊^{j}y_1𝟏_{m+1}d₊^{m+1}𝟏_0 ∈ I𝟏_0`,

the second term being a word in the *unstarred* generators alone. This is the step of the proof of
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0` that places `z_kG`, in the case
its recursion bottoms out in — `G` a terminal block of
raising arrows. -/
theorem zElt_mul_dPlusPow_sub_mem_kernelIdealE0 (m j : ℕ) :
    zElt K q u (m + 1 + j) (j + 1) * dPlusPow K q u 0 (m + 1 + j)
        + (u * q ^ (m + 1)) •
            (dPlusPow K q u (m + 1) j *
              (yElt K q u (m + 1) 1 * dPlusPow K q u 0 (m + 1)))
      ∈ kernelIdealE0 K q u := by
  have h := smul_mem_kernelIdealE0 (-(u * q ^ (m + 1)))
    (mul_mem_kernelIdealE0 (dPlusPow K q u (m + 1) j)
      (mul_mem_kernelIdealE0 (yElt K q u (m + 1) 1)
        (dPlusStar_mul_dPlusPow_sub_mem_kernelIdealE0 (K := K) (q := q) (u := u) m)))
  have heq : -(u * q ^ (m + 1)) •
        (dPlusPow K q u (m + 1) j * (yElt K q u (m + 1) 1 *
          (dPlusStar K q u m * dPlusPow K q u 0 m - dPlusPow K q u 0 (m + 1))))
      = zElt K q u (m + 1 + j) (j + 1) * dPlusPow K q u 0 (m + 1 + j)
        + (u * q ^ (m + 1)) •
            (dPlusPow K q u (m + 1) j *
              (yElt K q u (m + 1) 1 * dPlusPow K q u 0 (m + 1))) := by
    rw [zElt_mul_dPlusPow m j, mul_sub, mul_sub, smul_sub, neg_smul, neg_smul, sub_neg_eq_add]
  exact heq ▸ h

end HJO.Dyck.Tilde.Atilde
