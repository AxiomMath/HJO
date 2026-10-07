/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ConjugationBottom
public meta import HJO.Attr

/-! # The zeroth summand of the conjugation operator exists

`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` says that a conjugation operator `𝒩` acts
on `Λ = V_0` as `f ↦ ε_±(∇(ω̄ f))`, so that map is the only candidate for the zeroth summand of any
`𝒩`. This file proves that the candidate has every property `HJO.Sweep.IsConjugationOperator` asks
of `𝒩` at `V_0`, and in particular that it is an **involution**.

## Why this is a check on `HJO.Sweep.exists_isConjugationOperator` and not only a lemma about `∇`

Involutivity of `ε_±∇ω̄` is a *consequence* of the existence of a conjugation operator: by
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` a conjugation operator restricted to the
zeroth summand is `ε_±∇ω̄`, and `HJO.Sweep.IsConjugationOperator` asks `𝒩𝒩 = id`. So had `ε_±∇ω̄`
failed to be an involution, `HJO.Sweep.exists_isConjugationOperator` would be **false** under the
hypotheses of `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` — a Macdonald conjugator
preserving the homogeneous components and fixing `1`, with `σ` an involution inverting `q` and `u`.
The check passes, and `HJO.Sweep.signGrading_conjugator_omegaBar_involutive` says so.

## The unstarred reachability, which is where the content sits

`HJO.Sym.eq_top_of_one_mem_of_closed` reaches all of `Λ` from `1` using multiplication by `e_1` and
`D^*_1`. The composite `ε_±∇ω̄` does *not* interact with `D^*_1` in any form available here.
What it has are

* `ε_±∇ω̄(e_1f) = -D_1(ε_±∇ω̄ f)`, and
* `ε_±∇ω̄(D_1f) = -e_1·ε_±∇ω̄ f`,

an exchange of multiplication by `e_1` with `D_1` — *unstarred*. Those two say at once that the
square of `ε_±∇ω̄` commutes with multiplication by `e_1` and with `D_1`, and fixes `1`; so what
closes the argument is reachability from `1` under `e_1·` and `D_1`, which is
`HJO.Sweep.eq_top_of_one_mem_of_closed_dop`. That is not a second reachability theorem: it is
`HJO.Sym.eq_top_of_one_mem_of_closed` read through `ω̄`, which is degree-preserving, exchanges `D_1`
with `D^*_1` (`HJO.Sym.omegaBar_dop`) and negates `e_1`. It deserves to be stated on its own.

## Main results

* `HJO.Sweep.omegaBar_dopStar`: `ω̄(D^*_kf) = D_k(ω̄ f)`, the converse direction of
  `HJO.Sym.omegaBar_dop`.
* `HJO.Sweep.eq_top_of_one_mem_of_closed_dop`: reachability from `1` under `e_1·` and `D_1`.
* `HJO.Sweep.signGrading_conjugator_omegaBar_involutive`: `ε_±∇ω̄` is an involution of `Λ`.
* `HJO.Sweep.exists_conjugation_vzero`: the zeroth summand of a conjugation operator exists — a
  `σ`-antilinear involution of `Λ` fixing `1` and satisfying the `V_0` instance of each
  intertwining clause of `HJO.Sweep.IsConjugationOperator`, written with the operators of `V_*`
  themselves.

## References

This file formalises the zeroth summand of the conjugation operator
`HJO.Sweep.IsConjugationOperator`, built from the Macdonald conjugator
`HJO.Sym.IsMacdonaldConjugator`, the sign grading `HJO.Sym.signGrading` and `HJO.Sym.omegaBar`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

/-! ### `ω̄` carries the starred operator back to the unstarred one -/

section OmegaBarDopStar

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}

/-- **`ω̄(D^*_kf) = D_k(ω̄f)`**, the direction `HJO.Sym.omegaBar_dop` does not state. `ω̄` is an
involution, so substituting `ω̄f` in `ω̄(D_kf) = D^*_k(ω̄f)` and applying `ω̄` once more turns the
one into the other. -/
theorem omegaBar_dopStar (hσ : ∀ c, σ (σ c) = c) (hq : σ q = q⁻¹) (hu : σ u = u⁻¹) (k : ℕ)
    (f : Lambda L) : omegaBar σ (DopStar q u k f) = Dop q u k (omegaBar σ f) := by
  have h := omegaBar_dop hq hu k (omegaBar σ f)
  rw [omegaBar_omegaBar hσ] at h
  rw [← h, omegaBar_omegaBar hσ]

end OmegaBarDopStar

/-! ### Reachability from the unit under `e_1·` and `D_1` -/

section ReachDop

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}

/-- **The unstarred `HJO.Sym.eq_top_of_one_mem_of_closed`**: the only `𝕜`-subspace of `Λ` that
contains `1`, is closed under multiplication by `e_1` and is closed under `D_1` is `Λ` itself.

This is `HJO.Sym.eq_top_of_one_mem_of_closed` conjugated by `ω̄`. The preimage `W' = {g : ω̄g ∈ W}`
is a `𝕜`-subspace because `ω̄` is antilinear over the bijection `σ`; it contains `1`, it is closed
under `e_1·` because `ω̄(e_1g) = -e_1ω̄g`, and it is closed under `D^*_1` because
`ω̄(D^*_1g) = D_1(ω̄g)`. So `HJO.Sym.eq_top_of_one_mem_of_closed` makes `W'` everything, and `W` is
everything because `ω̄` is an involution.

This deserves a statement of its own: the exchange relations available for the
composite of `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` are unstarred, so the
starred reachability cannot be applied to them directly. -/
theorem eq_top_of_one_mem_of_closed_dop (hσ : ∀ c, σ (σ c) = c) (hq : σ q = q⁻¹) (hu : σ u = u⁻¹)
    (hM : paramProduct q u ≠ 0) {W : Submodule L (Lambda L)} (hone : (1 : Lambda L) ∈ W)
    (helem : ∀ f ∈ W, elemSymm L 1 * f ∈ W) (hdop : ∀ f ∈ W, Dop q u 1 f ∈ W) : W = ⊤ := by
  set W' : Submodule L (Lambda L) :=
    { carrier := {g | omegaBar σ g ∈ W}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        exact map_add (omegaBar σ) a b ▸ Submodule.add_mem _ ha hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [omegaBar_smul]
        exact Submodule.smul_mem _ _ ha } with hW'
  have hmem : ∀ g : Lambda L, g ∈ W' ↔ omegaBar σ g ∈ W := fun _ => Iff.rfl
  have htop : W' = ⊤ := by
    refine eq_top_of_one_mem_of_closed hM ((hmem 1).2 ?_) (fun g hg => (hmem _).2 ?_)
      (fun g hg => (hmem _).2 ?_)
    · rw [map_one]; exact hone
    · rw [omegaBar_elemSymm_one_mul]
      exact Submodule.neg_mem _ (helem _ ((hmem g).1 hg))
    · rw [omegaBar_dopStar hσ hq hu]
      exact hdop _ ((hmem g).1 hg)
  refine top_unique fun f _ => ?_
  have h : omegaBar σ f ∈ W' := htop ▸ Submodule.mem_top
  rw [hmem, omegaBar_omegaBar hσ] at h
  exact h

end ReachDop

/-! ### The two clauses of `HJO.Sweep.IsConjugationOperator` that need nothing of `∇` -/

section Plain

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}
  {nabla : Module.End L (Lambda L)}

omit [Algebra ℚ L] in
/-- **`ε_±∇ω̄` fixes `1`.** `ω̄` and `ε_±` are ring maps and `∇` is asked to fix `1`. -/
theorem signGrading_conjugator_omegaBar_one (hone : nabla 1 = 1) :
    signGrading L (nabla (omegaBar σ (1 : Lambda L))) = 1 := by
  rw [map_one, hone, map_one]

omit [Algebra ℚ L] in
/-- **`ε_±∇ω̄` is antilinear over `σ`.** `ω̄` moves a scalar by `σ` and the other two factors are
`L`-linear. -/
theorem signGrading_conjugator_omegaBar_smul (c : L) (f : Lambda L) :
    signGrading L (nabla (omegaBar σ (c • f))) = σ c • signGrading L (nabla (omegaBar σ f)) := by
  rw [omegaBar_smul, map_smul, map_smul]

end Plain

/-! ### `ε_±∇ω̄` is an involution -/

section Involutive

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {σ : L ≃+* L}
  {nabla : Module.End L (Lambda L)} (hnabla : IsMacdonaldConjugator q u nabla)
  (hcomp : ∀ n : ℕ, ∀ f ∈ LambdaComp L n, nabla f ∈ LambdaComp L n)

include hnabla hcomp

/-- **`ε_±∇ω̄` turns multiplication by `e_1` into `-D_1`.** `ω̄` negates `e_1`, and `ε_±∇` turns
multiplication by `e_1` into `D_1`; the sign is `ω̄`'s. -/
theorem signGrading_conjugator_omegaBar_elemSymm_one_mul (f : Lambda L) :
    signGrading L (nabla (omegaBar σ (elemSymm L 1 * f)))
      = -Dop q u 1 (signGrading L (nabla (omegaBar σ f))) := by
  rw [omegaBar_elemSymm_one_mul, map_neg, map_neg,
    signGrading_conjugator_elemSymm_one_mul hnabla hcomp]

/-- **`ε_±∇ω̄` turns `D_1` into minus multiplication by `e_1`.** `ω̄` carries `D_1` to `D^*_1` by
`HJO.Sym.omegaBar_dop`, and `ε_±∇` carries `D^*_1` to minus multiplication by `e_1`. -/
theorem signGrading_conjugator_omegaBar_dop_one (hq : σ q = q⁻¹) (hu : σ u = u⁻¹) (f : Lambda L) :
    signGrading L (nabla (omegaBar σ (Dop q u 1 f)))
      = -(elemSymm L 1 * signGrading L (nabla (omegaBar σ f))) := by
  rw [omegaBar_dop hq hu, signGrading_conjugator_dopStar_one hnabla hcomp]

variable (hσ : ∀ c, σ (σ c) = c) (hq : σ q = q⁻¹) (hu : σ u = u⁻¹)
  (hM : paramProduct q u ≠ 0) (hone : nabla 1 = 1)

include hσ hq hu hM hone

/-- **`ε_±∇ω̄` is an involution of `Λ`.**

This is the clause `𝒩𝒩 = id` of `HJO.Sweep.IsConjugationOperator` at the zeroth summand, and by
`HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` it is a *necessary* condition for
`HJO.Sweep.exists_isConjugationOperator` under these hypotheses: had it failed, that statement would
be false.

The square `M∘M` of `M = ε_±∇ω̄` is `L`-linear, `M` being antilinear over the involution `σ`. It
fixes `1`. And it commutes with multiplication by `e_1` and with `D_1`, each by applying the two
exchange relations of `M` in turn, the two signs cancelling both times:

  `M(M(e_1f)) = M(-D_1(Mf)) = e_1M(M f)`,   `M(M(D_1f)) = M(-e_1·Mf) = D_1(M(M f))`.

So the fixed points of `M∘M` form a `𝕜`-subspace containing `1` and closed under `e_1·` and `D_1`,
which `HJO.Sweep.eq_top_of_one_mem_of_closed_dop` makes all of `Λ`. -/
theorem signGrading_conjugator_omegaBar_involutive (f : Lambda L) :
    signGrading L (nabla (omegaBar σ (signGrading L (nabla (omegaBar σ f))))) = f := by
  set M : Lambda L → Lambda L := fun g => signGrading L (nabla (omegaBar σ g)) with hMdef
  have hMadd : ∀ a b : Lambda L, M (a + b) = M a + M b := fun a b => by
    simp only [hMdef, map_add]
  have hMzero : M 0 = 0 := by simp only [hMdef, map_zero]
  have hMneg : ∀ a : Lambda L, M (-a) = -M a := fun a => by simp only [hMdef, map_neg]
  have hMsmul : ∀ (c : L) (g : Lambda L), M (c • g) = σ c • M g := fun c g =>
    signGrading_conjugator_omegaBar_smul c g
  have hMone : M 1 = 1 := signGrading_conjugator_omegaBar_one hone
  have hMe : ∀ g : Lambda L, M (elemSymm L 1 * g) = -Dop q u 1 (M g) :=
    signGrading_conjugator_omegaBar_elemSymm_one_mul hnabla hcomp
  have hMd : ∀ g : Lambda L, M (Dop q u 1 g) = -(elemSymm L 1 * M g) :=
    signGrading_conjugator_omegaBar_dop_one hnabla hcomp hq hu
  set W : Submodule L (Lambda L) :=
    { carrier := {g | M (M g) = g}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hMadd, hMadd, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, hMzero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [hMsmul, hMsmul, hσ, ha] } with hWdef
  have hmem : ∀ g : Lambda L, g ∈ W ↔ M (M g) = g := fun _ => Iff.rfl
  have htop : W = ⊤ := by
    refine eq_top_of_one_mem_of_closed_dop hσ hq hu hM ((hmem 1).2 ?_) (fun g hg => (hmem _).2 ?_)
      (fun g hg => (hmem _).2 ?_)
    · rw [hMone, hMone]
    · rw [hMe, hMneg, hMd, neg_neg, (hmem g).1 hg]
    · rw [hMd, hMneg, hMe, neg_neg, (hmem g).1 hg]
  exact (hmem f).1 (htop ▸ Submodule.mem_top)

/-- **The zeroth summand of a conjugation operator exists.** There is a `σ`-antilinear involution of
`Λ` fixing `1` which satisfies the `V_0` instance of each intertwining clause of
`HJO.Sweep.IsConjugationOperator`, in the form those clauses take there:
`HJO.Sweep.conj_vzero_elemSymm_one_mul` for `e_1 = d_-d_+` and `HJO.Sweep.conj_vzero_neg_dop_one`
for `-D_1 = d_-d^*_+`.

By `HJO.Sweep.conjugation_eq_signGrading_conjugator_omegaBar` this map is the *only* candidate for
`𝒩` on `V_0`, so this discharges the whole of `HJO.Sweep.exists_isConjugationOperator` at the zeroth
summand and leaves the summands `V_k` with `k ≥ 1`, where the letterwise relations no longer
determine the operator and the construction goes through the presentation of `Ã` instead —
see `HJO.Sweep.exists_isConjugationOperator_of_exists_action`. -/
theorem exists_conjugation_vzero :
    ∃ A : Lambda L →+ Lambda L,
      (∀ (c : L) (f : Lambda L), A (c • f) = σ c • A f)
      ∧ A 1 = 1
      ∧ (∀ f : Lambda L, A (A f) = f)
      ∧ (∀ f : Lambda L, vzero L (A (elemSymm L 1 * f))
          = dminusVstar q (dplusStarVstar q u (vzero L (A f))))
      ∧ ∀ f : Lambda L, vzero L (A (Dop q u 1 f))
          = -dminusVstar q (cmDPlusVstar q (vzero L (A f))) := by
  refine ⟨AddMonoidHom.mk' (fun g => signGrading L (nabla (omegaBar σ g)))
    (fun a b => by simp only [map_add]), fun c f => ?_, ?_, ?_, fun f => ?_, fun f => ?_⟩
  · exact signGrading_conjugator_omegaBar_smul c f
  · exact signGrading_conjugator_omegaBar_one hone
  · exact signGrading_conjugator_omegaBar_involutive hnabla hcomp hσ hq hu hM hone
  · change vzero L (signGrading L (nabla (omegaBar σ (elemSymm L 1 * f)))) = _
    rw [signGrading_conjugator_omegaBar_elemSymm_one_mul hnabla hcomp,
      ← dminusVstar_dplusStarVstar_vzero q u]
    rfl
  · change vzero L (signGrading L (nabla (omegaBar σ (Dop q u 1 f)))) = _
    rw [signGrading_conjugator_omegaBar_dop_one hnabla hcomp hq hu, map_neg,
      ← dminusVstar_cmDPlusVstar_vzero q]
    rfl

end Involutive

end HJO.Sweep
