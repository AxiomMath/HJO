/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.Thm52Injective
public import HJO.Shuffle.MellitConjIntertwine
public meta import HJO.Attr

/-! # The kernel of `Ãe_0 → V_*`, and the existence of a conjugation operator

Let `ρ` be an action of the extended Dyck path algebra `Ã` on `V_*` in which the idempotents, the
loops, the lowering and both raising arrows act by the operators of Carlsson and Mellit. Composing
with the algebra map `𝔸_q → Ã` gives an action of `𝔸_q`, and on `𝔸_q𝟏_0` the map
`fe_0 ↦ f(1)` of `Ã𝟏_0` restricts to the evaluation map of `HJO.Sweep.exists_linearEquiv_e0Ideal`.
That theorem — the evaluation `𝔸_q𝟏_0 → V_*` is a linear isomorphism — therefore supplies the two
facts about `Ã𝟏_0 → V_*` that the algebra alone cannot:

* it is **surjective**, already on the image of `𝔸_q𝟏_0`;
* it is **injective on the image of `𝔸_q𝟏_0`**, so that, combined with the algebra-level exhaustion
  `Ã𝟏_0 = 𝔸_q𝟏_0 + I𝟏_0` and the containment `I𝟏_0 ⊆ ker`, its kernel on `Ã𝟏_0` is exactly
  `I𝟏_0`.

From these the four results below follow: the map descends to a surjection
`Ã𝟏_0/I𝟏_0 → V_*` restricting to the isomorphism of `HJO.Sweep.exists_linearEquiv_e0Ideal`; the
kernel is `I𝟏_0`; the operators define an action of `Ã` with that kernel (Carlsson and Mellit's
Theorem 7.3); and the transport of a star swap of `Ã` along the resulting isomorphism
`Ã𝟏_0/I𝟏_0 ≅ V_*` is a conjugation operator (the existence half of their Theorem 7.4).

## Main results

* `HJO.Sweep.aqE0_inf_ker_evalOne_eq_bot`: the map is injective on the image of `𝔸_q𝟏_0`.
* `HJO.Sweep.exists_mem_atildeE0_evalOne_eq`: the map is surjective from `Ã𝟏_0`.
* `HJO.Sweep.exists_quotient_linearMap_evalOne`: the map descends to a surjection from
  `Ã𝟏_0/I𝟏_0`.
* `HJO.Sweep.atildeE0_inf_ker_evalOne_eq`: the kernel on `Ã𝟏_0` is `I𝟏_0`; over `ℚ(q, u)` this is
  `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`.
* `HJO.Sweep.exists_action_atilde_ker_eq`: Carlsson and Mellit's Theorem 7.3; over `ℚ(q, u)` this
  is `HJO.Standing.exists_action_atilde_ker_eq_param`.
* `HJO.Sweep.exists_isConjugationOperator`: a conjugation operator exists.

## Implementation notes

**The kernel statements carry the bar of `HJO.Sym.paramInvLambda`.** The exhaustion
`Ã𝟏_0 = 𝔸_q𝟏_0 + I𝟏_0` moves `d^*_+` past the corner elements by star-swapped images of
`𝔸_q`-identities, so it is proved for coefficients carrying a ring involution inverting `q` and `u`,
with `u` invertible; the same hypothesis appears at
`HJO.Dyck.Tilde.Atilde.dPlusStar_mul_mem_aqE0_sup_kernelIdealE0`. The coefficient field `ℚ(q, u)`
carries it, `q ↦ q⁻¹`, `u ↦ u⁻¹`, and the statements over that field with no hypothesis are
`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` and
`HJO.Standing.exists_action_atilde_ker_eq_param`. The surjectivity and descent of
`HJO.Sweep.exists_quotient_linearMap_evalOne` do not use it.

**The conjugation operator carries all seven clauses of `HJO.Sweep.IsConjugationOperator`.** The
structure `HJO.Sweep.IsConjugationOperator` records the summand clause (`𝒩` preserves each
`V_k`) and the loop clause (`𝒩T_i = T̂_i𝒩`, with `T̂_i = q^{-1}(T_i + (q-1))` the polynomial
inverse) as fields `map_piece` and `map_loop`. `HJO.Sweep.exists_isConjugationOperator` also
returns the two clauses beside the structure, redundantly; both follow from the full intertwining
`𝒩ρ(x) = ρ(σx)𝒩`, `x ∈ Ã`, which the transport satisfies outright.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Theorems 5.2, 7.3 and 7.4. -/

@[expose] public section

namespace HJO.Sweep

/-! ### The action of `𝔸_q` underlying an action of `Ã` -/

section Restrict

variable {L : Type*} [Field L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))

/-- The map `fe_0 ↦ f(1)` of `Ã` reads, on the image of `𝔸_q`, as the evaluation map of the
restricted action. -/
theorem evalOne_toTilde (x : Dyck.Aq L q) :
    evalOne ρ (Dyck.toTilde L q u x) = evalOneAq (ρ.comp (Dyck.toTilde L q u)) x := rfl

/-- The image of `𝔸_q𝟏_0` lies in `Ã𝟏_0`. -/
theorem toTilde_mem_atildeE0 {x : Dyck.Aq L q} (hx : x ∈ Dyck.Aq.e0Ideal L q) :
    Dyck.toTilde L q u x ∈ Dyck.Tilde.Atilde.atildeE0 L q u := by
  obtain ⟨y, rfl⟩ := Dyck.Aq.mem_e0Ideal_iff.1 hx
  exact ⟨Dyck.toTilde L q u y, by
    rw [Dyck.Tilde.Atilde.rightE0_apply, map_mul, Dyck.toTilde_e]⟩

/-- The submodule `aqE0` is the image of `𝔸_q𝟏_0`. -/
theorem mem_aqE0_iff {x : Dyck.Tilde.Atilde L q u} :
    x ∈ Dyck.Tilde.Atilde.aqE0 L q u ↔
      ∃ y ∈ Dyck.Aq.e0Ideal L q, Dyck.toTilde L q u y = x := by
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a * Dyck.Aq.e L q 0, ⟨a, rfl⟩, ?_⟩
    rw [map_mul, Dyck.toTilde_e]
    rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := Dyck.Aq.mem_e0Ideal_iff.1 hy
    exact ⟨Dyck.toTilde L q u a, ⟨a, rfl⟩, by
      rw [Dyck.Tilde.Atilde.rightE0_apply, map_mul, Dyck.toTilde_e]⟩

variable (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)

include hρe in
/-- The restriction of an action of `Ã` along `𝔸_q → Ã` is an action of `𝔸_q`. -/
theorem isDpaAction_comp_toTilde : IsDpaAction q (ρ.comp (Dyck.toTilde L q u)) :=
  ⟨fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_e, hρe]⟩

end Restrict

/-! ### Injectivity on `𝔸_q𝟏_0` and surjectivity, from `HJO.Sweep.exists_linearEquiv_e0Ideal` -/

section Thm52

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
  (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hρT : ∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
  (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
  (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)

include hρe hρT hρd hρup

/-- **`HJO.Sweep.exists_linearEquiv_e0Ideal` for the restricted action**: the evaluation map of
`𝔸_q𝟏_0` through `ρ` is an isomorphism onto `V_*` with the properties of
`HJO.Sweep.exists_linearEquiv_e0Ideal`. -/
theorem exists_linearEquiv_e0Ideal_comp_toTilde :
    ∃ f : Dyck.Aq.e0Ideal L q ≃ₗ[L] Vstar L,
      (∀ x : Dyck.Aq.e0Ideal L q,
        f x = evalOneAq (ρ.comp (Dyck.toTilde L q u)) (x : Dyck.Aq L q)) ∧
      (∀ (a : Dyck.Aq L q) (x : Dyck.Aq.e0Ideal L q),
        f ⟨a * (x : Dyck.Aq L q), Dyck.Aq.mul_mem_e0Ideal a x.2⟩
          = (ρ.comp (Dyck.toTilde L q u)) a (f x)) ∧
      f ⟨Dyck.Aq.e L q 0, Dyck.Aq.e_zero_mem_e0Ideal⟩ = oneVstar L ∧
      ∀ k : ℕ, Submodule.map (f : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L)
          ((Dyck.Aq.cornerE0 L q k).comap (Dyck.Aq.e0Ideal L q).subtype)
        = LinearMap.range (ofPiece L k) :=
  exists_linearEquiv_e0Ideal (isDpaAction_comp_toTilde ρ hρe)
    (fun k i => by rw [AlgHom.comp_apply, Dyck.toTilde_Tg, hρT])
    (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dMinus, hρd])
    (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dPlus, hρup])

/-- **The map `fe_0 ↦ f(1)` is injective on the image of `𝔸_q𝟏_0`**, by the injectivity half of
`HJO.Sweep.exists_linearEquiv_e0Ideal`. -/
theorem aqE0_inf_ker_evalOne_eq_bot :
    Dyck.Tilde.Atilde.aqE0 L q u ⊓ LinearMap.ker (evalOne ρ) = ⊥ := by
  refine eq_bot_iff.2 fun x ⟨hx, hx0⟩ => ?_
  obtain ⟨y, hy, rfl⟩ := mem_aqE0_iff.1 hx
  have hx0' : evalOneAq (ρ.comp (Dyck.toTilde L q u)) y = 0 := hx0
  rw [Submodule.mem_bot,
    evalOneAq_injOn_e0Ideal (isDpaAction_comp_toTilde ρ hρe)
      (fun k i => by rw [AlgHom.comp_apply, Dyck.toTilde_Tg, hρT])
      (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dMinus, hρd])
      (fun k => by rw [AlgHom.comp_apply, Dyck.toTilde_dPlus, hρup]) y hy hx0', map_zero]

/-- **The map `fe_0 ↦ f(1)` is surjective from `Ã𝟏_0`**, already from the image of `𝔸_q𝟏_0`, by
the surjectivity half of `HJO.Sweep.exists_linearEquiv_e0Ideal`. -/
theorem exists_mem_atildeE0_evalOne_eq (F : Vstar L) :
    ∃ x ∈ Dyck.Tilde.Atilde.atildeE0 L q u, evalOne ρ x = F := by
  obtain ⟨f, hf, -⟩ := exists_linearEquiv_e0Ideal_comp_toTilde ρ hρe hρT hρd hρup
  obtain ⟨y, rfl⟩ := f.surjective F
  exact ⟨Dyck.toTilde L q u y, toTilde_mem_atildeE0 y.2, by rw [evalOne_toTilde, hf]⟩

end Thm52

/-! ### `HJO.Sweep.exists_quotient_linearMap_evalOne` -/

section Surjective

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
  (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
  (hρT : ∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
  (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
  (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
  (hρupStar : ∀ k : ℕ,
    ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k)

include hρe hρT hρd hρup hρupStar

/-- **The extended module map is surjective and descends.** The map
`Ã𝟏_0 → V_*`, `fe_0 ↦ f(1)`, induces a surjective linear map `φ` from `Ã𝟏_0/I𝟏_0` to `V_*`, and
composing `φ` with `𝔸_q𝟏_0 → Ã𝟏_0/I𝟏_0` gives the isomorphism `f` of
`HJO.Sweep.exists_linearEquiv_e0Ideal`.

The quotient is taken of `Ã𝟏_0` by `I𝟏_0` read inside it. The map descends because `I𝟏_0` lies in
the kernel (`HJO.Sweep.kernelIdealE0_le_ker`), and it is surjective because its restriction to
`𝔸_q𝟏_0` is (`HJO.Sweep.exists_mem_atildeE0_evalOne_eq`). -/
@[hjo "lem_cm_kernel_surjective"]
theorem exists_quotient_linearMap_evalOne :
    ∃ φ : (Dyck.Tilde.Atilde.atildeE0 L q u ⧸
        (Dyck.Tilde.Atilde.kernelIdealE0 L q u).comap
          (Dyck.Tilde.Atilde.atildeE0 L q u).subtype) →ₗ[L] Vstar L,
      Function.Surjective φ ∧
      (∀ x : Dyck.Tilde.Atilde.atildeE0 L q u, φ (Submodule.Quotient.mk x) = evalOne ρ x) ∧
      ∃ f : Dyck.Aq.e0Ideal L q ≃ₗ[L] Vstar L,
        (∀ x : Dyck.Aq.e0Ideal L q,
          f x = evalOneAq (ρ.comp (Dyck.toTilde L q u)) (x : Dyck.Aq L q)) ∧
        (∀ (a : Dyck.Aq L q) (x : Dyck.Aq.e0Ideal L q),
          f ⟨a * (x : Dyck.Aq L q), Dyck.Aq.mul_mem_e0Ideal a x.2⟩
            = (ρ.comp (Dyck.toTilde L q u)) a (f x)) ∧
        f ⟨Dyck.Aq.e L q 0, Dyck.Aq.e_zero_mem_e0Ideal⟩ = oneVstar L ∧
        (∀ k : ℕ, Submodule.map (f : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L)
            ((Dyck.Aq.cornerE0 L q k).comap (Dyck.Aq.e0Ideal L q).subtype)
          = LinearMap.range (ofPiece L k)) ∧
        ∀ x : Dyck.Aq.e0Ideal L q,
          φ (Submodule.Quotient.mk ⟨Dyck.toTilde L q u x, toTilde_mem_atildeE0 x.2⟩) = f x := by
  let ev : Dyck.Tilde.Atilde.atildeE0 L q u →ₗ[L] Vstar L :=
    (evalOne ρ).comp (Dyck.Tilde.Atilde.atildeE0 L q u).subtype
  obtain ⟨f, hf, hfmul, hfone, hfk⟩ := exists_linearEquiv_e0Ideal_comp_toTilde ρ hρe hρT hρd hρup
  refine ⟨Submodule.liftQ _ ev fun x hx => kernelIdealE0_le_ker ρ hρe hρup hρupStar hx,
    fun F => ?_, fun x => rfl, f, hf, hfmul, hfone, hfk, fun x => (hf x).symm⟩
  obtain ⟨x, hx, rfl⟩ := exists_mem_atildeE0_evalOne_eq ρ hρe hρT hρd hρup F
  exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

end Surjective

/-! ### `HJO.Standing.atildeE0_inf_ker_evalOne_eq_param` and
`HJO.Standing.exists_action_atilde_ker_eq_param` -/

section Exact

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  [Invertible u] {bar : L ≃+* L} (hbar : bar q = ⅟q) (hbaru : bar u = ⅟u)
  (hbb : ∀ c : L, bar (bar c) = c)

include hbar hbaru hbb

/-- **`HJO.Standing.atildeE0_inf_ker_evalOne_eq_param`: the kernel of `Ãe_0 → V_*` is `Ie_0`.** For
every action of `Ã` on `V_*` by the operators of Carlsson and Mellit, the kernel of `fe_0 ↦ f(1)` on
`Ã𝟏_0` is `I𝟏_0`.

The hypothesis of `HJO.Sweep.atildeE0_inf_ker_eq_kernelIdealE0` — injectivity on the image of
`𝔸_q𝟏_0` — is `HJO.Sweep.aqE0_inf_ker_evalOne_eq_bot`, from `HJO.Sweep.exists_linearEquiv_e0Ideal`.
The bar is `HJO.Sym.paramInvLambda`, which the exhaustion `Ã𝟏_0 = 𝔸_q𝟏_0 + I𝟏_0` uses; see the
implementation notes. -/
theorem atildeE0_inf_ker_evalOne_eq
    (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
    (hρe : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
    (hρT : ∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
    (hρd : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
    (hρup : ∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
    (hρupStar : ∀ k : ℕ,
      ρ (Dyck.Tilde.Atilde.dPlusStar L q u k) = raiseVstar (dplusStarPiece q u) k) :
    Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
      = Dyck.Tilde.Atilde.kernelIdealE0 L q u :=
  atildeE0_inf_ker_eq_kernelIdealE0 ρ hρe hρup hρupStar hbar hbaru hbb (by
    rw [aqE0_inf_ker_evalOne_eq_bot ρ hρe hρT hρd hρup]
    exact bot_le)

/-- **`HJO.Standing.exists_action_atilde_ker_eq_param`: Carlsson and Mellit's Theorem 7.3.** The
operators `T_i`, `d_-`, `d_+`, `d^*_+` and the projections onto the summands define an action of `Ã`
on `V_*`, and the kernel of `Ãe_0 → V_*`, `fe_0 ↦ f(1)`, is `Ie_0`.

The action is `HJO.Sweep.exists_action_atilde`, whose `q + 1 ≠ 0` it inherits; the kernel is
`HJO.Sweep.atildeE0_inf_ker_evalOne_eq`. -/
theorem exists_action_atilde_ker_eq (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k)
      ∧ Dyck.Tilde.Atilde.atildeE0 L q u ⊓ LinearMap.ker (evalOne ρ)
          = Dyck.Tilde.Atilde.kernelIdealE0 L q u := by
  obtain ⟨ρ, hρe, hρT, hρd, hρup, hρupStar⟩ := exists_action_atilde q u hq1
  exact ⟨ρ, hρe, hρT, hρd, hρup, hρupStar,
    atildeE0_inf_ker_evalOne_eq hbar hbaru hbb ρ hρe hρT hρd hρup hρupStar⟩

end Exact

/-! ### `HJO.Sweep.exists_isConjugationOperator` -/

section Conjugation

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} [Invertible q] [Invertible (q - 1)]
  [Invertible u] {bar : L ≃+* L}

/-- **A conjugation operator realising a star swap.** There are an action `ρ` of `Ã` on `V_*` by
the operators of Carlsson and Mellit, a star swap `σ` of `Ã` and a conjugation operator `𝒩` with
`𝒩(ρ(x)F) = ρ(σx)(𝒩F)` for every `x ∈ Ã` and `F ∈ V_*`.

`𝒩` is the transport of `σ` along `Ã𝟏_0/I𝟏_0 ≅ V_*`, which is
`HJO.Sweep.exists_quotient_linearMap_evalOne` together with
`HJO.Sweep.exists_action_atilde_ker_eq`. -/
theorem exists_isConjugationOperator_intertwines (hq1 : q + 1 ≠ 0) (hbar : bar q = ⅟q)
    (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c) :
    ∃ (ρ : Dyck.Tilde.Atilde L q u →ₐ[L] Module.End L (Vstar L))
      (σA : Dyck.Tilde.Atilde L q u →+ Dyck.Tilde.Atilde L q u) (N : Vstar L →+ Vstar L),
      (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.e L q u k) = pieceProj L k)
      ∧ (∀ k i : ℕ, ρ (Dyck.Tilde.Atilde.Tg L q u k i) = loopVstar (braidModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dMinus L q u k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlus L q u k) = raiseVstar (cmDPlusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Tilde.Atilde.dPlusStar L q u k)
          = raiseVstar (dplusStarPiece q u) k)
      ∧ Dyck.IsStarSwap q bar (Dyck.Tilde.Atilde.e L q u) (Dyck.Tilde.Atilde.dPlus L q u)
          (Dyck.Tilde.Atilde.dPlusStar L q u) (Dyck.Tilde.Atilde.dMinus L q u)
          (Dyck.Tilde.Atilde.Tg L q u) σA
      ∧ IsConjugationOperator q u bar N
      ∧ ∀ (x : Dyck.Tilde.Atilde L q u) (F : Vstar L), N (ρ x F) = ρ (σA x) (N F) := by
  obtain ⟨ρ, hρe, hρT, hρd, hρup, hρupStar, hker⟩ :=
    exists_action_atilde_ker_eq hbar hbaru hbb hq1
  obtain ⟨σA, h⟩ := Dyck.Tilde.Atilde.exists_isStarSwap hbar hbaru hbb
  obtain ⟨N, hsmul, hinv, hone, hint⟩ := exists_conj_intertwines_of_evalOne ρ hρe hρup hρupStar h
    (exists_mem_atildeE0_evalOne_eq ρ hρe hρT hρd hρup) hker.le
  exact ⟨ρ, σA, N, hρe, hρT, hρd, hρup, hρupStar, h,
    isConjugationOperator_of_intertwines hint hρe h.map_e hρd hρup hρupStar h.map_dMinus
      h.map_dPlus hρT h.map_T hsmul hinv hone, hint⟩

/-- **A conjugation operator exists**, for a bar as in `HJO.Sym.paramInvLambda`
and `q`, `q - 1`, `q + 1`, `u` invertible. The seven clauses of `HJO.Sweep.IsConjugationOperator`
are the fields of `HJO.Sweep.IsConjugationOperator`; the statement also returns two of them beside
the structure, redundantly: the operator preserves each summand `V_k`, and it carries each loop
`T_i` on `V_k` (`k ≥ 2`, `1 ≤ i ≤ k - 1`, written `i + 2 ≤ k` in the shifted indexing of the loops)
to its polynomial inverse `T̂_i = q^{-1}(T_i + (q - 1))`. -/
@[hjo "lem_cm_conjugation_exists"]
theorem exists_isConjugationOperator (hq1 : q + 1 ≠ 0) (hbar : bar q = ⅟q)
    (hbaru : bar u = ⅟u) (hbb : ∀ c : L, bar (bar c) = c) :
    ∃ N : Vstar L →+ Vstar L, IsConjugationOperator q u bar N
      ∧ (∀ (k : ℕ) (F : Vstar L), N (pieceProj L k F) = pieceProj L k (N F))
      ∧ ∀ {k i : ℕ}, i + 2 ≤ k → ∀ F : Vstar L,
          N (loopVstar (braidModPiece q) k i F)
            = ⅟q • (loopVstar (braidModPiece q) k i (N F) + (q - 1) • pieceProj L k (N F)) := by
  obtain ⟨ρ, σA, N, hρe, hρT, -, -, -, h, hN, hint⟩ :=
    exists_isConjugationOperator_intertwines hq1 hbar hbaru hbb
  refine ⟨N, hN, pieceProj_comm_of_intertwines hint hρe h.map_e, fun {k i} hik F => ?_⟩
  have := hint (Dyck.Tilde.Atilde.Tg L q u k i) F
  rwa [h.map_T hik, hρT, Dyck.tinvOf, map_smul, map_add, map_smul, hρT, hρe] at this

end Conjugation

end HJO.Sweep

end
