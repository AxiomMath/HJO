/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCommute
public import HJO.Shuffle.DpaAction
public meta import HJO.Attr

/-! # Building an action out of the operators of an action already given

`HJO/CMStructure/DpaActionBuild.lean` builds an action of `𝔸_q` on `V_*` out of three families
of maps *between the graded pieces*. Mellit's replication
(`HJO.Sweep.exists_isDpaAction_replication`, `HJO.Sweep.exists_isDpaAction_replication_star`) builds
one out of the operators of an action already given: its braid and lowering operators are reused
unchanged and its raising operator is the old one multiplied by a loop. Those are endomorphisms of
the whole of `V_*`, not maps between pieces, so this file does the same construction with the three
families abstract endomorphisms of `V_*` and the nine incidence relations of `HJO.Dyck.Aq` as
hypotheses rather than as consequences of a sandwiching.

## Main definitions

* `HJO.Sweep.deltaRep` — the commutator `d₊d₋ - d₋d₊` of an abstract pair of arrow families.
* `HJO.Sweep.IsDpaRepOps` — the eighteen relations of `HJO.Dyck.Aq` for a triple of families of
  endomorphisms of `V_*`, the two vertex relations excepted: those hold for `HJO.Sweep.pieceProj`
  outright.
* `HJO.Sweep.IsReplicationData` — what the replication construction reads of the pair it starts
  from: an action `σ`, two families `Ξ, Ξ'` of loops standing for `y_1` and `y_2` in the *other*
  algebra, and the six identities relating them to `σ`'s generators.

## Main results

* `HJO.Sweep.IsDpaRepOps.exists_isDpaAction` — eighteen relations give an action.
* `HJO.Sweep.IsReplicationData.isDpaRepOps`, `HJO.Sweep.IsReplicationData.exists_isDpaAction` —
  the replication construction, at an arbitrary scalar: `T_i ↦ T_i`, `d_- ↦ d_-`,
  `d_+ ↦ c·Ξ_1d_+` is an action for every `c`.

## Implementation notes

**The construction is the one of `HJO.Sweep.IsDpaOperators.exists_isDpaAction`, with the incidence
relations moved into the hypotheses.** There the generators go to `ι_k ∘ (map) ∘ π_j` and the nine
path-algebra relations collapse to `π_kι_k = 1` and `π_kι_l = 0`. Here the operators are given, so
those nine are asserted; for the two vertex relations there is nothing to assert, the image of `𝟏_k`
being `HJO.Sweep.pieceProj` in both constructions.

**Every relation of `HJO.Dyck.Aq` in which only `T_i` and `d_-` occur is free.** The replicated
action sends those generators to the *same* operators as the action it is built from, so each such
relation
is the image under an algebra homomorphism of the corresponding relation of `𝔸_q`. That is why
`HJO.Sweep.IsReplicationData` says nothing about them: only the six identities involving the raising
operator and the loops `Ξ` are inputs.

**The scalar is arbitrary.** `HJO.Sweep.exists_isDpaAction_replication` writes the new raising
operator as `-(qu)^{-1}z_1d_+` and `u` is nowhere assumed invertible.
Every relation the construction has to check is homogeneous in the scalar — the two sides of each
carry the same power of it — so the construction goes through for an arbitrary `c` and the
invertibility of `u` is needed only to *name* the value. Both forms are proved.

**This is the construction shared by** `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star`, which are its two instances.

## References

A. Mellit, *Toric
braids and `(m, n)`-parking functions*, §3.2.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q]

/-- **The loop read back from its polynomial inverse**: `T_i = qT̂_i - (q-1)e_k`, which is
`HJO.Dyck.braidInvGen` solved for `T_i`. An operator commuting with the image of `T̂_i` and with the
image of `e_k` therefore commutes with the image of `T_i`, and conversely. -/
theorem Tg_eq_smul_Tinv_sub (k i : ℕ) :
    Tg K q k i = q • Tinv K q k i - (q - 1) • e K q k := by
  rw [Tinv_eq, smul_smul, mul_invOf_self, one_smul]
  abel

omit [Invertible q] in
/-- `HJO.Dyck.Aq.Delta` written out, at the index shape `HJO.Dyck.Aq`'s fourth relation reads. -/
theorem Delta_eq_sub (k : ℕ) :
    Delta K q k = dPlus K q k * dMinus K q k - dMinus K q (k + 1) * dPlus K q (k + 1) := rfl

omit [Invertible q] in
/-- `HJO.Dyck.Aq.Delta` one step up, with the second pair of indices written `k + 2`. -/
theorem Delta_succ_eq_sub (k : ℕ) :
    Delta K q (k + 1)
      = dPlus K q (k + 1) * dMinus K q (k + 1) - dMinus K q (k + 2) * dPlus K q (k + 2) := rfl

end HJO.Dyck.Aq

namespace HJO.Sweep

/-! ### The eighteen relations for a triple of families of endomorphisms -/

section Build

variable {L : Type*} [CommRing L] {q : L}

/-- **The commutator `d₊d₋ - d₋d₊` at the vertex `k + 1`** of an abstract pair of arrow families on
`V_*`, the element `HJO.Dyck.Aq`'s last two relations are written from. -/
noncomputable def deltaRep (Dv Uv : ℕ → Module.End L (Vstar L)) (k : ℕ) :
    Module.End L (Vstar L) :=
  Uv k * Dv k - Dv (k + 1) * Uv (k + 1)

/-! ### Distributivity over the pointwise difference

The `Sub` instance `Module.End L (Vstar L)` carries is `LinearMap.instSub`, the pointwise one, and
it is not syntactically the `Sub` of the ring structure; so `mul_sub`, `sub_mul` and `smul_sub` do
not rewrite in a goal about these endomorphisms even though they are true of them. These three are
the same statements proved pointwise, and they do rewrite. -/

theorem endMul_sub (x y z : Module.End L (Vstar L)) : x * (y - z) = x * y - x * z := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.mul_apply]

theorem endSub_mul (x y z : Module.End L (Vstar L)) : (y - z) * x = y * x - z * x := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.mul_apply]

theorem endSmul_sub (c : L) (y z : Module.End L (Vstar L)) : c • (y - z) = c • y - c • z := by
  refine LinearMap.ext fun v => ?_
  simp [smul_sub]

/-- **The relations of `HJO.Dyck.Aq` for a triple of families of endomorphisms of `V_*`**: the seven
incidence relations that are not automatic, the vanishing of the loops the quiver does not have, and
the nine relations of the presentation. The two vertex relations of `HJO.Dyck.Aq` are absent because
the image of `𝟏_k` is `HJO.Sweep.pieceProj`, for which they are `HJO.Sweep.pieceProj_mul_pieceProj`
and `HJO.Sweep.pieceProj_mul_pieceProj_of_ne`. -/
structure IsDpaRepOps (q : L) (Tv : ℕ → ℕ → Module.End L (Vstar L))
    (Dv Uv : ℕ → Module.End L (Vstar L)) : Prop where
  /-- `𝟏_kT = T`. -/
  proj_mul_loop : ∀ k i : ℕ, pieceProj L k * Tv k i = Tv k i
  /-- `T𝟏_k = T`. -/
  loop_mul_proj : ∀ k i : ℕ, Tv k i * pieceProj L k = Tv k i
  /-- `𝟏_kd₋ = d₋`. -/
  proj_mul_lower : ∀ k : ℕ, pieceProj L k * Dv k = Dv k
  /-- `d₋𝟏_{k+1} = d₋`. -/
  lower_mul_proj : ∀ k : ℕ, Dv k * pieceProj L (k + 1) = Dv k
  /-- `𝟏_{k+1}d₊ = d₊`. -/
  proj_mul_raise : ∀ k : ℕ, pieceProj L (k + 1) * Uv k = Uv k
  /-- `d₊𝟏_k = d₊`. -/
  raise_mul_proj : ∀ k : ℕ, Uv k * pieceProj L k = Uv k
  /-- The quiver has the loops `T_1, …, T_{k-1}` at the vertex `k` and no others. -/
  loop_eq_zero : ∀ {k i : ℕ}, k ≤ i + 1 → Tv k i = 0
  /-- The Hecke relation `(T_{i+1} - 1)(T_{i+1} + q) = 0`. -/
  quadratic : ∀ {k i : ℕ}, i + 2 ≤ k →
    (Tv k i - pieceProj L k) * (Tv k i + q • pieceProj L k) = 0
  /-- The braid relation. -/
  braid : ∀ {k i : ℕ}, i + 3 ≤ k →
    Tv k i * Tv k (i + 1) * Tv k i = Tv k (i + 1) * Tv k i * Tv k (i + 1)
  /-- Two distant loops commute. -/
  comm : ∀ {k i j : ℕ}, i + 2 ≤ k → j + 2 ≤ k → i + 1 < j → Tv k i * Tv k j = Tv k j * Tv k i
  /-- `T_{i+1}d₋ = d₋T_{i+1}`. -/
  loop_mul_lower : ∀ {m i : ℕ}, i + 2 ≤ m → Tv m i * Dv m = Dv m * Tv (m + 1) i
  /-- `d₋²T_{m+1} = d₋²`. -/
  lower_lower_mul_loop : ∀ m : ℕ, Dv m * Dv (m + 1) * Tv (m + 2) m = Dv m * Dv (m + 1)
  /-- `d₊T_{i+1} = T_{i+2}d₊`. -/
  raise_mul_loop : ∀ {k i : ℕ}, i + 2 ≤ k → Uv k * Tv k i = Tv (k + 1) (i + 1) * Uv k
  /-- `T_1d₊² = d₊²`. -/
  loop_mul_raise_raise : ∀ k : ℕ, Tv (k + 2) 0 * (Uv (k + 1) * Uv k) = Uv (k + 1) * Uv k
  /-- `d₋(d₊d₋ - d₋d₊)T_{j+1} = q(d₊d₋ - d₋d₊)d₋`. -/
  lower_mul_delta : ∀ j : ℕ,
    Dv (j + 1) * deltaRep Dv Uv (j + 1) * Tv (j + 2) j = q • (deltaRep Dv Uv j * Dv (j + 1))
  /-- `T_1(d₊d₋ - d₋d₊)d₊ = qd₊(d₊d₋ - d₋d₊)`. -/
  loop_mul_delta : ∀ m : ℕ,
    Tv (m + 2) 0 * deltaRep Dv Uv (m + 1) * Uv (m + 1) = q • (Uv (m + 1) * deltaRep Dv Uv m)

variable {Tv : ℕ → ℕ → Module.End L (Vstar L)} {Dv Uv : ℕ → Module.End L (Vstar L)}

/-- The assignment of the generators of `HJO.Dyck.Aq` to the given endomorphisms of `V_*`. -/
noncomputable def genOpRep (Tv : ℕ → ℕ → Module.End L (Vstar L))
    (Dv Uv : ℕ → Module.End L (Vstar L)) : Dyck.Gen → Module.End L (Vstar L)
  | Dyck.Gen.vertex k => pieceProj L k
  | Dyck.Gen.up k => Uv k
  | Dyck.Gen.down k => Dv k
  | Dyck.Gen.braid k i => Tv k i

/-- **The eighteen relations of `HJO.Dyck.Aq` hold for the assignment.** -/
theorem IsDpaRepOps.lift_genOpRep_rel (h : IsDpaRepOps q Tv Dv Uv)
    {x y : FreeAlgebra L Dyck.Gen} (hxy : Dyck.Rel L q x y) :
    FreeAlgebra.lift L (genOpRep Tv Dv Uv) x = FreeAlgebra.lift L (genOpRep Tv Dv Uv) y := by
  have hE : ∀ k : ℕ, FreeAlgebra.lift L (genOpRep Tv Dv Uv) (Dyck.freeE L k) = pieceProj L k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hU : ∀ k : ℕ, FreeAlgebra.lift L (genOpRep Tv Dv Uv) (Dyck.freeUp L k) = Uv k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hD : ∀ k : ℕ, FreeAlgebra.lift L (genOpRep Tv Dv Uv) (Dyck.freeDown L k) = Dv k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hT : ∀ k i : ℕ, FreeAlgebra.lift L (genOpRep Tv Dv Uv) (Dyck.freeT L k i) = Tv k i :=
    fun _ _ => FreeAlgebra.lift_ι_apply _ _
  have hDel : ∀ k : ℕ,
      FreeAlgebra.lift L (genOpRep Tv Dv Uv) (Dyck.freeDelta L k) = deltaRep Dv Uv k := by
    intro k
    rw [Dyck.freeDelta, map_sub, map_mul, map_mul, hU, hD, hD, hU, deltaRep]
  cases hxy with
  | vertex_mul_self k =>
      simp only [map_mul, hE]
      exact pieceProj_mul_pieceProj k
  | vertex_mul_vertex hkl =>
      simp only [map_mul, map_zero, hE]
      exact pieceProj_mul_pieceProj_of_ne (Ne.symm hkl)
  | vertex_mul_up k => simp only [map_mul, hE, hU]; exact h.proj_mul_raise k
  | up_mul_vertex k => simp only [map_mul, hE, hU]; exact h.raise_mul_proj k
  | vertex_mul_down k => simp only [map_mul, hE, hD]; exact h.proj_mul_lower k
  | down_mul_vertex k => simp only [map_mul, hE, hD]; exact h.lower_mul_proj k
  | vertex_mul_braid k i => simp only [map_mul, hE, hT]; exact h.proj_mul_loop k i
  | braid_mul_vertex k i => simp only [map_mul, hE, hT]; exact h.loop_mul_proj k i
  | braid_eq_zero hki => simp only [map_zero, hT]; exact h.loop_eq_zero hki
  | quadratic hik =>
      simp only [map_mul, map_sub, map_add, map_smul, map_zero, hE, hT]
      exact h.quadratic hik
  | braid_braid hik => simp only [map_mul, hT]; exact h.braid hik
  | braid_comm hi hj hij => simp only [map_mul, hT]; exact h.comm hi hj hij
  | braid_down him => simp only [map_mul, hD, hT]; exact h.loop_mul_lower him
  | up_braid hik => simp only [map_mul, hU, hT]; exact h.raise_mul_loop hik
  | braid_up_up k => simp only [map_mul, hU, hT]; exact h.loop_mul_raise_raise k
  | down_down_braid m => simp only [map_mul, hD, hT]; exact h.lower_lower_mul_loop m
  | down_delta => simp only [map_mul, map_smul, hD, hT, hDel]; exact h.lower_mul_delta _
  | braid_delta => simp only [map_mul, map_smul, hU, hT, hDel]; exact h.loop_mul_delta _

/-- **The action a triple of families of endomorphisms generates.** -/
noncomputable def IsDpaRepOps.actionOf (h : IsDpaRepOps q Tv Dv Uv) :
    Dyck.Aq L q →ₐ[L] Module.End L (Vstar L) :=
  RingQuot.liftAlgHom L
    ⟨FreeAlgebra.lift L (genOpRep Tv Dv Uv), fun _ _ hr => h.lift_genOpRep_rel hr⟩

@[simp]
theorem IsDpaRepOps.actionOf_mk (h : IsDpaRepOps q Tv Dv Uv) (x : FreeAlgebra L Dyck.Gen) :
    h.actionOf (Dyck.Aq.mk L q x) = FreeAlgebra.lift L (genOpRep Tv Dv Uv) x :=
  RingQuot.liftAlgHom_mkAlgHom_apply L (FreeAlgebra.lift L (genOpRep Tv Dv Uv))
    (s := Dyck.Rel L q) (fun _ _ hr => h.lift_genOpRep_rel hr) x

theorem IsDpaRepOps.actionOf_e (h : IsDpaRepOps q Tv Dv Uv) (k : ℕ) :
    h.actionOf (Dyck.Aq.e L q k) = pieceProj L k := by
  rw [Dyck.Aq.e, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

theorem IsDpaRepOps.actionOf_Tg (h : IsDpaRepOps q Tv Dv Uv) (k i : ℕ) :
    h.actionOf (Dyck.Aq.Tg L q k i) = Tv k i := by
  rw [Dyck.Aq.Tg, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

theorem IsDpaRepOps.actionOf_dMinus (h : IsDpaRepOps q Tv Dv Uv) (k : ℕ) :
    h.actionOf (Dyck.Aq.dMinus L q k) = Dv k := by
  rw [Dyck.Aq.dMinus, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

theorem IsDpaRepOps.actionOf_dPlus (h : IsDpaRepOps q Tv Dv Uv) (k : ℕ) :
    h.actionOf (Dyck.Aq.dPlus L q k) = Uv k := by
  rw [Dyck.Aq.dPlus, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

theorem IsDpaRepOps.isDpaAction (h : IsDpaRepOps q Tv Dv Uv) : IsDpaAction q h.actionOf :=
  ⟨h.actionOf_e⟩

/-- **Eighteen relations give an action.** -/
theorem IsDpaRepOps.exists_isDpaAction (h : IsDpaRepOps q Tv Dv Uv) :
    ∃ ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = Tv k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = Dv k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = Uv k) :=
  ⟨h.actionOf, h.isDpaAction, h.actionOf_Tg, h.actionOf_dMinus, h.actionOf_dPlus⟩

end Build

/-! ### The replication construction -/

section Replication

variable {L : Type*} [CommRing L] {a : L}
  {σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)} {Ξ Ξ' : ℕ → Module.End L (Vstar L)}

/-- **What the replication construction reads of the pair it starts from.** `σ` is an action of
`𝔸_a` on `V_*` and `Ξ_k, Ξ'_k` stand for the images of the loops `y_1, y_2` at the vertex `k` under
the *other* action of the intertwined pair — `z_1, z_2` in
`HJO.Sweep.exists_isDpaAction_replication` and `y_1, y_2` in
`HJO.Sweep.exists_isDpaAction_replication_star`. The identities are the ones both proofs use: the
raising generator of `σ` moves `Ξ` up to `Ξ'`, the lowering generator moves each of them down, `Ξ_k`
commutes with every loop of `σ` above the first, and `Ξ_kΞ'_k` commutes with the first. -/
structure IsReplicationData (a : L) (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L))
    (Ξ Ξ' : ℕ → Module.End L (Vstar L)) : Prop where
  /-- `σ` is an action in the sense of `HJO.Sweep.IsDpaAction`. -/
  map_e : ∀ k : ℕ, σ (Dyck.Aq.e L a k) = pieceProj L k
  /-- `Ξ_k` is a loop at the vertex `k`, absorbed by the projection on the left. -/
  proj_mul_loopVar : ∀ k : ℕ, pieceProj L k * Ξ k = Ξ k
  /-- `d₊Ξ_k = Ξ'_{k+1}d₊`, the raising generator moving the first loop up to the second. -/
  raise_mul_loopVar : ∀ k : ℕ, 1 ≤ k →
    σ (Dyck.Aq.dPlus L a k) * Ξ k = Ξ' (k + 1) * σ (Dyck.Aq.dPlus L a k)
  /-- `d₋Ξ_{m+1} = Ξ_md₋`. -/
  lower_mul_loopVar : ∀ m : ℕ, 1 ≤ m →
    σ (Dyck.Aq.dMinus L a m) * Ξ (m + 1) = Ξ m * σ (Dyck.Aq.dMinus L a m)
  /-- `d₋Ξ'_{m+1} = Ξ'_md₋`. -/
  lower_mul_loopVar' : ∀ m : ℕ, 2 ≤ m →
    σ (Dyck.Aq.dMinus L a m) * Ξ' (m + 1) = Ξ' m * σ (Dyck.Aq.dMinus L a m)
  /-- `Ξ_kT_{s+1} = T_{s+1}Ξ_k` for `1 ≤ s`, the loops `Ξ` does not touch. -/
  loopVar_mul_loop : ∀ k s : ℕ, 1 ≤ s → s + 2 ≤ k →
    Ξ k * σ (Dyck.Aq.Tg L a k s) = σ (Dyck.Aq.Tg L a k s) * Ξ k
  /-- `Ξ_kΞ'_kT_1 = T_1Ξ_kΞ'_k`: the first loop commutes with the *product* of the two. -/
  loopVar_pair_mul_loop : ∀ k : ℕ, 2 ≤ k →
    Ξ k * Ξ' k * σ (Dyck.Aq.Tg L a k 0) = σ (Dyck.Aq.Tg L a k 0) * (Ξ k * Ξ' k)

/-- The braid family of the replicated action: the old one. -/
noncomputable def repLoop (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)) (k i : ℕ) :
    Module.End L (Vstar L) :=
  σ (Dyck.Aq.Tg L a k i)

/-- The lowering family of the replicated action: the old one. -/
noncomputable def repLower (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)) (k : ℕ) :
    Module.End L (Vstar L) :=
  σ (Dyck.Aq.dMinus L a k)

/-- The raising family of the replicated action: `c·Ξ_1d₊`. -/
noncomputable def repRaise (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L))
    (Ξ : ℕ → Module.End L (Vstar L)) (c : L) (k : ℕ) : Module.End L (Vstar L) :=
  c • (Ξ (k + 1) * σ (Dyck.Aq.dPlus L a k))

theorem repLoop_apply (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)) (k i : ℕ) :
    repLoop σ k i = σ (Dyck.Aq.Tg L a k i) := rfl

theorem repLower_apply (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L)) (k : ℕ) :
    repLower σ k = σ (Dyck.Aq.dMinus L a k) := rfl

theorem repRaise_apply (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L))
    (Ξ : ℕ → Module.End L (Vstar L)) (c : L) (k : ℕ) :
    repRaise σ Ξ c k = c • (Ξ (k + 1) * σ (Dyck.Aq.dPlus L a k)) := rfl

/-- `HJO.Sweep.repRaise` one step up, with the index of the loop written `k + 2`. -/
theorem repRaise_succ (σ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L))
    (Ξ : ℕ → Module.End L (Vstar L)) (c : L) (k : ℕ) :
    repRaise σ Ξ c (k + 1) = c • (Ξ (k + 2) * σ (Dyck.Aq.dPlus L a (k + 1))) := rfl

namespace IsReplicationData

variable (h : IsReplicationData a σ Ξ Ξ') (c : L)

include h

/-! #### The identities, at the index shapes the relations read -/

theorem raise_mul_loopVar_succ (k : ℕ) :
    σ (Dyck.Aq.dPlus L a (k + 1)) * Ξ (k + 1) = Ξ' (k + 2) * σ (Dyck.Aq.dPlus L a (k + 1)) :=
  h.raise_mul_loopVar (k + 1) (by omega)

theorem raise_mul_loopVar_succ_succ (k : ℕ) :
    σ (Dyck.Aq.dPlus L a (k + 2)) * Ξ (k + 2) = Ξ' (k + 3) * σ (Dyck.Aq.dPlus L a (k + 2)) :=
  h.raise_mul_loopVar (k + 2) (by omega)

theorem lower_mul_loopVar_succ (k : ℕ) :
    σ (Dyck.Aq.dMinus L a (k + 1)) * Ξ (k + 2) = Ξ (k + 1) * σ (Dyck.Aq.dMinus L a (k + 1)) :=
  h.lower_mul_loopVar (k + 1) (by omega)

theorem lower_mul_loopVar'_succ (k : ℕ) :
    σ (Dyck.Aq.dMinus L a (k + 2)) * Ξ' (k + 3) = Ξ' (k + 2) * σ (Dyck.Aq.dMinus L a (k + 2)) :=
  h.lower_mul_loopVar' (k + 2) (by omega)

/-! #### The commutator of the replicated operators -/

/-- **The commutator of the replicated operators is `c·Ξ_1` times the old one.** -/
theorem deltaRep_eq (k : ℕ) :
    deltaRep (repLower σ) (repRaise σ Ξ c) k = c • (Ξ (k + 1) * σ (Dyck.Aq.Delta L a k)) := by
  have hA : repRaise σ Ξ c k * repLower σ k
      = c • (Ξ (k + 1) * (σ (Dyck.Aq.dPlus L a k) * σ (Dyck.Aq.dMinus L a k))) := by
    rw [repRaise_apply, repLower_apply, smul_mul_assoc, mul_assoc]
  have hB : repLower σ (k + 1) * repRaise σ Ξ c (k + 1)
      = c • (Ξ (k + 1)
          * (σ (Dyck.Aq.dMinus L a (k + 1)) * σ (Dyck.Aq.dPlus L a (k + 1)))) := by
    rw [repLower_apply, repRaise_succ, mul_smul_comm, ← mul_assoc, h.lower_mul_loopVar_succ k,
      mul_assoc]
  rw [Dyck.Aq.Delta_eq_sub, map_sub, map_mul, map_mul, endMul_sub, endSmul_sub, deltaRep, hA, hB]

/-- `HJO.Sweep.IsReplicationData.deltaRep_eq` one step up, with the index of the loop written
`k + 2`. -/
theorem deltaRep_eq_succ (k : ℕ) :
    deltaRep (repLower σ) (repRaise σ Ξ c) (k + 1)
      = c • (Ξ (k + 2) * σ (Dyck.Aq.Delta L a (k + 1))) :=
  h.deltaRep_eq c (k + 1)

/-- **The two replicated raising operators compose to `c²Ξ_1Ξ_2` times the old composite.** -/
theorem repRaise_mul_repRaise (k : ℕ) :
    repRaise σ Ξ c (k + 1) * repRaise σ Ξ c k
      = (c * c) • (Ξ (k + 2) * Ξ' (k + 2)
          * σ (Dyck.Aq.dPlus L a (k + 1) * Dyck.Aq.dPlus L a k)) := by
  rw [repRaise_succ, repRaise_apply, smul_mul_assoc, mul_smul_comm, smul_smul, map_mul]
  congr 1
  rw [mul_assoc (Ξ (k + 2)), ← mul_assoc (σ (Dyck.Aq.dPlus L a (k + 1))),
    h.raise_mul_loopVar_succ k]
  simp only [mul_assoc]

/-- **The old commutator conjugates `Ξ_1` to `Ξ_2`**, the relation "the commutator
`d_+d_- - d_-d_+` conjugates `y_1` to `y_2`". -/
theorem delta_mul_loopVar (m : ℕ) :
    σ (Dyck.Aq.Delta L a (m + 1)) * Ξ (m + 2)
      = Ξ' (m + 2) * σ (Dyck.Aq.Delta L a (m + 1)) := by
  have h1 : σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.dMinus L a (m + 1)) * Ξ (m + 2)
      = Ξ' (m + 2) * (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.dMinus L a (m + 1))) := by
    rw [mul_assoc, h.lower_mul_loopVar_succ m, ← mul_assoc, h.raise_mul_loopVar_succ m, mul_assoc]
  have h2 : σ (Dyck.Aq.dMinus L a (m + 2)) * σ (Dyck.Aq.dPlus L a (m + 2)) * Ξ (m + 2)
      = Ξ' (m + 2) * (σ (Dyck.Aq.dMinus L a (m + 2)) * σ (Dyck.Aq.dPlus L a (m + 2))) := by
    rw [mul_assoc, h.raise_mul_loopVar_succ_succ m, ← mul_assoc, h.lower_mul_loopVar'_succ m,
      mul_assoc]
  rw [Dyck.Aq.Delta_succ_eq_sub, map_sub, map_mul, map_mul, endSub_mul, endMul_sub, h1, h2]

/-! #### The eighteen relations -/

/-- **The replicated operators satisfy the relations of `HJO.Dyck.Aq`.** -/
theorem isDpaRepOps : IsDpaRepOps a (repLoop σ) (repLower σ) (repRaise σ Ξ c) where
  proj_mul_loop k i := by
    rw [repLoop_apply, ← h.map_e, ← map_mul, Dyck.Aq.e_mul_Tg]
  loop_mul_proj k i := by
    rw [repLoop_apply, ← h.map_e, ← map_mul, Dyck.Aq.Tg_mul_e]
  proj_mul_lower k := by
    rw [repLower_apply, ← h.map_e, ← map_mul, Dyck.Aq.e_mul_dMinus]
  lower_mul_proj k := by
    rw [repLower_apply, ← h.map_e, ← map_mul, Dyck.Aq.dMinus_mul_e]
  proj_mul_raise k := by
    rw [repRaise_apply, mul_smul_comm, ← mul_assoc, h.proj_mul_loopVar (k + 1)]
  raise_mul_proj k := by
    rw [repRaise_apply, smul_mul_assoc, mul_assoc, ← h.map_e, ← map_mul, Dyck.Aq.dPlus_mul_e]
  loop_eq_zero hki := by
    rw [repLoop_apply, Dyck.Aq.Tg_eq_zero hki, map_zero]
  quadratic hik := by
    simp only [repLoop_apply, ← h.map_e, ← map_smul σ, ← map_sub σ, ← map_add σ, ← map_mul σ]
    rw [Dyck.Aq.quadratic hik, map_zero]
  braid hik := by
    simp only [repLoop_apply, ← map_mul σ]
    rw [Dyck.Aq.braid_braid hik]
  comm hi hj hij := by
    simp only [repLoop_apply, ← map_mul σ]
    rw [Dyck.Aq.Tg_comm hi hj hij]
  loop_mul_lower him := by
    simp only [repLoop_apply, repLower_apply, ← map_mul σ]
    rw [Dyck.Aq.Tg_mul_dMinus him]
  lower_lower_mul_loop m := by
    simp only [repLower_apply, repLoop_apply, ← map_mul σ]
    rw [Dyck.Aq.dMinus_dMinus_mul_Tg]
  raise_mul_loop {k i} hik := by
    rw [repRaise_apply, repLoop_apply, repLoop_apply, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [mul_assoc, ← map_mul, Dyck.Aq.dPlus_mul_Tg hik, map_mul, ← mul_assoc,
      h.loopVar_mul_loop (k + 1) (i + 1) (by omega) (by omega)]
    simp only [mul_assoc]
  loop_mul_raise_raise k := by
    rw [h.repRaise_mul_repRaise c k, repLoop_apply, mul_smul_comm]
    congr 1
    rw [← mul_assoc, ← h.loopVar_pair_mul_loop (k + 2) (by omega),
      mul_assoc (Ξ (k + 2) * Ξ' (k + 2)), ← map_mul, Dyck.Aq.Tg_mul_dPlus_dPlus]
  lower_mul_delta j := by
    have hkey : σ (Dyck.Aq.dMinus L a (j + 1))
          * (σ (Dyck.Aq.Delta L a (j + 1)) * σ (Dyck.Aq.Tg L a (j + 2) j))
        = a • (σ (Dyck.Aq.Delta L a j) * σ (Dyck.Aq.dMinus L a (j + 1))) := by
      rw [← mul_assoc, ← map_mul σ, ← map_mul σ, Dyck.Aq.dMinus_mul_Delta, map_smul σ, map_mul σ]
    have hmain : σ (Dyck.Aq.dMinus L a (j + 1)) * (Ξ (j + 2) * σ (Dyck.Aq.Delta L a (j + 1)))
          * σ (Dyck.Aq.Tg L a (j + 2) j)
        = a • (Ξ (j + 1) * σ (Dyck.Aq.Delta L a j) * σ (Dyck.Aq.dMinus L a (j + 1))) := by
      rw [← mul_assoc, h.lower_mul_loopVar_succ j,
        mul_assoc (Ξ (j + 1) * σ (Dyck.Aq.dMinus L a (j + 1))), mul_assoc (Ξ (j + 1)), hkey,
        mul_smul_comm, ← mul_assoc]
    rw [h.deltaRep_eq_succ c j, h.deltaRep_eq c j, repLower_apply, repLoop_apply,
      mul_smul_comm, smul_mul_assoc, hmain, smul_smul, smul_mul_assoc, smul_smul, mul_comm c a]
  loop_mul_delta m := by
    have hkey : σ (Dyck.Aq.Tg L a (m + 2) 0)
          * σ (Dyck.Aq.Delta L a (m + 1)) * σ (Dyck.Aq.dPlus L a (m + 1))
        = a • (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.Delta L a m)) := by
      rw [← map_mul σ, ← map_mul σ, Dyck.Aq.Tg_mul_Delta, map_smul σ, map_mul σ]
    have hLinner : σ (Dyck.Aq.Tg L a (m + 2) 0) * (Ξ (m + 2) * σ (Dyck.Aq.Delta L a (m + 1)))
          * (Ξ (m + 2) * σ (Dyck.Aq.dPlus L a (m + 1)))
        = a • (Ξ (m + 2) * Ξ' (m + 2)
            * (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.Delta L a m))) := by
      rw [← mul_assoc, ← mul_assoc,
        mul_assoc (σ (Dyck.Aq.Tg L a (m + 2) 0) * Ξ (m + 2)) (σ (Dyck.Aq.Delta L a (m + 1)))
          (Ξ (m + 2)),
        h.delta_mul_loopVar m, ← mul_assoc,
        mul_assoc (σ (Dyck.Aq.Tg L a (m + 2) 0)) (Ξ (m + 2)) (Ξ' (m + 2)),
        ← h.loopVar_pair_mul_loop (m + 2) (by omega),
        mul_assoc (Ξ (m + 2) * Ξ' (m + 2)) (σ (Dyck.Aq.Tg L a (m + 2) 0))
          (σ (Dyck.Aq.Delta L a (m + 1))),
        mul_assoc (Ξ (m + 2) * Ξ' (m + 2))
          (σ (Dyck.Aq.Tg L a (m + 2) 0) * σ (Dyck.Aq.Delta L a (m + 1)))
          (σ (Dyck.Aq.dPlus L a (m + 1))),
        hkey, mul_smul_comm]
    have hRinner : Ξ (m + 2) * σ (Dyck.Aq.dPlus L a (m + 1))
          * (Ξ (m + 1) * σ (Dyck.Aq.Delta L a m))
        = Ξ (m + 2) * Ξ' (m + 2)
            * (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.Delta L a m)) := by
      rw [← mul_assoc,
        mul_assoc (Ξ (m + 2)) (σ (Dyck.Aq.dPlus L a (m + 1))) (Ξ (m + 1)),
        h.raise_mul_loopVar_succ m,
        ← mul_assoc (Ξ (m + 2)) (Ξ' (m + 2)) (σ (Dyck.Aq.dPlus L a (m + 1))),
        mul_assoc (Ξ (m + 2) * Ξ' (m + 2)) (σ (Dyck.Aq.dPlus L a (m + 1)))
          (σ (Dyck.Aq.Delta L a m))]
    have hL : repLoop σ (m + 2) 0 * deltaRep (repLower σ) (repRaise σ Ξ c) (m + 1)
          * repRaise σ Ξ c (m + 1)
        = (c * c * a) • (Ξ (m + 2) * Ξ' (m + 2)
            * (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.Delta L a m))) := by
      rw [h.deltaRep_eq_succ c m, repLoop_apply, repRaise_succ, mul_smul_comm, mul_smul_comm,
        smul_mul_assoc, smul_smul, hLinner, smul_smul]
    have hR : a • (repRaise σ Ξ c (m + 1) * deltaRep (repLower σ) (repRaise σ Ξ c) m)
        = (c * c * a) • (Ξ (m + 2) * Ξ' (m + 2)
            * (σ (Dyck.Aq.dPlus L a (m + 1)) * σ (Dyck.Aq.Delta L a m))) := by
      rw [h.deltaRep_eq c m, repRaise_succ, smul_mul_assoc, mul_smul_comm, smul_smul, hRinner,
        smul_smul, show a * c * c = c * c * a from by ring]
    rw [hL, hR]

/-- **The replication construction**: the braid and lowering operators of `σ` together with
`c·Ξ_1d₊` generate an action of `𝔸_a` on `V_*`, for every scalar `c`. -/
theorem exists_isDpaAction :
    ∃ ρ₁ : Dyck.Aq L a →ₐ[L] Module.End L (Vstar L), IsDpaAction a ρ₁
      ∧ (∀ k i : ℕ, ρ₁ (Dyck.Aq.Tg L a k i) = σ (Dyck.Aq.Tg L a k i))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dMinus L a k) = σ (Dyck.Aq.dMinus L a k))
      ∧ (∀ k : ℕ, ρ₁ (Dyck.Aq.dPlus L a k)
          = c • (Ξ (k + 1) * σ (Dyck.Aq.dPlus L a k))) :=
  (h.isDpaRepOps c).exists_isDpaAction

end IsReplicationData

end Replication

end HJO.Sweep

end
