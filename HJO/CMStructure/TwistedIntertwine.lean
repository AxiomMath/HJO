/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AlphabetShift
public import HJO.CMStructure.TwistedAction
public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.CMRaising
public import HJO.Shuffle.MellitShiftGenerators
public meta import HJO.Attr

/-! # The two operators intertwine the twisted action, and the starred family of twists

Three results. The raising and the lowering operator of the Dyck path algebra both commute
past the twisted action `∗_k` of `HJO.Sweep.twistedAction`, changing only the rank of the twist; and
the family `∗_m`, `0 ≤ m ≤ k`, of `HJO.Sweep.twistedMult` twists by the alphabet with the first `m`
letters dilated by `u`.

## Main definitions

* `HJO.Sweep.twistPowerSums`, `HJO.Sweep.twistedMult`, `HJO.Sweep.twistedActionMult`: the power
  sums of the twisting alphabet, the substitution `σ_{m,k}` and the multiplication `f ∗_m G` built
  from it.

## Main results

* `HJO.Sweep.cmDPlus_twistedAction`, `d_+(tw_k(F)G) = tw_{k+1}(F)d_+G`.
* `HJO.Sweep.dminusCM_twistedAction`,
  `d_-(tw_k(F)G) = tw_{k-1}(F)d_-G`.
* `HJO.Sweep.twistedMult_C`: the remark that `∗_0` is the `∗_k` of `HJO.Sweep.twistedAction`.

## Implementation notes

**Both intertwining lemmas are one displacement identity plus one linearity.** The substitution
`τ_{k+1,k+1}` carries `tw_k(F)` to `tw_{k+1}(F)` and `τ^-_{k+1,k+1}` carries `tw_{k+1}(F)` back to
`tw_k(F)` — `HJO.Sweep.qshift_twist` and `HJO.Sweep.qshiftNeg_twist`, each a comparison of two
`𝕜`-algebra homomorphisms out of `Λ` on the power sums, where the extra letter `y_{k+1}` is added to
or cancelled from the sum `∑_{i≤k}y_i^r`. After that, `d_+` is the braid word `T_{[1,k]}` after the
substitution, and the word passes `tw_{k+1}(F)` because that element is symmetric in `y_1, …, y_k`
(`HJO.Sweep.swapAux_twist`); `d_-` is the coefficient extraction after the substitution, and the
extraction passes `tw_{k-1}(F)` because that element is free of `y_k`
(`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`).

**`G ∈ V_k` is not used in either.** Both are usually stated for `G ∈ V_k`; the arguments above
never read the support of `G`, so both are stated for every `G` of the total space. That is a
generalisation, and it is what the
one-total-space convention of `HJO.Shuffle.SweepModule` makes visible: the domain
is a membership statement about the operators, not a hypothesis of these identities.

**`σ_{m,k}` is `Γ₊` at an explicit letter family.** `HJO.Sweep.twistedMult` describes `σ_{m,k}` as
the endomorphism of `V_k` adding the virtual alphabet `(q-1)(u∑_{i≤m}y_i + ∑_{i>m}y_i)`, which is
exactly `HJO.Sweep.alphabetShift` at the family
`P r = (q^r-1)(u^r∑_{i≤m}y_i^r + ∑_{i>m}y_i^r)`. So no second substitution is built: the scalar
attached to `p_r` is `q^r - 1` and `u^r`, the virtual reading of the letters recorded on
`HJO.Sweep.qshift`, and under the monomial reading `(q-1)^r`, `u` the relations of the layer are
false. `HJO.Sweep.twistedMult_C` is the consistency check that `∗_0` restricted to
`Λ` is the twist of `HJO.Sweep.twist`.

## References

Lemmas `HJO.Sweep.cmDPlus_twistedAction` and `HJO.Sweep.dminusCM_twistedAction`, and definition
`HJO.Sweep.twistedMult`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### A transposition fixes the twist -/

section Symmetry

variable {L : Type*} [Field L]

/-- `s_i` sends `y_m` to `y_{σ m}` for the transposition `σ = (i, i+1)` of the `1`-based
indices. The three cases are the two letters interchanged and the rest. -/
theorem swapAux_auxVar_swap {i m : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) :
    swapAux L i (auxVar m : Total L) = auxVar (Equiv.swap i (i + 1) m) := by
  rcases eq_or_ne m i with rfl | h1
  · rw [swapAux_auxVar_self hi, Equiv.swap_apply_left]
  rcases eq_or_ne m (i + 1) with rfl | h2
  · rw [Equiv.swap_apply_right, auxVar, Nat.add_sub_cancel, swapAux_X, Equiv.swap_apply_right,
      auxVar]
  · rw [swapAux_auxVar_of_ne hm h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **`s_i` fixes the power sum `y_1^r + ⋯ + y_k^r`** for `1 ≤ i ≤ k - 1`: it permutes the two
summands it touches, both of which are in range. -/
theorem swapAux_sum_auxVar_pow {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (r : ℕ) :
    swapAux L i (∑ m ∈ Finset.Icc 1 k, (auxVar m : Total L) ^ r)
      = ∑ m ∈ Finset.Icc 1 k, (auxVar m : Total L) ^ r := by
  rw [map_sum]
  refine Finset.sum_equiv (Equiv.swap i (i + 1)) (fun m => ?_) (fun m hm => ?_)
  · rcases eq_or_ne m i with rfl | h1
    · rw [Equiv.swap_apply_left]
      simp only [Finset.mem_Icc]
      omega
    rcases eq_or_ne m (i + 1) with rfl | h2
    · rw [Equiv.swap_apply_right]
      simp only [Finset.mem_Icc]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    rw [map_pow, swapAux_auxVar_swap hi hm1]

/-- **`s_i` fixes `tw_k(F)`** for `1 ≤ i ≤ k - 1`: the twist is a polynomial in the power sums of
`Λ` and in the symmetric sums `y_1^r + ⋯ + y_k^r`, and `s_i` fixes each of those. This is what lets
the braid word of `d_+` pass the twist. -/
theorem swapAux_twist (q : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Sym.Lambda L) :
    swapAux L i (twist L q k F) = twist L q k F := by
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : A.comp (twist L q k) = twist L q k := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, twist_X, hAapp, map_add, map_mul, swapAux_C, swapAux_C,
      swapAux_sum_auxVar_pow hi hik]
  exact (hAapp (twist L q k F)).symm.trans
    (congrArg (fun f : Sym.Lambda L →ₐ[L] Total L => f F) key)

end Symmetry

/-! ### The substitutions move the rank of the twist -/

section Rank

variable {L : Type*} [Field L]

/-- **`τ_{k+1,k+1}` raises the rank of the twist**: `τ_{k+1,k+1}(tw_k(F)) = tw_{k+1}(F)`. Both sides
are images of `F` under `𝕜`-algebra homomorphisms out of `Λ`, and on `p_r` the substitution adds the
letter `(q-1)y_{k+1}` that is missing from the sum `∑_{i≤k}y_i^r`. -/
theorem qshift_twist (q : L) (k : ℕ) (F : Sym.Lambda L) :
    qshift q (k + 1) (twist L q k F) = twist L q (k + 1) F := by
  have key : (qshift q (k + 1)).comp (twist L q k) = twist L q (k + 1) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, twist_X, twist_X, map_add, map_mul, map_sum,
      show (MvPolynomial.C (MvPolynomial.C (q ^ (j + 1) - 1)) : Total L)
        = scal (q ^ (j + 1) - 1) from rfl,
      qshift_powerSum, qshift_scal,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)
        (fun m => (auxVar m : Total L) ^ (j + 1))]
    rw [Finset.sum_congr rfl (fun m _ => by rw [map_pow, qshift_auxVar_apply] :
      ∀ m ∈ Finset.Icc 1 k, qshift q (k + 1) ((auxVar m : Total L) ^ (j + 1))
        = (auxVar m : Total L) ^ (j + 1))]
    ring
  exact congrArg (fun f : Sym.Lambda L →ₐ[L] Total L => f F) key

/-- **`τ^-_{k+1,k+1}` lowers the rank of the twist**: `τ^-_{k+1,k+1}(tw_{k+1}(F)) = tw_k(F)`. The
substitution subtracts exactly the letter `(q-1)y_{k+1}` that the sum `∑_{i≤k+1}y_i^r` has over
`∑_{i≤k}y_i^r`. -/
theorem qshiftNeg_twist (q : L) (k : ℕ) (F : Sym.Lambda L) :
    qshiftNeg q (k + 1) (twist L q (k + 1) F) = twist L q k F := by
  have key : (qshiftNeg q (k + 1)).comp (twist L q (k + 1)) = twist L q k := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, twist_X, twist_X, map_add, map_mul, map_sum,
      show (MvPolynomial.C (MvPolynomial.C (q ^ (j + 1) - 1)) : Total L)
        = scal (q ^ (j + 1) - 1) from rfl,
      qshiftNeg_powerSum, qshiftNeg_scal,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)
        (fun m => qshiftNeg q (k + 1) ((auxVar m : Total L) ^ (j + 1)))]
    rw [Finset.sum_congr rfl (fun m _ => by rw [map_pow, qshiftNeg_auxVar_apply] :
      ∀ m ∈ Finset.Icc 1 k, qshiftNeg q (k + 1) ((auxVar m : Total L) ^ (j + 1))
        = (auxVar m : Total L) ^ (j + 1)), map_pow, qshiftNeg_auxVar_apply]
    ring
  exact congrArg (fun f : Sym.Lambda L →ₐ[L] Total L => f F) key

end Rank

/-! ### The two intertwining lemmas -/

section Intertwine

variable {L : Type*} [Field L]

/-- **The raising operator intertwines the twisted action.**
`d_+(tw_k(F)G) = tw_{k+1}(F)d_+G`.

`d_+` is `T_{[1,k]}` after `τ_{k+1,k+1}`. The substitution raises the rank of the twist
(`HJO.Sweep.qshift_twist`), and the braid word passes the raised twist because that element is
symmetric in `y_1, …, y_{k+1}`, in particular in each adjacent pair `y_j, y_{j+1}` with `j ≤ k`
(`HJO.Sweep.swapAux_twist`).

The `G ∈ V_k` is not used: nothing above reads the support of `G`. -/
@[hjo "lem_cm_twisted_dplus"]
theorem cmDPlus_twistedAction (q : L) (k : ℕ) (F : Sym.Lambda L) (G : Total L) :
    cmDPlus q k (twistedAction L q k F G) = twistedAction L q (k + 1) F (cmDPlus q k G) := by
  rw [twistedAction, twistedAction, cmDPlus_apply, cmDPlus_apply, map_mul, qshift_twist,
    cmAscWord_mul_of_swapAux_eq q (by omega : 1 ≤ k + 1)
      (fun j hj1 hjk => swapAux_twist q hj1 (by omega) F)]

variable [Algebra ℚ L]

/-- **The lowering operator intertwines the twisted action.**
`d_-(tw_k(F)G) = tw_{k-1}(F)d_-G`, read at `k + 1` so that no truncated subtraction occurs.

`d_-` is the coefficient extraction of `HJO.Sweep.dminusCM` after `τ^-_{k+1,k+1}`. The substitution
lowers the rank of the twist (`HJO.Sweep.qshiftNeg_twist`), and the extraction passes the twist
because `tw_k(F)` lies in `V_k`, hence is free of `y_{k+1}`
(`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`).

As for the raising operator, the `G ∈ V_{k+1}` is not used. -/
@[hjo "lem_cm_twisted_dminus"]
theorem dminusCM_twistedAction (q : L) (k : ℕ) (F : Sym.Lambda L) (G : Total L) :
    dminusCM q (k + 1) (twistedAction L q (k + 1) F G)
      = twistedAction L q k F (dminusCM q (k + 1) G) := by
  rw [twistedAction, twistedAction, dminusCM_succ_apply, dminusCM_succ_apply, map_mul,
    qshiftNeg_twist, lowerCoeffShift_mul_of_mem_piece (twist_mem_piece q k F)]

end Intertwine

/-! ### The starred family of twisted multiplications -/

section Mult

variable {L : Type*} [Field L]

/-- The power sums of the virtual alphabet `(q-1)(u∑_{i≤m}y_i + ∑_{i>m}y_i)` of
`HJO.Sweep.twistedMult`: `P r = (q^r-1)(u^r∑_{i≤m}y_i^r + ∑_{i>m}y_i^r)`.

The scalars are `q^r - 1` and `u^r`, the virtual reading of the letters `(q-1)y_i` and `uy_i` that
`HJO.Sweep.qshift` records: under the monomial reading `(q-1)^r` the relations of the layer are
false. -/
noncomputable def twistPowerSums (q u : L) (m k : ℕ) (r : ℕ) : Total L :=
  scal (q ^ r - 1) *
    (scal (u ^ r) * ∑ i ∈ Finset.Icc 1 m, (auxVar i : Total L) ^ r
      + ∑ i ∈ Finset.Icc (m + 1) k, (auxVar i : Total L) ^ r)

/-- Each power sum of the twisting alphabet is free of the alphabet `X`: it is a polynomial in the
auxiliary variables. This is the hypothesis `HJO.Sweep.alphabetShift_neg_alphabetShift` reads, so
the substitution below is invertible. -/
theorem twistPowerSums_mem_auxSubalg (q u : L) (m k r : ℕ) :
    twistPowerSums q u m k r ∈ auxSubalg L := by
  refine mul_mem ((auxSubalg L).algebraMap_mem _) (add_mem (mul_mem
    ((auxSubalg L).algebraMap_mem _) (sum_mem fun i _ => pow_mem (auxVar_mem_auxSubalg i) r))
    (sum_mem fun i _ => pow_mem (auxVar_mem_auxSubalg i) r))

/-- Each power sum of the twisting alphabet lies in `V_k`, provided `m ≤ k`: every letter it reads
is one of `y_1, …, y_k`. This is what makes the substitution an endomorphism of `V_k`. -/
theorem twistPowerSums_mem_piece (q u : L) {m k : ℕ} (hmk : m ≤ k) (r : ℕ) :
    twistPowerSums q u m k r ∈ piece L k := by
  refine mul_mem (Subalgebra.algebraMap_mem _ _) (add_mem (mul_mem
    (Subalgebra.algebraMap_mem _ _) (sum_mem fun i hi => ?_)) (sum_mem fun i hi => ?_))
  · rw [Finset.mem_Icc] at hi
    exact pow_mem (auxVar_mem_piece hi.1 (by omega)) r
  · rw [Finset.mem_Icc] at hi
    exact pow_mem (auxVar_mem_piece (by omega) hi.2) r

/-- **The substitution `σ_{m,k}` of `HJO.Sweep.twistedMult`**: the `𝕜`-algebra endomorphism of `V_k`
adding the virtual alphabet `(q-1)(u∑_{i≤m}y_i + ∑_{i>m}y_i)`, so that
`σ_{m,k}(p_r) = p_r + (q^r-1)(u^r∑_{i≤m}y_i^r + ∑_{i>m}y_i^r)`.

It is `HJO.Sweep.alphabetShift` of `HJO.Sweep.alphabetShift` at the family
`HJO.Sweep.twistPowerSums`, and not a second substitution: adding a virtual alphabet is determined
by its power sums, which is what that constant takes. `HJO.Sweep.twistedMult_mem_piece` is the
codomain `V_k`. -/
@[hjo "def_cm_twisted_mult"]
noncomputable def twistedMult (q u : L) (m k : ℕ) : Total L →ₐ[L] Total L :=
  alphabetShift (twistPowerSums q u m k)

/-- **The defining property of `σ_{m,k}`**: it adds `(q^r-1)(u^r∑_{i≤m}y_i^r + ∑_{i>m}y_i^r)` to the
power sum `p_r`, for every `r ≥ 1`. -/
@[hjo "def_cm_twisted_mult"]
theorem twistedMult_powerSum (q u : L) (m k r : ℕ) :
    twistedMult q u m k (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) + twistPowerSums q u m k (r + 1) :=
  alphabetShift_powerSum _ r

/-- `σ_{m,k}` fixes every auxiliary variable: it moves the alphabet `X` and nothing else. -/
@[hjo "def_cm_twisted_mult", simp]
theorem twistedMult_auxVar (q u : L) (m k j : ℕ) :
    twistedMult q u m k (auxVar j : Total L) = auxVar j :=
  alphabetShift_auxVar_apply _ j

/-- **`σ_{m,k}` carries `V_k` to `V_k`**, which is the domain and codomain `HJO.Sweep.twistedMult`
gives it: it fixes `y_1, …, y_k` and sends a power sum to a power sum plus an element of `V_k`. The
hypothesis `m ≤ k` is the `0 ≤ m ≤ k`. -/
@[hjo "def_cm_twisted_mult"]
theorem twistedMult_mem_piece (q u : L) {m k : ℕ} (hmk : m ≤ k) {F : Total L}
    (hF : F ∈ piece L k) : twistedMult q u m k F ∈ piece L k := by
  refine mem_piece_of_algHom (fun c => ?_) (fun j _ => ?_) hF
  · induction c using MvPolynomial.induction_on with
    | C a =>
      rw [show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda L) : Total L) = scal a from rfl,
        twistedMult, alphabetShift_scal]
      exact Subalgebra.algebraMap_mem _ _
    | add p r hp hr => rw [map_add, map_add]; exact add_mem hp hr
    | mul_X p j hp =>
      rw [map_mul, map_mul]
      refine mul_mem hp ?_
      rw [show (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) from by
        rw [Sym.powerSum, Nat.add_sub_cancel], twistedMult_powerSum]
      exact add_mem (Subalgebra.algebraMap_mem _ _) (twistPowerSums_mem_piece q u hmk (j + 1))
  · rw [show (MvPolynomial.X j : Total L) = auxVar (j + 1) from by
      rw [auxVar, Nat.add_sub_cancel], twistedMult_auxVar]
    exact auxVar_mem_piece (by omega) (by omega)

/-- **The twisted multiplication `∗_m` of `HJO.Sweep.twistedMult`**: `f ∗_m G = σ_{m,k}(f)·G`. -/
@[hjo "def_cm_twisted_mult"]
noncomputable def twistedActionMult (L : Type*) [Field L] (q u : L) (m k : ℕ) (f G : Total L) :
    Total L :=
  twistedMult q u m k f * G

@[hjo "def_cm_twisted_mult"]
theorem twistedActionMult_apply (q u : L) (m k : ℕ) (f G : Total L) :
    twistedActionMult L q u m k f G = twistedMult q u m k f * G := rfl

/-- **`∗_m` lands in `V_k`**, both factors doing so. -/
@[hjo "def_cm_twisted_mult"]
theorem twistedActionMult_mem_piece (q u : L) {m k : ℕ} (hmk : m ≤ k) {f G : Total L}
    (hf : f ∈ piece L k) (hG : G ∈ piece L k) :
    twistedActionMult L q u m k f G ∈ piece L k :=
  mul_mem (twistedMult_mem_piece q u hmk hf) hG

/-- **`∗_0` is the `∗_k` of `HJO.Sweep.twistedAction`**, which is the expected identification:
at `m = 0` the dilated block of the twisting alphabet is empty, so `σ_{0,k}` restricted to `Λ` is
the twisting homomorphism `tw_k` of `HJO.Sweep.twist`, and `f ∗_0 G = tw_k(f)G = f ∗_k G`. -/
@[hjo "def_cm_twisted_mult"]
theorem twistedMult_C (q u : L) (k : ℕ) (f : Sym.Lambda L) :
    twistedMult q u 0 k (MvPolynomial.C f) = twist L q k f := by
  have key : (twistedMult q u 0 k).comp (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L))
      = twist L q k := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hC : (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L)) (MvPolynomial.X j)
        = MvPolynomial.C (Sym.powerSum L (j + 1)) := by
      rw [IsScalarTower.coe_toAlgHom', MvPolynomial.algebraMap_eq,
        show (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) from by
          rw [Sym.powerSum, Nat.add_sub_cancel]]
    rw [AlgHom.comp_apply, hC, twistedMult_powerSum, twist_X, twistPowerSums,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl,
      show (MvPolynomial.C (MvPolynomial.C (q ^ (j + 1) - 1)) : Total L)
        = scal (q ^ (j + 1) - 1) from rfl]
    simp
  exact congrArg (fun g : Sym.Lambda L →ₐ[L] Total L => g f) key

/-- `∗_0` on a symmetric function is the twisted action of `HJO.Sweep.twistedAction`. -/
@[hjo "def_cm_twisted_mult"]
theorem twistedActionMult_zero (q u : L) (k : ℕ) (f : Sym.Lambda L) (G : Total L) :
    twistedActionMult L q u 0 k (MvPolynomial.C f) G = twistedAction L q k f G := by
  rw [twistedActionMult_apply, twistedMult_C, twistedAction]

end Mult

end HJO.Sweep
