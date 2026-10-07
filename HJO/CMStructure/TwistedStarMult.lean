/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.TwistedIntertwine
public meta import HJO.Attr

/-! # The starred family of twists against the two lowering and raising operators

Two lemmas about the family `∗_m` of twisted multiplications of `HJO.Sweep.twistedMult`:
the starred raising operator moves the index of the twist up by one, and Carlsson and Mellit's
lowering operator leaves it alone.

* `HJO.Sweep.dplusStar_twistedActionMult`: `d^*_+(f ∗_m G) = f ∗_{m+1} d^*_+G` for `0 ≤ m ≤ k`.
* `HJO.Sweep.dminusCM_twistedActionMult`: `d_-(f ∗_m G) = f ∗_m d_-G` for `0 ≤ m < k`.

## Main results

* `HJO.Sweep.dplusStar_twistedActionMult`.
* `HJO.Sweep.dminusCM_twistedActionMult`, `HJO.Sweep.dminusCM_twistedActionMult_C`:
  the lowering identity, once with the `f ∈ Λ` weakened to `f ∈ V_{k-1}` and once in the stated
  form, at `f ∈ Λ`.

## Implementation notes

**Both lemmas are one identity on the twisting alphabet.** `σ_{m,k}` is `Γ₊` at the family
`HJO.Sweep.twistPowerSums`, so every operator that is built from substitutions passes it by a
composition of alphabet shifts:

* `HJO.Sweep.alphabetShift_alphabetShift_of_mem_auxSubalg`: two shifts compose to the shift by the
  sum of the alphabets, provided the inner alphabet is free of `X`;
* `HJO.Sweep.cycleShift_alphabetShift`: `cy_{k+1}` conjugates a shift into the shift by the moved
  alphabet, because `cy_{k+1}` fixes `Λ` and carries the `y`-variables to elements free of `X`.

With those, `d^*_+ = cy_{k+1}∘τ_{k+1,k+1}` carries `σ_{m,k}` to `σ_{m+1,k+1}` in two steps
(`HJO.Sweep.qshift_twistedMult`, `HJO.Sweep.cycleShift_twistPowerSums`): the substitution adds the
letter `(q-1)y_{k+1}`, which the twisting alphabet of rank `k+1` has over the one of rank `k`, and
the cyclic shift then carries `y_i` to `y_{i+1}` throughout while wrapping that new letter to
`(q-1)uy_1` — exactly the term the index `m+1` requires. Dually `τ^-_{k+1,k+1}` removes the letter
again (`HJO.Sweep.qshiftNeg_twistedMult`), and the extraction of `d_-` passes the result because it
lies in `V_k` (`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`).

**`f ∈ Λ` is load-bearing in the starred lemma and free in the other.** `cy_{k+1}` renames the
`y`-variables, so it fixes `f` only when `f` carries none: at a general `f` the left-hand side reads
`cy_{k+1}(f)` where the right-hand side reads `f`, and the two differ already at `f = y_1`. For the
lowering operator no such rename occurs and the hypothesis weakens to `f ∈ V_{k-1}`, which is what
the commutation with the coefficient extraction needs;
`HJO.Sweep.dminusCM_twistedActionMult_C` records the case `f ∈ Λ`.

**`G ∈ V_k` is not used in either**, as in `HJO.Sweep.cmDPlus_twistedAction`: `d^*_+` is
multiplicative on the whole total space and `d_-` is linear over `V_k`, and neither argument reads
the support of `G`. The hypothesis is therefore dropped.

**The index bounds are exact.** `m ≤ k` is read twice in the starred lemma, once for
`Icc (m+1) (k+1) = Icc (m+1) k ∪ {k+1}` and once for `cy_{k+1}(y_i) = y_{i+1}` at every `i ≤ m`; and
`m < k` — here `m ≤ k` at rank `k+1` — is read twice in the lowering lemma, once for the same
decomposition and once for `σ_{m,k}(f) ∈ V_k`. At `m = k` the lowering lemma fails twice over. The
letter `y_k` is then dilated by `u`, where `τ^-_{k,k}` removes the undilated `(q-1)y_k`, so the
composite substitution keeps the term `(q^r-1)(u^r-1)y_k^r`, which is not free of `y_k` and does not
come out of the extraction; and the right-hand side `f ∗_m d_-G` is outside the range `0 ≤ m ≤ k-1`
that `HJO.Sweep.twistedMult` gives the twist at rank `k-1` at all, `σ_{k,k-1}` reading a letter
`y_k` that `V_{k-1}` does not have. The second defect survives at `u = 1`, where the first vanishes.
So the `m < k` is exactly the well-formedness condition of its own right-hand side.

## References

Following A. Mellit, *Toric braids and
`(m,n)`-parking functions*, §3.6.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Two sums over a shifted interval -/

/-- Reindexing a sum over `Icc a b` by `i ↦ i + 1`. Used to compare the twisting alphabet with its
image under the cyclic shift, which raises every index it reads by one. -/
theorem sum_Icc_map_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, f (i + 1) = ∑ i ∈ Finset.Icc (a + 1) (b + 1), f i := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]
  rfl

/-- Splitting off the bottom term of a sum over `Icc 1 (n+1)`: the term `f 1` is the one the wrapped
letter of the cyclic shift supplies. -/
theorem sum_Icc_one_eq_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (n + 1), f i = f 1 + ∑ i ∈ Finset.Icc 2 (n + 1), f i := by
  rw [show Finset.Icc 1 (n + 1) = insert 1 (Finset.Icc 2 (n + 1)) from by
    ext i
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega]
  exact Finset.sum_insert (by simp)

/-! ### Composing alphabet shifts -/

section Compose

variable {L : Type*} [Field L]

/-- **Two alphabet shifts compose to the shift by the sum of the alphabets**, provided the inner
alphabet is free of the letters of `X`: the outer shift then fixes each `P r`, so on `p_r` the
composite adds `P r + Q r`, and both shifts fix the `y`-variables.

The hypothesis is the same one `HJO.Sweep.alphabetShift_neg_alphabetShift` reads, and for the same
reason: without it the outer shift moves the inner shift's own letters. -/
theorem alphabetShift_alphabetShift_of_mem_auxSubalg {P Q : ℕ → Total L}
    (hP : ∀ r, P r ∈ auxSubalg L) (F : Total L) :
    alphabetShift Q (alphabetShift P F) = alphabetShift (fun r => P r + Q r) F := by
  have key : (alphabetShift Q).comp (alphabetShift P)
      = alphabetShift (fun r => P r + Q r) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, alphabetShift_powerSum,
        map_add, alphabetShift_of_mem_auxSubalg _ (hP (r + 1))]
      ring
    · simp only [AlgHom.comp_apply, alphabetShift_X]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`τ^-_{k,i}` is `Γ₊` at the virtual alphabet `-(q-1)y_i`**, the mirror of
`HJO.Sweep.qshift_eq_alphabetShift`. Unlike that one this is not an identity of definitions, the
substitution of `HJO.Sweep.qshiftNeg` subtracting where `Γ₊` adds, so the two algebra maps are
compared on the power sums and the `y`-variables. -/
theorem qshiftNeg_eq_alphabetShift (q : L) (i : ℕ) (F : Total L) :
    qshiftNeg q i F
      = alphabetShift (fun r => -(scal (q ^ r - 1) * (auxVar i : Total L) ^ r)) F := by
  have key : (qshiftNeg q i : Total L →ₐ[L] Total L)
      = alphabetShift (fun r => -(scal (q ^ r - 1) * (auxVar i : Total L) ^ r)) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshiftNeg_powerSum,
        alphabetShift_powerSum]
      ring
    · simp only [qshiftNeg_auxVar, alphabetShift_X]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- `cy_{k+1}` sends every `y`-variable to an element free of the alphabet `X`: to another variable,
or to the wrapped letter `uy_1`. This is what makes an alphabet shift fix the image, and so is the
hypothesis `HJO.Sweep.cycleShift_alphabetShift` reads. -/
theorem cycleShift_X_mem_auxSubalg (u : L) (k j : ℕ) :
    cycleShift u k (MvPolynomial.X j : Total L) ∈ auxSubalg L := by
  rcases lt_trichotomy j k with h | h | h
  · rw [cycleShift_X_of_lt u h]
    exact Algebra.subset_adjoin ⟨j + 1, rfl⟩
  · rw [h, show (MvPolynomial.X k : Total L) = auxVar (k + 1) from by
      rw [auxVar, Nat.add_sub_cancel], cycleShift_auxVar_last]
    exact mul_mem ((auxSubalg L).algebraMap_mem u) (auxVar_mem_auxSubalg 1)
  · rw [cycleShift_X_of_gt u h]
    exact Algebra.subset_adjoin ⟨j, rfl⟩

/-- **`cy_{k+1}` conjugates an alphabet shift into the shift by the moved alphabet**:
`cy_{k+1}∘Γ₊(Z) = Γ₊(cy_{k+1}Z)∘cy_{k+1}`.

Both composites are `𝕜`-algebra endomorphisms of the total space. On a power sum the left side gives
`p_r + cy_{k+1}(P r)` because `cy_{k+1}` fixes `Λ`, and so does the right side; on a `y`-variable
both give its image under `cy_{k+1}`, the outer shift fixing that image by
`HJO.Sweep.cycleShift_X_mem_auxSubalg`. No hypothesis on the alphabet is needed. -/
theorem cycleShift_alphabetShift (u : L) (k : ℕ) (P : ℕ → Total L) (F : Total L) :
    cycleShift u k (alphabetShift P F)
      = alphabetShift (fun r => cycleShift u k (P r)) (cycleShift u k F) := by
  have hCapp : ∀ G : Total L, ((cycleShift u k).restrictScalars L) G = cycleShift u k G :=
    fun _ => rfl
  have key : ((cycleShift u k).restrictScalars L).comp (alphabetShift P)
      = (alphabetShift fun r => cycleShift u k (P r)).comp
        ((cycleShift u k).restrictScalars L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, hCapp,
        alphabetShift_powerSum, map_add, cycleShift_C]
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, hCapp, hCapp, alphabetShift_X,
        alphabetShift_of_mem_auxSubalg _ (cycleShift_X_mem_auxSubalg u k n)]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

end Compose

/-! ### The twisting alphabet under the two substitutions and the cyclic shift -/

section Alphabet

variable {L : Type*} [Field L]

/-- **The twisting alphabet of rank `k+1` is the one of rank `k` plus the letter `(q-1)y_{k+1}`**,
provided `m ≤ k`, so that `y_{k+1}` lands in the undilated block. This is the letter that
`τ_{k+1,k+1}` adds and `τ^-_{k+1,k+1}` removes. -/
theorem twistPowerSums_add_letter (q u : L) {m k : ℕ} (hmk : m ≤ k) (r : ℕ) :
    twistPowerSums q u m k r + scal (q ^ r - 1) * (auxVar (k + 1) : Total L) ^ r
      = twistPowerSums q u m (k + 1) r := by
  rw [twistPowerSums, twistPowerSums,
    Finset.sum_Icc_succ_top (show m + 1 ≤ k + 1 by omega)
      (fun i => (auxVar i : Total L) ^ r)]
  ring

/-- **`τ_{k+1,k+1}` raises the rank of the twist**: `τ_{k+1,k+1}∘σ_{m,k} = σ_{m,k+1}`. Both are
alphabet shifts, so the claim is the identity of alphabets
`HJO.Sweep.twistPowerSums_add_letter`. -/
theorem qshift_twistedMult (q u : L) {m k : ℕ} (hmk : m ≤ k) (F : Total L) :
    qshift q (k + 1) (twistedMult q u m k F) = twistedMult q u m (k + 1) F := by
  rw [twistedMult, twistedMult, qshift_eq_alphabetShift,
    alphabetShift_alphabetShift_of_mem_auxSubalg (twistPowerSums_mem_auxSubalg q u m k)]
  exact congrArg (fun P : ℕ → Total L => alphabetShift P F)
    (funext fun r => twistPowerSums_add_letter q u hmk r)

/-- **`τ^-_{k+1,k+1}` lowers the rank of the twist**: `τ^-_{k+1,k+1}∘σ_{m,k+1} = σ_{m,k}`, for
`m ≤ k`. The substitution removes exactly the letter `(q-1)y_{k+1}` that the alphabet of rank `k+1`
has over the one of rank `k`.

`m ≤ k` — the `m < k+1` — is load-bearing: at `m = k+1` the letter `y_{k+1}` is dilated
by `u` and the residue `(q^r-1)(u^r-1)y_{k+1}^r` survives. -/
theorem qshiftNeg_twistedMult (q u : L) {m k : ℕ} (hmk : m ≤ k) (F : Total L) :
    qshiftNeg q (k + 1) (twistedMult q u m (k + 1) F) = twistedMult q u m k F := by
  rw [twistedMult, qshiftNeg_eq_alphabetShift,
    alphabetShift_alphabetShift_of_mem_auxSubalg (twistPowerSums_mem_auxSubalg q u m (k + 1)),
    twistedMult]
  refine congrArg (fun P : ℕ → Total L => alphabetShift P F) (funext fun r => ?_)
  rw [← twistPowerSums_add_letter q u hmk r]
  ring

/-- **The cyclic shift raises the index of the twist**:
`cy_{k+1}` carries the twisting alphabet of index `m` at rank `k+1` to the one of index `m+1`, for
`m ≤ k`.

The dilated block `u∑_{i≤m}y_i` becomes `u∑_{2≤i≤m+1}y_i`, the undilated block
`∑_{m<i≤k+1}y_i` becomes `∑_{m+1<i≤k+1}y_i` together with the wrapped letter `uy_1`, and that
wrapped letter is the missing first term of the dilated block at index `m+1`. -/
theorem cycleShift_twistPowerSums (q u : L) {m k : ℕ} (hmk : m ≤ k) (r : ℕ) :
    cycleShift u k (twistPowerSums q u m (k + 1) r) = twistPowerSums q u (m + 1) (k + 1) r := by
  have hsu : (scal u * (auxVar 1 : Total L)) ^ r = scal (u ^ r) * (auxVar 1 : Total L) ^ r := by
    rw [mul_pow, scal_eq_algebraMap, scal_eq_algebraMap, map_pow]
  have hlow : ∀ i ∈ Finset.Icc 1 m, cycleShift u k ((auxVar i : Total L) ^ r)
      = (auxVar (i + 1) : Total L) ^ r := fun i hi => by
    have h := Finset.mem_Icc.1 hi
    rw [map_pow, cycleShift_auxVar u h.1 (by omega)]
  have hmid : ∀ i ∈ Finset.Icc (m + 1) k, cycleShift u k ((auxVar i : Total L) ^ r)
      = (auxVar (i + 1) : Total L) ^ r := fun i hi => by
    have h := Finset.mem_Icc.1 hi
    rw [map_pow, cycleShift_auxVar u (by omega) h.2]
  rw [twistPowerSums, twistPowerSums, map_mul, map_add, map_mul, cycleShift_scal, cycleShift_scal,
    map_sum, map_sum, Finset.sum_congr rfl hlow,
    Finset.sum_Icc_succ_top (show m + 1 ≤ k + 1 by omega)
      (fun i => cycleShift u k ((auxVar i : Total L) ^ r)),
    Finset.sum_congr rfl hmid, map_pow, cycleShift_auxVar_last,
    sum_Icc_map_succ (fun i => (auxVar i : Total L) ^ r) 1 m,
    sum_Icc_map_succ (fun i => (auxVar i : Total L) ^ r) (m + 1) k,
    sum_Icc_one_eq_add (fun i => (auxVar i : Total L) ^ r) m, hsu]
  ring

end Alphabet

/-! ### The two lemmas -/

section Nodes

variable {L : Type*} [Field L]

/-- **`d^*_+` moves the index of the twist up by one**, on the substitution:
`d^*_+∘σ_{m,k} = σ_{m+1,k+1}` on `Λ`, for `m ≤ k`.

`d^*_+` is `cy_{k+1}∘τ_{k+1,k+1}`; the substitution raises the rank of the twist
(`HJO.Sweep.qshift_twistedMult`) and the cyclic shift then raises its index
(`HJO.Sweep.cycleShift_twistPowerSums`), fixing the argument `f` because `f` lies in `Λ`. -/
theorem dplusStarAlg_twistedMult (q u : L) {m k : ℕ} (hmk : m ≤ k) (f : Sym.Lambda L) :
    dplusStarAlg q u k (twistedMult q u m k (MvPolynomial.C f))
      = twistedMult q u (m + 1) (k + 1) (MvPolynomial.C f) := by
  rw [dplusStarAlg_apply, qshift_twistedMult q u hmk, twistedMult, cycleShift_alphabetShift,
    cycleShift_C, twistedMult]
  exact congrArg (fun P : ℕ → Total L => alphabetShift P (MvPolynomial.C f))
    (funext fun r => cycleShift_twistPowerSums q u hmk r)

variable [Algebra ℚ L]

/-- **The starred raising operator shifts the twist.**
`d^*_+(f ∗_m G) = f ∗_{m+1} d^*_+G` for `0 ≤ m ≤ k`, `f ∈ Λ` and `G` in the total space.

`d^*_+` is the composite of two algebra maps, hence multiplicative
(`HJO.Sweep.dplusStarAlg_eq_dplusStar`), so the whole content is what it does to the twisting
substitution, which is `HJO.Sweep.dplusStarAlg_twistedMult`.

The `G ∈ V_k` is not used: nothing above reads the support of `G`, both sides applying
the same operator to it. Its `f ∈ Λ` is load-bearing, `cy_{k+1}` renaming the `y`-variables, and so
is `m ≤ k`, which keeps the dilated block inside the range where `cy_{k+1}` is a shift. -/
@[hjo "lem_cm_twisted_dplus_star"]
theorem dplusStar_twistedActionMult (q u : L) {m k : ℕ} (hmk : m ≤ k) (f : Sym.Lambda L)
    (G : Total L) :
    dplusStar q u k (twistedActionMult L q u m k (MvPolynomial.C f) G)
      = twistedActionMult L q u (m + 1) (k + 1) (MvPolynomial.C f) (dplusStar q u k G) := by
  rw [twistedActionMult_apply, twistedActionMult_apply, ← dplusStarAlg_eq_dplusStar,
    ← dplusStarAlg_eq_dplusStar, map_mul, dplusStarAlg_twistedMult q u hmk]

/-- **The lowering operator preserves the twist.**
`d_-(f ∗_m G) = f ∗_m d_-G`, read at rank `k+1` so that no truncated subtraction occurs; the
range `0 ≤ m < k` is the hypothesis `m ≤ k` here.

`d_-` is the coefficient extraction of `HJO.Sweep.dminusCM` after `τ^-_{k+1,k+1}`. The substitution
lowers the rank of the twist (`HJO.Sweep.qshiftNeg_twistedMult`), and the extraction passes
`σ_{m,k}(f)` because that element lies in `V_k`, hence is free of `y_{k+1}`
(`HJO.Sweep.lowerCoeffShift_mul_of_mem_piece`, `HJO.Sweep.twistedMult_mem_piece`).

The `f ∈ Λ` is weakened to `f ∈ V_k`, which is all the two steps need, and its
`G ∈ V_{k+1}` is dropped. `m ≤ k` — the `m < k` — is load-bearing, and at `m = k+1` the
statement is false. There the letter `y_{k+1}` sits in the dilated block, so `τ^-_{k+1,k+1}`, which
removes the undilated letter `(q-1)y_{k+1}`, does not remove it: the composite is the shift by
`(q^r-1)(u^r∑_{i≤k+1}y_i^r - y_{k+1}^r)`, which still reads `y_{k+1}` and therefore does not come
out of the coefficient extraction, and which is no twisting alphabet of rank `k` whatever the index.
Already at `u = 1`, `q ≠ 1`, `f = p_1` and `G = 1` the two sides differ by `(q-1)y_{k+1}e_1`. -/
@[hjo "lem_cm_twisted_m_dminus"]
theorem dminusCM_twistedActionMult (q u : L) {m k : ℕ} (hmk : m ≤ k) {f : Total L}
    (hf : f ∈ piece L k) (G : Total L) :
    dminusCM q (k + 1) (twistedActionMult L q u m (k + 1) f G)
      = twistedActionMult L q u m k f (dminusCM q (k + 1) G) := by
  rw [twistedActionMult_apply, twistedActionMult_apply, dminusCM_succ_apply, dminusCM_succ_apply,
    map_mul, qshiftNeg_twistedMult q u hmk,
    lowerCoeffShift_mul_of_mem_piece (twistedMult_mem_piece q u hmk hf)]

/-- **`HJO.Sweep.dminusCM_twistedActionMult` in its stated form**, at `f ∈ Λ`: a coefficient from
`Λ` lies in every graded piece, so this is the case `f ∈ V_k` of
`HJO.Sweep.dminusCM_twistedActionMult`. -/
@[hjo "lem_cm_twisted_m_dminus"]
theorem dminusCM_twistedActionMult_C (q u : L) {m k : ℕ} (hmk : m ≤ k) (f : Sym.Lambda L)
    (G : Total L) :
    dminusCM q (k + 1) (twistedActionMult L q u m (k + 1) (MvPolynomial.C f) G)
      = twistedActionMult L q u m k (MvPolynomial.C f) (dminusCM q (k + 1) G) :=
  dminusCM_twistedActionMult q u hmk (Subalgebra.algebraMap_mem _ f) G

end Nodes

end HJO.Sweep
