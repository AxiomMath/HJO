/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitColumnChainTelescope
public import HJO.Shuffle.MellitVertexStepGeneral
public meta import HJO.Attr

/-! # The `(2,b)` row of `HJO.Mellit.lhsRewrite_sweepWitness` at a general `f`

`HJO/Shuffle/MellitColumnChainTelescope.lean` closes the `(a,1)` column of
`HJO.Mellit.lhsRewrite_sweepWitness` at a general `f` (`HJO.Sweep.lhsSlope_succ_one`), and
`HJO/Shuffle/MellitLhsSlopeMediant.lean` closes the `(1,b)` row
(`HJO.Mellit.lhsSlope_one_left`). Both boundaries have a slope word of one letter repeated:
`β_{a,1} = z^{a-1}` and `β_{1,b} = y^{b-1}`. **This file closes the first family whose word mixes
the two letters: the whole `(2,b)` row, at a general `f`, at every `b`.**

`HJO.Sweep.lhsSlope_two_odd`: `HJO.Mellit.LhsSlope q u 2 (2k+1)` for every `k ≥ 1`. The parity is no
restriction — `Nat.Coprime 2 b` forces `b` odd — so this is the row at every slope at which it is
defined. Its smallest member is `(2,3)`, the **smallest slope in the range `1 < a < b` of `hlhs`**,
and it is otherwise known only at `f = 1` (`HJO.Mellit.lhsBase_two_three`).

## Why the row is a one-step computation

The slope word has `b - 1` letters `y` and `a - 1` letters `z`, so `a = 2` is exactly the family
whose word carries a **single** `z`. By `HJO.Mellit.slopeEval_mediant` at the two parents `(1,k+1)`
and `(1,k)`, whose words are both pure `Y`, that word is the palindrome

`β_{2,2k+1} = y^kzy^k`,   i.e.   `Ξ_{2,2k+1} = Y^kZY^k`   (`HJO.Sweep.slopeEval_two_odd`).

`Y` is multiplication by `-y_1`, so the two blocks contribute `(-1)^k` each and the row carries no
sign of its own. The single `Z` is one application of the vertex relation
`HJO.Sweep.zLetter_auxVar_mul` --- `Z(y_1G) = y_1T(G)` --- followed by the composition law
`HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum`, which sends the pair `(j,g)` to
`∑_l(qu)^l(l, D_{j-l}g)`. Reading `d_-` off by
`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C` gives the sweep side outright
(`HJO.Sweep.exists_forall_dminus_slopeOperator_two_odd`):

`d_-(Ξ_{2,2k+1}(Φf)) = C(∑_{l ≥ 0}(qu)^lD_{k+1+l}(D_{k-l}f))`.

There is **no nest and no induction on the slope**: one `z` means one level.

On the `Λ` side, `Split 2 (2k+1) = (1,k)` (`HJO.Sweep.split_two_odd`), so both halves of
`HJO.Sym.Qop`'s recursion are base cases and `Q_{2,2k+1} = M^{-1}(D_{k+1}D_k - D_kD_{k+1})`
(`HJO.Sweep.qop_two_odd`, no hypothesis on `q`, `u` or `M`). The two sides then agree by **one
application of the pair commutator** `HJO.Sym.smul_sum_sum_dopInt_dopInt` at
`(m,n) = (k+1,k)`, where the gap `m - n` is `1` so its outer sum has a single row
(`HJO.Sweep.qop_two_odd_apply`).

So the row costs one instance of an identity already proved in the library, and that is as much
the content of what follows as the theorem is: **the `(2,b)` row is not the hard part of the general
slope.**

## What this does *not* close, precisely

`HJO.Mellit.lhsRewrite_sweepWitness` is stated at a general slope and this is one row of it. The
next family is `a = 3`, and this file states exactly what it costs, in the two residue classes
coprimality allows:

* `Q_{3,3j+1} = M^{-1}(Q_{2,2j+1}D_j - D_jQ_{2,2j+1})`   (`HJO.Sweep.qop_three_of_mod_one`),
* `Q_{3,3j+2} = M^{-1}(D_{j+1}Q_{2,2j+1} - Q_{2,2j+1}D_{j+1})`  (`HJO.Sweep.qop_three_of_mod_two`),

both with **no hypothesis on `q`, `u` or `M`**. In each the `(2,·)` factor is automatically of odd
height, so it is an instance of the row above and is known in closed form: **the whole `a = 3`
family is one basic operator commuted past the two-letter word this file evaluates**, where the
`(a,1)` column commuted `D_0` past a nest of length `b`.

So the input `a = 3` needs is the two-level Leibniz collection of
`HJO/Shuffle/MellitColumnChainTelescope.lean` --- the same `HJO.Sweep.chainComm_succ` step and
the same geometric-run coefficient `HJO.Sweep.chainGeomCoeff` --- at a *pair* of starting indices
rather than at the single index `0`, and with the passing letter `D_j` or `D_{j+1}` rather than
`D_0`. **The coefficient-generalisation trick therefore does transfer in shape**; what does not
transfer is the column's accident that one side of every commutator is the single letter `D_0` at
index `0`, which is what made `HJO.Sweep.chainGeomCoeff`'s run start at `(qu)^{l-min(j,l)}` with a
single `j`.

The two binders of `HJO.Mellit.shuffle_of_lhs_and_induction` are `hlhs` and `hind`, and **neither is
touched**. `hind` is untouched outright. `hlhs` asks for `HJO.Mellit.LhsComputes`, the clause at
every composition `α`, and `HJO/Shuffle/MellitLhsCompInduction.lean` shows that the
singleton clause `HJO.Mellit.LhsSlope` does **not** drive its append step at any slope: at
`α = (1,1)` the step names `Q_{2a,2b}` at the doubled, non-coprime slope with coefficient `u(q-1)`
(`HJO.Mellit.qop_double_apply_one_of_lhsWord`). So `LhsSlope` at the whole coprime slope lattice
would still not discharge `hlhs`, and this row does not either.

## Genericity

* `HJO.Sweep.split_two_odd`, `HJO.Sweep.slopeEval_two_odd`, `HJO.Sweep.qop_two_odd`: **no
  hypothesis on `q`, `u` or `M`**. The normalisation `M⁻¹` of `HJO.Sym.Qop` is carried symbolically.
* The sweep side: `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, all three real and for the reason recorded in
  `HJO/Shuffle/MellitStraightMonomial.lean` --- the letter `Z = (qu)^{-1}z_1` of
  `HJO.Sweep.slopeOperator` is the zero map at each
  (`HJO.Sweep.zLetter_eq_zero_of_mul_eq_zero`, `HJO.Sweep.zLetter_eq_zero_of_q_eq_one`), so the row
  would read `0 = something nonzero`.
* `HJO.Sweep.qop_two_odd_apply` and `HJO.Sweep.lhsSlope_two_odd`: additionally `M ≠ 0`, used only to
  divide by `HJO.Sym.Qop`'s normalisation. The pair commutator it is applied to carries nothing.
* **`u ≠ 1` is not an extra condition, and not an improvement either.** `M ≠ 0` is
  `(1-q)(1-u) ≠ 0`, so it already says `u ≠ 1`; the `(2,3)` instance at `f = 1`
  (`HJO.Mellit.lhsBase_two_three`) takes `q ≠ 1` and `u ≠ 1` and builds `M ≠ 0` from them, while
  this takes `M ≠ 0` and `q ≠ 1`. The two hypothesis sets are the **same** band
  `q ∉ {0,1}`, `u ∉ {0,1}`, which is why `HJO.Sweep.lhsBase_two_three_of_row` can drop the
  `u ≠ 1` binder and is not stronger for doing so.

## Implementation notes

`HJO.Mellit.lhsRewrite_sweepWitness` states its clause at a *general* slope and this is one row
of it, exactly as the `(a,1)` column was one column.
`HJO.Mellit.slopeWord_mediant`,
`HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain` and
`HJO.Sym.smul_sum_sum_dopInt_dopInt` are applied here, not added to.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The slope word of the `(2,b)` row -/

/-- `Split 2 (2k+1) = (1,k)` for `k ≥ 1`. -/
theorem split_two_odd {k : ℕ} (hk : 1 ≤ k) : Sym.Split 2 (2 * k + 1) = (1, k) :=
  Sym.split_eq_of_spec (by omega)
    ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega)) le_rfl (by omega) hk (by omega) (by ring)

/-- **`Ξ_{2,2k+1} = Y^kZY^k`**: the slope word of the `(2,b)` row is the palindrome
`y^kzy^k`, the mediant factorisation `HJO.Mellit.slopeEval_mediant` at the two parents
`(1,k+1)` and `(1,k)`, both of whose words are pure `Y`. -/
theorem slopeEval_two_odd {A : Type*} [Monoid A] (Y Z : A) {k : ℕ} (hk : 1 ≤ k) :
    Mellit.slopeEval Y Z 2 (2 * k + 1) = Y ^ k * (Z * Y ^ k) := by
  have h := Mellit.slopeEval_mediant Y Z (m₁ := 1) (n₁ := k + 1) (m₂ := 1) (n₂ := k)
    le_rfl (by omega) le_rfl hk (by ring) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  rw [show (1 : ℕ) + 1 = 2 from rfl, show k + 1 + k = 2 * k + 1 from by ring] at h
  rw [h, Mellit.slopeEval_one_left Y Z (by omega), Mellit.slopeEval_one_left Y Z (by omega),
    show k + 1 - 1 = k from rfl, ← mul_assoc, ← pow_succ,
    show k - 1 + 1 = k from by omega]

/-! ### The sweep side -/

omit [Algebra ℚ L] in
/-- `Y^k` on a monomial in `y_1`: `Y = -(y_1·)`, so `Y^k(y_1^mG) = (-1)^ky_1^{m+k}G`. -/
private theorem negY_pow_apply (k m : ℕ) (G : Total L) :
    ((-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ k) ((auxVar 1 : Total L) ^ m * G)
      = (-1 : L) ^ k • ((auxVar 1 : Total L) ^ (m + k) * G) := by
  rw [Mellit.neg_mulLeft_pow_apply, neg_pow,
    show ((-1 : Total L) ^ k) = algebraMap L (Total L) ((-1 : L) ^ k) from by
      rw [map_pow, map_neg, map_one],
    ← Algebra.smul_def, smul_mul_assoc]
  refine congrArg (fun x => ((-1 : L) ^ k) • x) ?_
  rw [pow_add]
  ring

/-- **The slope operator of the `(2,b)` row on the clause's argument, in closed form.** For `k ≥ 1`
and every large enough truncation `R`,

`Ξ_{2,2k+1}(Φf) = ∑_{l ≥ 0}(qu)^l y_1^{k+1+l}d^*_+(C(D_{k-l}f))`.

The two `Y^k` of `HJO.Sweep.slopeEval_two_odd` each contribute `(-1)^k`, so the row carries no
sign; the single `Z` is one application of `HJO.Sweep.zLetter_auxVar_mul` followed by the
composition law `HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum`. -/
theorem exists_forall_slopeOperator_two_odd (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (f : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      slopeOperator q u 1 2 (2 * k + 1) (Mellit.slopeArg q u f)
        = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
            ((auxVar 1 : Total L) ^ (k + 1 + l)
              * dplusStar q u 0
                  (MvPolynomial.C (Sym.DopInt q u ((k : ℤ) - (l : ℤ)) f) : Total L)) := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_bopExt_dplusStar_coeff_eq_zero q u k
    (dplusStar q u 0 (MvPolynomial.C f : Total L))
  refine ⟨R₀, fun R hR => ?_⟩
  have hmem : (auxVar 1 : Total L) ^ k * dplusStar q u 0 (MvPolynomial.C f : Total L)
      ∈ piece L 1 :=
    Subalgebra.mul_mem _ (pow_mem (auxVar_mem_piece le_rfl le_rfl) k)
      (dplusStar_zero_C_mem_piece_one q u f)
  have hinner : ((-LinearMap.mulLeft L (auxVar 1 : Total L)) ^ k) (Mellit.slopeArg q u f)
      = (-1 : L) ^ k • ((auxVar 1 : Total L)
          * ((auxVar 1 : Total L) ^ k * dplusStar q u 0 (MvPolynomial.C f : Total L))) := by
    rw [show Mellit.slopeArg q u f
        = (auxVar 1 : Total L) ^ 1 * dplusStar q u 0 (MvPolynomial.C f : Total L) from by
      rw [Mellit.slopeArg_def, pow_one], negY_pow_apply]
    refine congrArg (fun x => ((-1 : L) ^ k) • x) ?_
    rw [pow_add, pow_one, mul_assoc]
  rw [slopeOperator_eq_slopeEval, slopeEval_two_odd _ _ hk, Module.End.mul_apply,
    Module.End.mul_apply, hinner, map_smul, zLetter_auxVar_mul hq0 hu0 hq1 hmem,
    vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum hq1 k R f (hR₀ R hR), Finset.mul_sum,
    map_smul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul_comm, map_smul, ← mul_assoc, ← pow_succ', negY_pow_apply, smul_comm ((q * u) ^ l),
    smul_smul, show ((-1 : L) ^ k * (-1 : L) ^ k) = 1 from by
      rw [← pow_add, show k + k = 2 * k from by ring, pow_mul]; norm_num, one_smul,
    show l + 1 + k = k + 1 + l from by omega]

/-- **The sweep side of the clause on the `(2,b)` row, inside the integer-indexed basic
operators.** For `k ≥ 1` and every large enough truncation `R`,

`d_-(Ξ_{2,2k+1}(Φf)) = C(∑_{l ≥ 0}(qu)^lD_{k+1+l}(D_{k-l}f))`. -/
theorem exists_forall_dminus_slopeOperator_two_odd (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (f : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      dminus q 1 (slopeOperator q u 1 2 (2 * k + 1) (Mellit.slopeArg q u f))
        = MvPolynomial.C (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
            Sym.DopInt q u ((k : ℤ) + 1 + (l : ℤ))
              (Sym.DopInt q u ((k : ℤ) - (l : ℤ)) f)) := by
  obtain ⟨R₀, hR₀⟩ := exists_forall_slopeOperator_two_odd hq0 hu0 hq1 hk f
  refine ⟨R₀, fun R hR => ?_⟩
  rw [hR₀ R hR, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, dminus_auxVar_pow_mul_dplusStar_C, ← Sym.dopInt_natCast,
    show (((k + 1 + l : ℕ)) : ℤ) = (k : ℤ) + 1 + (l : ℤ) from by push_cast; ring, C_smul]

/-! ### The `Λ` side -/

/-- **`Q_{2,2k+1}` is the commutator `M^{-1}[D_{k+1}, D_k]`**: the split of the `(2,b)` row is
`(1,k)` (`HJO.Sweep.split_two_odd`), so both halves of `HJO.Sym.Qop`'s recursion are base cases.

**No hypothesis on `q`, `u` or `M`**: `M⁻¹` is carried symbolically. -/
theorem qop_two_odd {k : ℕ} (hk : 1 ≤ k) :
    Sym.Qop q u 2 (2 * k + 1)
      = ((1 - q) * (1 - u))⁻¹ • (Sym.Dop q u (k + 1) * Sym.Dop q u k
          - Sym.Dop q u k * Sym.Dop q u (k + 1)) := by
  rw [Sym.qop_eq_qopPrim q u ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega)),
    Sym.qopPrim_of_one_lt q u (2 * k + 1) (by omega), split_two_odd hk]
  simp only []
  rw [show 2 - 1 = 1 from rfl, show 2 * k + 1 - k = k + 1 from by omega,
    Sym.qopPrim_of_le_one q u (k + 1) le_rfl, Sym.qopPrim_of_le_one q u k le_rfl]

/-- **The `Λ` side of the clause on the `(2,b)` row, as the same `D`-sum the sweep side is.** For
`k ≥ 1` and every large enough truncation,

`Q_{2,2k+1}f = ∑_{l ≥ 0}(qu)^lD_{k+1+l}(D_{k-l}f)`,

which is the pair commutator `HJO.Sym.smul_sum_sum_dopInt_dopInt` at `(m,n) = (k+1,k)`, where the
gap is `1` so the outer sum has a single row. `M ≠ 0` is used to divide by `HJO.Sym.Qop`'s
normalisation and nowhere else: the commutator identity itself carries no hypothesis. -/
theorem qop_two_odd_apply (hM : (1 - q) * (1 - u) ≠ 0) {k : ℕ} (hk : 1 ≤ k)
    (f : Sym.Lambda L) {T : ℕ} (hT : (Sym.plethShift q u f).natDegree < T) {R : ℕ}
    (hRT : T ≤ R) (hRm : (k : ℤ) + 1 + (T : ℤ) ≤ (R : ℤ)) :
    Sym.Qop q u 2 (2 * k + 1) f
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u ((k : ℤ) + 1 + (l : ℤ))
            (Sym.DopInt q u ((k : ℤ) - (l : ℤ)) f) := by
  have hcomm := Sym.smul_sum_sum_dopInt_dopInt q u f hT ((k : ℤ) + 1) (k : ℤ) (by omega)
    (R := R) hRT hRm
  rw [show ((k : ℤ) + 1 - (k : ℤ)).toNat = 1 from by
      rw [show (k : ℤ) + 1 - (k : ℤ) = 1 from by ring]; rfl,
    Finset.sum_range_one] at hcomm
  have hsum : ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
      Sym.DopInt q u ((k : ℤ) + 1 + ((0 : ℕ) : ℤ) + (l : ℤ))
        (Sym.DopInt q u ((k : ℤ) + 1 - 1 - ((0 : ℕ) : ℤ) - (l : ℤ)) f)
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u ((k : ℤ) + 1 + (l : ℤ))
            (Sym.DopInt q u ((k : ℤ) - (l : ℤ)) f) :=
    Finset.sum_congr rfl fun l _ => by
      rw [show (k : ℤ) + 1 + ((0 : ℕ) : ℤ) + (l : ℤ) = (k : ℤ) + 1 + (l : ℤ) from by
          push_cast; ring,
        show (k : ℤ) + 1 - 1 - ((0 : ℕ) : ℤ) - (l : ℤ) = (k : ℤ) - (l : ℤ) from by
          push_cast; ring]
  rw [hsum] at hcomm
  have hcast : Sym.Dop q u (k + 1) = Sym.DopInt q u ((k : ℤ) + 1) := by
    rw [← Sym.dopInt_natCast]
    congr 1
  rw [qop_two_odd hk]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [hcast, ← Sym.dopInt_natCast, ← hcomm, smul_smul, inv_mul_cancel₀ hM, one_smul]

/-! ### The clause on the `(2,b)` row -/

/-- **The clause `HJO.Mellit.lhsRewrite_sweepWitness` on the whole `(2,b)` row, at a general `f`:**
`HJO.Mellit.LhsSlope q u 2 (2k+1)` for every `k ≥ 1`.

The two sides are the *same* `D`-sum. The sweep side is
`HJO.Sweep.exists_forall_dminus_slopeOperator_two_odd`, the `Λ` side
`HJO.Sweep.qop_two_odd_apply`, and the truncation is chosen large enough for both.

`b = 2k+1` is no restriction: `Nat.Coprime 2 b` forces `b` odd, so this is the `(2,b)` row at every
slope at which it is defined. The smallest instance is `(2,3)`, which is otherwise known only at
`f = 1` (`HJO.Mellit.lhsBase_two_three`), and it is the smallest slope in the range
`1 < a < b` of `hlhs`. -/
@[hjo "lem_mellit_lhs_slope_two_row"]
theorem lhsSlope_two_odd (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) : Mellit.LhsSlope q u 2 (2 * k + 1) := by
  intro f
  obtain ⟨R₀, hR₀⟩ := exists_forall_dminus_slopeOperator_two_odd hq0 hu0 hq1 hk f
  set T : ℕ := (Sym.plethShift q u f).natDegree + 1 with hTdef
  refine Eq.trans ?_ (congrArg (fun x => ((-1 : L) ^ (2 * k + 1 + 1)) • x)
    (hR₀ (max R₀ (k + 1 + T)) (le_max_left _ _)).symm)
  rw [qop_two_odd_apply hM hk f (T := T) (by omega)
      (le_trans (by omega) (le_max_right R₀ (k + 1 + T)))
      (by
        have : k + 1 + T ≤ max R₀ (k + 1 + T) := le_max_right _ _
        exact_mod_cast (by push_cast; omega : (k : ℤ) + 1 + (T : ℤ)
          ≤ ((max R₀ (k + 1 + T) : ℕ) : ℤ))),
    show ((-1 : L) ^ (2 * k + 1 + 1)) = 1 from by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring, pow_mul]; norm_num, one_smul]

/-! ### What the next family costs: `a = 3` is one `D` against this row -/

/-- `Split 3 (3j+1) = (1,j)` for `j ≥ 1`. -/
theorem split_three_of_mod_one {j : ℕ} (hj : 1 ≤ j) : Sym.Split 3 (3 * j + 1) = (1, j) :=
  Sym.split_eq_of_spec (by omega)
    ((Nat.prime_three.coprime_iff_not_dvd).2 (by omega)) le_rfl (by omega) hj (by omega) (by ring)

/-- `Split 3 (3j+2) = (2,2j+1)`. -/
theorem split_three_of_mod_two (j : ℕ) : Sym.Split 3 (3 * j + 2) = (2, 2 * j + 1) :=
  Sym.split_eq_of_spec (by omega)
    ((Nat.prime_three.coprime_iff_not_dvd).2 (by omega)) (by omega) (by omega) (by omega)
    (by omega) (by ring)

/-- **`Q_{3,3j+1} = M^{-1}[Q_{2,2j+1}, D_j]`.** The split of `(3,3j+1)` is `(1,j)`
(`HJO.Sweep.split_three_of_mod_one`), so the two halves of `HJO.Sym.Qop`'s recursion are the base
case `D_j` and the `(2,b)` row this file evaluates --- its complement `(2, 3j+1-j) = (2, 2j+1)` is
automatically of odd height, as it must be to be coprime.

**This is the precise statement of what `a = 3` costs**: one basic operator commuted past the
two-letter word `HJO.Sweep.qop_two_odd_apply` puts in closed form. No hypothesis on `q`, `u` or
`M`. -/
theorem qop_three_of_mod_one {j : ℕ} (hj : 1 ≤ j) :
    Sym.Qop q u 3 (3 * j + 1)
      = ((1 - q) * (1 - u))⁻¹ • (Sym.Qop q u 2 (2 * j + 1) * Sym.Dop q u j
          - Sym.Dop q u j * Sym.Qop q u 2 (2 * j + 1)) := by
  rw [Sym.qop_eq_qopPrim q u ((Nat.prime_three.coprime_iff_not_dvd).2 (by omega)),
    Sym.qopPrim_of_one_lt q u (3 * j + 1) (by omega), split_three_of_mod_one hj]
  simp only []
  rw [show 3 - 1 = 2 from rfl, show 3 * j + 1 - j = 2 * j + 1 from by omega,
    Sym.qopPrim_of_le_one q u j le_rfl,
    ← Sym.qop_eq_qopPrim q u ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega))]

/-- **`Q_{3,3j+2} = M^{-1}[D_{j+1}, Q_{2,2j+1}]`.** The other residue class: the split of
`(3,3j+2)` is `(2,2j+1)` (`HJO.Sweep.split_three_of_mod_two`), so the `(2,b)` row is now the split
rather than the complement and the complement `(1, 3j+2-(2j+1)) = (1,j+1)` is the base case. The
same cost, with the two factors interchanged. No hypothesis on `q`, `u` or `M`. -/
theorem qop_three_of_mod_two (j : ℕ) :
    Sym.Qop q u 3 (3 * j + 2)
      = ((1 - q) * (1 - u))⁻¹ • (Sym.Dop q u (j + 1) * Sym.Qop q u 2 (2 * j + 1)
          - Sym.Qop q u 2 (2 * j + 1) * Sym.Dop q u (j + 1)) := by
  rw [Sym.qop_eq_qopPrim q u ((Nat.prime_three.coprime_iff_not_dvd).2 (by omega)),
    Sym.qopPrim_of_one_lt q u (3 * j + 2) (by omega), split_three_of_mod_two j]
  simp only []
  rw [show 3 - 2 = 1 from rfl, show 3 * j + 2 - (2 * j + 1) = j + 1 from by omega,
    Sym.qopPrim_of_le_one q u (j + 1) le_rfl,
    ← Sym.qop_eq_qopPrim q u ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega))]

/-- Cross-check of the two split formulas against the values computed outright: at `j = 1` the first
is `HJO.Sym.split_three_four` (`HJO/Shuffle/MellitQopThreeFour.lean`, by `decide`), and at
`j = 1` the second is `Split 3 5 = (2,3)`. -/
theorem split_three_low : Sym.Split 3 4 = ((1 : ℕ), (1 : ℕ)) ∧ Sym.Split 3 5 = ((2 : ℕ), (3 : ℕ)) :=
  ⟨split_three_of_mod_one (j := 1) le_rfl, split_three_of_mod_two 1⟩

/-! ### Cross-check against the independently proved `(2,3)` instance -/

/-- **Cross-check: the row reproves the `(2,3)` base case at `f = 1`**
(`HJO.Mellit.lhsBase_two_three`), whose route is entirely different --- both sides evaluated to
`-e_1e_2 + (1-q-u)e_3` by exact expansion in degree three, against
`HJO.Sym.qop_two_three_apply_one`. The statement is written out here rather than cited, so that its
agreement with `HJO.Mellit.lhsBase_two_three` is what the kernel checks.

The `u ≠ 1` binder of `HJO.Mellit.lhsBase_two_three` is absent here only because `M ≠ 0` is taken
directly instead of being built from `q ≠ 1` and `u ≠ 1`: the two hypothesis sets are the same, and
this is **not** a strengthening. -/
theorem lhsBase_two_three_of_row (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) :
    (-1 : L) ^ (3 : ℕ) • Sym.Qop q u 2 3 (1 : Sym.Lambda L)
      = (-1 : L) ^ (2 - 1 : ℕ) •
        MvPolynomial.constantCoeff (Mellit.lowerRun q 1 (Mellit.stageWordTotal q u 2 3 [1])) :=
  Mellit.lhsBase_of_lhsSlope q u (lhsSlope_two_odd hM hq0 hu0 hq1 (k := 1) le_rfl)

/-- **The cross-check is a cross-check**: the two theorems are proofs of the *same* proposition, so
this `rfl` typechecks only if `HJO.Sweep.lhsBase_two_three_of_row` did not quietly restate
`HJO.Mellit.lhsBase_two_three`. -/
theorem lhsBase_two_three_of_row_eq (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0)
    (hq1 : q ≠ 1) (hu1 : u ≠ 1) :
    Mellit.lhsBase_two_three hq0 hu0 hq1 hu1 = lhsBase_two_three_of_row hM hq0 hu0 hq1 := rfl

end HJO.Sweep

end
