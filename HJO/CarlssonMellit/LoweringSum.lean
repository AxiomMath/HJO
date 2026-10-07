/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CharWordPartial
public import HJO.CarlssonMellit.ChiPrimeExpansion
public import HJO.CarlssonMellit.MuStep
public import HJO.CarlssonMellit.ZFirTelescope
public meta import HJO.Attr

/-! # Towards the lowering sum

`HJO.Dyck.IsLoweringSum` is the identity that Carlsson and Mellit's subsection "Lowering operator"
in Section 4 establishes; it is proved, as `HJO.Dyck.isLoweringSum`, in
`HJO/CarlssonMellit/LoweringSumClosed.lean`. This file carries out the parts of Carlsson and
Mellit's own argument that the files it imports already support, and names exactly what is left for
that later file.

## Main results

* `HJO.Dyck.isLoweringSum_of_isSigmaCharacter_dminusCM`: `HJO.Dyck.IsLoweringSum` is *equivalent* to
  the lowering recursion at the lower level. Its display is that of
  `HJO.Dyck.insertFront_partialCharSeries_identityTuple` with the scalar `(q-1)^{N-k+1}` in front,
  so its whole content is the character identity
  `ι_{k-1}(θ_{k-1}(d_-G)) = (q-1)^{N-k+1}ν_{Id_{k-1}}(π)` at the lower level.
* `HJO.Dyck.auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum`: Carlsson and Mellit's formula
  `χ'_{k,r}(π) = ∑_{i}f_{i,r}g_i(π)[X + y_k]` for every `r`, given the expansion of `χ'_{Id_k}(π)`
  at `r = 0`.
* `HJO.Dyck.one_sub_C_scalarFrac_mul_summableSum_unnormalisedCharSeries_lowerTuple`: the sum over
  the freed label, `(1-q)∑_{r ≥ 0}χ'_{k,r}(π) = ∑_{i}h_i[(1-q)(X+y_k)]g_i(π)[X+y_k]`, together with
  the monomialwise finiteness of the sum over `r`.
* `HJO.Dyck.exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries`: the
  display of Carlsson and Mellit immediately before their equation (4.15),
  `(1-q)·y_1 ⋯ y_{k-1}·Φ_{k-1}(ν_{Id_{k-1}}(π)) = ∑_{i}h_i[(1-q)(X+y_k)]g_i(π)[X+y_k]`. This is as
  far as their argument is carried here; the first display of their lowering computation enters it
  as `HJO.Dyck.insertFront_partialCharSeries_identityTuple`.
* `HJO.Dyck.dminusCM_eq_sum_of_qshiftNeg_eq`: half of Carlsson and Mellit's (4.16) —
  `HJO.Sweep.dminusCM` read on an expansion of `τ^-_{k,k}(G)` in powers of `y_k`,
  `d_-G = ∑_j(-1)^je_{j+1}F_j`.

`HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries_lowerTuple` and
`HJO.Dyck.isZDelta_zSwapCoeff_mul_realiseAddLetter` are the two halves of the induction proving
that formula, and
`HJO.Dyck.one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries_identityTuple` and its
primed form are the same identity with the alphabets carried as hypotheses.

## The hypothesis carried, and why

Carlsson and Mellit's argument rests on the unique expansion
`χ'_{Id_k}(π) = ∑_{j ≥ 1}y_k^jg_j(π)[X + y_k]` with `g_j(π) ∈ V_{k-1}`, which is
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`. Its uniqueness half,
`HJO.Dyck.eq_of_sum_pow_mul_realiseAddLetter_eq`, is proved in
`HJO/CarlssonMellit/ChiPrimeExpansion.lean`; its existence half needs more than a one-sentence
appeal, as explained there, and is proved only later, in
`HJO/CarlssonMellit/ChiPrimeExpansionExists.lean`. So the expansion is carried here as the
hypothesis `hexp` of `HJO.Dyck.auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum`, written with
`HJO.Dyck.realiseAddLetter` — the same spelling the uniqueness half uses, so that a proof of the
lemma discharges it with nothing to adapt.

## What the argument still owes

The step this file does not reach is Carlsson and Mellit's last, their equations (4.15) and (4.16)
and the comparison between them: that `∑_{i ≥ 0}-h_{i+1}[-X](χ_k(π)[X-(q-1)y_k]|_{y_k^i})` is
`d_-χ_k(π)`. Its two halves stand differently.

*The plethystic half is proved.* `h_{i+1}[-X] = (-1)^{i+1}e_{i+1}` is
`HJO.Sym.plethNegate_completeHomog`, which is the identity used in the final line of the argument.

*The bookkeeping half is where the gap is.* `HJO.Sweep.dminusCM` is `HJO.Sweep.lowerCoeffShift`
after `HJO.Sweep.qshiftNeg`, so it reads an expansion of `τ^-_{k,k}(G)` in powers of the *auxiliary
variable* `y_k` of `V_k`, on the monomial basis of `Λ[y]`; that reading is
`HJO.Dyck.dminusCM_eq_sum_of_qshiftNeg_eq` above. The `g_i(π)` are instead the coefficients of the
expansion of `χ'_{Id_k}(π)` in powers of the *distinguished letter* of the merged alphabet, read
through `HJO.Dyck.realiseAddLetter` — that is, after `ι_k` and after the substitution `X ↦ X + y_k`.
Nothing in this file identifies the two families, and Carlsson and Mellit's (4.16) is exactly that
identification. What it needs and what is not proved here: that `ι_k` and the extraction of a
`y_k`-coefficient commute on `V_k`, so that the `F_j` of the first expansion realise to the `c_j` of
`HJO.Sym.zPart`; and the passage from `X` to `X + y_k` and from `X` to `X - (q-1)y_k` under `θ`,
which is what turns the second expansion into the first. Both are supplied in
`HJO/CarlssonMellit/LoweringSumClosed.lean`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, arXiv:1508.06239v3, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 4, subsection "Lowering operator". The lemma
`HJO.Dyck.isLoweringSum`, using `HJO.Sweep.dminusCM`, `HJO.Sweep.theta`,
`HJO.Dyck.IsSigmaCharacter`, `HJO.Sym.insertFront`, `HJO.Dyck.lowerCharPiece`, `HJO.Sym.zSwapCoeff`
and `HJO.Sweep.addLetter`, and resting on `HJO.Dyck.isSummableFamily_zvar_mul_lowerCharPiece`,
`HJO.Dyck.isZDelta_zvar_mul_lowerCharPiece`, `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries`,
`HJO.Sym.isZDelta_mul_of_zSwap_eq`, `HJO.Sym.eq_of_isZDelta`,
`HJO.Dyck.realiseAddLetter_mem_zSymmSubring` and
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`.
-/

@[expose] public section

namespace HJO.Dyck

/-! ### The lowering sum is the lowering recursion at the lower level -/

section Reduction

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The display of `HJO.Dyck.isLoweringSum` is the character identity at the lower level.** Its
right-hand side is the scalar `(q-1)^{N-k+1}` times the right-hand side of
`HJO.Dyck.insertFront_partialCharSeries_identityTuple`, and `Φ_{k-1}` is `𝕜`-linear by
`HJO.Sym.insertFront_smul`; so the display follows from — and, `Φ_{k-1}` being injective on the
series of bounded front degree, is equivalent to — the statement that `d_-G` is an
`Id_{k-1}`-character of `π`.

This is the converse of `HJO.Dyck.isSigmaCharacter_dminusCM`, and together the two say that the
display of `HJO.Dyck.isLoweringSum` and `HJO.Dyck.isSigmaCharacter_dminusCM'` are the same
statement. -/
theorem insertFront_apply_theta_dminusCM_of_isSigmaCharacter (q : K) {m N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck (m + 1) N x)
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m} {G : Sweep.Total K}
    (h : IsSigmaCharacter q m ι x (identityTuple m) (Sweep.dminusCM q (m + 1) G)) :
    Sym.insertFront K m (ι (Sweep.theta q (Sweep.dminusCM q (m + 1) G))) =
      (q - 1) ^ (N - m) • Sym.summableSum
        fun r : ℕ => Sym.zvar K (m + 1) (m + r) * lowerCharPiece q m x r := by
  rw [IsSigmaCharacter] at h
  rw [h, Sym.insertFront_smul, insertFront_partialCharSeries_identityTuple q hx]

/-- **`HJO.Dyck.isLoweringSum` reduces to the lowering recursion.** If `d_-G` is an
`Id_{k-1}`-character of `π` at every instance the character recursion reads, then
`HJO.Dyck.IsLoweringSum` holds — so the hypothesis `HJO.Dyck.IsLoweringSum` of
`HJO.Dyck.mem_piece_and_isSigmaCharacter_partialWordOp` and of
`HJO.Dyck.realisation_constantCoeff_markedWordOp'` can be discharged by proving the lowering
recursion directly, without going through the displayed sum. -/
theorem isLoweringSum_of_isSigmaCharacter_dminusCM {q : K}
    (h : ∀ (m N : ℕ) (x : Fin N → ℕ), IsPartialDyck (m + 1) N x →
      ∀ ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K m, IsAuxRealisation m ι →
        ∀ ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1), IsAuxRealisation (m + 1) ι' →
          ∀ G ∈ Sweep.piece K (m + 1),
            IsSigmaCharacter q (m + 1) ι' x (identityTuple (m + 1)) G →
              IsSigmaCharacter q m ι x (identityTuple m) (Sweep.dminusCM q (m + 1) G)) :
    IsLoweringSum q := fun m N x hx ι hι ι' hι' G hG hchar =>
  insertFront_apply_theta_dminusCM_of_isSigmaCharacter q hx
    (h m N x hx ι hι ι' hι' G hG hchar)

end Reduction

/-! ### The freed characteristic series in terms of the expansion coefficients -/

section Step

variable {K : Type*} [CommRing K] [IsDomain K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **The freed characteristic series satisfy the equation of `HJO.Sym.IsZDelta`**:
`χ'_{σ^{[r+1]}}(π) = Δ_{k+r}(χ'_{σ^{[r]}}(π))`. This is
`HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries` at the lower tuple `σ^{[r]}`, whose hypotheses
are `HJO.Dyck.lowerTuple_injective`, the occurrence of the entry `k + r` at the last position, and
the vacuity of the ordering condition — no entry of `σ^{[r]}` equals `k + r + 1`, the earlier
entries being the labels `0, …, k-2`. -/
theorem isZDelta_auxToFrac_unnormalisedCharSeries_lowerTuple (q : K)
    (hx : IsPartialDyck (m + 1) N x) (r : ℕ) :
    Sym.IsZDelta q r
      (Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r)))
      (Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m (r + 1)))) := by
  have hb : ∀ b : Fin (m + 1), lowerTuple m r b ≠ m + r + 1 := by
    intro b
    induction b using Fin.lastCases with
    | last => rw [lowerTuple_last]; omega
    | cast j =>
      rw [lowerTuple_castSucc]
      have hj := j.isLt
      omega
  have h := isZDelta_auxToFrac_unnormalisedCharSeries (r := r) q hx (lowerTuple_injective m r)
    ⟨Fin.last m, lowerTuple_last m r⟩ fun a b _ hbb => absurd hbb (hb b)
  rwa [transposeTuple_lowerTuple] at h

/-- **Each term of the expansion satisfies the equation of `HJO.Sym.IsZDelta`**: with
`G_i = g_i(π)[X + y_k]` symmetric in the whole merged alphabet, `Δ_{k+r}(f_{i,r}G_i)` is
`f_{i,r+1}G_i`.

This is the step Carlsson and Mellit describe as "the extra symmetry in the `y_k` variable is used
to pass `Δ_{y_k,x_1}` by multiplication by `g_i(π)[X + y_k]`": `HJO.Sym.isZDelta_mul_of_zSwap_eq`
moves the coefficient through, and what makes its hypothesis hold is
`HJO.Dyck.realiseAddLetter_mem_zSymmSubring`. -/
theorem isZDelta_zSwapCoeff_mul_realiseAddLetter (q : K) (hι : IsAuxRealisation (m + 1) ι)
    {g : Sweep.Total K} (hg : g ∈ Sweep.piece K m) (i r : ℕ) :
    Sym.IsZDelta q r (Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι g)
      (Sym.zSwapCoeff K m q i (r + 1) * realiseAddLetter K m ι g) := by
  have hsymm := realiseAddLetter_mem_zSymmSubring hι hg
  have hfix := Sym.zSymmSubring_le_zSwapFixedSubring K m r hsymm
  have h := Sym.isZDelta_mul_of_zSwap_eq
    (Sym.zGraded_subset_zRing K m i (Sym.zSwapCoeff_mem_zGraded q i r)) hfix.1 hfix.2
    (Sym.isZDelta_zSwapCoeff q i r)
  rwa [mul_comm (realiseAddLetter K m ι g), mul_comm (realiseAddLetter K m ι g)] at h

/-- **The freed characteristic series in terms of the expansion coefficients**: for every `r ≥ 0`

`χ'_{k,r}(π) = ∑_{i}f_{i,r}g_i(π)[X + y_k]`,

with `f_{i,r}` the iterated swapping coefficients of `HJO.Sym.zSwapCoeff` and
`g_i(π)[X + y_k]` the realised expansion coefficients of `HJO.Dyck.realiseAddLetter`.

The hypothesis `hexp` is the `r = 0` case, which is
`HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`: `f_{i,0} = y_k^i` by
`HJO.Sym.zSwapCoeff_zero` and `σ^{[0]} = Id_k` by `HJO.Dyck.lowerTuple_zero`. Its existence half is
proved only in a later file — see this module's header — so it is carried here as a hypothesis
rather than used.

The induction is Carlsson and Mellit's: both sides satisfy the equation of `HJO.Sym.IsZDelta` at the
step from `r` to `r + 1`, the left by `HJO.Dyck.isZDelta_auxToFrac_unnormalisedCharSeries` at the
lower tuple and the right term by term by `HJO.Sym.isZDelta_mul_of_zSwap_eq` over
`HJO.Sym.isZDelta_summableSum` for finite sums, so `HJO.Sym.eq_of_isZDelta` identifies the two
successors. -/
theorem auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum (q : K)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) {s : Finset ℕ}
    {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ s, g i ∈ Sweep.piece K m)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ s, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i))
    (r : ℕ) :
    Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r))
      = ∑ i ∈ s, Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i) := by
  induction r with
  | zero =>
    rw [lowerTuple_zero, hexp]
    exact Finset.sum_congr rfl fun i _ => by rw [Sym.zSwapCoeff_zero]
  | succ r ih =>
    refine Sym.eq_of_isZDelta (q := q) (r := r)
      (F := ∑ i ∈ s, Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i)) ?_ ?_
    · rw [← ih]
      exact isZDelta_auxToFrac_unnormalisedCharSeries_lowerTuple q hx r
    · refine Sym.isZDelta_sum (fun i hi => Sym.mul_mem_zRing
        (Sym.zGraded_subset_zRing K m i (Sym.zSwapCoeff_mem_zGraded q i r))
        (realiseAddLetter_mem_zRing hι (hg i hi))) fun i hi => ?_
      exact isZDelta_zSwapCoeff_mul_realiseAddLetter q hι (hg i hi) i r

end Step

/-! ### Finite sums of monomialwise finite families -/

section FinsetSum

variable {I σ R J : Type*} [CommSemiring R] {F : J → I → MvPowerSeries σ R}

/-- The family that is `0` at every index is monomialwise finite. -/
private theorem isSummableFamily_zero :
    Sym.IsSummableFamily (fun _ : I => (0 : MvPowerSeries σ R)) :=
  Sym.isSummableFamily_iff.2 fun e =>
    Set.Finite.subset Set.finite_empty fun _ hl =>
      absurd (map_zero (MvPowerSeries.coeff (σ := σ) (R := R) e)) hl

/-- The sum of the family that is `0` at every index is `0`. -/
private theorem summableSum_zero :
    Sym.summableSum (fun _ : I => (0 : MvPowerSeries σ R)) = 0 :=
  MvPowerSeries.ext fun e => by rw [Sym.coeff_summableSum]; simp

/-- A finite sum of monomialwise finite families is monomialwise finite. -/
private theorem isSummableFamily_finset_sum : ∀ (t : Finset J),
    (∀ j ∈ t, Sym.IsSummableFamily (F j)) → Sym.IsSummableFamily fun l => ∑ j ∈ t, F j l := by
  classical
  intro t
  induction t using Finset.cons_induction with
  | empty => exact fun _ => by simpa using isSummableFamily_zero
  | cons a v ha ih =>
    intro h
    rw [show (fun l => ∑ j ∈ Finset.cons a v ha, F j l) = fun l => F a l + ∑ j ∈ v, F j l from
      funext fun l => Finset.sum_cons ..]
    exact Sym.isSummableFamily_add (h a (Finset.mem_cons_self ..))
      (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

/-- **A finite sum of monomialwise finite families may be summed in either order.** The lemma
`HJO.Sym.isZDelta_summableSum` is the corresponding statement for the swapping operator; this is the
bare exchange of a `Finset` sum with a `HJO.Sym.summableSum`, and it belongs in
`HJO/CarlssonMellit/ZDeltaSums.lean` beside `HJO.Sym.summableSum_add`. -/
private theorem summableSum_finset_sum : ∀ (t : Finset J),
    (∀ j ∈ t, Sym.IsSummableFamily (F j)) →
      Sym.summableSum (fun l => ∑ j ∈ t, F j l) = ∑ j ∈ t, Sym.summableSum (F j) := by
  classical
  intro t
  induction t using Finset.cons_induction with
  | empty => exact fun _ => by simpa using summableSum_zero
  | cons a v ha ih =>
    intro h
    rw [show (fun l => ∑ j ∈ Finset.cons a v ha, F j l) = fun l => F a l + ∑ j ∈ v, F j l from
      funext fun l => Finset.sum_cons .., Finset.sum_cons,
      ← ih fun j hj => h j (Finset.mem_cons_of_mem hj),
      Sym.summableSum_add (h a (Finset.mem_cons_self ..))
        (isSummableFamily_finset_sum v fun j hj => h j (Finset.mem_cons_of_mem hj))]

end FinsetSum

/-! ### Summing the pieces over the freed label -/

section Telescope

variable {K : Type*} [CommRing K] [IsDomain K] {m N : ℕ} {x : Fin N → ℕ}
  {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (m + 1)}

/-- **The sum of the freed characteristic series over the freed label**:

`(1-q)∑_{r ≥ 0}χ'_{k,r}(π) = ∑_{i}h_i[(1-q)(X + y_k)]·g_i(π)[X + y_k]`,

the sum over `r` being monomialwise finite. This is Carlsson and Mellit's

`χ'_{k-1}(Nπ)[X + y_k] = (1-q)^{-1}∑_{i ≥ 1}h_i[(1-q)(X+y_k)]g_i(π)[X+y_k]`

with the division by `1-q` not performed — `1-q` is not a unit of `P°_{k+1}` — exactly as
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` states their equation (4.14).

The proof is Carlsson and Mellit's: `HJO.Dyck.auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum`
replaces each piece by `∑_i f_{i,r}g_i(π)[X+y_k]`, the finite sum over `i` and the monomialwise sum
over `r` are exchanged, the coefficients `g_i(π)[X+y_k]` come out of the sum over `r`, and
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff` evaluates `∑_{r ≥ 0}f_{i,r}` one index `i`
at a time.

The alphabets are hypotheses, as in `HJO.Sym.zSwapCoeff_succ_eq_mul_completeHomog` and
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`: `Φ_t` is `(1-q)X_{t-1} + z_t`, `Ψ_t` is
`(1-q)X_{t-1}` and `Λ` is `(1-q)(X + y_k)`, and
`HJO.Sym.exists_ringHom_powerSum_eq_truncTwist_add_letter`,
`HJO.Sym.exists_ringHom_powerSum_eq_truncTwist` and `HJO.Sym.exists_ringHom_powerSum_eq_fullTwist`
say that all three exist. `hu` is Carlsson and Mellit's `j ≥ 1`: the expansion has no constant term,
which is `HJO.Dyck.zPart_auxToFrac_unnormalisedCharSeries_identityTuple_zero`. -/
theorem one_sub_C_scalarFrac_mul_summableSum_unnormalisedCharSeries_lowerTuple
    {A : Type*} [CommRing A] [Algebra ℚ A] (q : K) {base : A →+* Sym.AuxFrac K m}
    {Φ Ψ : ℕ → Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    {Λ : Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ Sym.zSymmSubring K m)
    (hΦp : ∀ t j : ℕ, 0 < j → Φ t (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * (∑ b ∈ Finset.range t, Sym.zLetterSeries K m b ^ j) + Sym.zLetterSeries K m t ^ j)
    (hΨC : ∀ (t : ℕ) (a : A), Ψ t (MvPolynomial.C a)
      = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a)))
    (hΨp : ∀ t j : ℕ, 0 < j → Ψ t (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * ∑ b ∈ Finset.range t, Sym.zLetterSeries K m b ^ j)
    (hΛC : ∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a)))
    (hΛp : ∀ j : ℕ, 0 < j → Λ (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) {u : Finset ℕ}
    {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m) (hu : (0 : ℕ) ∉ u)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    (Sym.IsSummableFamily fun r : ℕ => Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (lowerTuple m r))) ∧
      (1 - MvPowerSeries.C (Sym.scalarFrac K q)) * Sym.summableSum (fun r : ℕ =>
          Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r)))
        = ∑ i ∈ u, Λ (Sym.completeHomog A i) * realiseAddLetter K m ι (g i) := by
  have hcomm : ∀ i : ℕ,
      (fun r : ℕ => Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i))
        = fun r : ℕ => realiseAddLetter K m ι (g i) * Sym.zSwapCoeff K m q i r :=
    fun i => funext fun r => mul_comm _ _
  have hne : ∀ i ∈ u, ∃ n, i = n + 1 := fun i hi =>
    ⟨i - 1, by rcases Nat.eq_zero_or_pos i with rfl | hpos; exacts [absurd hi hu, by omega]⟩
  have hsummable : ∀ i ∈ u, Sym.IsSummableFamily
      fun r : ℕ => Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i) := by
    intro i hi
    obtain ⟨n, rfl⟩ := hne i hi
    rw [hcomm]
    exact Sym.isSummableFamily_mul_left (Sym.isSummableFamily_zSwapCoeff hΦC hΦp n) _
  rw [show (fun r : ℕ => Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (lowerTuple m r)))
      = fun r : ℕ => ∑ i ∈ u, Sym.zSwapCoeff K m q i r * realiseAddLetter K m ι (g i) from
    funext (auxToFrac_unnormalisedCharSeries_lowerTuple_eq_sum q hx hι hg hexp)]
  refine ⟨isSummableFamily_finset_sum u hsummable, ?_⟩
  rw [summableSum_finset_sum u hsummable, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨n, rfl⟩ := hne i hi
  rw [hcomm, ← Sym.mul_summableSum (Sym.isSummableFamily_zSwapCoeff hΦC hΦp n), mul_left_comm,
    (Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff hΦC hΦp hΨC hΨp hΛC hΛp n).2, mul_comm]

omit [IsDomain K] in
/-- Pushing a monomialwise finite sum into `P°_{k+1}`: `auxToFrac` acts coefficientwise, so it
commutes with `HJO.Sym.summableSum`. -/
private theorem auxToFrac_summableSum {I : Type*} {k : ℕ} {F : I → Sym.AuxAlphabetSeries K k}
    (hF : Sym.IsSummableFamily F) :
    Sym.auxToFrac K k (Sym.summableSum F) = Sym.summableSum fun l => Sym.auxToFrac K k (F l) :=
  Sym.map_summableSum hF
    (algebraMap (MvPolynomial (Fin k) K) (Sym.AuxFrac K k)).toAddMonoidHom
    (Sym.coeff_auxToFrac k)

/-- **The display of Carlsson and Mellit immediately before their equation (4.15)**: for a partial
Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1`,

`(1-q)·y_1 ⋯ y_{k-1}·Φ_{k-1}(ν_{Id_{k-1}}(π)) = ∑_{i}h_i[(1-q)(X+y_k)]·g_i(π)[X+y_k]`,

which is their

`χ'_{k-1}(Nπ)[X + y_k] = (1-q)^{-1}∑_{i ≥ 1}h_i[(1-q)(X+y_k)]g_i(π)[X+y_k]`

with the division by `1-q` written as a product, as in
`HJO.Sym.one_sub_C_scalarFrac_mul_summableSum_zSwapCoeff`, and with the normalisation of
`HJO.Dyck.partialCharSeries` in place of their unnormalised `χ'` — the prescribed factor
`y_1 ⋯ y_{k-1}` of `HJO.Dyck.unnormalisedCharSeries_lowerTuple` appearing explicitly.

The first display of their lowering computation, `χ'_{k-1}(Nπ)[X+y_k] = ∑_{r ≥ 0}χ'_{k,r}(π)`,
enters here as `HJO.Dyck.insertFront_partialCharSeries_identityTuple`, which is that step in the
normalisation of `HJO.Dyck.lowerCharPiece`; `HJO.Dyck.unnormalisedCharSeries_lowerTuple` restores
the prescribed factor, and
`HJO.Dyck.one_sub_C_scalarFrac_mul_summableSum_unnormalisedCharSeries_lowerTuple` is the rest. -/
theorem one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries_identityTuple
    {A : Type*} [CommRing A] [Algebra ℚ A] (q : K) {base : A →+* Sym.AuxFrac K m}
    {Φ Ψ : ℕ → Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    {Λ : Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    (hΦC : ∀ a : A, Φ 0 (MvPolynomial.C a) ∈ Sym.zSymmSubring K m)
    (hΦp : ∀ t j : ℕ, 0 < j → Φ t (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * (∑ b ∈ Finset.range t, Sym.zLetterSeries K m b ^ j) + Sym.zLetterSeries K m t ^ j)
    (hΨC : ∀ (t : ℕ) (a : A), Ψ t (MvPolynomial.C a)
      = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a)))
    (hΨp : ∀ t j : ℕ, 0 < j → Ψ t (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * ∑ b ∈ Finset.range t, Sym.zLetterSeries K m b ^ j)
    (hΛC : ∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a)))
    (hΛp : ∀ j : ℕ, 0 < j → Λ (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) {u : Finset ℕ}
    {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m) (hu : (0 : ℕ) ∉ u)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    (1 - MvPowerSeries.C (Sym.scalarFrac K q))
        * (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
          * Sym.auxToFrac K (m + 1)
              (Sym.insertFront K m (partialCharSeries q m x (identityTuple m))))
      = ∑ i ∈ u, Λ (Sym.completeHomog A i) * realiseAddLetter K m ι (g i) := by
  have hsum0 := isSummableFamily_zvar_mul_lowerCharPiece q m x
  have hsum1 : Sym.IsSummableFamily fun r : ℕ =>
      Sym.auxToFrac K (m + 1) (Sym.zvar K (m + 1) (m + r) * lowerCharPiece q m x r) :=
    hsum0.map (algebraMap (MvPolynomial (Fin (m + 1)) K) (Sym.AuxFrac K (m + 1))).toAddMonoidHom
      (Sym.coeff_auxToFrac (m + 1))
  have hfac : (fun r : ℕ =>
        Sym.auxToFrac K (m + 1) (unnormalisedCharSeries q (m + 1) x (lowerTuple m r)))
      = fun r : ℕ => MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
        * Sym.auxToFrac K (m + 1) (Sym.zvar K (m + 1) (m + r) * lowerCharPiece q m x r) :=
    funext fun r => by
      rw [unnormalisedCharSeries_lowerTuple hx.le_length, mul_assoc, map_mul,
        auxToFrac_C_prod_X_castSucc]
  rw [insertFront_partialCharSeries_identityTuple q hx, auxToFrac_summableSum hsum0,
    Sym.mul_summableSum hsum1, ← hfac]
  exact (one_sub_C_scalarFrac_mul_summableSum_unnormalisedCharSeries_lowerTuple q hΦC hΦp hΨC hΨp
    hΛC hΛp hx hι hg hu hexp).2

/-- **The same with every alphabet but `(1-q)(X + y_k)` discharged.** The truncated alphabets
`Φ_t = (1-q)X_{t-1} + z_t` and `Ψ_t = (1-q)X_{t-1}` are internal to the telescoping, so they are
produced here from `HJO.Sym.exists_ringHom_powerSum_eq_truncTwist_add_letter` and
`HJO.Sym.exists_ringHom_powerSum_eq_truncTwist` rather than carried; what remains is the alphabet
`(1-q)(X + y_k)` the statement names, which `HJO.Sym.exists_ringHom_powerSum_eq_fullTwist` supplies
and `HJO.Dyck.exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries`
discharges as well. -/
theorem one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries_identityTuple'
    {A : Type*} [CommRing A] [Algebra ℚ A] (q : K) {base : A →+* Sym.AuxFrac K m}
    {Λ : Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1)}
    (hΛC : ∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a)))
    (hΛp : ∀ j : ℕ, 0 < j → Λ (Sym.powerSum A j)
      = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
          * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) {u : Finset ℕ}
    {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m) (hu : (0 : ℕ) ∉ u)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    (1 - MvPowerSeries.C (Sym.scalarFrac K q))
        * (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
          * Sym.auxToFrac K (m + 1)
              (Sym.insertFront K m (partialCharSeries q m x (identityTuple m))))
      = ∑ i ∈ u, Λ (Sym.completeHomog A i) * realiseAddLetter K m ι (g i) := by
  obtain ⟨Φ, hΦC, hΦp⟩ := Sym.exists_ringHom_powerSum_eq_truncTwist_add_letter (A := A) q base
  obtain ⟨Ψ, hΨC, hΨp⟩ := Sym.exists_ringHom_powerSum_eq_truncTwist (A := A) q base
  exact one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries_identityTuple q
    (fun a => Sym.mem_zSymmSubring_of_eq_C_auxFracCastSucc (hΦC 0) a) hΦp hΨC hΨp hΛC hΛp hx hι
    hg hu hexp

/-- **Carlsson and Mellit's display before (4.15), with no alphabet carried.** The alphabet
`(1-q)(X + y_k)` exists by `HJO.Sym.exists_ringHom_powerSum_eq_fullTwist`, so the identity can be
stated as an existence statement: for a partial Dyck path `π ∈ 𝔻_{k,N}` of level `k = m + 1` whose
`χ'_{Id_k}(π)` expands as `∑_{i ≥ 1}y_k^ig_i(π)[X+y_k]`,

`(1-q)·y_1 ⋯ y_{k-1}·Φ_{k-1}(ν_{Id_{k-1}}(π)) = ∑_{i}h_i[(1-q)(X+y_k)]·g_i(π)[X+y_k]`.

This is the last display of their subsection "Lowering operator" before their equation (4.15), and
it is as far as their argument is carried here. What is left is the comparison of this with
`HJO.Sweep.dminusCM`; see this module's header. -/
theorem exists_ringHom_one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries
    {A : Type*} [CommRing A] [Algebra ℚ A] (q : K) (base : A →+* Sym.AuxFrac K m)
    (hx : IsPartialDyck (m + 1) N x) (hι : IsAuxRealisation (m + 1) ι) {u : Finset ℕ}
    {g : ℕ → Sweep.Total K} (hg : ∀ i ∈ u, g i ∈ Sweep.piece K m) (hu : (0 : ℕ) ∉ u)
    (hexp : Sym.auxToFrac K (m + 1)
        (unnormalisedCharSeries q (m + 1) x (identityTuple (m + 1)))
      = ∑ i ∈ u, MvPowerSeries.C (Sym.yFrac K (Fin.last m)) ^ i * realiseAddLetter K m ι (g i)) :
    ∃ Λ : Sym.Lambda A →+* Sym.AuxAlphabetSeriesFrac K (m + 1),
      (∀ a : A, Λ (MvPolynomial.C a) = MvPowerSeries.C (Sym.auxFracCastSucc K m (base a))) ∧
        (∀ j : ℕ, 0 < j → Λ (Sym.powerSum A j)
          = (1 - MvPowerSeries.C (Sym.scalarFrac K q) ^ j)
              * Sym.summableSum fun b => Sym.zLetterSeries K m b ^ j) ∧
          (1 - MvPowerSeries.C (Sym.scalarFrac K q))
              * (MvPowerSeries.C (Sym.auxFracCastSucc K m (lowerAuxScalar K m))
                * Sym.auxToFrac K (m + 1)
                    (Sym.insertFront K m (partialCharSeries q m x (identityTuple m))))
            = ∑ i ∈ u, Λ (Sym.completeHomog A i) * realiseAddLetter K m ι (g i) := by
  obtain ⟨Λ, hΛC, hΛp⟩ := Sym.exists_ringHom_powerSum_eq_fullTwist (A := A) q base
  exact ⟨Λ, hΛC, hΛp,
    one_sub_C_scalarFrac_mul_auxToFrac_insertFront_partialCharSeries_identityTuple'
      q hΛC hΛp hx hι hg hu hexp⟩

end Telescope

/-! ### How `d_-` reads an expansion in the last auxiliary variable -/

section Dminus

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
/-- A monomial occurring in an element of `V_k` does not use the variable `y_{k+1}`. -/
private theorem coeff_eq_zero_of_mem_piece {m : ℕ} {F : Sweep.Total K}
    (hF : F ∈ Sweep.piece K m) {d : ℕ →₀ ℕ} (hd : d m ≠ 0) : MvPolynomial.coeff d F = 0 := by
  rw [Sweep.piece, MvPolynomial.mem_supported] at hF
  by_contra hc
  exact absurd (hF ((MvPolynomial.mem_vars_iff_mem_support m).2
    ⟨d, MvPolynomial.mem_support_iff.2 hc, Finsupp.mem_support_iff.2 hd⟩)) (lt_irrefl m)

/-- **The coefficient extraction of `HJO.Sweep.dminusCM` on one term of an expansion in `y_{k+1}`**:
for `F ∈ V_k`, free of `y_{k+1}`, the operator `HJO.Sweep.lowerCoeffShift` carries `Fy_{k+1}^j` to
`(-1)^je_{j+1}F`.

The operator is `Λ`-linear and is prescribed on the monomial basis of `Λ[y]`, so the statement is
read off one monomial of `F` at a time: multiplying by `y_{k+1}^j` raises the exponent there from
`0` to `j`, the sign and the elementary function are the same for every monomial of `F`, and
deleting that exponent returns the monomial. -/
theorem lowerCoeffShift_mul_pow_of_mem_piece {m : ℕ} {F : Sweep.Total K}
    (hF : F ∈ Sweep.piece K m) (j : ℕ) :
    Sweep.lowerCoeffShift K m (F * (MvPolynomial.X m : Sweep.Total K) ^ j)
      = (-1 : Sweep.Total K) ^ j * MvPolynomial.C (Sym.elemSymm K (j + 1)) * F := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [Finset.sum_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d m = 0 := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hd (coeff_eq_zero_of_mem_piece hF h)
  have hpow : ((MvPolynomial.X m : Sweep.Total K)) ^ j
      = MvPolynomial.monomial (Finsupp.single m j) 1 := MvPolynomial.X_pow_eq_monomial
  have hmul : MvPolynomial.monomial d (MvPolynomial.coeff d F)
        * (MvPolynomial.X m : Sweep.Total K) ^ j
      = MvPolynomial.coeff d F •
          MvPolynomial.monomial (d + Finsupp.single m j) (1 : Sym.Lambda K) := by
    rw [hpow, MvPolynomial.monomial_mul, MvPolynomial.smul_monomial, smul_eq_mul]
  have hval : (d + Finsupp.single m j) m = j := by
    rw [Finsupp.add_apply, hdm, Finsupp.single_eq_same, zero_add]
  have herase : Finsupp.erase m (d + Finsupp.single m j) = d := by
    refine Finsupp.ext fun a => ?_
    rcases eq_or_ne a m with rfl | ha
    · rw [Finsupp.erase_same, hdm]
    · rw [Finsupp.erase_ne ha, Finsupp.add_apply, Finsupp.single_eq_of_ne ha, add_zero]
  rw [hmul, map_smul, Sweep.lowerCoeffShift_monomial, hval, herase,
    show MvPolynomial.monomial d (MvPolynomial.coeff d F)
        = MvPolynomial.coeff d F • MvPolynomial.monomial d (1 : Sym.Lambda K) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], mul_smul_comm]

/-- **`HJO.Sweep.dminusCM` on an expansion in the last auxiliary variable**: if
`τ^-_{k,k}(G) = ∑_jF_jy_k^j` with every `F_j ∈ V_{k-1}`, then `d_-G = ∑_j(-1)^je_{j+1}F_j`.

This is `HJO.Sweep.dminusCM` read off its definition, stated for an expansion supplied from
outside rather than constructed: `HJO.Sweep.dminusCM` is `HJO.Sweep.lowerCoeffShift` after
`HJO.Sweep.qshiftNeg`, and the former is prescribed on the monomial basis. It is one of the two
things Carlsson and Mellit's equation (4.16) needs; the other, an identification of the `F_j` with
the expansion coefficients `g_j(π)` of `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter`, is
not proved here — see this module's header. -/
theorem dminusCM_eq_sum_of_qshiftNeg_eq (q : K) {m : ℕ} {G : Sweep.Total K} {t : Finset ℕ}
    {F : ℕ → Sweep.Total K} (hF : ∀ j ∈ t, F j ∈ Sweep.piece K m)
    (h : Sweep.qshiftNeg q (m + 1) G
      = ∑ j ∈ t, F j * (MvPolynomial.X m : Sweep.Total K) ^ j) :
    Sweep.dminusCM q (m + 1) G
      = ∑ j ∈ t, (-1 : Sweep.Total K) ^ j * MvPolynomial.C (Sym.elemSymm K (j + 1)) * F j := by
  have hd : Sweep.dminusCM q (m + 1) G
      = Sweep.lowerCoeffShift K m (Sweep.qshiftNeg q (m + 1) G) := by
    rw [Sweep.dminusCM, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.restrictScalars_apply, Nat.add_sub_cancel]
  rw [hd, h, map_sum]
  exact Finset.sum_congr rfl fun j hj => lowerCoeffShift_mul_pow_of_mem_piece (hF j hj) j

end Dminus

end HJO.Dyck
