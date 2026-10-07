/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.Superization
public import HJO.CarlssonMellit.SuperGesselSum
public import HJO.CarlssonMellit.NuZeroLevel
public import HJO.CarlssonMellit.CharSeriesLift
public import HJO.CarlssonMellit.ThetaBijective
public meta import HJO.Attr

/-! # The no-attack specialisation, and the level-zero characters

Carlsson and Mellit's Proposition 3.5 says that the characteristic series of a Dyck path, plethysed
by `(q-1)X`, collapses onto the labellings that give distinct letters to the two positions of every
attacking pair:

`ι(θ₀(f)) = (q-1)^{n}ν_σ(π)` whenever `ι(f) = χ(π)` and `σ` is the empty tuple.

That is `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries`, and read through
`HJO.Dyck.IsSigmaCharacter` it says exactly that such an `f` is a `σ`-character of `π` at level `0`.
Its converse-in-practice, `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`, says that a
level-zero `σ`-character is unique and is the lift of `χ(π)`: the character equation pins `θ₀(G)` up
to nothing, and `θ₀` and `ι` are both injective.

The route has three steps, of which the first two are already proved elsewhere.

* `HJO.ParkingFunctions.realisation_thetaLambda_of_eq_charSeries`, proved here: the fundamental
  expansion `HJO.Dyck.charSeries_eq_sum_gessel` of `χ(R,n)` is carried by the superization formula
  `HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` to an expansion in the super
  fundamentals, and `HJO.Dyck.sum_pow_invNumber_smul_superFundamental` collapses that to the single
  sum `∑_{v ∈ 𝒜^n}q^{inv^±(R,v)}z_v`.
* `HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` evaluates that sum as `(q-1)^{n}`
  times the no-attack sum.
* `HJO.Dyck.auxZeroMap_partialCharSeries_zero` identifies the no-attack sum with `ν_σ(π)` at
  level `0`.

## Main results

* `HJO.ParkingFunctions.realisation_thetaLambda_of_eq_charSeries`.
* `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries`.
* `HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter`.

## Implementation notes

*`HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` is stated as `HJO.Dyck.IsSigmaCharacter`, which is
the displayed equation and nothing more.* `HJO.Dyck.IsSigmaCharacter` is that equation at level `k`,
and at `k = 0` its exponent `N - k` is `n`; so the conclusion and the character predicate are the
same proposition, and stating it as the predicate is what lets
`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` consume it against its own hypothesis
without an intermediate rewrite.

*The level-zero bookkeeping is `HJO.Dyck.auxZeroMap`, and only its injectivity is used.* The
character equation lives in `P_0`, the super expansion in `𝒫`; the two are the same ring with the
coefficients spelt differently, so the proof of `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries`
transports the computation back through `HJO.Dyck.auxZeroMap_injective`.

*The separate `n = 0` case in `HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` is not needed.* It
exists there because `HJO.ParkingFunctions.realisation_thetaLambda_of_eq_charSeries` is stated at
`n ≥ 1`; none of the lemmas this file consumes carries that hypothesis —
`HJO.Dyck.charSeries_eq_sum_gessel`,
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel`,
`HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` and
`HJO.Dyck.sum_pow_invNumber_smul_superFundamental` are each stated at every `n` — so the proof is
uniform, and at `n = 0` it is the content of `HJO.Dyck.isSigmaCharacter_one_of_isEmpty` reproved.

*`HJO.Dyck.auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter` carries the genericity of `q` that
`HJO.Sweep.theta_bijOn_piece` needs*, in the form `IsUnit (q^{r+1} - 1)` rather than the `q^r ≠ 1`:
over the base field `𝕜 = ℚ(q,u)` the two agree, and the unit form is what the injectivity of `θ` is
actually proved from. It also carries `Field` and `CharZero`, which
`HJO.Dyck.exists_iota_eq_pathCharSeries` needs to produce the lift of `χ(π)`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer.
Math. Soc. **31** (2018) 661--697, Proposition 3.5 and Section 4.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

open HJO.Sym HJO.Dyck

/-- **The super expansion of the characteristic series.** For a set `R` of
increasing pairs of positions of `{1, …, n}` and `f ∈ Λ` with `ι(f) = χ(R,n)`,

`ι(θ₀(f)) = ∑_{v ∈ 𝒜^n}q^{inv^±(R,v)}z_v`.

`HJO.Dyck.charSeries_eq_sum_gessel` expands `ι(f)` in the fundamentals over the permutations of the
positions, weighted by `q^{inv(R,σ)}`;
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` replaces each fundamental by its
super counterpart, the descent sets lying in the window by `HJO.Sym.invDescentSet_subset_Ico` and
`f` being homogeneous of degree `n` by `HJO.Sym.mem_lambdaComp_of_coeff_iota`; and
`HJO.Dyck.sum_pow_invNumber_smul_superFundamental` is that combination read as one sum over `𝒜^n`.

The `n ≥ 1` and its hypothesis that `R` be *transitive* are both unused: only the
containment in the window enters, through `HJO.Dyck.charSeries_eq_sum_gessel` and
`HJO.Dyck.superInvSet_eq_invSet_superStd`. -/
@[hjo "lem_cm_super_expansion"]
theorem realisation_thetaLambda_of_eq_charSeries {K : Type*} [CommRing K] [Algebra ℚ K] [CharZero K]
    [NoZeroDivisors K] {ι : Lambda K →ₐ[K] AlphabetSeries K} (hι : IsRealisation ι) (q : K) {n : ℕ}
    {R : Finset (ℕ × ℕ)} (hR : ∀ p ∈ R, p.1 < p.2) {f : Lambda K}
    (hf : ι f = charSeries q n R) :
    ι (thetaLambda q f)
      = summableSum fun v : Fin n → SuperLetter =>
          q ^ superInvNumber (finPairs n R) v • superMonomial K q v := by
  classical
  have hmem : f ∈ LambdaComp K n := by
    refine mem_lambdaComp_of_coeff_iota hι fun d hd => ?_
    by_contra hne
    refine hd ?_
    rw [hf]
    refine coeff_charSeries_eq_zero_of_sum_ne fun hsum => hne ?_
    rw [show degHom d = d.sum fun _ e => e by simp [degHom, Finsupp.liftAddHom, Finsupp.sum], hsum]
  have hfe : ι f = ∑ σ : Equiv.Perm (Fin n),
      q ^ invNumber (finPairs n R) (fun i => σ i) • gessel K n (invDescentSet σ) := by
    rw [hf, charSeries_eq_sum_gessel q n R hR]
    simp only [finPairs]
  rw [realisation_thetaLambda_of_sum_smul_gessel hι q n univ
      (fun σ : Equiv.Perm (Fin n) => q ^ invNumber (finPairs n R) fun i => σ i)
      (fun σ => invDescentSet σ) (fun σ _ => invDescentSet_subset_Ico σ) hmem hfe,
    sum_pow_invNumber_smul_superFundamental K q (finPairs n R)
      fun p hp => Fin.lt_def.2 (hR _ (mem_finPairs.1 hp))]

end HJO.ParkingFunctions

namespace HJO.Dyck

open HJO.Sym HJO.ParkingFunctions

variable {K : Type*} [CommRing K]

/-- **Carlsson--Mellit, the no-attack specialisation.** Let `π` be a square Dyck
path of length `n`, let `ι_0` be a realisation with no auxiliary variables, let `σ` be the empty
tuple and let `f ∈ Λ` satisfy `ι(f) = χ(π)`. Then `f`, read inside `V_0`, is a `σ`-character of `π`:

`ι_0(θ_0(f)) = (q-1)^{n}ν_σ(π)`.

Only the monotonicity of the path is read, through `HJO.Dyck.isTransitiveAttackSet_attackSet`, which
is what `HJO.Dyck.summableSum_pow_superInvNumber_smul_superMonomial` needs; the `n ≥ 0` is vacuous
and its separate `n = 0` case is unnecessary. `HJO.Sweep.theta_C` makes `θ_0` on `V_0` the map
`HJO.Sym.thetaLambda` on `Λ`, and `HJO.Dyck.auxZeroMap_injective` transports the computation from
`𝒫` back to `P_0`. -/
@[hjo "lem_cm_chi_q1"]
theorem isSigmaCharacter_of_eq_pathCharSeries [Algebra ℚ K] [CharZero K] [NoZeroDivisors K]
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0} (hι : IsAuxRealisation 0 ι) (q : K)
    {n : ℕ} {x : Fin n → ℕ} (hx : Monotone x) {f : Sym.Lambda K}
    (hf : ofAuxRealisationZero ι f = pathCharSeries q x) (σ : Fin 0 → ℕ) :
    IsSigmaCharacter q 0 ι x σ (MvPolynomial.C f) := by
  have hsuper := realisation_thetaLambda_of_eq_charSeries (isRealisation_ofAuxRealisationZero hι) q
    (R := attackSet x) (fun _ hp => fst_lt_snd_of_mem_attackSet hp) hf
  change ι (Sweep.theta q (MvPolynomial.C f)) = (q - 1) ^ (n - 0) • partialCharSeries q 0 x σ
  refine auxZeroMap_injective ?_
  rw [map_smul, auxZeroMap_partialCharSeries_zero, Sweep.theta_C, auxZeroMap_apply_C, hsuper,
    summableSum_pow_superInvNumber_smul_superMonomial K q (isTransitiveAttackSet_attackSet hx),
    Nat.sub_zero]

/-- An element of `V_0` is a symmetric function read as a constant: `V_0` is the subalgebra
generated by no auxiliary variable, hence the image of `MvPolynomial.C`. This is
`HJO.Sweep.piece` at `k = 0`. -/
theorem exists_C_eq_of_mem_piece_zero {G : Sweep.Total K} (hG : G ∈ Sweep.piece K 0) :
    ∃ g : Sym.Lambda K, MvPolynomial.C g = G := by
  rw [Sweep.piece, show (Set.Iio 0 : Set ℕ) = ∅ from
      Set.eq_empty_of_forall_notMem fun _ h => Nat.not_lt_zero _ h,
    MvPolynomial.supported_empty, Algebra.mem_bot] at hG
  obtain ⟨g, hg⟩ := hG
  exact ⟨g, by rw [← hg, MvPolynomial.algebraMap_eq]⟩

/-- **A level-zero character is the characteristic series.** Let `π` be a
square Dyck path of length `n`, let `ι_0` be a realisation with no auxiliary variables, let `σ` be
the empty tuple and let `G ∈ V_0` be a `σ`-character of `π`. Then `ι_0(G) = χ(π)`.

`HJO.Dyck.exists_iota_eq_pathCharSeries` produces `f ∈ Λ` with `ι(f) = χ(π)`, and
`HJO.Dyck.isSigmaCharacter_of_eq_pathCharSeries` makes it a `σ`-character too. Two characters
satisfy the same equation, so `ι_0(θ_0(G)) = ι_0(θ_0(f))`; a realisation is injective by
`HJO.Sym.realisation_injective` and `θ` is injective by `HJO.Sweep.theta_bijOn_piece`, so `G = f`
and `ι_0(G) = χ(π)`. -/
@[hjo "lem_cm_char_zero"]
theorem auxZeroMap_eq_pathCharSeries_of_isSigmaCharacter {K : Type*} [Field K] [CharZero K]
    [Algebra ℚ K] {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K 0} (hι : IsAuxRealisation 0 ι)
    {q : K} (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) {n : ℕ} {x : Fin n → ℕ}
    (hx : IsSquareDyck n x) {G : Sweep.Total K} (hG : G ∈ Sweep.piece K 0) (σ : Fin 0 → ℕ)
    (hchar : IsSigmaCharacter q 0 ι x σ G) :
    auxZeroMap K (ι G) = pathCharSeries q x := by
  obtain ⟨g, rfl⟩ := exists_C_eq_of_mem_piece_zero hG
  obtain ⟨f, hf⟩ :=
    exists_iota_eq_pathCharSeries (isRealisation_ofAuxRealisationZero hι) q hx
  have hfchar : IsSigmaCharacter q 0 ι x σ (MvPolynomial.C f) :=
    isSigmaCharacter_of_eq_pathCharSeries hι q hx.mono hf σ
  have heq : ι (Sweep.theta q (MvPolynomial.C g)) = ι (Sweep.theta q (MvPolynomial.C f)) := by
    rw [show ι (Sweep.theta q (MvPolynomial.C g)) = _ from hchar, hfchar]
  have hthetaL : Sym.thetaLambda q g = Sym.thetaLambda q f := by
    refine realisation_injective (isRealisation_ofAuxRealisationZero hι) ?_
    rw [← auxZeroMap_apply_C, ← auxZeroMap_apply_C, ← Sweep.theta_C, ← Sweep.theta_C, heq]
  have hgf : g = f :=
    MvPolynomial.C_injective _ _ ((Sweep.theta_bijective hq).injective
      (show Sweep.theta q (MvPolynomial.C g) = Sweep.theta q (MvPolynomial.C f) by
        rw [Sweep.theta_C, Sweep.theta_C, hthetaL]))
  rw [auxZeroMap_apply_C, hgf, hf]

end HJO.Dyck
