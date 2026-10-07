/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.InsertRealisation
public import HJO.CarlssonMellit.EastStep
public import HJO.CarlssonMellit.NuEast
public import HJO.CarlssonMellit.CycleTupleSteps
public import HJO.CarlssonMellit.NuSwap
public import HJO.CarlssonMellit.PDeltaStarRealisation
public import HJO.CarlssonMellit.ThetaAddLetter
public import HJO.CarlssonMellit.ThetaBijective
public import HJO.CarlssonMellit.ThetaCommute
public import HJO.Shuffle.CMRaising
public meta import HJO.Attr

/-! # The raising recursion for the characters of a partial Dyck path

The Carlsson--Mellit recursion computes the characteristic series of a partial Dyck path through a
symmetric function: `G ∈ V_k` is an `Id_k`-*character* of `π` when
`ι_k(θ_k(G)) = (q-1)^{N-k} ν_{Id_k}(π)`, which is `HJO.Dyck.IsSigmaCharacter`. This file runs the
*raising* step of that recursion: applying `d_+` to a character of `π` produces a character of
`E_kπ`.

## Main results

* `HJO.Dyck.isSigmaCharacter_cmDPlus` — `d_+G` is an
  `Id_{k+1}`-character of `E_kπ`.
* `HJO.Dyck.isSigmaCharacter_cmDPlus_of_nuEast`: the same, granted the east-step identity of
  `HJO.Dyck.partialCharSeries_prependEast` as a hypothesis. This is where the induction is run; the
  lemma above is the one-line application of it.
* `HJO.Dyck.auxToFrac_smul` and `HJO.Sym.insertFront_smul`: the two scalar-linearity facts the
  recursion needs.

## Implementation notes

**The induction and the statement are two declarations.**
`HJO.Dyck.isSigmaCharacter_cmDPlus_of_nuEast` runs the whole downward induction and
carries `HJO.Dyck.partialCharSeries_prependEast` as the hypothesis `hnu`, stated verbatim;
`HJO.Dyck.isSigmaCharacter_cmDPlus` supplies it as
`partialCharSeries_prependEast q x hx.le_length` and is the statement. The split is kept because the
hypothesis form names exactly what the induction consumes, and nothing else about the east step.

The swapping identity the induction invokes at every step is
`HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple`, proved in `HJO/CarlssonMellit/NuSwap.lean`
from `HJO.Dyck.auxToFrac_unnormalisedCharSeries_transposeTuple`, and it is applied
below at the level `k+1` for the path `E_kπ` and the tuples `σ^{(m)}`, its side conditions being
`HJO.Dyck.cycleTuple_injective`, `HJO.Dyck.cycleTuple_lt`,
`HJO.Dyck.cycleTuple_castSucc_eq_self_iff`, `HJO.Dyck.cycleTuple_castSucc_eq_succ_iff` and
`HJO.Dyck.transposeTuple_cycleTuple_castSucc`.

*The hypothesis `q ≠ 0` is a genuine addition to the statement as usually given, and the proof
needs it.* That proof carries the scalar `q^{-(i-1)}` through its induction; each step of the
induction consumes one factor of `q`, produced by `HJO.Sym.pdeltaStar_pdelta` in the form
`Δ*_m(Δ_m(F)) = qF`. Written without negative powers, as here, the step derives
`q·(q^{i-1}·X_i) = q·((q-1)^{N-k}·ν_{σ^{(i)}})` and must cancel the `q`. Over a base such as
`ℚ(q,t)`, where `q` is a transcendental, `q ≠ 0` is invisible; over an arbitrary field it has
to be said. The statement as usually given has no hypothesis on `q`, while the
argument works inside `P°_k`, where `q^{-1}` exists only for `q ≠ 0`.

*The induction is carried in `P°_{k+1}` and the conclusion is read back in `P_{k+1}`.* `Δ*_m` acts
only on the fraction ring, so each statement `(*)` is an identity between images under the
coefficientwise inclusion `HJO.Sym.auxToFrac`; the conclusion is recovered by
`HJO.Sym.auxToFrac_injective`.

*The interpolating family `A_i` is the tail of the ascending word.* The argument sets
`A_{k+1} := τ_{k+1,k+1}(G)` and `A_i := T_i(A_{i+1})`, so `A_{i}` is `T_{[i,k]}(τ_{k+1,k+1}(G))`,
which is `HJO.Sweep.cmAscWord q i k (HJO.Sweep.qshift q (k+1) G)` — the empty word at `i = k+1` by
`HJO.Sweep.cmAscWord_self_pred` and the whole of `d_+` at `i = 1` by `HJO.Sweep.cmDPlus_apply`. No
separate recursion is introduced, and `HJO.Sweep.cmAscWord_apply_succ_left` is the recursion
`A_i = T_i(A_{i+1})`. Indices are `0`-based here, so the `A_i` is `A (i-1)` and its
`σ^{(i)}` is `HJO.Dyck.cycleTuple` at the index `i - 1`.

## How `HJO.Dyck.IsSigmaCharacter` fits the recursion

The shape of `HJO.Dyck.IsSigmaCharacter` — a *predicate* on `G`, with `ι_k` a hypothesis rather
than a construction, and with the scalar written as `(q-1)^{N-k} • -` in `P_k` — fits the recursion
without adjustment. Three points, each of which could have gone wrong:

* *Reading `(4.5)` as a property and not as a construction is what makes the step composable.* The
  induction never needs a value `χ_σ(π)` to exist, only the equation at the `G` in hand, so no
  well-definedness statement about `χ'_σ(π)` appears anywhere in this file.
* *The truncated exponent `N - k` is honest at the step.* The path grows from `𝔻_{k,N}` to
  `𝔻_{k+1,N+1}`, and `(N+1) - (k+1) = N - k` holds in `ℕ` *without* the hypothesis `k ≤ N` — so the
  scalar is literally unchanged and the step does not have to re-derive it. Had the exponent been
  written as an integer or as a separate natural-number argument, this step would have carried an
  arithmetic side condition.
* *`ι_k` living on the whole total space, pinned on `V_k`, is what lets the intermediate values be
  formed.* Each `ι_{k+1}(θ_{k+1}(A_i))` of the induction is a legitimate value with no membership
  proof attached, and the memberships `A_i ∈ V_{k+1}` are needed only where a *content* lemma
  (`HJO.Dyck.auxToFrac_realise_braid`, `HJO.Dyck.insertFront_realisation`) consumes them. Carrying
  them inside the induction, as here, costs one conjunct.

What the recursion needs beyond `HJO.Dyck.IsSigmaCharacter` lies in the layer around it: the
scalar-linearity of `Φ_k` and of the inclusion `P_k ⊆ P°_k`, both needed the moment the scalar
`(q-1)^{N-k}` has to move past them. They are supplied here as
`HJO.Sym.insertFront_smul` and `HJO.Dyck.auxToFrac_smul`.

## References

E. Carlsson and A.
Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Section 4.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [CommRing K] [IsDomain K]

/-- **The insertion is `𝕜`-linear on scalars**: `Φ_k(cF) = cΦ_k(F)`. The insertion is defined
coefficientwise by a monomialwise sum, so the scalar passes the sum by `smul_finsum`, which needs no
finiteness because the coefficient ring is a domain — and that matters: `HJO.Sym.insertFront` is the
extension by `0` of the `Φ_k`, so the sum defining it is genuinely unsummable at some
arguments, and there both sides are `0`.

This is part of the description of `HJO.Sym.insertFront`. -/
theorem insertFront_smul (k : ℕ) (c : K) (F : AuxAlphabetSeries K k) :
    insertFront K k (c • F) = c • insertFront K k F := by
  have hs : ∀ (m : ℕ) (H : AuxAlphabetSeries K m),
      c • H = MvPowerSeries.C (MvPolynomial.C c) * H := fun m H => by
    rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
  refine MvPowerSeries.ext fun e => ?_
  have hlhs : MvPowerSeries.coeff e (insertFront K k (c • F)) =
      ∑ᶠ a : ℕ, (MvPolynomial.C c : MvPolynomial (Fin (k + 1)) K) •
        (MvPolynomial.X (Fin.last k) ^ a * MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F)) := by
    rw [coeff_insertFront]
    refine finsum_congr fun a => ?_
    rw [hs k F, MvPowerSeries.coeff_C_mul, map_mul, MvPolynomial.rename_C, smul_eq_mul]
    ring
  have hrhs : MvPowerSeries.coeff e (c • insertFront K k F) =
      (MvPolynomial.C c : MvPolynomial (Fin (k + 1)) K) •
        ∑ᶠ a : ℕ, (MvPolynomial.X (Fin.last k) ^ a * MvPolynomial.rename Fin.castSucc
          (MvPowerSeries.coeff (Finsupp.single 0 a + e.mapDomain Nat.succ) F)) := by
    rw [hs (k + 1) (insertFront K k F), MvPowerSeries.coeff_C_mul, coeff_insertFront,
      smul_eq_mul]
  rw [hlhs, hrhs, smul_finsum]

end HJO.Sym

namespace HJO.Dyck

variable {K : Type*} [Field K]

/-- **The containment `P_k ⊆ P°_k` is `𝕜`-linear on scalars**: `c·F` goes to the constant series `c`
times the image of `F`. This is what moves the scalar `(q-1)^{N-k}` of `HJO.Dyck.IsSigmaCharacter`
across the inclusion; `HJO.Sym.auxToFrac_scalarSeries` is the case of the constant series
themselves. -/
theorem auxToFrac_smul (k : ℕ) (c : K) (F : Sym.AuxAlphabetSeries K k) :
    Sym.auxToFrac K k (c • F) = MvPowerSeries.C (Sym.scalarFrac K c) * Sym.auxToFrac K k F := by
  rw [Algebra.smul_def, map_mul, MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq,
    ← Sym.scalarSeries, Sym.auxToFrac_scalarSeries]

/-- A nonzero scalar of the base stays nonzero in the coefficient field of `P°_k`: the coefficient
field is a fraction ring of a polynomial ring over `𝕜`, and both maps are injective. -/
theorem scalarFrac_ne_zero {k : ℕ} {c : K} (hc : c ≠ 0) :
    Sym.scalarFrac K c ≠ (0 : Sym.AuxFrac K k) := by
  have h1 : (MvPolynomial.C c : MvPolynomial (Fin k) K) ≠ 0 := by simpa using hc
  exact fun h => h1 (IsFractionRing.injective (MvPolynomial (Fin k) K) (Sym.AuxFrac K k)
    (by rw [map_zero]; exact h))

/-- Scalars of the base multiply inside the coefficient field of `P°_k`. -/
theorem scalarFrac_mul (k : ℕ) (a b : K) :
    (Sym.scalarFrac K a : Sym.AuxFrac K k) * Sym.scalarFrac K b = Sym.scalarFrac K (a * b) := by
  unfold Sym.scalarFrac
  rw [← map_mul, ← map_mul]

/-- Multiplication by the constant series at a nonzero scalar of the base is injective on `P°_k`:
that scalar is a unit of the coefficient field, so the constant series is a unit. -/
theorem mul_left_cancel_C_scalarFrac {k : ℕ} {c : K} (hc : c ≠ 0)
    {F G : Sym.AuxAlphabetSeriesFrac K k}
    (h : MvPowerSeries.C (Sym.scalarFrac K c) * F = MvPowerSeries.C (Sym.scalarFrac K c) * G) :
    F = G := by
  have hunit : (MvPowerSeries.C (Sym.scalarFrac K c)⁻¹ * MvPowerSeries.C (Sym.scalarFrac K c) :
      Sym.AuxAlphabetSeriesFrac K k) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (scalarFrac_ne_zero hc), map_one]
  calc F = MvPowerSeries.C (Sym.scalarFrac K c)⁻¹ *
        (MvPowerSeries.C (Sym.scalarFrac K c) * F) := by rw [← mul_assoc, hunit, one_mul]
    _ = MvPowerSeries.C (Sym.scalarFrac K c)⁻¹ *
        (MvPowerSeries.C (Sym.scalarFrac K c) * G) := by rw [h]
    _ = G := by rw [← mul_assoc, hunit, one_mul]

/-- **The raising recursion, granted the east-step identity.** The statement of
`HJO.Dyck.isSigmaCharacter_cmDPlus`: for `k ≤ N`, a partial Dyck path `π` of length `N` and
`G ∈ V_k` an `Id_k`-character of `π`, the element `d_+G` is an `Id_{k+1}`-character of `E_kπ`.

The swapping identity the induction needs is `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple`,
read at the level `k+1` for the path `E_kπ` and the family of tuples `σ^{(m)}`; its side conditions
there — that `σ^{(m)}` lists the labels of the level without repetition and puts the label `m`
before the label `m+1` — are `HJO.Dyck.cycleTuple_injective`, `HJO.Dyck.cycleTuple_lt`,
`HJO.Dyck.cycleTuple_castSucc_eq_self_iff` and `HJO.Dyck.cycleTuple_castSucc_eq_succ_iff`, and its
transposition step is `HJO.Dyck.transposeTuple_cycleTuple_castSucc`.

The proof is the usual one, written without negative powers of `q`: with
`A_i := T_{[i,k]}(τ_{k+1,k+1}(G))` one shows by downward induction on `i` that
`q^{i-1}·ι_{k+1}(θ_{k+1}(A_i)) = (q-1)^{N-k}·ν_{σ^{(i)}}(E_kπ)` in `P°_{k+1}`. The base `i = k+1` is
`HJO.Sweep.addLetter_theta`, `HJO.Dyck.insertFront_realisation` and
`HJO.Dyck.partialCharSeries_prependEast`; the step is `HJO.Sweep.theta_braid`,
`HJO.Dyck.auxToFrac_realise_braid`, `hswap` and `HJO.Sym.pdeltaStar_pdelta`, the last of which
produces the factor of `q` that `q ≠ 0` cancels. At `i = 1` the tuple is `Id_{k+1}` and the scalar
is `1`.

The hypothesis `hnu` is the east-step identity
`HJO.Dyck.partialCharSeries_prependEast q x hx.le_length`, carried as a hypothesis so that the
induction names exactly what it consumes. -/
theorem isSigmaCharacter_cmDPlus_of_nuEast (q : K) (hq : q ≠ 0) {k N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck k N x)
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k} (hι : IsAuxRealisation k ι)
    {ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)} (hι' : IsAuxRealisation (k + 1) ι')
    (hnu : partialCharSeries q (k + 1) (prependEast k x) (cycleTuple (Fin.last k)) =
      q ^ k • Sym.insertFront K k (partialCharSeries q k x (identityTuple k)))
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k)
    (hchar : IsSigmaCharacter q k ι x (identityTuple k) G) :
    IsSigmaCharacter q (k + 1) ι' (prependEast k x) (identityTuple (k + 1))
      (Sweep.cmDPlus q k G) := by
  -- `E_kπ` is a partial Dyck path one level longer, which is what
  -- `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple` reads it as.
  have hE : IsPartialDyck (k + 1) (N + 1) (prependEast k x) :=
    isPartialDyck_prependEast hx.toIsSquareDyck hx.le_length
  -- `HJO.Dyck.auxToFrac_partialCharSeries_transposeTuple` at the level `k + 1`, for `E_kπ` and the
  -- interpolating tuples.
  have hswap : ∀ m : Fin k,
      Sym.auxToFrac K (k + 1)
          (partialCharSeries q (k + 1) (prependEast k x) (cycleTuple m.succ)) =
        Sym.pdelta q m.castSucc m.succ (Sym.auxToFrac K (k + 1)
          (partialCharSeries q (k + 1) (prependEast k x) (cycleTuple m.castSucc))) := by
    intro m
    have h := auxToFrac_partialCharSeries_transposeTuple (σ := cycleTuple m.castSucc)
      (i := m.castSucc) (j := m.succ) (m := (m : ℕ)) (a := 0) (b := m.succ) q
      (Nat.succ_le_succ hx.le_length) hE (cycleTuple_injective _) (cycleTuple_lt _) rfl rfl
      ((cycleTuple_castSucc_eq_self_iff m 0).2 rfl)
      ((cycleTuple_castSucc_eq_succ_iff m m.succ).2 rfl) (by simp)
    rwa [transposeTuple_cycleTuple_castSucc m] at h
  -- `A j` is the `A_{j+1}`, the tail `T_{[j+1,k]}` of the ascending word.
  set A : ℕ → Sweep.Total K :=
    fun j => Sweep.cmAscWord q (j + 1) k (Sweep.qshift q (k + 1) G) with hA
  -- The `(*)`, written without negative powers of `q`, together with the memberships
  -- `A_i ∈ V_{k+1}` its content lemmas consume.
  have key : ∀ d : ℕ, ∀ j : Fin (k + 1), (j : ℕ) + d = k →
      A (j : ℕ) ∈ Sweep.piece K (k + 1) ∧
      MvPowerSeries.C (Sym.scalarFrac K (q ^ (j : ℕ))) *
          Sym.auxToFrac K (k + 1) (ι' (Sweep.theta q (A (j : ℕ)))) =
        MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - k))) *
          Sym.auxToFrac K (k + 1)
            (partialCharSeries q (k + 1) (prependEast k x) (cycleTuple j)) := by
    intro d
    induction d with
    | zero =>
      -- The base `i = k + 1`: the word is empty, so `A_{k+1} = τ_{k+1,k+1}(G)`.
      intro j hj
      have hjk : j = Fin.last k := Fin.ext (by simpa using hj)
      have hAk : A (j : ℕ) = Sweep.qshift q (k + 1) G := by
        rw [hA, hjk]
        simp only [Fin.val_last]
        rw [Sweep.cmAscWord_self_pred]
        rfl
      refine ⟨hAk ▸ Sweep.qshift_mem_piece q (i := k + 1) (k := k) (m := k + 1)
        (by omega) (by omega) hG, ?_⟩
      have hthetaG : Sweep.theta q G ∈ Sweep.piece K k := Sweep.theta_mem_piece q le_rfl hG
      -- `ι_{k+1}(θ_{k+1}(A_{k+1})) = Φ_k(ι_k(θ_k(G))) = (q-1)^{N-k}·Φ_k(ν_{Id_k}(π))`.
      have hleft : ι' (Sweep.theta q (A (j : ℕ))) =
          (q - 1) ^ (N - k) • Sym.insertFront K k (partialCharSeries q k x (identityTuple k)) := by
        rw [hAk, ← Sweep.addLetter_theta q k G, ← insertFront_realisation hι hι' hthetaG,
          show ι (Sweep.theta q G) =
            (q - 1) ^ (N - k) • partialCharSeries q k x (identityTuple k) from hchar,
          Sym.insertFront_smul]
      -- `ν_{σ^{(k+1)}}(E_kπ) = q^k·Φ_k(ν_{Id_k}(π))`.
      have hright : partialCharSeries q (k + 1) (prependEast k x) (cycleTuple j) =
          q ^ k • Sym.insertFront K k (partialCharSeries q k x (identityTuple k)) := by
        rw [hjk]; exact hnu
      rw [hleft, hright, auxToFrac_smul, auxToFrac_smul, hjk]
      simp only [Fin.val_last]
      ring
    | succ d ih =>
      -- The step `i + 1 ↦ i`: one Demazure--Lusztig letter, one `Δ*_m`, one factor of `q`.
      intro j hj
      have hjlt : (j : ℕ) < k := by omega
      set m : Fin k := ⟨(j : ℕ), hjlt⟩ with hm
      have hcast : m.castSucc = j := Fin.ext rfl
      have hsuccval : ((m.succ : Fin (k + 1)) : ℕ) = (j : ℕ) + 1 := rfl
      obtain ⟨hmem', heq'⟩ := ih m.succ (by rw [hsuccval]; omega)
      -- `A_i = T_i(A_{i+1})`.
      have hstep : A (j : ℕ) = Sweep.braid q ((j : ℕ) + 1) (A (((m.succ : Fin (k + 1))) : ℕ)) := by
        rw [hA, hsuccval]
        exact Sweep.cmAscWord_apply_succ_left q (by omega) _
      refine ⟨hstep ▸ Sweep.braid_mem_piece q (by omega) (by omega) hmem', ?_⟩
      have hthetamem : Sweep.theta q (A (((m.succ : Fin (k + 1))) : ℕ)) ∈ Sweep.piece K (k + 1) :=
        Sweep.theta_mem_piece q le_rfl hmem'
      have hj' : ((m.succ : Fin (k + 1)) : ℕ) = (m.castSucc : ℕ) + 1 := rfl
      -- `ι_{k+1}(θ_{k+1}(A_i)) = Δ*_m(ι_{k+1}(θ_{k+1}(A_{i+1})))`.
      have hX : Sym.auxToFrac K (k + 1) (ι' (Sweep.theta q (A (j : ℕ)))) =
          Sym.pdeltaStar q m.castSucc m.succ (Sym.auxToFrac K (k + 1)
            (ι' (Sweep.theta q (A (((m.succ : Fin (k + 1))) : ℕ))))) := by
        rw [hstep, Sweep.theta_braid,
          auxToFrac_realise_braid q hι' m.castSucc m.succ hj' hthetamem]
        rfl
      -- Applying `Δ*_m` to the inductive hypothesis.
      have happ := congrArg (Sym.pdeltaStar q m.castSucc m.succ) heq'
      rw [Sym.pdeltaStar_mul_of_pswap_eq (Sym.pswap_C_scalarFrac _),
        Sym.pdeltaStar_mul_of_pswap_eq (Sym.pswap_C_scalarFrac _), ← hX, hswap m,
        Sym.pdeltaStar_pdelta (ne_of_lt (show m.castSucc < m.succ from Fin.castSucc_lt_succ)),
        hcast] at happ
      -- Cancelling the one factor of `q` that `HJO.Sym.pdeltaStar_pdelta` produced.
      refine mul_left_cancel_C_scalarFrac (c := q) hq ?_
      calc MvPowerSeries.C (Sym.scalarFrac K q) *
            (MvPowerSeries.C (Sym.scalarFrac K (q ^ (j : ℕ))) *
              Sym.auxToFrac K (k + 1) (ι' (Sweep.theta q (A (j : ℕ)))))
          = MvPowerSeries.C (Sym.scalarFrac K (q ^ (((m.succ : Fin (k + 1))) : ℕ))) *
              Sym.auxToFrac K (k + 1) (ι' (Sweep.theta q (A (j : ℕ)))) := by
            rw [hsuccval, ← mul_assoc, ← map_mul, scalarFrac_mul, ← pow_succ']
        _ = MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - k))) *
              (MvPowerSeries.C (Sym.scalarFrac K q) *
                Sym.auxToFrac K (k + 1)
                  (partialCharSeries q (k + 1) (prependEast k x) (cycleTuple j))) := happ
        _ = MvPowerSeries.C (Sym.scalarFrac K q) *
              (MvPowerSeries.C (Sym.scalarFrac K ((q - 1) ^ (N - k))) *
                Sym.auxToFrac K (k + 1)
                  (partialCharSeries q (k + 1) (prependEast k x) (cycleTuple j))) := by ring
  -- At `i = 1` the tuple is `Id_{k+1}`, the scalar is `1`, and `A_1` is `d_+G`.
  obtain ⟨-, hfinal⟩ := key k 0 (by rw [show ((0 : Fin (k + 1)) : ℕ) = 0 from rfl]; omega)
  have hone : (Sym.scalarFrac K (1 : K) : Sym.AuxFrac K (k + 1)) = 1 := by simp [Sym.scalarFrac]
  have hA0 : A 0 = Sweep.cmDPlus q k G := by
    rw [hA]
    exact (Sweep.cmDPlus_apply q k G).symm
  rw [show ((0 : Fin (k + 1)) : ℕ) = 0 from rfl, pow_zero, hone, map_one, one_mul,
    cycleTuple_zero_eq_identityTuple, hA0] at hfinal
  refine Sym.auxToFrac_injective (k + 1) (hfinal.trans ?_)
  rw [auxToFrac_smul, Nat.succ_sub_succ]

/-- **The raising recursion.** `HJO.Dyck.isSigmaCharacter_cmDPlus`: for `q ≠ 0`, a partial Dyck path
`π` of level `k` and length `N`, and `G ∈ V_k` an `Id_k`-character of `π`, the element `d_+G` is an
`Id_{k+1}`-character of `E_kπ`.

This is `HJO.Dyck.isSigmaCharacter_cmDPlus_of_nuEast` with its one hypothesis discharged: `hnu` is
`HJO.Dyck.partialCharSeries_prependEast`, whose own hypothesis `k ≤ N` is the field `le_length` of
`hx`.

*The hypothesis `q ≠ 0` is a genuine addition to the statement as usually given, and the proof
needs it*. See the module docstring: the downward
induction consumes one factor of `q` per step from `HJO.Sym.pdeltaStar_pdelta` and must cancel it,
which over `ℚ(q,t)` is invisible and over an arbitrary field is not. The conclusion is *not*
weakened to compensate. -/
@[hjo "lem_cm_raising"]
theorem isSigmaCharacter_cmDPlus (q : K) (hq : q ≠ 0) {k N : ℕ} {x : Fin N → ℕ}
    (hx : IsPartialDyck k N x)
    {ι : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K k} (hι : IsAuxRealisation k ι)
    {ι' : Sweep.Total K →ₐ[K] Sym.AuxAlphabetSeries K (k + 1)} (hι' : IsAuxRealisation (k + 1) ι')
    {G : Sweep.Total K} (hG : G ∈ Sweep.piece K k)
    (hchar : IsSigmaCharacter q k ι x (identityTuple k) G) :
    IsSigmaCharacter q (k + 1) ι' (prependEast k x) (identityTuple (k + 1))
      (Sweep.cmDPlus q k G) :=
  isSigmaCharacter_cmDPlus_of_nuEast q hq hx hι hι'
    (partialCharSeries_prependEast q x hx.le_length) hG hchar

end HJO.Dyck
