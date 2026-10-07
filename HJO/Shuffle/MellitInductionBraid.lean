/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendCluster
public import HJO.Shuffle.MellitRem41Node
public import HJO.Shuffle.BraidTypeDGapFree
public import HJO.Shuffle.BraidUnsweptFloor
public import HJO.Shuffle.MellitLhsEquivAbove
public import HJO.Shuffle.SweepAppendGeneric

/-! # The braid side of `HJO.Mellit.mellitInduction_sweepWitness`

Mellit's Section 6 proves the closed form of the invariant of a composition,
`D_{η,c_α} = (-1)^{(a-1)N} (qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`, in two steps: Theorem 5.8 reads
`D_{η,c_α}` as the braid value `π_ℓ(B_{s,v,α^{br}}) d_+^ℓ(1)` of the special-braid data of `c_α`
(the `q`-power factor being `1` because the two inversion counts of a minimal-gap colouring agree),
and an induction on the number of parts evaluates that braid value, each part contributing one
append step `b^{(A)}_{a,b} = (b_{a,b} y_1 z_1)^{A-1} b_{a,b}`.

This file carries out the induction, unconditionally, and assembles the clause from it.

The induction is run at a **fixed** path and rectangle. The data of
`HJO.Mellit.braidDataOfColouring` lists the components of `c_α` in increasing order of column, and
its rank-`j` prefix is the data of the first `j` components, read at the same `N` and the same
level. The append step of `HJO.Mellit.braidRep_specialBraid_dplusIter` relates the rank-`(j+1)`
prefix to the rank-`j` prefix, so the induction is on `j ≤ ℓ` with `N` and the level `η = aN + 1/2`
held fixed, and it never deletes a part from the rectangle; the `N`-dependence of the slope and of
the level does not enter.

At the prefix of rank `j + 1` the appended entry is the `j`-th component, at position
`v_j = 1 - θ - δ_j` with `δ_j = (η - aA_{j+1})/D`, `A_{j+1} = α_1 + ⋯ + α_{j+1}` and
`D = (a+b)(aN+1)N - 1`. For `j + 1 < ℓ` this offset is larger than one cell of the `1/(2D)`-grid,
so the grid criterion `HJO.Braid.gap_of_grid` does not apply, and the isotopy clause — no iterate
of an earlier component in the window `[v_j, 1 - θ)` — is proved directly
(`HJO.Mellit.braidDataOfColouring_gap_of_lt`). The `m`-th iterate of the `t`-th component is the
fractional part of `(n - η)/D` for `n` the residue of `aA_{t+1} - (m+1)a(aN+1)N` modulo `D`, and it
misses the window exactly when `n ∉ [aA_{j+1}, aN]`. Writing `m + 1 = (a+b)c + ρ` and
`ρa = (a+b)g + σ`, that residue is `a(A_{t+1} - c) - g` when
`σ = 0` and `(a+b-σ)(aN+1)N - 1 + a(A_{t+1} - c) - g` otherwise; coprimality of `a` and `a + b`
makes `σ = 0` force `ρ = 0`, and in neither case does the residue lie in `[aA_{j+1}, aN]`.

## Main results

* `HJO.Mellit.braidDataOfColouring_gap_of_lt` — the isotopy clause of
  `HJO.Mellit.braidRep_specialBraid_dplusIter` at every prefix of the data of a composition
  colouring.
* `HJO.Mellit.isAppendSetup_appendFinalTuple_of_lt` — `HJO.Braid.IsAppendSetup` at every prefix.
* `HJO.Mellit.sweepIn_braidRep_specialBraid_succ_of_lt` —
  `HJO.Mellit.braidRep_specialBraid_dplusIter` at every prefix.
* `HJO.Mellit.sweepIn_braidValueOfPath_sepLevel` and
  `HJO.Mellit.sweepIn_braidValueColouring_compColouring` — **the braid side of
  `HJO.Mellit.mellitInduction_sweepWitness`**: at `η = aN + 1/2` the braid value of `c_α` is
  `(-1)^{(a-1)N}(qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`.
* `HJO.Mellit.mellitInduction_of_sweepRecursionBEFloor` and
  `HJO.Mellit.mellitInduction_sweepWitness_of_sweepRecursionBEFloor` —
  `HJO.Mellit.mellitInduction_sweepWitness` at the witness from the type-`BE` clause of the braid
  recursion, the unswept clause being `HJO.Mellit.braidValueColouring_sweepRecursionUnsweptFloor`.

## Implementation notes

The braid representation `HJO.Sweep.braidRep` carries a square root `r` of `q`, so the assembly
holds at the parameters `q` that are squares in the coefficient field; the clause itself mentions no
square root.

The level is `aN + 1/2` throughout the braid side. Every separating admissible level gives the same
`D_{η,c_α}` (`HJO.Mellit.isColouringValue_sweepWitness`), so nothing is lost.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Section 6.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-- **Special-braid data restricts along an injection of index sets.** Every clause of
`HJO.Braid.IsSpecialBraidData` quantifies over the indices one or two at a time, so it survives
passing to a subfamily; the distinctness clause transports because the reindexing is injective. -/
theorem IsSpecialBraidData.comp_injective {s θ : ℚ} {k j : ℕ} {v : Fin k → ℚ} {α : Fin k → ℕ}
    (hdata : IsSpecialBraidData s θ k v α) {f : Fin j → Fin k} (hf : Function.Injective f) :
    IsSpecialBraidData s θ j (v ∘ f) (α ∘ f) where
  slope_pos := hdata.slope_pos
  theta_spec := hdata.theta_spec
  mem_Ioo i := hdata.mem_Ioo (f i)
  one_le_mult i := hdata.one_le_mult (f i)
  ne_theta i m hm := hdata.ne_theta (f i) m hm
  injective i i' m m' hm hm' h :=
    ⟨hf (hdata.injective (f i) (f i') m m' hm hm' h).1, (hdata.injective _ _ m m' hm hm' h).2⟩

end HJO.Braid

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-- Dividing `i + 1` and then the remainder times `a` by `a + b`: the quotients and remainders
`c, ρ, g, σ` satisfy the bounds the window arithmetic needs. -/
theorem exists_div_mod_window {a b p i : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (hi : i + 3 ≤ (a + b) * p) :
    ∃ c ρ g σ : ℕ, (a + b) * c + ρ = i + 1 ∧ (a + b) * g + σ = ρ * a ∧ σ < a + b ∧
      c + 1 ≤ p ∧ g + 1 ≤ a ∧ (σ = 0 → 1 ≤ c) := by
  have hab0 : 0 < a + b := by omega
  have hρ : (i + 1) % (a + b) < a + b := Nat.mod_lt _ hab0
  refine ⟨_, _, _, _, Nat.div_add_mod _ _, Nat.div_add_mod _ _, Nat.mod_lt _ hab0, ?_, ?_, ?_⟩
  · have h1 := Nat.div_add_mod (i + 1) (a + b)
    have := Nat.lt_of_mul_lt_mul_left (a := a + b) (b := (i + 1) / (a + b)) (c := p) (by omega)
    omega
  · have h2 := Nat.div_add_mod ((i + 1) % (a + b) * a) (a + b)
    have h3 := Nat.mul_lt_mul_of_pos_right hρ ha
    have := Nat.lt_of_mul_lt_mul_left (a := a + b)
      (b := (i + 1) % (a + b) * a / (a + b)) (c := a) (by omega)
    omega
  · intro hσ0
    have hcop : Nat.Coprime (a + b) a := by
      rw [Nat.add_comm]; exact Nat.coprime_add_self_left.2 hab.symm
    have hρ0 := Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero hσ0)) hρ
    have h1 := Nat.div_add_mod (i + 1) (a + b)
    rw [hρ0] at h1
    rcases Nat.eq_zero_or_pos ((i + 1) / (a + b)) with h | h
    · rw [h] at h1; omega
    · exact h

/-- **The window arithmetic**, with `Q = (aN+1)N` and `D = (a+b)Q - 1` abstracted: for
`p ≤ A_t ≤ A_j`, `A_t ≤ N` and `i + 3 ≤ (a+b)p`, the fractional part of
`(bQ + aA_t - 1 - η)/D - i·aQ/D` lies below `(bQ + aA_j - 1 - η)/D + aQ/D` at `η = aN + 1/2`. -/
theorem fract_window_lt_aux {a b At Aj p i : ℕ} {N Q D η : ℚ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hpA : p ≤ At) (hAt : At ≤ Aj) (hAj : (At : ℚ) ≤ N)
    (hi : i + 3 ≤ (a + b) * p) (hDdef : D = (a : ℚ) * Q + (b : ℚ) * Q - 1) (hD : 0 < D)
    (hQge : (a : ℚ) * N + 1 ≤ Q) (hη : η = (a : ℚ) * N + 1 / 2) :
    Int.fract (((b : ℚ) * Q + (a : ℚ) * (At : ℚ) - 1 - η) / D - (i : ℚ) * ((a : ℚ) * Q / D))
      < ((b : ℚ) * Q + (a : ℚ) * (Aj : ℚ) - 1 - η) / D + (a : ℚ) * Q / D := by
  obtain ⟨c, ρ, g, σ, h1, h2, hσ, hcp, hga, hc1⟩ := exists_div_mod_window ha hab hi
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have h1q : ((a : ℚ) + b) * c + ρ = i + 1 := by exact_mod_cast h1
  have h2q : ((a : ℚ) + b) * g + σ = ρ * a := by exact_mod_cast h2
  have hcpq : (c : ℚ) + 1 ≤ p := by exact_mod_cast hcp
  have hgaq : (g : ℚ) + 1 ≤ a := by exact_mod_cast hga
  have hpAq : (p : ℚ) ≤ At := by exact_mod_cast hpA
  have hAtq : (At : ℚ) ≤ Aj := by exact_mod_cast hAt
  have hσq : (σ : ℚ) + 1 ≤ a + b := by exact_mod_cast hσ
  have hg0 : (0 : ℚ) ≤ g := Nat.cast_nonneg _
  have hN0 : (0 : ℚ) ≤ N := (Nat.cast_nonneg At).trans hAj
  have hQ0 : 0 ≤ Q := by nlinarith
  have hDσ : (σ : ℚ) * Q ≤ D - Q + 1 := by
    rw [hDdef]; nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ) + b - 1 - σ) hQ0]
  have hs1 : (g : ℚ) + 1 ≤ (a : ℚ) * At - c * a := by
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ)) (by linarith : (0 : ℚ) ≤ At - c - 1)]
  have hsN : (a : ℚ) * At ≤ (a : ℚ) * N := mul_le_mul_of_nonneg_left hAj (by linarith)
  have hsj : (a : ℚ) * At ≤ (a : ℚ) * Aj := mul_le_mul_of_nonneg_left hAtq (by linarith)
  have hca : (0 : ℚ) ≤ c * a := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hσQ : (0 : ℚ) ≤ σ * Q := mul_nonneg (Nat.cast_nonneg _) hQ0
  -- the numerator, reduced modulo `D`
  obtain ⟨r, hrdef⟩ : ∃ r : ℚ, r = (D + ((a : ℚ) * At - c * a - g) - σ * Q - η) / D := ⟨_, rfl⟩
  have hnum : ((b : ℚ) * Q + (a : ℚ) * (At : ℚ) - 1 - η) / D - (i : ℚ) * ((a : ℚ) * Q / D)
      = ((-((c * a + g : ℕ) : ℤ) : ℤ) : ℚ) + r := by
    have key : ((b : ℚ) * Q + (a : ℚ) * (At : ℚ) - 1 - η) - (i : ℚ) * ((a : ℚ) * Q)
        = (-((c : ℚ) * a + g)) * D + (D + ((a : ℚ) * At - c * a - g) - σ * Q - η) := by
      linear_combination ((c : ℚ) * a + g - 1) * hDdef + Q * a * h1q + Q * h2q
    rw [hrdef, show ((b : ℚ) * Q + (a : ℚ) * (At : ℚ) - 1 - η) / D - (i : ℚ) * ((a : ℚ) * Q / D)
        = (((b : ℚ) * Q + (a : ℚ) * (At : ℚ) - 1 - η) - (i : ℚ) * ((a : ℚ) * Q)) / D by ring,
      key, add_div, mul_div_cancel_right₀ _ hD.ne']
    push_cast
    ring
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact div_nonneg (by rw [hη]; linarith) hD.le
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hD, hη]
    linarith
  rw [hnum, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨hr0, hr1⟩, hrdef, ← add_div,
    div_lt_div_iff_of_pos_right hD]
  -- the residue misses the window `[aA_j, aN]`
  rcases Nat.eq_zero_or_pos σ with rfl | hσpos
  · have hca1 : (a : ℚ) ≤ c * a :=
      le_mul_of_one_le_left (by linarith) (by exact_mod_cast hc1 rfl)
    rw [Nat.cast_zero, hDdef]
    linarith only [hca1, hsj, hg0, ha']
  · have hσQ1 : Q ≤ σ * Q := le_mul_of_one_le_left hQ0 (by exact_mod_cast hσpos)
    have haA : (0 : ℚ) ≤ (a : ℚ) * Aj := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    rw [hDdef]
    linarith only [hσQ1, hQge, hsN, hca, hg0, haA]

/-- **The window arithmetic in the colouring's own normalisation**:
`HJO.Mellit.fract_window_lt_aux` at `Q = (aN+1)N`, with `θ = aQ/D`. -/
theorem fract_window_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b)
    {At Aj p i : ℕ} (hpA : p ≤ At) (hAt : At ≤ Aj) (hAj : At ≤ N) (hi : i + 3 ≤ (a + b) * p) :
    Int.fract (((b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * (At : ℚ) - 1 - sepLevel a N) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        - (i : ℚ) * sweepTheta a b N)
      < ((b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * (Aj : ℚ) - 1 - sepLevel a N) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        + sweepTheta a b N := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hN' : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have h := fract_window_lt_aux (N := (N : ℚ)) (Q := ((a : ℚ) * N + 1) * N)
    (D := (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
    (η := sepLevel a N) ha hb hab hpA hAt (by exact_mod_cast hAj) hi (by ring) hD
    (by nlinarith [mul_le_mul_of_nonneg_left hN' (by positivity : (0 : ℚ) ≤ (a : ℚ) * N + 1)])
    rfl
  rw [sweepTheta_eq_div_rankSpan ha hb hN]
  simp only [mul_assoc] at h ⊢
  exact h

/-! ### Prefixes of the colouring data -/

/-- Lowering the rank of the colouring data is restricting it along `Fin.castLE`. -/
theorem braidDataOfColouring_fst_comp_castLE (a b N : ℕ) (y : Heights a b N) (η : ℚ) {j k : ℕ}
    (h : j ≤ k) :
    (braidDataOfColouring a b N y η k).1 ∘ Fin.castLE h = (braidDataOfColouring a b N y η j).1 := by
  funext t
  rw [Function.comp_apply, braidDataOfColouring_fst, braidDataOfColouring_fst, Fin.val_castLE]

/-- The multiplicity half of `HJO.Mellit.braidDataOfColouring_fst_comp_castLE`. -/
theorem braidDataOfColouring_snd_comp_castLE (a b N : ℕ) (y : Heights a b N) (η : ℚ) {j k : ℕ}
    (h : j ≤ k) :
    (braidDataOfColouring a b N y η k).2 ∘ Fin.castLE h = (braidDataOfColouring a b N y η j).2 := by
  funext t
  rw [Function.comp_apply, braidDataOfColouring_snd, braidDataOfColouring_snd, Fin.val_castLE]

/-- **Every prefix of the data of a composition colouring is special-braid data.** -/
theorem isSpecialBraidData_braidDataOfColouring_of_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {j : ℕ} (hj : j ≤ α.length) :
    IsSpecialBraidData (sweepSlope a b N) (sweepTheta a b N) j
      (braidDataOfColouring a b N y η j).1 (braidDataOfColouring a b N y η j).2 := by
  have h := (isSpecialBraidData_braidDataOfColouring_hasAboveReturns ha hb hN hab hηa hηs hηN
    hret).comp_injective (Fin.castLE_injective hj)
  rwa [braidDataOfColouring_fst_comp_castLE, braidDataOfColouring_snd_comp_castLE] at h

/-- The multiplicity of a component of a prefix: `(a+b)α_i - 1`. -/
theorem braidDataOfColouring_snd_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) {α : List ℕ}
    {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < α.length) :
    (braidDataOfColouring a b N y η k).2 i = (a + b) * α[(i : ℕ)] - 1 := by
  rw [braidDataOfColouring_snd]
  exact card_componentCrossingIndices_hasAboveReturns ha hb hN hab hηa hηs hηN hret hi

/-- The final position of a component of a prefix, as in
`HJO.Mellit.iterate_braidDataOfColouring_fst_eq`. -/
theorem iterate_braidDataOfColouring_fst_eq_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) (hηle : η ≤ sepLevel a N)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ} (i : Fin k)
    (hi : (i : ℕ) < α.length) :
    (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η k).2 i - 1]
        ((braidDataOfColouring a b N y η k).1 i)
      = ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have h := iterate_braidDataOfColouring_fst_eq ha hb hN hab hηa hηs hηN hηle hret
    (k := α.length - 1) (by omega) ⟨i, by omega⟩
  rw [braidDataOfColouring_snd, braidDataOfColouring_fst] at h ⊢
  exact h

/-- **The isotopy clause at every prefix.** No iterate of an earlier component lies in the window
`[v_j, 1 - θ)` below the start, at the level `aN + 1/2`. -/
theorem braidDataOfColouring_gap_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {j : ℕ}
    (hj : j < α.length) :
    ∀ (t : Fin j) (i : ℕ),
      i + 1 < (braidDataOfColouring a b N y (sepLevel a N) (j + 1)).2 t.castSucc →
      (nextCrossing (sweepTheta a b N))^[i]
          ((braidDataOfColouring a b N y (sepLevel a N) (j + 1)).1 t.castSucc) <
        (braidDataOfColouring a b N y (sepLevel a N) (j + 1)).1 (Fin.last j)
          + sweepTheta a b N := by
  intro t i hi
  have hηa := isAdmissibleLevel_sepLevel a N
  have hηs : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have hηN := cast_mul_lt_sepLevel a N
  have hdata := isSpecialBraidData_braidDataOfColouring_of_le ha hb hN hab hηa hηs hηN hret
    (j := j + 1) hj
  obtain ⟨hθ0, hθ1⟩ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have ht : (t : ℕ) < α.length := by omega
  rw [iterate_nextCrossing_eq_fract hθ0 hθ1 (hdata.mem_Ioo _).1 (hdata.mem_Ioo _).2 i
    (fun m hm => hdata.ne_theta _ m (by omega))]
  rw [braidDataOfColouring_snd_of_lt ha hb hN hab hηa hηs hηN hret t.castSucc
    (by rw [Fin.val_castSucc]; exact ht)] at hi
  rw [braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret t.castSucc
      (by rw [Fin.val_castSucc]; exact ht),
    braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret (Fin.last j)
      (by rw [Fin.val_last]; exact hj)]
  simp only [Fin.val_castSucc, Fin.val_last] at hi ⊢
  have hsucc : (α.take ((t : ℕ) + 1)).sum = (α.take (t : ℕ)).sum + α[(t : ℕ)] :=
    List.sum_take_succ α _ ht
  have hmono : (α.take ((t : ℕ) + 1)).sum ≤ (α.take (j + 1)).sum :=
    List.monotone_sum_take α (by omega)
  have hle : (α.take ((t : ℕ) + 1)).sum ≤ N := by
    have h := List.monotone_sum_take α (show (t : ℕ) + 1 ≤ α.length by omega)
    simp only [List.take_length] at h
    exact h.trans hret.2.2.1.le
  exact fract_window_lt ha hb hN hab (p := α[(t : ℕ)]) (by omega) hmono hle (by omega)

/-- The drift of the run of the `j`-th component together with the prefix offset is the drift of a
run of `N - A_j` turns together with the offset of the full composition. -/
theorem prefix_drift_eq {α : List ℕ} {j : ℕ} (hj : j < α.length) (hN : α.sum = N) :
    ((α[j] * (a + b) : ℕ) : ℚ) * appendDrift a b N +
        ((((N - (α.take (j + 1)).sum) * (a + b) : ℕ) : ℚ) * appendDrift a b N
          + appendOffset a b N (sepLevel a N))
      = ((((N - (α.take j).sum) * (a + b)) : ℕ) : ℚ) * appendDrift a b N
          + appendOffset a b N (sepLevel a N) := by
  have hsucc : (α.take (j + 1)).sum = (α.take j).sum + α[j] := List.sum_take_succ α j hj
  have hle : (α.take (j + 1)).sum ≤ N := by
    have h := List.monotone_sum_take α (show j + 1 ≤ α.length by omega)
    simp only [List.take_length] at h
    exact h.trans hN.le
  have hnat : α[j] * (a + b) + (N - (α.take (j + 1)).sum) * (a + b)
      = (N - (α.take j).sum) * (a + b) := by
    rw [← Nat.add_mul]; congr 1; omega
  rw [← hnat, Nat.cast_add, add_mul, add_assoc]

/-- **`HJO.Braid.IsAppendSetup` at every prefix of a composition colouring**, at the level
`aN + 1/2`, the drift `HJO.Mellit.appendDrift` and the offset
`δ_j = (N - A_{j+1})(a+b)e + δ`, so that the appended entry is the `j`-th component. -/
theorem isAppendSetup_appendFinalTuple_of_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) (hlt : a < b) {α : List ℕ} {y : Heights a b N}
    (hret : HasAboveReturns α y) {j : ℕ} (hj : j < α.length) :
    IsAppendSetup a b α[j] j (appendDrift a b N)
      ((((N - (α.take (j + 1)).sum) * (a + b) : ℕ) : ℚ) * appendDrift a b N
        + appendOffset a b N (sepLevel a N))
      (sweepTheta a b N) (appendFinalTuple a b N y (sepLevel a N) j) := by
  have hηa := isAdmissibleLevel_sepLevel a N
  have hηs : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have hηN := cast_mul_lt_sepLevel a N
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hsucc : (α.take (j + 1)).sum = (α.take j).sum + α[j] := List.sum_take_succ α j hj
  have hle : (α.take (j + 1)).sum ≤ N := by
    have h := List.monotone_sum_take α (show j + 1 ≤ α.length by omega)
    simp only [List.take_length] at h
    exact h.trans hret.2.2.1.le
  refine
    { one_le_a := ha
      one_le_b := hb
      coprime := hab
      a_lt_b := hlt
      one_le_A := hret.2.1 _ (List.getElem_mem hj)
      e_pos := appendDrift_pos ha hb hN
      delta_nonneg := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (appendDrift_pos ha hb hN).le)
        (appendOffset_pos ha hb hN hηN).le
      theta_eq := sweepTheta_eq_add_appendDrift ha hb hN
      drift := ?_
      start := ?_
      cluster_lo := ?_
      cluster_hi := ?_ }
  · rw [prefix_drift_eq hj hret.2.2.1]
    exact appendDrift_sum_lt ha hb hN hlt le_rfl (by omega)
  · rw [appendFinalTuple_zero, braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN
      hret (Fin.last j) (by rw [Fin.val_last]; exact hj), Fin.val_last,
      show 1 - sweepTheta a b N - ((((N - (α.take (j + 1)).sum) * (a + b) : ℕ) : ℚ) *
          appendDrift a b N + appendOffset a b N (sepLevel a N))
        = (1 - sweepTheta a b N - appendOffset a b N (sepLevel a N)) -
          (((N - (α.take (j + 1)).sum) * (a + b) : ℕ) : ℚ) * appendDrift a b N by ring,
      one_sub_sweepTheta_sub_appendOffset ha hb hN, appendDrift]
    have hdne : ((a : ℚ) + b) ≠ 0 := by positivity
    push_cast [Nat.cast_sub hle]
    field_simp
    ring
  · intro t
    rw [appendFinalTuple_succ, iterate_braidDataOfColouring_fst_eq_of_lt ha hb hN hab hηa hηs hηN
      le_rfl hret t.castSucc (by rw [Fin.val_castSucc]; omega), Fin.val_castSucc]
    exact sweepTheta_sub_lt_final ha hb hN hlt le_rfl _
  · intro t
    rw [appendFinalTuple_succ, iterate_braidDataOfColouring_fst_eq_of_lt ha hb hN hab hηa hηs hηN
      le_rfl hret t.castSucc (by rw [Fin.val_castSucc]; omega), Fin.val_castSucc,
      prefix_drift_eq hj hret.2.2.1]
    refine final_lt_sweepTheta_sub ha hb hN ?_
    have := sum_take_lt hret.2.1 (show (t : ℕ) < j from t.isLt) (by omega)
    omega

/-! ### The append step at every prefix, and the induction -/

section Induction

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter` at every prefix of a composition colouring.** The
rank-`(j+1)` prefix of the data of `c_α` at the level `aN + 1/2` is the rank-`j` prefix with the
`j`-th component appended, and the append step multiplies by `(-1)^{(a-1)α_j}(qu)^{1-α_j}` and
post-composes the stage `G_{j+1,α_j}`. -/
theorem sweepIn_braidRep_specialBraid_succ_of_lt {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b) (hlt : a < b)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {j : ℕ} (hj : j < α.length) :
    sweepIn q u a b (j + 1)
        ((braidRepMellit q u hq hq1 hqp hr (j + 1)
            (specialBraid (sweepTheta a b N)
              (braidDataOfColouring a b N y (sepLevel a N) (j + 1)).1
              (braidDataOfColouring a b N y (sepLevel a N) (j + 1)).2)
          (dplusIterPiece q (j + 1)) : pieceSub L (j + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * α[j]) * (q * u) ^ (1 - (α[j] : ℤ))) •
          stage (sweepWitness q u a b) Ω a b j α[j] (sweepIn q u a b j
            ((braidRepMellit q u hq hq1 hqp hr j
                (specialBraid (sweepTheta a b N)
                  (braidDataOfColouring a b N y (sepLevel a N) j).1
                  (braidDataOfColouring a b N y (sepLevel a N) j).2)
              (dplusIterPiece q j) : pieceSub L j) : Total L)) := by
  have hηa := isAdmissibleLevel_sepLevel a N
  have hηs : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have hηN := cast_mul_lt_sepLevel a N
  have hdata := isSpecialBraidData_braidDataOfColouring_of_le ha hb hN hab hηa hηs hηN hret
    (j := j + 1) hj
  have H := isAppendSetup_appendFinalTuple_of_lt ha hb hN hab hlt hret hj
  have key := sweepIn_braidRep_specialBraid (u := u) hq hq1 hqp hr hΩ H hdata.comp_rotateLast
    (by
      simp only [Function.comp_apply, rotateLast_zero]
      rw [braidDataOfColouring_snd_of_lt ha hb hN hab hηa hηs hηN hret (Fin.last j)
        (by rw [Fin.val_last]; exact hj)]
      simp only [Fin.val_last]
      rw [Nat.mul_comm])
    (by
      simp only [Function.comp_apply, rotateLast_zero]
      rw [← appendFinalTuple_zero]
      exact H.start)
    (by
      intro t i hi
      simp only [Function.comp_apply, rotateLast_zero, rotateLast_succ] at hi ⊢
      exact braidDataOfColouring_gap_of_lt ha hb hN hab hret hj t i hi)
    (by
      intro t
      simp only [Function.comp_apply, rotateLast_zero, rotateLast_succ]
      exact braidDataOfColouring_fst_lt_of_lt ha hb hN hab hηa hηs hηN hret t.castSucc
        (Fin.last j) (by rw [Fin.val_castSucc, Fin.val_last]; exact t.isLt)
        (by rw [Fin.val_last]; exact hj))
    (by
      rw [show ((braidDataOfColouring a b N y (sepLevel a N) (j + 1)).2 ∘ rotateLast j) ∘ Fin.succ
            = (braidDataOfColouring a b N y (sepLevel a N) (j + 1)).2 ∘ Fin.castSucc from
          comp_rotateLast_comp_succ _]
      exact moveTuple_eq_appendFinalTuple a b N y (sepLevel a N) j)
  rwa [specialBraid_comp_rotateLast hdata,
    show ((braidDataOfColouring a b N y (sepLevel a N) (j + 1)).1 ∘ rotateLast j) ∘ Fin.succ
        = (braidDataOfColouring a b N y (sepLevel a N) j).1 from
      (comp_rotateLast_comp_succ _).trans (braidDataOfColouring_fst_comp_castSucc a b N y _ j),
    show ((braidDataOfColouring a b N y (sepLevel a N) (j + 1)).2 ∘ rotateLast j) ∘ Fin.succ
        = (braidDataOfColouring a b N y (sepLevel a N) j).2 from
      (comp_rotateLast_comp_succ _).trans (braidDataOfColouring_snd_comp_castSucc a b N y _ j)]
    at key

/-- At rank `0` the braid is the identity and `d_+^0(1) = 1`. -/
theorem coe_braidRepMellit_specialBraid_zero {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (θ : ℚ) (v : Fin 0 → ℚ) (β : Fin 0 → ℕ) :
    ((braidRepMellit q u hq hq1 hqp hr 0 (specialBraid θ v β) (dplusIterPiece q 0)
      : pieceSub L 0) : Total L) = 1 := by
  rw [specialBraid_zero, map_one, Module.End.one_apply, coe_dplusIterPiece]
  rfl

/-- **The closed form at every prefix.** For the colouring of an above-diagonal path of return
composition `α` at the level `aN + 1/2`, the braid value of the rank-`j` prefix of its data is
`(-1)^{(a-1)A_j}(qu)^{j-A_j} G_{j,α_j} ⋯ G_{1,α_1}(1)`, where `A_j = α_1 + ⋯ + α_j`. -/
theorem sweepIn_braidRep_specialBraid_take {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b) (hlt : a < b)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) :
    ∀ j, j ≤ α.length →
      sweepIn q u a b j
          ((braidRepMellit q u hq hq1 hqp hr j
              (specialBraid (sweepTheta a b N)
                (braidDataOfColouring a b N y (sepLevel a N) j).1
                (braidDataOfColouring a b N y (sepLevel a N) j).2)
            (dplusIterPiece q j) : pieceSub L j) : Total L)
        = inductionScalar q u a (α.take j) • stageWord (sweepWitness q u a b) Ω a b (α.take j)
  | 0, _ => by
    rw [coe_braidRepMellit_specialBraid_zero, sweepIn_zero_one, List.take_zero,
      inductionScalar_nil, one_smul, stageWord]
    rfl
  | j + 1, hj => by
    have hjl : j < α.length := by omega
    have hpos : ∀ x ∈ α.take j, 0 < x := fun x hx => hret.2.1 x (List.mem_of_mem_take hx)
    have hA : 0 < α[j] := hret.2.1 _ (List.getElem_mem hjl)
    rw [sweepIn_braidRep_specialBraid_succ_of_lt hq hq1 hqp hr hΩ ha hb hN hab hlt hret hjl,
      sweepIn_braidRep_specialBraid_take hq hq1 hqp hr hΩ ha hb hN hab hlt hret j hjl.le,
      map_smul, smul_smul, List.take_succ_eq_append_getElem hjl, inductionScalar_append q u hpos hA,
      stageWord_append, List.length_take, min_eq_left hjl.le]

/-- **The braid side of `HJO.Mellit.mellitInduction_sweepWitness`, unconditionally.** At the level
`aN + 1/2`, the braid value `π_ℓ(B_{s,v,α^{br}}) d_+^ℓ(1)` of the colouring of an above-diagonal
path of return composition `α` — with its `q`-power factor, which is `1` because the two inversion
counts agree — is `(-1)^{(a-1)N} (qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`. -/
theorem sweepIn_braidValueOfPath_sepLevel {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b) (hlt : a < b)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) :
    sweepIn q u a b α.length (braidValueOfPath q u hq hq1 hqp hr y (sepLevel a N))
      = inductionScalar q u a α • stageWord (sweepWitness q u a b) Ω a b α := by
  have hηa := isAdmissibleLevel_sepLevel a N
  have hηs : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  have hηN := cast_mul_lt_sepLevel a N
  have hE := card_colouringEast_hasAboveReturns hηa hηs hab ha hb hN hηN hret
  have hNo := card_colouringNorth_hasAboveReturns hηa hηs hab ha hb hN hret
  have hinv := invFin_eq_invIni_of_separatesDiagonal ha hb hN hηa hηs hret.1
  rw [hNo] at hinv
  rw [braidValueOfPath, braidValueOfData, hE, hinv, sub_self, zpow_zero, one_smul,
    sweepIn_braidRep_specialBraid_take hq hq1 hqp hr hΩ ha hb hN hab hlt hret α.length le_rfl,
    List.take_length]

/-- **The braid side of `HJO.Mellit.mellitInduction_sweepWitness` at the composition colouring.**
`HJO.Mellit.sweepIn_braidValueOfPath_sepLevel` read through the representative path of
`HJO.Mellit.braidValueColouring`, which at a separating level has return composition `α` by
`HJO.Mellit.colouring_eq_compColouring_iff`. -/
theorem sweepIn_braidValueColouring_compColouring {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b) (hlt : a < b)
    {α : List ℕ} (hpos : ∀ x ∈ α, 0 < x) (hsum : α.sum = N) :
    sweepIn q u a b α.length
        (braidValueColouring q u hq hq1 hqp hr a b N (sepLevel a N) (compColouring a b α))
      = inductionScalar q u a α • stageWord (sweepWitness q u a b) Ω a b α := by
  have hηa := isAdmissibleLevel_sepLevel a N
  have hηs : SeparatesDiagonal a b N (sepLevel a N) := separatesDiagonal_sepLevel hN
  obtain ⟨hy, hc⟩ := colouringRep_spec
    (isAdmissibleColouring_compColouring hηa hηs hab ha hb hpos hsum)
  have hret := (colouring_eq_compColouring_iff hηa hηs hab ha hb hpos hsum hy).1 hc
  exact sweepIn_braidValueOfPath_sepLevel hq hq1 hqp hr hΩ ha hb hN hab hlt hret

end Induction

/-! ### The assembly -/

section Assembly

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Mellit.mellitInduction_sweepWitness` from the type-`BE` clause of the braid recursion.**
Given a square root `r` of `q` and the floored `BE` clause of the level recursion for the braid
candidate at every positive `N`, the clause `HJO.Mellit.MellitInduction` holds at the witness. -/
theorem mellitInduction_of_sweepRecursionBEFloor {q u r : L} (hq : q ≠ 0) (hq1 : q ≠ 1)
    (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 0 < a) (hlt : a < b)
    (hBE : ∀ N : ℕ, 0 < N →
      SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N)) :
    MellitInduction (sweepWitness q u a b) a b := by
  have hb : 0 < b := by omega
  intro Ω hΩ N η hηa hηs α hpos hsum
  rw [isColouringValue_sweepWitness q u hab ha hb N η hηa hηs α hpos hsum]
  subst hsum
  change braidValue q u a b α = inductionScalar q u a α • stageWord (sweepWitness q u a b) Ω a b α
  rcases Nat.eq_zero_or_pos α.sum with h0 | hN
  · have hnil : α = [] := by
      rcases α with _ | ⟨x, l⟩
      · rfl
      · have := hpos x (List.mem_cons_self ..)
        simp only [List.sum_cons] at h0
        omega
    subst hnil
    rw [braidValue_nil q u hab ha hb, inductionScalar_nil, one_smul, stageWord]
    rfl
  · have hηa' := isAdmissibleLevel_sepLevel a α.sum
    have hηs' : SeparatesDiagonal a b α.sum (sepLevel a α.sum) := separatesDiagonal_sepLevel hN
    rw [braidValue_eq_sweepIn ha hb hpos,
      ← braidValueColouring_eq_dsc_of_BEUnsweptFloor q u hq hq1 hqp hr hu ha hb hN hlt
        (hBE _ hN) (braidValueColouring_sweepRecursionUnsweptFloor q u hq hq1 hqp hr ha hb hN hlt)
        hηa' (cast_mul_lt_sepLevel a α.sum)
        (isAdmissibleColouring_compColouring hηa' hηs' hab ha hb hpos rfl)]
    exact sweepIn_braidValueColouring_compColouring hq hq1 hqp hr hΩ ha hb hN hab hlt hpos rfl

/-- `AlgebraicIndependent ℤ ![q, u]` forces `q + 1 ≠ 0`: `q² - 1` is a unit. -/
theorem add_one_ne_zero_of_algebraicIndependent_fst {K : Type*} [Field K] {q u : K}
    (hqu : AlgebraicIndependent ℤ ![q, u]) : q + 1 ≠ 0 := fun h => by
  have hunit := isUnit_pow_sub_one_of_algebraicIndependent_fst hqu 1
  have hq : q = -1 := eq_neg_of_add_eq_zero_left h
  rw [hq] at hunit
  norm_num at hunit

/-- **`HJO.Mellit.mellitInduction_sweepWitness` in the shape of the `hind` binder of
`HJO.Mellit.shuffle_of_lhs_and_induction`, at every `q` that is a square, from the type-`BE` clause
of the braid recursion.** The genericity conditions the braid representation and the clauses ask
for are read off `AlgebraicIndependent ℤ ![q, u]`. -/
theorem mellitInduction_sweepWitness_of_sweepRecursionBEFloor
    (hBE : ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ (r : L) (hr : r * r = q)
      (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (a b N : ℕ), Nat.Coprime a b → 1 < a →
        a < b → 0 < N →
          SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N)) :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → IsSquare q → ∀ a b : ℕ, Nat.Coprime a b →
      1 < a → a < b → MellitInduction (sweepWitness q u a b) a b := by
  intro q u hqu hsq a b hab ha hlt
  obtain ⟨r, hr⟩ := hsq
  have hq := ne_zero_of_algebraicIndependent_fst hqu
  have hq1 := ne_one_of_algebraicIndependent_fst hqu
  have hqp := add_one_ne_zero_of_algebraicIndependent_fst hqu
  exact mellitInduction_of_sweepRecursionBEFloor hq hq1 hqp hr.symm
    (ne_zero_of_algebraicIndependent_snd hqu) hab (by omega) hlt
    (fun N hN => hBE q u hqu r hr.symm hq hq1 hqp a b N hab ha hlt hN)

end Assembly

end HJO.Mellit

end
