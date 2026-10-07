/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidAppendGrid
public import HJO.Shuffle.BraidRotation
public import HJO.Shuffle.MellitProp57
public meta import HJO.Attr

/-! # The final positions of a composition colouring, and `HJO.Braid.IsAppendSetup`

`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` puts every *initial* position of a composition
colouring in closed form. `HJO.Braid.IsAppendSetup` asks about the *final* ones: its `cluster_lo`
and `cluster_hi` clauses locate the other `k` points after they have finished moving, and its
`drift` clause bounds the accumulated perturbation. This file computes the final positions, in
closed form, and discharges every clause.

## The computation

Component `t` starts at `v_t = (bP + aA_{t+1} - 1 - \eta)/D` with `P = (aN+1)N` and
`D = (a+b)P - 1`, and it moves `\beta_t - 1 = (a+b)\alpha_{t+1} - 2` times. Since `\theta = aP/D`
and `(a+b)P = D + 1`,

```
(a+b)\alpha\theta = \alpha a (D+1)/D = \alpha a + \alpha a/D,
```

so the whole run of moves shifts the position by an *integer* plus a small correction, and the
fractional part collapses:

```
nx_\theta^{\beta_t - 1}(v_t) = (aP + aA_t - \eta)/D = \theta + (aA_t - \eta)/D,
```

where `A_t = \alpha_1 + \cdots + \alpha_t` is the partial sum **before** component `t`'s own part.
The appended component's part has dropped out; what remains is a point just below `\theta`, which is
exactly the sentence "in the final position all points are clustered close to `finish`" of
A. Mellit, *Toric braids and (m, n)-parking functions*, arXiv:1604.07456, Section 6.

## Main results

* `HJO.Mellit.iterate_braidDataOfColouring_fst_eq` — the display above: the final position of every
  component, in closed form.
* `HJO.Mellit.appendDrift` and `HJO.Mellit.sweepTheta_eq_add_appendDrift` — **the value of `e`**:
  `\theta = a/(a+b) + e` with `e = a/((a+b)D)`. `HJO.Braid.IsAppendSetup` leaves `e` free and asks
  only `0 < e`; the colouring pins it.
* `HJO.Mellit.appendFinalTuple` — the tuple `hmove` asks for, taken as a *definition*, so that
  `hmove` is `rfl` and its content migrates into `start`, `cluster_lo` and `cluster_hi`.
* `HJO.Mellit.isAppendSetup_appendFinalTuple` — **`HJO.Braid.IsAppendSetup`, discharged.** Every one
  of its twelve fields is now a theorem about the composition colouring at the pinned
  `e = HJO.Mellit.appendDrift` and `\delta = HJO.Mellit.appendOffset`.
* `HJO.Mellit.sweepIn_braidRep_specialBraid_appendFinalTuple` — **the append clause with all seven
  hypotheses discharged**, at `\eta = HJO.Mellit.sepLevel a N`.

## What the clauses cost

`cluster_hi` is the arithmetic statement `A_t + \alpha_\ell < N`: the partial sum before an
*earlier* component plus the appended component's own part misses `N` by at least the part of the
component between them. `cluster_lo` and `drift` both reduce to
`(a+b)((aN+1)N - aN - 1/2) > 1`, which needs `a + b \ge 3` — available from the structure's own
`a_lt_b`, and the only place `a < b` is spent.
Nothing needs `q`, `u`, a field or a representation.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep Braid

variable {a b N : ℕ}

/-- `HJO.Mellit.sepLevel` is a separating level: it lies above `aN`. -/
theorem cast_mul_lt_sepLevel (a N : ℕ) : ((a * N : ℕ) : ℚ) < sepLevel a N := by
  rw [sepLevel]
  push_cast
  linarith

/-! ### The value of the perturbation `e` -/

/-- **The perturbation of `HJO.Braid.IsAppendSetup`**, at the composition colouring:
`e = a/((a+b)D)` with `D = a(aN+1)N + b(aN+1)N - 1`. The structure leaves `e` free and asks only
`0 < e`; `\theta = a/(a+b) + e` pins it, since `\theta D = a(aN+1)N` and `(a+b)(aN+1)N = D + 1`. -/
noncomputable def appendDrift (a b N : ℕ) : ℚ :=
  (a : ℚ) / (((a : ℚ) + b) *
    ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1))

theorem appendDrift_pos (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) : 0 < appendDrift a b N := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  exact div_pos ha' (by positivity)

/-- **`theta_eq`: `\theta = a/(a+b) + e` at `e = HJO.Mellit.appendDrift`.** The slope is `b/a`
perturbed, and the perturbation is exactly one part in `(a+b)D`. -/
theorem sweepTheta_eq_add_appendDrift (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N = (a : ℚ) / ((a : ℚ) + b) + appendDrift a b N := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hθ := sweepTheta_mul_rankSpan (a := a) (b := b) (N := N) ha hb hN
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hd : (0 : ℚ) < (a : ℚ) + b := by linarith
  rw [appendDrift, div_add_div _ _ hd.ne' (by positivity), eq_div_iff (by positivity)]
  linear_combination ((a : ℚ) + b) ^ 2 * hθ

/-! ### The final position of a component -/

/-- **The one identity behind the final position**, with the colouring's data abstracted away:
lowering `(bQ + a(A+p) - 1 - \eta)/D` by `((a+b)p - 2)\theta`, where `D = aQ + bQ - 1` and
`\theta D = aQ`, lands on `(aQ + aA - \eta)/D` shifted by the **integer** `1 - pa`. Every occurrence
of the part `p` has left the fractional part; that is the whole mechanism of
`HJO.Mellit.iterate_braidDataOfColouring_fst_eq`, and stating it separately keeps the colouring's
casts out of the `ring` call. -/
theorem append_iterate_shift {ar br Q A p η θ : ℚ} (hD : ar * Q + br * Q - 1 ≠ 0)
    (hθ : θ * (ar * Q + br * Q - 1) = ar * Q) :
    (br * Q + ar * (A + p) - 1 - η) / (ar * Q + br * Q - 1) - ((ar + br) * p - 2) * θ
      = (ar * Q + ar * A - η) / (ar * Q + br * Q - 1) + (1 - p * ar) := by
  have h1 : (br * Q + ar * (A + p) - 1 - η) / (ar * Q + br * Q - 1)
      - (ar * Q + ar * A - η) / (ar * Q + br * Q - 1)
      = ((br * Q + ar * (A + p) - 1 - η) - (ar * Q + ar * A - η)) / (ar * Q + br * Q - 1) :=
    div_sub_div_same _ _ _
  have h2 : ((br * Q + ar * (A + p) - 1 - η) - (ar * Q + ar * A - η)) / (ar * Q + br * Q - 1)
      = ((ar + br) * p - 2) * θ + (1 - p * ar) := by
    rw [div_eq_iff hD]
    linear_combination (2 - (ar + br) * p) * hθ
  linarith [h1, h2]

/-- **THE FINAL POSITION OF EVERY COMPONENT OF A COMPOSITION COLOURING.**

```
nx_\theta^{\beta_t - 1}(v_t) = (a(aN+1)N + aA_t - \eta)/D,     A_t = \alpha_1 + \cdots + \alpha_t,
```

the partial sum being the one **before** component `t`'s own part: the run of `\beta_t - 1` moves
consumes exactly `\alpha_{t+1}`, which is what makes the answer a function of `A_t` alone.

The mechanism is that `(a+b)\theta = a + a/D`, so `((a+b)\alpha - 2)\theta` is an integer plus
`(\alpha a - 2a(aN+1)N)/D`, and `HJO.Braid.iterate_nextCrossing_eq_fract` turns the run into a
single fractional part, which the integer does not see. The two bounds placing the value in
`[0, 1)` are `\eta \le aN + 1/2 \le a(aN+1)N` below and `A_t \le N` above. -/
theorem iterate_braidDataOfColouring_fst_eq (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) (hηle : η ≤ sepLevel a N)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ}
    (hlen : α.length = k + 1) (i : Fin (k + 1)) :
    (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η (k + 1)).2 i - 1]
        ((braidDataOfColouring a b N y η (k + 1)).1 i)
      = ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hDne : (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 ≠ 0 := hD.ne'
  have hθD := sweepTheta_mul_rankSpan (a := a) (b := b) (N := N) ha hb hN
  have hdata := isSpecialBraidData_braidDataOfColouring_succ ha hb hN hab hηa hηs hηN hret hlen
  obtain ⟨hθ0, hθ1⟩ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hb' : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
  have hN' : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hi : (i : ℕ) < α.length := by rw [hlen]; exact i.isLt
  -- the multiplicity, and the number of moves
  have hβ : (braidDataOfColouring a b N y η (k + 1)).2 i = (a + b) * α[(i : ℕ)] - 1 := by
    rw [braidDataOfColouring_snd]
    exact card_componentCrossingIndices_hasAboveReturns ha hb hN hab hηa hηs hηN hret hi
  have hpart : 1 ≤ α[(i : ℕ)] := hret.2.1 _ (List.getElem_mem hi)
  have hab2 : 2 ≤ (a + b) * α[(i : ℕ)] := by
    have : 2 * 1 ≤ (a + b) * α[(i : ℕ)] := Nat.mul_le_mul (by omega) hpart
    omega
  -- the run of moves avoids the puncture
  have hne : ∀ j, j < (braidDataOfColouring a b N y η (k + 1)).2 i - 1 →
      (nextCrossing (sweepTheta a b N))^[j] ((braidDataOfColouring a b N y η (k + 1)).1 i)
        ≠ sweepTheta a b N := fun j hj => hdata.ne_theta i j (by omega)
  -- the partial sums
  have hsucc : (α.take ((i : ℕ) + 1)).sum = (α.take (i : ℕ)).sum + α[(i : ℕ)] :=
    List.sum_take_succ α _ hi
  have hle : (α.take (i : ℕ)).sum ≤ N := by
    have h := List.monotone_sum_take α (show (i : ℕ) ≤ α.length by omega)
    simp only [List.take_length] at h
    exact h.trans hret.2.2.1.le
  have hleq : (((α.take (i : ℕ)).sum : ℕ) : ℚ) ≤ (N : ℚ) := by exact_mod_cast hle
  have hA0 : (0 : ℚ) ≤ (((α.take (i : ℕ)).sum : ℕ) : ℚ) := Nat.cast_nonneg _
  have hηq : (a : ℚ) * N < η := by push_cast at hηN; exact hηN
  have hηle' : η ≤ (a : ℚ) * N + 1 / 2 := by rw [sepLevel] at hηle; linarith
  -- the position of the target in `[0, 1)`
  have haN : (1 : ℚ) ≤ (a : ℚ) * N := by nlinarith
  have haN2 : (1 : ℚ) ≤ ((a : ℚ) * N) * ((a : ℚ) * N) := by nlinarith
  have hbP : (2 : ℚ) ≤ (b : ℚ) * ((a : ℚ) * N + 1) * N := by nlinarith
  have haA : (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) ≤ (a : ℚ) * N :=
    mul_le_mul_of_nonneg_left hleq (by linarith)
  have hlo : (0 : ℚ) ≤ ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) - η)
      := by nlinarith
  have hhi : (a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) - η
      < (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 := by linarith
  -- the run of moves is a single fractional part, and the part `α[i]` leaves it as an integer
  have haux := append_iterate_shift (ar := (a : ℚ)) (br := (b : ℚ))
    (Q := ((a : ℚ) * N + 1) * N) (A := (((α.take (i : ℕ)).sum : ℕ) : ℚ))
    (p := ((α[(i : ℕ)] : ℕ) : ℚ)) (η := η) (θ := sweepTheta a b N)
    (fun h => hDne (by linear_combination h)) (by linear_combination hθD)
  have hz : ((b : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take ((i : ℕ) + 1)).sum : ℕ) - 1 - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        - ((((a + b) * α[(i : ℕ)] - 2 : ℕ)) : ℚ) * sweepTheta a b N
      = ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((α.take (i : ℕ)).sum : ℕ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
        + ((1 - (α[(i : ℕ)] : ℤ) * (a : ℤ) : ℤ) : ℚ) := by
    rw [Nat.cast_sub hab2, hsucc]
    push_cast [-Nat.cast_list_sum]
    linear_combination haux
  rw [iterate_nextCrossing_eq_fract hθ0 hθ1 (hdata.mem_Ioo i).1 (hdata.mem_Ioo i).2 _ hne,
    braidDataOfColouring_fst_hasAboveReturns ha hb hN hab hηa hηs hηN hret i hi, hβ,
    show (a + b) * α[(i : ℕ)] - 1 - 1 = (a + b) * α[(i : ℕ)] - 2 from by omega, hz,
    Int.fract_add_intCast,
    Int.fract_eq_self.2 ⟨div_nonneg hlo hD.le, by rw [div_lt_one hD]; exact hhi⟩]

/-- **The closed form checked against an explicit instance.** For `(a,b,N) = (2,3,2)` with return
composition `[1,1]` and `\eta = 9/2`, component `0` starts at `53/98`
(`HJO.Mellit.braidDataOfColouring_fst_hasAboveReturns` at `A_1 = 1`) and moves `\beta_0 - 1 = 3`
times; `nx_\theta` at `\theta = 40/98` sends `53/98 \mapsto 13/98 \mapsto 71/98 \mapsto 31/98`, and
`(a(aN+1)N + 0 - \eta)/D = (20 - 9/2)/49 = 31/98`. The cluster is at `31/98`, against
`\theta - 1/(a+b) = 20.4/98` below and `\theta - (A(a+b)e + \delta) = 35/98` above: both clauses
hold with room. -/
theorem iterate_braidDataOfColouring_fst_example :
    (nextCrossing (sweepTheta 2 3 2))^[(braidDataOfColouring 2 3 2
          (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 2).2 0 - 1]
        ((braidDataOfColouring 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 2).1 0)
      = 31 / 98 := by
  rw [iterate_braidDataOfColouring_fst_eq (a := 2) (b := 3) (N := 2) (k := 1) (by norm_num)
    (by norm_num) (by norm_num) (by decide) (isAdmissibleLevel_sepLevel 2 2)
    (separatesDiagonal_sepLevel (by norm_num)) (cast_mul_lt_sepLevel 2 2) le_rfl
    hasAboveReturns_example (by norm_num) 0]
  rw [sepLevel]
  norm_num

/-! ### The tuple `hmove` asks for, taken as a definition -/

/-- **The tuple of final positions, at the relabelled colouring data.** The `hmove` of
`HJO.Mellit.braidRep_specialBraid_dplusIter` asserts `moveTuple θ (v ∘ ρ) (moves) = w` for a tuple
`w` that lemma leaves free; naming the left-hand side discharges `hmove` by `rfl` and moves the
content into the `start`, `cluster_lo` and `cluster_hi` clauses of `HJO.Braid.IsAppendSetup`, where
it belongs. -/
noncomputable def appendFinalTuple (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    Fin (k + 1) → ℚ :=
  moveTuple (sweepTheta a b N) ((braidDataOfColouring a b N y η (k + 1)).1 ∘ rotateLast k)
    ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc)).map Fin.succ)

/-- **`hmove`, by definition.** -/
theorem moveTuple_eq_appendFinalTuple (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    moveTuple (sweepTheta a b N) ((braidDataOfColouring a b N y η (k + 1)).1 ∘ rotateLast k)
        ((specialMoveList ((braidDataOfColouring a b N y η (k + 1)).2 ∘ Fin.castSucc)).map Fin.succ)
      = appendFinalTuple a b N y η k := rfl

/-- The appended entry is never moved — the move list is `Fin.succ` of something — so it keeps the
position `HJO.Braid.rotateLast` put at index `0`, the colouring's last. -/
theorem appendFinalTuple_zero (a b N : ℕ) (y : Heights a b N) (η : ℚ) (k : ℕ) :
    appendFinalTuple a b N y η k 0 = (braidDataOfColouring a b N y η (k + 1)).1 (Fin.last k) := by
  rw [appendFinalTuple, moveTuple_apply_of_notMem _ (by
    intro h
    obtain ⟨t, _, ht⟩ := List.mem_map.1 h
    exact Fin.succ_ne_zero t ht), Function.comp_apply, rotateLast_zero]

/-- Every other entry is moved `β_t - 1` times, `HJO.Braid.specialBraid` putting `β_t - 1` copies of
`t` in the list. -/
theorem appendFinalTuple_succ (a b N : ℕ) (y : Heights a b N) (η : ℚ) {k : ℕ} (t : Fin k) :
    appendFinalTuple a b N y η k t.succ
      = (nextCrossing (sweepTheta a b N))^[(braidDataOfColouring a b N y η (k + 1)).2 t.castSucc
          - 1]
          ((braidDataOfColouring a b N y η (k + 1)).1 t.castSucc) := by
  rw [appendFinalTuple, moveTuple_apply_eq_iterate,
    List.count_map_of_injective _ _ (Fin.succ_injective k), count_specialMoveList,
    Function.comp_apply, Function.comp_apply, rotateLast_succ]

/-! ### The parts of the composition -/

theorem getLast_eq_getElem_of_length {α : List ℕ} {k : ℕ} (hlen : α.length = k + 1)
    (hα : α ≠ []) : α.getLast hα = α[k]'(by omega) := by
  rw [List.getLast_eq_getElem hα]
  congr 1
  omega

/-- `N` splits as the sum before the last part plus the last part. -/
theorem sum_take_add_getLast {α : List ℕ} {k N : ℕ} (hlen : α.length = k + 1) (hα : α ≠ [])
    (hsum : α.sum = N) : (α.take k).sum + α.getLast hα = N := by
  have h := List.sum_take_succ α k (by omega)
  rw [show k + 1 = α.length from hlen.symm, List.take_length] at h
  rw [getLast_eq_getElem_of_length hlen hα, ← h, hsum]

/-! ### The `drift` clause, and the two cluster clauses -/

theorem sweepTheta_eq_div_rankSpan (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) :
    sweepTheta a b N = ((a : ℚ) * ((a : ℚ) * N + 1) * N) /
      ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  rw [eq_div_iff hD.ne']
  exact sweepTheta_mul_rankSpan ha hb hN

/-- **The whole of what `HJO.Braid.IsAppendSetup` charges for the run**, over the span `D`:
`A(a+b)e + δ = (Aa + η - aN)/D`. The `(a+b)` of the drift cancels the `(a+b)` in
`HJO.Mellit.appendDrift`, which is why the two clauses that read it are inequalities between
integers. -/
theorem appendDrift_sum (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (η : ℚ) (A : ℕ) :
    ((A * (a + b) : ℕ) : ℚ) * appendDrift a b N + appendOffset a b N η
      = ((A : ℚ) * a + η - (a : ℚ) * N) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hDne : (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 ≠ 0 := hD.ne'
  have ha' : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
  have hb' : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hdne : ((a : ℚ) + b) ≠ 0 := by positivity
  rw [appendDrift, appendOffset]
  push_cast
  field_simp
  ring

/-- `a + b ≥ 3` from the structure's own `a_lt_b`: the one place `a < b` is spent, and all it is
spent on is keeping `1/(a+b)` below `1/2`. -/
theorem three_le_add (ha : 0 < a) (hlt : a < b) : (3 : ℚ) ≤ (a : ℚ) + b := by
  have h1 : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have h2 : (2 : ℚ) ≤ (b : ℚ) := by exact_mod_cast show 2 ≤ b by omega
  linarith

/-- The bound both `drift` and `cluster_lo` reduce to: `(aN+1)N` exceeds `aN + 1/2` by at least
`1/2`, since `aN(N-1) ≥ 0` and `N ≥ 1`. -/
theorem half_le_sub_sepLevel (ha : 0 < a) (hN : 0 < N) {η : ℚ} (hηle : η ≤ sepLevel a N)
    (c : ℚ) (hc : 0 ≤ c) : (1 : ℚ) / 2 ≤ ((a : ℚ) * N + 1) * N + c - η := by
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hN' : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hηle' : η ≤ (a : ℚ) * N + 1 / 2 := by rw [sepLevel] at hηle; linarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ))
      (by linarith : (0 : ℚ) ≤ (N : ℚ)))
    (by linarith : (0 : ℚ) ≤ (N : ℚ) - 1)]

/-- **`drift`, discharged.** `A(a+b)e + δ = (Aa + η - aN)/D < 1/(a+b)` because
`(a+b)((aN+1)N - Aa - η + aN) > 1`: the bracket is at least `1/2` by
`HJO.Mellit.half_le_sub_sepLevel` at `A ≤ N`, and `a + b ≥ 3`. -/
theorem appendDrift_sum_lt (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hlt : a < b) {η : ℚ}
    (hηle : η ≤ sepLevel a N) {A : ℕ} (hAN : A ≤ N) :
    ((A * (a + b) : ℕ) : ℚ) * appendDrift a b N + appendOffset a b N η < 1 / ((a : ℚ) + b) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hDne : (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 ≠ 0 := hD.ne'
  have hd3 := three_le_add (a := a) (b := b) ha hlt
  have hdpos : (0 : ℚ) < (a : ℚ) + b := by linarith
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hAq : ((A : ℕ) : ℚ) ≤ (N : ℚ) := by exact_mod_cast hAN
  have hA0 : (0 : ℚ) ≤ ((A : ℕ) : ℚ) := Nat.cast_nonneg _
  -- the bracket is at least `1/2`
  have hS : (1 : ℚ) / 2 ≤ ((a : ℚ) * N + 1) * N - (A : ℚ) * a - η + (a : ℚ) * N := by
    have h := half_le_sub_sepLevel (a := a) (N := N) ha hN hηle ((a : ℚ) * N - (A : ℚ) * a)
      (by nlinarith)
    linarith
  have hnum : (0 : ℚ) < ((a : ℚ) + b) *
      (((a : ℚ) * N + 1) * N - (A : ℚ) * a - η + (a : ℚ) * N) - 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ) + b - 3) (by linarith :
      (0 : ℚ) ≤ ((a : ℚ) * N + 1) * N - (A : ℚ) * a - η + (a : ℚ) * N)]
  rw [appendDrift_sum ha hb hN, div_lt_div_iff₀ hD hdpos]
  linarith [hnum]

/-- **`cluster_lo`, discharged.** Every final position `\theta + (aA_t - \eta)/D` is above
`\theta - 1/(a+b)`, since `(a+b)((aN+1)N + aA_t - \eta) > 1`. -/
theorem sweepTheta_sub_lt_final (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hlt : a < b) {η : ℚ}
    (hηle : η ≤ sepLevel a N) (At : ℕ) :
    sweepTheta a b N - 1 / ((a : ℚ) + b)
      < ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((At : ℕ) : ℚ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have hDne : (a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1 ≠ 0 := hD.ne'
  have hd3 := three_le_add (a := a) (b := b) ha hlt
  have hdpos : (0 : ℚ) < (a : ℚ) + b := by linarith
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hAt : (0 : ℚ) ≤ ((At : ℕ) : ℚ) := Nat.cast_nonneg _
  have hS : (1 : ℚ) / 2 ≤ ((a : ℚ) * N + 1) * N + (a : ℚ) * ((At : ℕ) : ℚ) - η :=
    half_le_sub_sepLevel (a := a) (N := N) ha hN hηle _ (by positivity)
  have hnum : (0 : ℚ) < ((a : ℚ) + b) *
      (((a : ℚ) * N + 1) * N + (a : ℚ) * ((At : ℕ) : ℚ) - η) - 1 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ (a : ℚ) + b - 3) (by linarith :
      (0 : ℚ) ≤ ((a : ℚ) * N + 1) * N + (a : ℚ) * ((At : ℕ) : ℚ) - η)]
  rw [sweepTheta_eq_div_rankSpan ha hb hN, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add',
    div_sub_div_same, div_lt_div_iff₀ hD hdpos]
  linarith [hnum]

/-- **`cluster_hi`, discharged.** The final position of component `t` is below
`\theta - (A_\ell(a+b)e + \delta)` exactly when `A_t + A_\ell < N`, the level `\eta` cancelling on
both sides. So the clause is the purely combinatorial statement that the partial sum before an
earlier component, plus the appended component's own part, misses `N` — which it does, by the part
of the component in between. -/
theorem final_lt_sweepTheta_sub (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} {At A : ℕ}
    (hsum : At + A < N) :
    ((a : ℚ) * ((a : ℚ) * N + 1) * N + (a : ℚ) * ((At : ℕ) : ℚ) - η) /
        ((a : ℚ) * ((a : ℚ) * N + 1) * N + (b : ℚ) * ((a : ℚ) * N + 1) * N - 1)
      < sweepTheta a b N
        - (((A * (a + b) : ℕ) : ℚ) * appendDrift a b N + appendOffset a b N η) := by
  have hD := rankSpan_pos (a := a) (b := b) (N := N) ha hb hN
  have ha' : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hq : ((At : ℕ) : ℚ) + ((A : ℕ) : ℚ) < (N : ℚ) := by
    have : ((At + A : ℕ) : ℚ) < ((N : ℕ) : ℚ) := by exact_mod_cast hsum
    push_cast at this
    linarith
  rw [appendDrift_sum ha hb hN, sweepTheta_eq_div_rankSpan ha hb hN, div_sub_div_same,
    div_lt_div_iff_of_pos_right hD]
  nlinarith

/-! ### `HJO.Braid.IsAppendSetup`, discharged -/

/-- **`HJO.Braid.IsAppendSetup` AT THE COMPOSITION COLOURING.** Every field is now a theorem, at the
pinned `e = HJO.Mellit.appendDrift` and `\delta = HJO.Mellit.appendOffset`, and at the tuple
`HJO.Mellit.appendFinalTuple` which makes `hmove` an identity.

The four that were substantive:

* `start` — `HJO.Mellit.appendFinalTuple_zero` with
  `HJO.Mellit.braidDataOfColouring_fst_last_succ_eq`: the appended entry is never moved.
* `drift` — `HJO.Mellit.appendDrift_sum_lt`.
* `cluster_lo` — `HJO.Mellit.sweepTheta_sub_lt_final` at the final position computed by
  `HJO.Mellit.iterate_braidDataOfColouring_fst_eq`.
* `cluster_hi` — `HJO.Mellit.final_lt_sweepTheta_sub`, whose content is `A_t + \alpha_\ell < N`.

Only `a_lt_b` is taken from outside, and it is a field of the structure rather than a cost: the
standing hypothesis of the main theorem is `1 < a < b`. -/
theorem isAppendSetup_appendFinalTuple (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hab : Nat.Coprime a b) (hlt : a < b) {η : ℚ} (hηa : IsAdmissibleLevel η)
    (hηs : SeparatesDiagonal a b N η) (hηN : ((a * N : ℕ) : ℚ) < η) (hηle : η ≤ sepLevel a N)
    {α : List ℕ} {y : Heights a b N} (hret : HasAboveReturns α y) {k : ℕ}
    (hlen : α.length = k + 1) (hα : α ≠ []) :
    IsAppendSetup a b (α.getLast hα) k (appendDrift a b N) (appendOffset a b N η)
      (sweepTheta a b N) (appendFinalTuple a b N y η k) := by
  have hsplit := sum_take_add_getLast hlen hα hret.2.2.1
  refine
    { one_le_a := ha
      one_le_b := hb
      coprime := hab
      a_lt_b := hlt
      one_le_A := hret.2.1 _ (List.getLast_mem hα)
      e_pos := appendDrift_pos ha hb hN
      delta_nonneg := (appendOffset_pos ha hb hN hηN).le
      theta_eq := sweepTheta_eq_add_appendDrift ha hb hN
      drift := appendDrift_sum_lt ha hb hN hlt hηle (by omega)
      start := ?_
      cluster_lo := ?_
      cluster_hi := ?_ }
  · rw [appendFinalTuple_zero]
    exact braidDataOfColouring_fst_last_succ_eq ha hb hN hab hηa hηs hηN hret hlen
  · intro t
    rw [appendFinalTuple_succ, iterate_braidDataOfColouring_fst_eq ha hb hN hab hηa hηs hηN hηle
      hret hlen t.castSucc, Fin.val_castSucc]
    exact sweepTheta_sub_lt_final ha hb hN hlt hηle _
  · intro t
    rw [appendFinalTuple_succ, iterate_braidDataOfColouring_fst_eq ha hb hN hab hηa hηs hηN hηle
      hret hlen t.castSucc, Fin.val_castSucc]
    refine final_lt_sweepTheta_sub ha hb hN ?_
    have := sum_take_lt hret.2.1 (show (t : ℕ) < k from t.isLt) (by omega)
    omega

/-- **The hypotheses are jointly satisfiable.** `HJO.Mellit.hasAboveReturns_example` is an
above-diagonal `(4,6)`-path of return composition `[1,1]` with `1 < a = 2 < b = 3` coprime, so
`HJO.Mellit.isAppendSetup_appendFinalTuple` is not vacuous: it produces an actual
`HJO.Braid.IsAppendSetup`. -/
theorem isAppendSetup_example :
    IsAppendSetup 2 3 ([1, 1].getLast (by simp)) 1 (appendDrift 2 3 2)
      (appendOffset 2 3 2 (sepLevel 2 2)) (sweepTheta 2 3 2)
      (appendFinalTuple 2 3 2 (![0, 3, 3, 6, 6] : Heights 2 3 2) (sepLevel 2 2) 1) :=
  isAppendSetup_appendFinalTuple (a := 2) (b := 3) (N := 2) (k := 1) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num) (isAdmissibleLevel_sepLevel 2 2)
    (separatesDiagonal_sepLevel (by norm_num)) (cast_mul_lt_sepLevel 2 2) le_rfl
    hasAboveReturns_example (by norm_num) (by simp)

/-! ### The append clause with all seven hypotheses discharged -/

section AppendAtLast

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`HJO.Mellit.braidRep_specialBraid_dplusIter` AT THE COMPOSITION COLOURING, WITH ALL SEVEN
HYPOTHESES DISCHARGED.** On top of the `hdata`, `hβ`, `hw₀` and `hstart` of
`HJO.Mellit.sweepIn_braidRep_specialBraid_rotateLast_appendOffset`:

* `HJO.Braid.IsAppendSetup` is `HJO.Mellit.isAppendSetup_appendFinalTuple`, at
  `e = HJO.Mellit.appendDrift` and `\delta = HJO.Mellit.appendOffset`;
* `hgap` is `HJO.Mellit.braidDataOfColouring_gap`, the grid criterion at `n = 2D`;
* `hmove` is `HJO.Mellit.moveTuple_eq_appendFinalTuple`, which holds by definition.

The level is `HJO.Mellit.sepLevel a N`, and that is not a choice: `HJO.Mellit.eq_sepLevel_of_le`
shows it is the only admissible level at which the offset fits inside one cell of the
`1/(2D)`-grid, so it is the only level at which `hgap` is available by this route.

What remains of the hypotheses is the colouring's standing data — `0 < a`, `0 < b`, `0 < N`,
`Nat.Coprime a b`, `a < b`, `HJO.Mellit.HasAboveReturns` — together with the genericity
`HJO.Mellit.braidRep_specialBraid_dplusIter` itself asks of the scalars, `q \ne 0`, `q \ne 1`,
`q + 1 \ne 0` and a square root of `q`. No genericity beyond that lemma's own is spent: the whole
offset layer is lattice arithmetic. -/
theorem sweepIn_braidRep_specialBraid_appendFinalTuple {q u r : L} {k : ℕ}
    {y : Heights a b N} {α : List ℕ}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q)
    {Ω : ℕ → ℕ → ℕ → ((sweepWitness q u a b).W →ₗ[L] (sweepWitness q u a b).W)}
    (hΩ : IsReplicationFamily (sweepWitness q u a b) Ω)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hab : Nat.Coprime a b) (hlt : a < b)
    (hret : HasAboveReturns α y) (hlen : α.length = k + 1) (hα : α ≠ []) :
    sweepIn q u a b (k + 1)
        ((braidRepMellit q u hq hq1 hqp hr (k + 1)
            (specialBraid (sweepTheta a b N)
              (braidDataOfColouring a b N y (sepLevel a N) (k + 1)).1
              (braidDataOfColouring a b N y (sepLevel a N) (k + 1)).2)
          (dplusIterPiece q (k + 1)) : pieceSub L (k + 1)) : Total L)
      = ((-1 : L) ^ ((a - 1) * α.getLast hα) * (q * u) ^ (1 - (α.getLast hα : ℤ))) •
          stage (sweepWitness q u a b) Ω a b k (α.getLast hα) (sweepIn q u a b k
            ((braidRepMellit q u hq hq1 hqp hr k
                (specialBraid (sweepTheta a b N)
                  (braidDataOfColouring a b N y (sepLevel a N) k).1
                  (braidDataOfColouring a b N y (sepLevel a N) k).2)
              (dplusIterPiece q k) : pieceSub L k) : Total L)) :=
  sweepIn_braidRep_specialBraid_rotateLast_appendOffset hq hq1 hqp hr hΩ ha hb hN hab
    (isAdmissibleLevel_sepLevel a N) (separatesDiagonal_sepLevel hN) (cast_mul_lt_sepLevel a N)
    hret hlen hα
    (isAppendSetup_appendFinalTuple ha hb hN hab hlt (isAdmissibleLevel_sepLevel a N)
      (separatesDiagonal_sepLevel hN) (cast_mul_lt_sepLevel a N) le_rfl hret hlen hα)
    (braidDataOfColouring_gap ha hb hN hab (isAdmissibleLevel_sepLevel a N)
      (separatesDiagonal_sepLevel hN) (cast_mul_lt_sepLevel a N) le_rfl hret hlen)
    (moveTuple_eq_appendFinalTuple a b N y (sepLevel a N) k)

end AppendAtLast

end HJO.Mellit

end
