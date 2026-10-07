/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidCDLetterTrain
public import HJO.Shuffle.BraidCDLetterResidual
public import HJO.Shuffle.MellitZopOneV1
public import HJO.Shuffle.BraidRankRaise
public import HJO.CarlssonMellit.AmbientBrackets
public meta import HJO.Attr

/-! # `T_{k↘1} z_1` on the vacuum: the type-`D` clause

`HJO/Shuffle/BraidCDLetterResidual.lean` leaves the type-`D` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` hanging on one hypothesis `hletter`: that the
extra letter of `HJO.Braid.braidStep`, applied to the vacuum `d_+^{k}(1)` and then carried through
the rotated upper braid, is `q^{k-1-j}` times the upper braid value. **This file discharges it at a
level gap of at most one, and the clause with it.**

## The letter is `T_{k↘1}z_1` and it multiplies the vacuum by `q^{(k-1)/2}`

Type `C` closed because the braid word collapsed. Type `D` closes because the letter **acts on the
vacuum as a scalar**, which is the only thing the clause can allow: its factor is the bare `q^{a}`,
with no `HJO.Sweep.corner`, so the added move must not move the vector at all.

1. **`z_1` multiplies the vacuum by `q^{k}u`.** `HJO.Sweep.zopOneStar_auxVarProd`: on
   `d_+^{k}(1) = (-1)^{k}y_1⋯y_k` (`HJO.Sweep.dplusIter_eq_smul_auxVarProd`) the train `T^*_{k↘1}`
   of `HJO.Sweep.zop` acts trivially, `d_-^{(k)}` strips the top letter against `-e_1`, and the two
   orders of `d^*_+` and `d_-` differ by exactly the one-letter displacement `(q-1)uy_1` of
   `τ_{k+1,k+1}` — so the commutator is `-(q-1)u` times the vacuum and the prefactor
   `q^{k}/(1-q)` turns that into `q^{k}u`. Then `HJO.Sweep.braidRep`'s `z_1 ↦ (qu)^{-1}z_1` gives
   `q^{k-1}`, and the recursion `z_{i+1} = q^{-1}T_iz_iT_i` gives `q^{k-i}` at every index
   (`HJO.Sweep.zop_dplusIter`), each `T_i` fixing the vacuum
   (`HJO.Sweep.braid_dplusIter`).
   **`u ≠ 0` is spent here and is unavoidable**: at `u = 0` the letter `π_k(z_1)` is the zero map
   (`HJO.Sweep.braidRepLetterTotal_z1_of_mul_eq_zero`) and the clause would read `0 = R_+`.
2. **The ranks are `1` and `k`, so the train is the full `T_{k↘1}`.**
   `HJO.Mellit.Isolates.entryRank_braidData_fst_lo_of_eventType_D` and
   `..._hi_of_eventType_D`. The geometry is two inequalities and no case analysis: the moving
   position at the lower level is the normalised rank of `(X, Y)` itself
   (`HJO.Mellit.Isolates.colStep_colouringEast_of_eventType_D`), and `rk̂(X, Y) < η₊`, so it lies
   **below the whole rigid rotation** `HJO.Mellit.levelDropShift` while every other position is at
   least that — the wrapped entry is the strict **minimum**. At the upper level the same entry sits
   within one rank step of the ceiling `1 - θ` that every position obeys
   (`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`), and one rank step is at least the
   rotation, so it is the strict **maximum**. So `π_k` of the letter is
   `q^{-(k-1)/2}T_{k↘1}` after `q^{k-1}`, and `T_{k↘1}` fixes the vacuum too: the letter multiplies
   it by `q^{(k-1)/2}` and nothing else
   (`HJO.Sweep.braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece`).
3. **The inversion count is the type-`C` one, mirrored.** The moving entry travels from the top of
   the upper tuple to the bottom of the lower one, so
   `HJO.Braid.tupleInversions_sub_tupleInversions_of_top_bot` applies verbatim and
   `HJO.Braid.invIni` changes by `j - (k-1-j)`; `HJO.Braid.invFin` does not change at all,
   the two final tuples being rigid shifts of one another
   (`HJO.Mellit.Isolates.invFin_eq_of_eventType_D`). Together with `q^{(k-1)/2}` that is
   `r^{2(k-1-j)} = q^{k-1-j}`, `HJO.Mellit.sweepOperator`'s own exponent at type `D`
   (`HJO.Mellit.Isolates.sweepRight_eq_of_eventType_D`), with nothing left over.

## The rigid shift is invisible at type `D`, with no stage excluded

At type `C` the shift carried exactly one stage position across the puncture — the last stage of the
moving index — and the repair was the sharpened `HJO.Mellit.braidValueOfData_congr_add_of_lt`. **At
type `D` no stage crosses at all.** `HJO.Mellit.sameSide_levelDropShift_of_ne` excludes only the
lattice point `(X, Y + 1)`, and a type-`D` event has `ht y (X+1) ≤ Y`
(`HJO.Paths.eventType_eq_D_iff` with `X < aN`), so `(X, Y+1)` fails the crossing condition
`y ≤ ŷ_{x+1}` and is realised at no stage
of any component. So `HJO.Mellit.braidValueOfData_congr_add` itself is enough, and the sharpened
form is not needed here.

## What is closed, and the scope limit

`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_step` is the type-`D`
clause with no hypothesis about the braid, carrying one extra hypothesis on the levels:
`η₊ ≤ η₋ + 1`. **That hypothesis is load-bearing at two points and is not bookkeeping.** It gives
`HJO.Mellit.levelDropShift ≤ θ`, which is what stops the rigid rotation from wrapping
(`hlt` of `HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D`, discharged in this
file); and it makes one rank step at least the rotation, which is what makes the moving entry the
strict maximum. At a gap above `1` both can fail and the identification of the rotated tuple with
`HJO.Braid.moveOne` of the lower one is unproved. The sweep iteration runs on consecutive levels, so
this is the range in which the clause is applied — the same shape as the type-`C` clause's
`..._of_succ`.

**This does not prove `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`.** With type `A`
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_A_uncond`) and type `C`
(`HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_C_of_succ`) this closes
three of its four clauses; the `BE` clause, the origin clause, the unswept clause and all six
recursions are untouched.

## Genericity

`q ≠ 0`, `q ≠ 1`, `q + 1 ≠ 0`, `r * r = q` — `HJO.Sweep.braidRep`'s own exclusions — **and `u ≠ 0`,
which the clause being reduced did not carry**. It is a real hypothesis, not a convenience: the
type-`D` letter is a `z`, `HJO.Sweep.braidRep` sends `z_1 ↦ (qu)^{-1}z_1`, and at `u = 0` that is
the zero map in a field. `q ≠ 1` is spent on the `q^{k}/(1-q)` of `HJO.Sweep.zop` as well as on
`HJO.Sweep.corner`. The geometry is `ℕ`, `ℤ` and `ℚ` and needs `0 < a`, `0 < b`, `0 < N` only.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

/-- **The descending reading of `HJO.Braid.trainUp` at the top index**:
`T^*_{k↘1} = T_{k-1}^{-1}⋯T_1^{-1}` for `k ≥ 1`. At `k = 1` the two branches of `HJO.Braid.trainUp`
meet, both being the empty product, so no case split survives into the statement. The mirror of
`HJO.Braid.trainDown_bot_eq_prod`. -/
theorem trainUp_top_eq_prod {M : Type*} [Monoid M] (T Tinv : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    trainUp T Tinv k 1 = ((List.range' 1 (k - 1)).reverse.map Tinv).prod := by
  by_cases hk1 : k = 1
  · subst hk1; simp [trainUp, ascendingWord]
  · rw [trainUp, ite_eq_right (show ¬ k ≤ 1 by omega), descendingWord]

end HJO.Braid

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The Hall--Littlewood extension on a monomial in the auxiliary variables

`HJO.Sweep.bopExt` is `𝕜[y]`-linear (`HJO.Sweep.bopExt_monomial_mul`), so on a monomial it is
multiplication by `B_r(1)`. That is all the `d_-` halves of `HJO.Sweep.zop` need on the vacuum. -/

/-- `HJO.Sweep.bopExt_monomial_mul` at a single variable. -/
theorem bopExt_X_mul (q : L) (r : ℤ) (j : ℕ) (F : Total L) :
    bopExt q r ((MvPolynomial.X j : Total L) * F)
      = (MvPolynomial.X j : Total L) * bopExt q r F :=
  bopExt_monomial_mul q r (Finsupp.single j 1) F

/-- `HJO.Sweep.bopExt` commutes with multiplication by any product of auxiliary variables. -/
theorem bopExt_prod_X_mul (q : L) (r : ℤ) (s : Finset ℕ) (f : ℕ → ℕ) (F : Total L) :
    bopExt q r ((∏ j ∈ s, (MvPolynomial.X (f j) : Total L)) * F)
      = (∏ j ∈ s, (MvPolynomial.X (f j) : Total L)) * bopExt q r F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, mul_assoc, bopExt_X_mul, ih, ← mul_assoc]

/-- `B_r` on the unit of the total space is `B_r(1)` of the base. -/
theorem bopExt_one_eq_C_bop (q : L) (r : ℤ) :
    bopExt q r (1 : Total L) = MvPolynomial.C (Sym.Bop q r (1 : Sym.Lambda L)) := by
  conv_lhs => rw [show (1 : Total L) = MvPolynomial.C (1 : Sym.Lambda L) from (map_one _).symm]
  rw [bopExt_C]

theorem bopExt_auxVarProd (q : L) (r : ℤ) (m : ℕ) :
    bopExt q r (auxVarProd L m)
      = auxVarProd L m * MvPolynomial.C (Sym.Bop q r (1 : Sym.Lambda L)) := by
  have h := bopExt_prod_X_mul q r (Finset.range m) (fun j => j) (1 : Total L)
  rw [mul_one, bopExt_one_eq_C_bop] at h
  rw [auxVarProd, h]

theorem bopExt_prod_X_succ (q : L) (r : ℤ) (m : ℕ) :
    bopExt q r (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L))
      = (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L))
        * MvPolynomial.C (Sym.Bop q r (1 : Sym.Lambda L)) := by
  have h := bopExt_prod_X_mul q r (Finset.range m) (fun j => j + 1) (1 : Total L)
  rw [mul_one, bopExt_one_eq_C_bop] at h
  exact h

/-- **`B_1(1) = -e_1`**, the one value of the Hall--Littlewood operator the vacuum computation
reads: `HJO.Sym.bop_one` at `r = 1`, with `HJO.Sym.elemSymmAlt`'s sign and
`HJO.Sym.elemSymm_one` turning `e_1` into `p_1`. -/
theorem bop_one_one (q : L) : Sym.Bop q (1 : ℤ) (1 : Sym.Lambda L) = -Sym.powerSum L 1 := by
  rw [Sym.bop_one, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, Sym.elemSymmAlt_natCast,
    Sym.elemSymm_one]
  ring

omit [Algebra ℚ L] in
/-- `y_2⋯y_{m+1}` lies in `V_{m+1}`. -/
theorem prod_X_succ_mem_piece (m : ℕ) :
    (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L)) ∈ piece L (m + 1) := by
  refine prod_mem fun j hj => ?_
  have h := auxVar_mem_piece (L := L) (i := j + 2) (k := m + 1) (by omega)
    (by rw [Finset.mem_range] at hj; omega)
  rwa [auxVar, show j + 2 - 1 = j + 1 from rfl] at h

omit [Algebra ℚ L] in
/-- **`cy_{k+1}` shifts `y_1⋯y_m` up by one whenever `m ≤ k`**: the wrapping letter `y_{k+1}` does
not occur, so no `u` appears. `HJO.Sweep.cycleShift_auxVarProd` is the case `m = k`. -/
theorem cycleShift_auxVarProd_of_le (u : L) {m k : ℕ} (hmk : m ≤ k) :
    cycleShift u k (auxVarProd L m)
      = ∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L) := by
  rw [auxVarProd, map_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h := cycleShift_auxVar u (i := j + 1) (k := k) (by omega) (by omega)
  rwa [auxVar, auxVar, show j + 1 - 1 = j from rfl, show j + 1 + 1 - 1 = j + 1 from rfl] at h

/-! ### The trains on the vacuum tower -/

omit [Algebra ℚ L] in
/-- `T_i` fixes the vacuum tower, in the endomorphism form the trains compose. -/
theorem braidEnd_dplusIter (q : L) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 1 ≤ j) :
    braidEnd q i (dplusIter q j) = dplusIter q j := braid_dplusIter q hi hij

omit [Algebra ℚ L] in
/-- **`T^*_{k↘1}` fixes `d_+^{k}(1)`.** The train of `HJO.Sweep.zop` is the word
`T_{k-1}^{-1}⋯T_1^{-1}` by `HJO.Braid.trainUp_top_eq_prod`, and every index it reads is below
`k`. -/
theorem trainUpEnd_top_dplusIter (q : L) (hq : q ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    trainUpEnd q m 1 (dplusIter q m) = dplusIter q m := by
  rw [trainUpEnd, Braid.trainUp_top_eq_prod _ _ m hm]
  refine list_prod_braidInvEnd_dplusIter q hq _ fun i hi => ?_
  simp only [List.mem_reverse, List.mem_range'_1] at hi
  omega

omit [Algebra ℚ L] in
/-- `T^*_{k↘1}` fixes `y_1⋯y_k`, the vacuum tower up to its sign. -/
theorem trainUpEnd_top_auxVarProd (q : L) (hq : q ≠ 0) {m : ℕ} (hm : 1 ≤ m) :
    trainUpEnd q m 1 (auxVarProd L m) = auxVarProd L m := by
  have h := trainUpEnd_top_dplusIter q hq hm
  rw [dplusIter_eq_smul_auxVarProd, map_smul] at h
  exact smul_right_injective (Total L) (r := ((-1 : L) ^ m)) (by simp) h

omit [Algebra ℚ L] in
/-- **`T_{k↘1}` fixes `d_+^{k}(1)`.** The train of `HJO.Braid.braidStep`'s letter, in the uninverted
letters: `HJO.Braid.trainDown_one_eq_prod` and `HJO.Sweep.braid_dplusIter`. -/
theorem trainDownEnd_top_dplusIter (q : L) {m : ℕ} (hm : 1 ≤ m) :
    trainDownEnd q m 1 (dplusIter q m) = dplusIter q m := by
  rw [trainDownEnd, Braid.trainDown_one_eq_prod _ _ m hm]
  generalize hl : (List.range' 1 (m - 1)).reverse = l
  have hmem : ∀ i ∈ l, 1 ≤ i ∧ i + 1 ≤ m := by
    intro i hi
    rw [← hl] at hi
    simp only [List.mem_reverse, List.mem_range'_1] at hi
    omega
  clear hl
  induction l with
  | nil => simp
  | cons i t ih =>
    rw [List.map_cons, List.prod_cons]
    change braidEnd q i (((t.map (braidEnd q)).prod) (dplusIter q m)) = _
    rw [ih fun j hj => hmem j (List.mem_cons_of_mem _ hj)]
    exact braidEnd_dplusIter q (hmem i List.mem_cons_self).1 (hmem i List.mem_cons_self).2

/-! ### `z_1` on the vacuum: the two halves of `HJO.Sweep.zop` -/

/-- **The `d_-^{(k)}` half:** `d_-^{(k)}(y_1⋯y_k) = B_1(1)·y_1⋯y_{k-1}`. `τ^-_{k,k}` fixes the
monomial and `HJO.Sweep.dminus_auxVar_pow_mul` strips the top letter `y_k`, which occurs to the
first power. -/
theorem dminus_auxVarProd_self (q : L) (m : ℕ) :
    dminus q (m + 1) (auxVarProd L (m + 1))
      = auxVarProd L m * MvPolynomial.C (Sym.Bop q (1 : ℤ) (1 : Sym.Lambda L)) := by
  rw [auxVarProd_succ, mul_comm,
    show (auxVar (m + 1) : Total L) = (auxVar (m + 1) : Total L) ^ 1 from (pow_one _).symm,
    dminus_auxVar_pow_mul q m 1 (auxVarProd_mem_piece L m), Nat.cast_one, bopExt_auxVarProd]

omit [Algebra ℚ L] in
/-- **`d^*_+{}^{(k)}` shifts the whole vacuum up by one letter:**
`d^*_+(y_1⋯y_{k}) = y_2⋯y_{k+1}`. No `u` appears, the wrapping letter `y_{k+1}` not occurring. -/
theorem dplusStar_auxVarProd_self (q u : L) (m : ℕ) :
    dplusStar q u (m + 1) (auxVarProd L (m + 1))
      = (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L)) * auxVar (m + 2) := by
  rw [dplusStar_apply, qshift_auxVarProd, auxVarProd_succ, map_mul,
    cycleShift_auxVarProd_of_le u (Nat.le_succ m),
    cycleShift_auxVar u (i := m + 1) (k := m + 1) (by omega) le_rfl]

/-- **The `d^*_+{}^{(k-1)}d_-^{(k)}` half, evaluated.** The displacement `τ_{k+1,k+1}` turns the
constant `B_1(1) = -p_1` into `-(p_1 + (q-1)y_k)` and then `cy_k` wraps that `y_k` round to
`uy_1` (`HJO.Sweep.cycleShift_auxVar_last`) — which is the one-letter discrepancy the commutator of
`HJO.Sweep.zop` measures. -/
theorem dplusStar_auxVarProd_mul_C_bop (q u : L) (m : ℕ) :
    dplusStar q u m (auxVarProd L m * MvPolynomial.C (Sym.Bop q (1 : ℤ) (1 : Sym.Lambda L)))
      = (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L))
        * -(MvPolynomial.C (Sym.powerSum L 1) + scal (q - 1) * (scal u * auxVar 1)) := by
  rw [dplusStar_apply, map_mul, qshift_auxVarProd, map_mul,
    cycleShift_auxVarProd_of_le u le_rfl, bop_one_one, map_neg, map_neg, map_neg]
  congr 2
  rw [show Sym.powerSum L 1 = Sym.powerSum L (0 + 1) from rfl, qshift_powerSum, map_add,
    cycleShift_C]
  simp only [zero_add, pow_one]
  rw [map_mul, scal, cycleShift_C, ← scal, cycleShift_auxVar_last]

/-- **The `d_-^{(k+1)}d^*_+{}^{(k)}` half, evaluated.** The same `B_1(1)`, now against the shifted
monomial: no displacement of the base is met, which is why the two halves differ by the one letter
only. -/
theorem dminus_prod_X_succ_mul (q : L) (m : ℕ) :
    dminus q (m + 2) ((∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L)) * auxVar (m + 2))
      = (∏ j ∈ Finset.range m, (MvPolynomial.X (j + 1) : Total L))
        * MvPolynomial.C (Sym.Bop q (1 : ℤ) (1 : Sym.Lambda L)) := by
  rw [mul_comm,
    show (auxVar (m + 2) : Total L) = (auxVar (m + 2) : Total L) ^ 1 from (pow_one _).symm,
    show m + 2 = (m + 1) + 1 from rfl, dminus_auxVar_pow_mul q (m + 1) 1 (prod_X_succ_mem_piece m),
    Nat.cast_one, bopExt_prod_X_succ]

/-- **`z_1(y_1⋯y_k) = q^{k}u·y_1⋯y_k`.** The train of `HJO.Sweep.zop` acts trivially
(`HJO.Sweep.trainUpEnd_top_auxVarProd`) and the commutator `d^*_+d_- - d_-d^*_+` is the
one-letter displacement `-(q-1)uy_1` times `y_2⋯y_k`, so the prefactor `q^{k}/(1-q)` leaves exactly
`q^{k}u`. `q ≠ 1` is spent on that prefactor and `q ≠ 0` on the train. -/
theorem zopOneStar_auxVarProd (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) :
    zopOneStar q u (m + 1) (auxVarProd L (m + 1))
      = (q ^ (m + 1) * u) • auxVarProd L (m + 1) := by
  have h1q : (1 : L) - q ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  rw [zopOneStar]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, Nat.add_sub_cancel]
  rw [trainUpEnd_top_auxVarProd q hq (Nat.le_add_left 1 m), dminus_auxVarProd_self,
    dplusStar_auxVarProd_mul_C_bop, dplusStar_auxVarProd_self, dminus_prod_X_succ_mul,
    bop_one_one, map_neg, Algebra.smul_def, Algebra.smul_def, ← scal_eq_algebraMap,
    ← scal_eq_algebraMap, auxVarProd_succ']
  have key : (scal (q ^ (m + 1) * u) : Total L)
      = -(scal (q ^ (m + 1) / (1 - q)) * (scal (q - 1) * scal u)) := by
    rw [← scal_mul, ← scal_mul, scal_eq_algebraMap, scal_eq_algebraMap, ← map_neg]
    congr 1
    field_simp
    ring
  rw [key]
  ring

/-- `HJO.Sweep.zopOneStar_auxVarProd` on the vacuum tower itself. -/
theorem zopOneStar_dplusIter (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) :
    zopOneStar q u (m + 1) (dplusIter q (m + 1)) = (q ^ (m + 1) * u) • dplusIter q (m + 1) := by
  rw [dplusIter_eq_smul_auxVarProd, map_smul, zopOneStar_auxVarProd q u hq hq1 m, smul_comm]

/-- **`z_i(d_+^{k}(1)) = q^{k-i+1}u·d_+^{k}(1)` for `1 ≤ i ≤ k`.** The base case is
`HJO.Sweep.zopOneStar_dplusIter` and the recursion `z_{i+1} = q^{-1}T_iz_iT_i` of `HJO.Sweep.zop`
costs one power of `q` per step, each `T_i` fixing the vacuum. -/
theorem zop_dplusIter (q u : L) (hq : q ≠ 0) (hq1 : q ≠ 1) (k : ℕ) :
    ∀ i, 1 ≤ i → i ≤ k → zop q u k i (dplusIter q k) = (q ^ (k - i + 1) * u) • dplusIter q k := by
  intro i
  induction i with
  | zero => omega
  | succ p ih =>
    intro _ hik
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [show 0 + 1 = 1 from rfl, zop_one, zopOneStar_dplusIter q u hq hq1 m,
        show m + 1 - 1 + 1 = m + 1 from by omega]
    · obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [show n + 1 + 1 = n + 2 from rfl, zop_succ]
      simp only [LinearMap.smul_apply, Module.End.mul_apply]
      rw [braidEnd_dplusIter q (by omega) (by omega), ih (by omega) (by omega), map_smul,
        braidEnd_dplusIter q (by omega) (by omega), smul_smul]
      congr 1
      rw [show k - (n + 1) + 1 = (k - (n + 2) + 1) + 1 from by omega, pow_succ]
      field_simp

/-- **THE TYPE-`D` LETTER ON THE VACUUM: `π_k(T_{k↘1}z_1)d_+^{k}(1) = q^{(k-1)/2}d_+^{k}(1)`.**
The letter acts on the vacuum as a **scalar**, which is what the type-`D` clause of
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` demands of it: that clause's factor is the
bare `q^{a}`, with no `HJO.Sweep.corner`, so the added move must fix the vector up to a scalar.

Two `r`-powers meet: `HJO.Sweep.braidRep` sends `z_1` to `(qu)^{-1}z_1`, and
`HJO.Sweep.zop_dplusIter` makes that `q^{k-1}` on the vacuum — **this is where `u ≠ 0` is spent**;
and the train contributes `q^{-(k-1)/2}` (`HJO.Sweep.representedBy_braidTrainDown_top`) while
fixing the vacuum (`HJO.Sweep.trainDownEnd_top_dplusIter`). -/
theorem braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece (q u : L) (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) {r : L} (hr : r * r = q) (hu : u ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    braidRepMellit q u hq hq1 hqp hr k (braidTrainDown k k 1 * braidGenZ k 1)
        (dplusIterPiece q k)
      = (r ^ (k - 1)) • dplusIterPiece q k := by
  have hr0 : r ≠ 0 := fun h => hq (by rw [← hr, h, mul_zero])
  refine Subtype.ext ?_
  rw [Submodule.coe_smul, coe_dplusIterPiece, braidRepMellit,
    ((representedBy_braidTrainDown_top (q := q) (u := u) (r := r)
        (h := braidRepRespects_mellit q u hq hq1 hqp hr k) hk).mul
      (representedBy_braidGenZ_of_le (hq := hq) (hq1 := hq1) (hqp := hqp) (hr := hr)
        le_rfl hk)).apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smul_apply, coe_dplusIterPiece,
    zop_dplusIter q u hq hq1 k 1 le_rfl hk]
  simp only [map_smul, trainDownEnd_top_dplusIter q hk, smul_smul]
  congr 1
  rw [← hr, inv_pow]
  field_simp
  ring

end HJO.Sweep

namespace HJO.Mellit

open Braid Finset ParkingFunctions Paths Sweep

variable {a b N : ℕ}

/-! ### The rigid rotation against `θ` and against one rank step -/

/-- **The rigid rotation of a level drop is the position the UPPER LEVEL occupies at the lower
one.** `HJO.Mellit.levelDropShift` and `HJO.Mellit.levelPosition` are the same formula, so this is
`rfl` — and it is what turns statements about the rotation into statements about ranks, where the
isolation clause lives. -/
theorem levelDropShift_eq_levelPosition (a b N : ℕ) (ηlo ηhi : ℚ) :
    levelDropShift a b N ηlo ηhi = levelPosition a b N ηlo ηhi := rfl

/-- **A level gap of at most one keeps the rotation below `θ`.** The attack window is at least `1`
on a rectangle with a row and a column, so `(η₊ − η₋)/D ≤ 1/D ≤ ω/D = θ`. -/
theorem levelDropShift_le_sweepTheta (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hstep : ηhi ≤ ηlo + 1) :
    levelDropShift a b N ηlo ηhi ≤ sweepTheta a b N := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have hN' : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have ht : (1 : ℚ) ≤ (a : ℚ) * N := by nlinarith
  have hM1 : (1 : ℚ) ≤ (a : ℚ) * ((a : ℚ) * N + 1) * N := by
    rw [show (a : ℚ) * ((a : ℚ) * N + 1) * N = ((a : ℚ) * N) * ((a : ℚ) * N + 1) from by ring]
    nlinarith
  rw [levelDropShift]
  have h1 : (ηhi - ηlo) / ((a : ℚ) * ((a : ℚ) * N + 1) * N) ≤ 1 := by
    rw [div_le_one hM]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le]

/-- **At a level gap of at most one, one rank step is at least the rigid rotation.** Positions at a
fixed level sit `1/D` apart per unit of rank while the rotation is `(η₊ − η₋)/D`, so this is the
inequality `η₊ − η₋ ≤ 1` read on the circle. It is what makes the moving entry of a type-`D` drop
the strict maximum: the entry sits within `levelDropShift` of the ceiling `1 − θ`, so no other
position can be above it without exceeding that ceiling. -/
theorem add_levelDropShift_le_levelPosition (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {ηlo ηhi : ℚ}
    (hstep : ηhi ≤ ηlo + 1) {ρ ρ' : ℚ} (h : ρ + 1 ≤ ρ') :
    levelPosition a b N ηhi ρ + levelDropShift a b N ηlo ηhi
      ≤ levelPosition a b N ηhi ρ' := by
  have hM := rankDen_pos (a := a) (N := N) ha hN
  have hθ := (sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN).1
  rw [levelPosition, levelPosition, levelDropShift, ← mul_add, ← add_div]
  have hnum : ρ - ηhi + (ηhi - ηlo) ≤ ρ' - ηhi := by linarith
  have hθ0 : (0 : ℚ) ≤ sweepTheta a b N := hθ.le
  gcongr

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-! ### The moving position at the lower level is below the whole rotation -/

/-- **At a type-`D` drop the moving position of the LOWER data is below the rigid rotation.** The
`j`-th crossed east step of the lower colouring is the event point `(X, Y)` itself
(`HJO.Mellit.Isolates.colStep_colouringEast_of_eventType_D`), so the position is
`levelPosition η₋ (rk̂(X, Y))`; and `rk̂(X, Y) < η₊` is the isolation clause, whose position at the
lower level is exactly `HJO.Mellit.levelDropShift`.

**This is the whole reason the wrapped entry is the strict minimum**: every other position is
`v_+ + levelDropShift` with `v_+ > 0`. -/
theorem braidData_fst_lo_lt_levelDropShift_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (braidDataOfColouring a b N y ηlo k).1 j < levelDropShift a b N ηlo ηhi := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hlopos : (0 : ℚ) < ηlo := lt_of_le_of_lt (Nat.cast_nonneg _) hηlo
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hcardE : #(colouringEast y ηlo) = #(colouringEast y ηhi) :=
    hI.card_colouringEast_eq_of_eventType_D ha hb hN hηlo hy hev
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.lo hlopos j
      (by rw [hcardE, hk]; exact j.isLt),
    hI.colStep_colouringEast_of_eventType_D ha hb hN hηlo hX hy hev hjlt hj hjlt,
    Function.update_self, levelDropShift_eq_levelPosition]
  exact levelPosition_lt_levelPosition ha hb hN ηlo hI.Plt

/-! ### The moving position at the upper level is within one rotation of the ceiling -/

/-- **At a type-`D` drop the moving position of the UPPER data is at least `1 − θ − c`.** Every
position lies below `1 − θ` (`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`); this is
the matching lower bound at the one index, and it says the entry sits in the topmost window of width
`levelDropShift`.

The argument is the wrap itself. `HJO.Mellit.Isolates.braidData_fst_succ_of_eventType_D` reads the
lower position as `Int.fract(v_+ + c + θ)`, and the fractional part cannot be trivial: without the
wrap the lower position would be at least `c + θ`, while
`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D` puts it below `c`. So the
wrap happens, and it is `v_- = v_+ + c + θ - 1 ≥ 0`. -/
theorem one_sub_sub_le_braidData_fst_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    1 - sweepTheta a b N - levelDropShift a b N ηlo ηhi
      ≤ (braidDataOfColouring a b N y ηhi k).1 j := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hθ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have hcle := levelDropShift_le_sweepTheta ha hb hN hstep
  have hclo : (0 : ℚ) ≤ levelDropShift a b N ηlo ηhi := by
    rw [levelDropShift_eq_levelPosition]
    have : levelPosition a b N ηlo ηlo ≤ levelPosition a b N ηlo ηhi :=
      levelPosition_le_levelPosition ha hb hN ηlo (hI.ltP.trans hI.Plt).le
    rwa [show levelPosition a b N ηlo ηlo = 0 from by rw [levelPosition]; ring] at this
  have hceil := braidDataOfColouring_fst_lt_one_sub_sweepTheta ha hb hN hI.hi hhipos j
    (by rw [hk]; exact j.isLt)
  have hpos : (0 : ℚ) < (braidDataOfColouring a b N y ηhi k).1 j := by
    rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j
      (by rw [hk]; exact j.isLt)]
    have hmem := (Finset.mem_filter.1 (colStep_mem hjlt)).2.2
    have := levelPosition_lt_levelPosition ha hb hN ηhi hmem
    rwa [show levelPosition a b N ηhi ηhi = 0 from by rw [levelPosition]; ring] at this
  have hlo := hI.braidData_fst_lo_lt_levelDropShift_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hfr := hI.braidData_fst_succ_of_eventType_D ha hb hN hηlo hy hev hjlt hj j rfl
  set s : ℚ := (braidDataOfColouring a b N y ηhi k).1 j + levelDropShift a b N ηlo ηhi
    + sweepTheta a b N with hs
  have hone : 1 ≤ s := by
    by_contra hcon
    rw [Int.fract_eq_self.2 ⟨by rw [hs]; linarith, by linarith⟩] at hfr
    rw [hs] at hfr
    linarith
  have hfr' : Int.fract s = s - 1 := by
    rw [show s = (s - 1) + 1 from by ring, Int.fract_add_one,
      Int.fract_eq_self.2 ⟨by linarith, by rw [hs]; linarith⟩]
    ring
  rw [hfr', hs] at hfr
  linarith

/-- **`hlt` of `HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D`, DISCHARGED at a level gap
of at most one.** The rotation alone does not carry the moving position past `1`, because every
position of a colouring's braid data is below `1 − θ`
(`HJO.Mellit.braidDataOfColouring_fst_lt_one_sub_sweepTheta`) and the rotation is at most `θ`
(`HJO.Mellit.levelDropShift_le_sweepTheta`).

This is the one remaining side condition of that identification, and `η₊ ≤ η₋ + 1` is what it
costs. At a larger gap the bound `1 − θ + c` exceeds `1` and the statement is unproved. -/
theorem braidData_fst_add_levelDropShift_lt_one_of_eventType_D (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    (hstep : ηhi ≤ ηlo + 1) {y : Heights a b N} {k : ℕ} (hk : #(colouringEast y ηhi) = k)
    (i : Fin k) :
    (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi < 1 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hceil := braidDataOfColouring_fst_lt_one_sub_sweepTheta ha hb hN hI.hi hhipos i
    (by rw [hk]; exact i.isLt)
  have hcle := levelDropShift_le_sweepTheta ha hb hN hstep
  linarith

/-! ### The two entry ranks of the type-`D` letter -/

/-- **THE TRAIN: at a type-`D` drop the moving entry of the LOWER position tuple is the strict
minimum, so its rank is `1`.** The wrapped entry lies below the whole rigid rotation
(`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D`) while every other entry is
an upper position — which is strictly positive — plus that same rotation. So the letter of
`HJO.Braid.braidStep` carries the full descending train `T_{k↘1}` and its generator sits at index
`1`. -/
theorem entryRank_braidData_fst_lo_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    entryRank (braidDataOfColouring a b N y ηlo k).1 j = 1 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hlo := hI.braidData_fst_lo_lt_levelDropShift_of_eventType_D ha hb hN hηlo hy hev hk j hj
  refine entryRank_eq_one_of_forall_ne_lt _ _ fun i hne => ?_
  have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  rw [hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i hi
    (fun hc => hne (Fin.ext hc))]
  have hpos : (0 : ℚ) < (braidDataOfColouring a b N y ηhi k).1 i := by
    rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi]
    have hmem := (Finset.mem_filter.1 (colStep_mem hi)).2.2
    have := levelPosition_lt_levelPosition ha hb hN ηhi hmem
    rwa [show levelPosition a b N ηhi ηhi = 0 from by rw [levelPosition]; ring] at this
  linarith

/-- **THE ENTRY RANK: at a type-`D` drop the moving entry of the UPPER position tuple is the strict
MAXIMUM, so its rank is `k`.** The entry sits in the topmost window of width `levelDropShift`
(`HJO.Mellit.Isolates.one_sub_sub_le_braidData_fst_of_eventType_D`), every position is below the
ceiling `1 − θ`, and one rank step is at least `levelDropShift`
(`HJO.Mellit.add_levelDropShift_le_levelPosition`) — so an entry above it would have to clear the
ceiling. The entries are distinct by `HJO.Braid.IsSpecialBraidData.injective` at stage `0`, which is
what upgrades `≤` to `<`. -/
theorem lt_braidData_fst_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) (i : Fin k) (hne : i ≠ j) :
    (braidDataOfColouring a b N y ηhi k).1 i < (braidDataOfColouring a b N y ηhi k).1 j := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  -- distinctness of the two positions
  have hdist : (braidDataOfColouring a b N y ηhi k).1 i
      ≠ (braidDataOfColouring a b N y ηhi k).1 j := fun hc =>
    hne (hdatahi.injective i j 0 0 (hdatahi.one_le_mult i) (hdatahi.one_le_mult j) hc).1
  by_contra hcon
  have hji : (braidDataOfColouring a b N y ηhi k).1 j < (braidDataOfColouring a b N y ηhi k).1 i :=
    lt_of_le_of_ne (not_lt.1 hcon) hdist.symm
  -- read both positions as normalised ranks
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi,
    braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j hjlt] at hji
  have hrk : ((pointRank a b N (colStep (colouringEast y ηhi) (j : ℕ)) : ℤ) : ℚ) + 1
      ≤ ((pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) : ℤ) : ℚ) := by
    have hlt : pointRank a b N (colStep (colouringEast y ηhi) (j : ℕ))
        < pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) := by
      by_contra hc
      exact absurd (levelPosition_le_levelPosition ha hb hN ηhi
        (show ((pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) : ℤ) : ℚ)
          ≤ ((pointRank a b N (colStep (colouringEast y ηhi) (j : ℕ)) : ℤ) : ℚ) from by
          exact_mod_cast not_lt.1 hc)) (not_le.2 hji)
    have : (pointRank a b N (colStep (colouringEast y ηhi) (j : ℕ)) : ℤ) + 1
        ≤ (pointRank a b N (colStep (colouringEast y ηhi) (i : ℕ)) : ℤ) := by omega
    exact_mod_cast this
  have hstepineq := add_levelDropShift_le_levelPosition (a := a) (b := b) (N := N) ha hb hN hstep
    hrk
  have hbot := hI.one_sub_sub_le_braidData_fst_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj
  have hceil := braidDataOfColouring_fst_lt_one_sub_sweepTheta ha hb hN hI.hi hhipos i hi
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos j hjlt] at hbot
  rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i hi] at hceil
  linarith

/-- `HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D` as the entry rank `HJO.Braid.braidStep`
reads. -/
theorem entryRank_braidData_fst_hi_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    entryRank (braidDataOfColouring a b N y ηhi k).1 j = k := by
  refine entryRank_eq_card_of_forall_le _ _ fun i => ?_
  by_cases h : i = j
  · rw [h]
  · exact (hI.lt_braidData_fst_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj i h).le

/-! ### The rigid shift of a type-`D` drop crosses the puncture at NO stage -/

/-- **The `hside` obligation of a type-`D` event, at EVERY stage.** `HJO.Mellit`'s
`sameSide_levelDropShift_of_ne` excludes only the lattice point `(X, Y + 1)`, and at a type-`D`
event that point is not a crossing of the path at all: `HJO.Paths.eventType_eq_D_iff` with
`X < aN` gives `ŷ_{X+1} ≤ Y`, while every stage position is realised at a point with
`y ≤ ŷ_{x+1}` (`HJO.Mellit.exists_pointRank_iterate_nextCrossing_eq_sub`).

**So type `D` does not need the sharpened rigid shift that type `C` did.** There the last stage of
the moving index was the one crossing that did straddle the puncture, and
`HJO.Mellit.braidValueOfData_congr_add_of_lt` is needed for it; here
`HJO.Mellit.braidValueOfData_congr_add` itself, which asks the condition at every stage including
the last, applies directly. -/
theorem sameSide_iterate_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) {y : Heights a b N}
    (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (t : Fin k) (m : ℕ)
    (hm : m ≤ (braidDataOfColouring a b N y ηhi k).2 t - 1) :
    SameSide (sweepTheta a b N) (levelDropShift a b N ηlo ηhi)
      ((nextCrossing (sweepTheta a b N))^[m] ((braidDataOfColouring a b N y ηhi k).1 t)) := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  obtain ⟨hY, hout⟩ := eventType_eq_D_iff.1 hev
  have hY' : Y = ht y X := hY
  have hout' : ¬ (X < a * N ∧ Y < ht y (X + 1)) := hout
  have hht : ht y (X + 1) ≤ Y := by
    by_contra hc
    exact hout' ⟨hX, by omega⟩
  obtain ⟨x, yy, hsum, hbot, hx, hyy0, hyyle, hrk, hfr⟩ :=
    exists_pointRank_iterate_nextCrossing_eq_sub ha hb hN hI.hi hηhi hy hk t hm
  rw [hfr]
  refine sameSide_levelDropShift_of_ne ha hb hN hI hx.le
    (le_trans (hyyle.trans (ht_le_mul y _)) (by omega)) hyy0 ?_
  intro hQ
  have hx1 : x = X := congrArg Prod.fst hQ
  have hy1 : yy = Y + 1 := congrArg Prod.snd hQ
  have hbad : Y + 1 ≤ ht y (X + 1) := by rw [← hx1, ← hy1]; exact hyyle
  omega

/-! ### The moving position advances onto the rotated upper tuple -/

/-- **`HJO.Mellit.Isolates.moveOne_braidData_fst_of_eventType_D` with both side conditions
discharged**, at a level gap of at most one. `hlt` is
`HJO.Mellit.Isolates.braidData_fst_add_levelDropShift_lt_one_of_eventType_D` and `hne` is
`HJO.Braid.IsSpecialBraidData.ne_theta` of the lower data. -/
theorem moveOne_braidData_fst_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j
      = fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := by
  have hX : X < a * N := hI.fst_lt hηlo
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hθ := sweepTheta_mem_Ioo (a := a) (b := b) (N := N) ha hb hN
  have hkNlo : #(colouringNorth y ηlo) = k := by
    rw [hI.colouringNorth_eq_of_eventType_D ha hN hX hev,
      card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]
    exact hk
  have hdatalo := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.lo hηlo hy hkNlo
  refine hI.moveOne_braidData_fst_of_eventType_D ha hb hN hηlo hy hev hk j hj hθ.1 hθ.2
    (hdatalo.ne_theta j 0 (hdatalo.one_le_mult j)) ?_
    (hI.braidData_fst_add_levelDropShift_lt_one_of_eventType_D ha hb hN hηlo hstep hk j)
  have hpos := (isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy
    (by rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk)).mem_Ioo j
  have hclo : (0 : ℚ) ≤ levelDropShift a b N ηlo ηhi := by
    rw [levelDropShift_eq_levelPosition]
    have : levelPosition a b N ηlo ηlo ≤ levelPosition a b N ηlo ηhi :=
      levelPosition_le_levelPosition ha hb hN ηlo (hI.ltP.trans hI.Plt).le
    rwa [show levelPosition a b N ηlo ηlo = 0 from by rw [levelPosition]; ring] at this
  linarith [hpos.1]

/-! ### The type-`D` letter, in closed form -/

/-- **THE TYPE-`D` LETTER, EVALUATED: `T_{k↘1}z_1`, at every rank.** The generator is a `z` because
the moving position of the lower data lies below the puncture — it lies below the whole rigid
rotation, which is at most `θ`
(`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D`,
`HJO.Mellit.levelDropShift_le_sweepTheta`) — and that is the letter-level reading of
`HJO.Mellit.Isolates.zCount_sub_eq_one_of_eventType_D`, which predicts one more `z` and no more `ỹ`.
The train is the full descending one because the ranks are `1` before the move and `k` after
(`HJO.Mellit.Isolates.entryRank_braidData_fst_lo_of_eventType_D`,
`HJO.Mellit.Isolates.entryRank_braidData_fst_hi_of_eventType_D`, the latter read through the rotated
tuple by `HJO.Braid.entryRank_congr_add`).

The mirror of `HJO.Mellit.Isolates.braidStep_positionPair_snd_of_eventType_C`, which reads the
type-`C` letter as `T_{1↘k}ỹ_k`: there the entry travels from the top to the bottom and the train is
inverted; here it travels from the bottom to the top. -/
theorem braidStep_braidData_fst_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    braidStep (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j
      = braidTrainDown k k 1 * braidGenZ k 1 := by
  have hlo := hI.braidData_fst_lo_lt_levelDropShift_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hcle := levelDropShift_le_sweepTheta ha hb hN hstep
  have hrank1 := hI.entryRank_braidData_fst_lo_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hmove := hI.moveOne_braidData_fst_eq_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj
  have hrankk : entryRank
      (moveOne (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1 j) j = k := by
    rw [hmove, entryRank_congr_add (c := levelDropShift a b N ηlo ηhi) (fun _ => rfl) j]
    exact hI.entryRank_braidData_fst_hi_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj
  rw [braidStep_of_lt (by linarith), hrank1, hrankk]

/-! ### The inversion counts of a type-`D` drop -/

/-- **At a type-`D` drop the two FINAL position tuples are rigid shifts of one another**, so
`HJO.Braid.invFin` does not change at all. The moving index is where this has content: the lower
component has one crossing more, at the **top** of its interval, so its last iterate is the upper
one's last iterate carried along by the rotation — one `HJO.Braid.nextCrossing` step absorbs the
extra multiplicity. -/
theorem positionPair_snd_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    (positionPair (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))).2
      = (positionPair (sweepTheta a b N)
          (fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi)
          (braidDataOfColouring a b N y ηhi k).2).2 := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hkN : #(colouringNorth y ηhi) = k := by
    rw [card_colouringNorth_eq_card_colouringEast hb hN hI.hi hηhi hy]; exact hk
  have hdatahi := isSpecialBraidData_braidDataOfColouring_of_card ha hb hN hI.hi hηhi hy hkN
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hmove := hI.moveOne_braidData_fst_eq_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj
  funext i
  rw [positionPair_snd, positionPair_snd]
  by_cases h : i = j
  · subst h
    rw [Function.update_self, show (braidDataOfColouring a b N y ηhi k).2 i + 1 - 1
        = ((braidDataOfColouring a b N y ηhi k).2 i - 1) + 1 from by
      have := hdatahi.one_le_mult i; omega, Function.iterate_succ_apply]
    congr 1
    have := congrFun hmove i
    rwa [moveOne_self] at this
  · rw [Function.update_of_ne h]
    congr 1
    have hi : (i : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact i.isLt
    exact hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i hi
      (fun hc => h (Fin.ext hc))

/-- **`HJO.Braid.invFin` is the SAME at the two levels of a type-`D` drop.** The two final
tuples are rigid shifts of one another
(`HJO.Mellit.Isolates.positionPair_snd_eq_of_eventType_D`) and `HJO.Braid.invFin_congr_add`
removes the shift, its hypothesis being
`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_D`. -/
theorem invFin_eq_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
        (Function.update (braidDataOfColouring a b N y ηhi k).2 j
          ((braidDataOfColouring a b N y ηhi k).2 j + 1))
      = invFin (sweepTheta a b N) (braidDataOfColouring a b N y ηhi k).1
          (braidDataOfColouring a b N y ηhi k).2 := by
  rw [invFin, hI.positionPair_snd_eq_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj, ← invFin,
    invFin_congr_add _ (levelDropShift a b N ηlo ηhi) _ _
      fun t m hm => hI.sameSide_iterate_of_eventType_D ha hb hN hηlo hy hev hk t m (by omega)]

/-- **THE INVERSION COUNT OF A TYPE-`D` DROP: `HJO.Braid.invIni` changes by `j - (k-1-j)`.**
The moving entry of the upper tuple is the strict maximum
(`HJO.Mellit.Isolates.lt_braidData_fst_of_eventType_D`) and the wrapped entry of the lower one is
the strict minimum
(`HJO.Mellit.Isolates.braidData_fst_lo_lt_levelDropShift_of_eventType_D`), and away from that index
the two tuples differ by the rigid rotation. So
`HJO.Braid.tupleInversions_sub_tupleInversions_of_top_bot` applies verbatim — the same count the
type-`C` residual used, with the roles of the two levels exchanged. -/
theorem invIni_sub_invIni_of_eventType_D (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo) (hstep : ηhi ≤ ηlo + 1)
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hev : eventType y (X, Y) = EventType.D) {k : ℕ}
    (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    ((invIni (sweepTheta a b N) (braidDataOfColouring a b N y ηlo k).1
          (braidDataOfColouring a b N y ηhi k).2 : ℤ)
        - (invIni (sweepTheta a b N) (braidDataOfColouring a b N y ηhi k).1
            (braidDataOfColouring a b N y ηhi k).2 : ℤ))
      = ((j : ℕ) : ℤ) - ((k - 1 - (j : ℕ) : ℕ) : ℤ) := by
  have hηhi : ((a * N : ℕ) : ℚ) < ηhi := hηlo.trans (hI.ltP.trans hI.Plt)
  have hhipos : (0 : ℚ) < ηhi := lt_of_le_of_lt (Nat.cast_nonneg _) hηhi
  have hjlt : (j : ℕ) < #(colouringEast y ηhi) := by rw [hk]; exact j.isLt
  have hlo := hI.braidData_fst_lo_lt_levelDropShift_of_eventType_D ha hb hN hηlo hy hev hk j hj
  have hagree : ∀ i : Fin k, i ≠ j → (braidDataOfColouring a b N y ηlo k).1 i
      = (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi := fun i hne =>
    hI.braidData_fst_of_eventType_D ha hb hN hηlo hy hev hjlt hj i (by rw [hk]; exact i.isLt)
      (fun hc => hne (Fin.ext hc))
  rw [invIni_eq_tupleInversions, invIni_eq_tupleInversions,
    ← tupleInversions_congr_add (c := levelDropShift a b N ηlo ηhi)
      (w := (braidDataOfColouring a b N y ηhi k).1)
      (w' := fun i => (braidDataOfColouring a b N y ηhi k).1 i + levelDropShift a b N ηlo ηhi)
      (fun _ => rfl)]
  refine tupleInversions_sub_tupleInversions_of_top_bot hagree
    (fun i hne => by
      have := hI.lt_braidData_fst_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj i hne
      simpa using this) (fun i hne => ?_)
  rw [hagree i hne]
  have hpos : (0 : ℚ) < (braidDataOfColouring a b N y ηhi k).1 i := by
    rw [braidDataOfColouring_fst_eq_levelPosition ha hb hN hI.hi hhipos i
      (by rw [hk]; exact i.isLt)]
    have hmem := (Finset.mem_filter.1 (colStep_mem (show (i : ℕ) < #(colouringEast y ηhi) by
      rw [hk]; exact i.isLt))).2.2
    have := levelPosition_lt_levelPosition ha hb hN ηhi hmem
    rwa [show levelPosition a b N ηhi ηhi = 0 from by rw [levelPosition]; ring] at this
  linarith

end Isolates

/-! ### The type-`D` clause -/

section Value

variable {L : Type*} [Field L] [Algebra ℚ L]

namespace Isolates

variable {X Y : ℕ} {ηlo ηhi : ℚ}

/-- **THE TYPE-`D` CLAUSE OF `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`, with no
hypothesis about the braid.** Every hypothesis is about the event — the two levels isolate the
point, the path is above the diagonal, the event type is `D` — together with `u ≠ 0` and the
level-gap bound `η₊ ≤ η₋ + 1`.

`hletter` of `HJO.Mellit.Isolates.braidValueColouring_eq_sweepOperator_of_eventType_D_of_letter` is
discharged in three steps, none of which is a reformulation:

* the **letter** is `T_{k↘1}z_1`
  (`HJO.Mellit.Isolates.braidStep_braidData_fst_of_eventType_D`) and it multiplies the vacuum by
  `q^{(k-1)/2}` and nothing else
  (`HJO.Sweep.braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece`) — the only thing
  the clause's bare `q^{a}` can allow;
* the **rest of the braid** is the upper one, the rotated tuple being the upper tuple shifted
  (`HJO.Mellit.Isolates.moveOne_braidData_fst_eq_of_eventType_D`) and the shift being invisible at
  every stage (`HJO.Mellit.Isolates.sameSide_iterate_of_eventType_D`,
  `HJO.Braid.specialBraid_congr_add_of_iterate`);
* the **inversion counts**: `HJO.Braid.invFin` is unchanged
  (`HJO.Mellit.Isolates.invFin_eq_of_eventType_D`) and `HJO.Braid.invIni` changes by
  `j - (k-1-j)` (`HJO.Mellit.Isolates.invIni_sub_invIni_of_eventType_D`), so the surviving power is
  `r^{(k-1-j)-j}·r^{k-1} = q^{k-1-j}`, which is `HJO.Mellit.sweepOperator`'s own exponent at type
  `D`.

This closes the third of the statement's four clauses; the `BE` clause,
the origin clause, the unswept clause and all six recursions are untouched. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_of_index (q u : L) {r : L}
    (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a)
    (hb : 0 < b) (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    (hstep : ηhi ≤ ηlo + 1) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) {k : ℕ} (hk : #(colouringEast y ηhi) = k) (j : Fin k)
    (hj : colStep (colouringEast y ηhi) (j : ℕ) = (X - 1, Y)) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hr0 : r ≠ 0 := ne_zero_of_sq_eq hq hr
  have hk1 : 1 ≤ k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hjk : (j : ℕ) < k := j.isLt
  refine hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_letter q u hq hq1 hqp hr ha hb hN
    hηlo hy hev hk j hj ?_
  -- the letter, in closed form, applied to the vacuum
  rw [hI.braidStep_braidData_fst_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj,
    braidRepMellit_braidTrainDown_top_mul_braidGenZ_one_dplusIterPiece q u hq hq1 hqp hr hu hk1,
    map_smul, Submodule.coe_smul,
    hI.moveOne_braidData_fst_eq_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj,
    specialBraid_congr_add_of_iterate _ (levelDropShift a b N ηlo ηhi) _ _
      (fun t m hm => hI.sameSide_iterate_of_eventType_D ha hb hN hηlo hy hev hk t m hm),
    braidValueOfData, smul_smul, smul_smul,
    hI.invFin_eq_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj]
  congr 1
  -- the inversion counts: `inv_fin` is unchanged and `inv_ini` moves by `j - (k-1-j)`
  have hini := hI.invIni_sub_invIni_of_eventType_D ha hb hN hηlo hstep hy hev hk j hj
  have hq2 : (q : L) ^ (k - 1 - (j : ℕ)) = r ^ (2 * ((k - 1 - (j : ℕ) : ℕ) : ℤ)) := by
    rw [two_mul, zpow_add₀ hr0, zpow_natCast, ← hr, mul_pow]
  rw [hq2, ← zpow_natCast r (k - 1), ← zpow_add₀ hr0, ← zpow_add₀ hr0]
  congr 1
  omega

/-- **THE TYPE-`D` CLAUSE, with the index of the moving component constructed rather than assumed.**
`HJO.Mellit.Isolates.mem_colouringEast_pred_hi_of_eventType_D` says the point one column left of a
type-`D` event is a crossed east step of the upper colouring, and `HJO.Mellit.exists_colStep`
produces its index. -/
theorem braidValueColouring_eq_sweepOperator_of_eventType_D_of_step (q u : L) {r : L} (hq : q ≠ 0)
    (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (hr : r * r = q) (hu : u ≠ 0) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) (hI : Isolates a b N X Y ηlo ηhi) (hηlo : ((a * N : ℕ) : ℚ) < ηlo)
    (hstep : ηhi ≤ ηlo + 1) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hev : eventType y (X, Y) = EventType.D) :
    braidValueColouring q u hq hq1 hqp hr a b N ηlo (colouring y ηlo)
      = sweepOperator q u y (X, Y)
          (braidValueColouring q u hq hq1 hqp hr a b N ηhi (colouring y ηhi)) := by
  have hX0 : 0 < X := hI.pos_fst_of_eventType_D hηlo hy hev
  obtain ⟨i, hi, hie⟩ :=
    exists_colStep (hI.mem_colouringEast_pred_hi_of_eventType_D ha hb hN hX0 hev)
  exact hI.braidValueColouring_eq_sweepOperator_of_eventType_D_of_index q u hq hq1 hqp hr hu ha hb
    hN hηlo hstep hy hev rfl (⟨i, hi⟩ : Fin #(colouringEast y ηhi)) hie

end Isolates

end Value

end HJO.Mellit

end
