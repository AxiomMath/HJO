/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidTrainRelations
public import HJO.Shuffle.SweepModule

/-! # The distant relations of the braid operators, and the letter substitution

`HJO/Shuffle/SweepModule.lean` defines `s_i` (`HJO.Sweep.swapAux`), `∂_i`
(`HJO.Sweep.dividedDiff`), the braid operator `T_i = s_i + (q-1)y_i∂_i`
(`HJO.Sweep.braid`) and the letter substitutions `τ_{k,m}`, `τ^-_{k,m}`
(`HJO.Sweep.qshift`, `HJO.Sweep.qshiftNeg`), and proves the Hecke relation and the invertibility of
`T_i`. It proves no relation *between* two of these operators at different indices. This file proves
the ones that hold for **distant** indices, which is where the Carlsson–Mellit relations layer
starts.

## Main results

* `HJO.Sweep.qshift_braid` — `HJO.Sweep.qshift` commutes with `HJO.Sweep.braid` at a distant letter.
  This is the lemma the whole chain `HJO.Sweep.cmDPlus_braid` →
  `HJO.Sweep.braid_dplusIter` → `HJO.Mellit.braidRep_specialBraid_dplusIter` rests on.
* `HJO.Sweep.braid_comm` — two braid operators at distant indices commute.
* `HJO.Sweep.braid_braid` — the `S_3` braid relation `T_iT_{i+1}T_i = T_{i+1}T_iT_{i+1}`.
* `HJO.Sweep.isBraidSystem_braidEnd` — `HJO.Braid.IsBraidSystem` for the braid operators,
  off the two relations above and the Hecke relation.
* `HJO.Sweep.cmAscWord` — the ascending braid word `T_{[a,b]}`, defined as
  `HJO.Braid.trainUp` at the upper index `b + 1` so that the whole train algebra applies to it
  unchanged.

## How the `S_3` relation is proved

`HJO.Sweep.braid` hides a quotient, so nothing can be expanded until the quotient is gone. The
division-free form is `HJO.Sweep.sub_mul_braid`,
`(y_{i+1}-y_i)T_iF = (q-1)y_iF + (y_{i+1}-qy_i)s_iF` — the defining formula of `T_i` with the
denominator cleared. Each three-fold composite is then pinned by three instances of it, and each
instance is transported by `s_i` or `s_{i+1}` (which are ring homomorphisms, so this is `congrArg`
and the action table on `y_i, y_{i+1}, y_{i+2}`) until everything is expressed in the six images of
`F` under `S_3`. `HJO.Sweep.swapAux_braid` is what makes those images six rather than seven, by
identifying `s_is_{i+1}s_i` with `s_{i+1}s_is_{i+1}`.

Multiplying through by `(y_{i+1}-y_i)²(y_{i+2}-y_{i+1})²(y_{i+2}-y_i)` clears every denominator, and
what is left is `HJO.Sweep.braid_relation_aux`: a polynomial identity in `24` indeterminates with
the operators stripped out entirely, so `linear_combination` verifies it by `ring`. The factor
cancels because `HJO.Sweep.Total L` is a domain. No fraction field, no group algebra of `S_3` and no
freeness result is needed, which is the advantage of this route.

Also proved here, and worth having on their own:

* `HJO.Sweep.dividedDiff_mul` — the Leibniz rule `∂_i(FG) = ∂_i(F)G + s_i(F)∂_i(G)`, and
  `HJO.Sweep.dividedDiff_mul_of_swapAux_eq`, that `∂_i` (hence `T_i`) is linear over the
  `s_i`-symmetric polynomials.

## What the braid system needs

`HJO.Sweep.isBraidSystem_braidEnd` is **not** provable from `HJO.Sweep.piece`, `HJO.Sweep.braid` and
`HJO.Braid.IsBraidSystem` alone: `HJO.Braid.IsBraidSystem` has four fields and the `S_3` relation is
one of them. Its proof invokes the two braid relations, so it depends on `HJO.Sweep.braid_braid` and
`HJO.Sweep.braid_comm`, both proved here.

## Method

Every commutation below is proved from the *uniqueness* of the divided difference,
`HJO.Sweep.dividedDiff_unique`: `∂_iF` is the only `G` with `(y_{i+1}-y_i)G = F - s_iF`, because
`y_{i+1}-y_i` is not a zero divisor. So to see that an operator `Φ` commutes with `∂_i` it is enough
that `Φ` commutes with `s_i` and fixes `y_i` and `y_{i+1}` — apply `Φ` to the defining equation and
read off the uniqueness. That is the argument for
`HJO.Sweep.qshift_braid`, and it also gives the distant `s`/`∂` and `∂`/`∂` commutations with
no further work.

For `τ_{k,m}` the step before that is a generator check. `τ_{k,m}` is an `𝕜`-algebra endomorphism
and `s_i` an `𝕜`-algebra automorphism of `HJO.Sweep.Total L = MvPolynomial ℕ Λ`, so
`MvPolynomial.algHom_ext'` reduces their commutation to two families: the auxiliary variables `y_n`
which `τ_{k,m}` fixes (`HJO.Sweep.qshift_auxVar`), and the power sums `p_r`, which `s_i` fixes and
`τ_{k,m}` moves by `(q^r-1)y_m^r` — and `s_i` fixes `y_m` exactly because `m ∉ {i, i+1}`. That
hypothesis is the whole content of the lemma; nothing else in the argument uses it.

## Index conventions

Each of these is a statement about `F ∈ V_k` with `1 ≤ i ≤ k-1` and `1 ≤ m ≤ k`. Here they are
stated on the total space with no `k`, as everywhere in `HJO.Sweep`: `s_i`, `∂_i` and `T_i` are
single endomorphisms of `Total L` whose restriction to `V_k` is the operator, so the
range condition on `i` carries no content and only the *distance* conditions remain. `1 ≤ m` is
however live and not decoration: `HJO.Sweep.auxVar` reads `y_0` as `y_1`, so at `m = 0` the
substitution is the one at `m = 1` and the excluded set would be `{1, 2}` rather than `{0, 1}`.
-/

@[expose] public section

namespace HJO.Sweep

open HJO.Sym

section Distant

variable {L : Type*} [Field L]

/-! ### Which variables a transposition fixes -/

/-- `s_i` fixes an auxiliary variable outside `{y_i, y_{i+1}}`, read through the internal `0`-based
index. -/
theorem swapAux_X_of_ne_of_ne {i n : ℕ} (h1 : n ≠ i - 1) (h2 : n ≠ i) :
    swapAux L i (MvPolynomial.X n : Total L) = MvPolynomial.X n := by
  rw [swapAux_X, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- `s_i` fixes `y_m` whenever `1 ≤ m` and `m ∉ {i, i+1}`. -/
theorem swapAux_auxVar_of_ne {i m : ℕ} (hm : 1 ≤ m) (h1 : m ≠ i) (h2 : m ≠ i + 1) :
    swapAux L i (auxVar m : Total L) = auxVar m := by
  rw [auxVar]
  exact swapAux_X_of_ne_of_ne (by omega) (by omega)

/-! ### Two distant transpositions, and the divided differences they carry -/

/-- **Two distant adjacent transpositions commute.** Their supports `{i-1, i}` and `{j-1, j}` are
disjoint once `i + 2 ≤ j`. -/
theorem swapAux_comm {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    swapAux L i (swapAux L j F) = swapAux L j (swapAux L i F) := by
  have key : ∀ n : ℕ, Equiv.swap (i - 1) i (Equiv.swap (j - 1) j n)
      = Equiv.swap (j - 1) j (Equiv.swap (i - 1) i n) := by
    intro n
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have h : (swapAux L i).toAlgHom.comp (swapAux L j).toAlgHom
      = (swapAux L j).toAlgHom.comp (swapAux L i).toAlgHom := by
    refine MvPolynomial.algHom_ext fun n => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, swapAux_X]
    rw [key]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) h

/-- `∂_i` is linear over a variable it does not move. -/
theorem dividedDiff_X_mul_of_ne {i n : ℕ} (hi : 1 ≤ i) (h1 : n ≠ i - 1) (h2 : n ≠ i)
    (F : Total L) :
    dividedDiff i (MvPolynomial.X n * F) = MvPolynomial.X n * dividedDiff i F := by
  refine (dividedDiff_unique hi ?_).symm
  rw [map_mul, swapAux_X_of_ne_of_ne h1 h2, ← mul_sub, ← dividedDiff_spec i F]
  ring

/-- `∂_i` is linear over a distant auxiliary variable. -/
theorem dividedDiff_auxVar_mul_of_ne {i m : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (h1 : m ≠ i)
    (h2 : m ≠ i + 1) (F : Total L) :
    dividedDiff i (auxVar m * F) = (auxVar m : Total L) * dividedDiff i F := by
  rw [auxVar]
  exact dividedDiff_X_mul_of_ne hi (by omega) (by omega) F

/-- `∂_j` is linear over the difference `y_{i+1} - y_i` when `i` is distant from `j`. This is the
form the commutation of two divided differences uses. -/
theorem dividedDiff_sub_mul_of_ne {i j : ℕ} (hj : 1 ≤ j) (h1 : i ≠ j - 1) (h2 : i ≠ j)
    (h3 : i - 1 ≠ j - 1) (h4 : i - 1 ≠ j) (F : Total L) :
    dividedDiff j ((MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * F)
      = (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * dividedDiff j F := by
  refine (dividedDiff_unique hj ?_).symm
  rw [map_mul, map_sub, swapAux_X_of_ne_of_ne h1 h2, swapAux_X_of_ne_of_ne h3 h4, ← mul_sub,
    ← dividedDiff_spec j F]
  ring

/-- **A distant transposition commutes with a divided difference**, the lower index on the inside.
By `HJO.Sweep.dividedDiff_unique` it is enough that `s_j` fixes `y_i` and `y_{i+1}` and commutes
with `s_i`. -/
theorem swapAux_dividedDiff_comm_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    swapAux L j (dividedDiff i F) = dividedDiff i (swapAux L j F) := by
  refine dividedDiff_unique hi ?_
  have h := congrArg (swapAux L j) (dividedDiff_spec i F)
  rw [map_mul, map_sub, swapAux_X_of_ne_of_ne (by omega) (by omega),
    swapAux_X_of_ne_of_ne (by omega) (by omega), map_sub, ← swapAux_comm hi hij] at h
  exact h

/-- **A distant transposition commutes with a divided difference**, the higher index on the
inside. -/
theorem swapAux_dividedDiff_comm_gt {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    swapAux L i (dividedDiff j F) = dividedDiff j (swapAux L i F) := by
  refine dividedDiff_unique (show 1 ≤ j by omega) ?_
  have h := congrArg (swapAux L i) (dividedDiff_spec j F)
  rw [map_mul, map_sub, swapAux_X_of_ne_of_ne (by omega) (by omega),
    swapAux_X_of_ne_of_ne (by omega) (by omega), map_sub, swapAux_comm hi hij] at h
  exact h

/-- **Two distant divided differences commute.** -/
theorem dividedDiff_comm {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    dividedDiff j (dividedDiff i F) = dividedDiff i (dividedDiff j F) := by
  refine dividedDiff_unique hi ?_
  rw [← dividedDiff_sub_mul_of_ne (show 1 ≤ j by omega) (by omega) (by omega) (by omega) (by omega),
    dividedDiff_spec i F, ← dividedDiffₗ_apply, map_sub, dividedDiffₗ_apply, dividedDiffₗ_apply,
    ← swapAux_dividedDiff_comm_gt hi hij]

/-! ### Two building blocks for the `S_3` relation -/

/-- **The Leibniz rule for the divided difference**, `∂_i(FG) = ∂_i(F)G + s_i(F)∂_i(G)`. Another
reading of `HJO.Sweep.dividedDiff_unique`: multiplying the right-hand side by `y_{i+1}-y_i` gives
`(F - s_iF)G + s_iF(G - s_iG) = FG - s_i(FG)`.

This is the rule any route to `HJO.Sweep.braid_braid` needs, and it is also what makes `∂_i` — and
hence `T_i` — linear over the polynomials symmetric in `y_i` and `y_{i+1}`
(`HJO.Sweep.dividedDiff_mul_of_swapAux_eq`). -/
theorem dividedDiff_mul (i : ℕ) (F G : Total L) :
    dividedDiff i (F * G) = dividedDiff i F * G + swapAux L i F * dividedDiff i G := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index, dividedDiff_zero_index, dividedDiff_zero_index, zero_mul,
      mul_zero, add_zero]
  refine (dividedDiff_unique hi ?_).symm
  have hF := dividedDiff_spec i F
  have hG := dividedDiff_spec i G
  rw [map_mul]
  linear_combination (G : Total L) * hF + swapAux L i F * hG

/-- **`∂_i` is linear over the `s_i`-symmetric polynomials**, by
`HJO.Sweep.dividedDiff_mul`: a factor `s_i` fixes has `∂_i` equal to `0`, so only the second Leibniz
term survives. -/
theorem dividedDiff_mul_of_swapAux_eq {i : ℕ} {P : Total L} (hP : swapAux L i P = P)
    (F : Total L) : dividedDiff i (P * F) = P * dividedDiff i F := by
  have h0 : dividedDiff i P = 0 := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact dividedDiff_zero_index P
    refine (dividedDiff_unique hi ?_).symm
    rw [hP, sub_self, mul_zero]
  rw [dividedDiff_mul, h0, zero_mul, hP, zero_add]

/-- **The braid operator, cleared of its denominator.**
`(y_{i+1}-y_i)T_iF = (q-1)y_iF + (y_{i+1}-qy_i)s_iF` — the defining formula of `T_i`, here as a
polynomial identity with no division in it. This is the shape in which the `S_3` relation is
approachable: `HJO.Sweep.braid` hides a quotient, and multiplying the three-fold composite by the
three differences `y_{i+1}-y_i`, `y_{i+2}-y_{i+1}`, `y_{i+2}-y_i` is what removes them. -/
theorem sub_mul_braid (q : L) (i : ℕ) (F : Total L) :
    (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) * braid q i F
      = scal (q - 1) * MvPolynomial.X (i - 1) * F
        + (MvPolynomial.X i - scal q * MvPolynomial.X (i - 1)) * swapAux L i F := by
  have hD := dividedDiff_spec i F
  have hy : (auxVar i : Total L) = MvPolynomial.X (i - 1) := rfl
  have hq : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  rw [braid_apply, hy, hq]
  linear_combination (scal (q - 1) * MvPolynomial.X (i - 1) : Total L) * hD

/-- **The three adjacent transpositions satisfy the `S_3` braid relation.** The `s`-part of
`HJO.Sweep.braid_braid`, and all of it that holds without the divided differences. -/
theorem swapAux_braid (i : ℕ) (hi : 1 ≤ i) (F : Total L) :
    swapAux L i (swapAux L (i + 1) (swapAux L i F))
      = swapAux L (i + 1) (swapAux L i (swapAux L (i + 1) F)) := by
  have key : ∀ n : ℕ, Equiv.swap (i - 1) i (Equiv.swap i (i + 1) (Equiv.swap (i - 1) i n))
      = Equiv.swap i (i + 1) (Equiv.swap (i - 1) i (Equiv.swap i (i + 1) n)) := by
    intro n
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have hsucc : i + 1 - 1 = i := by omega
  have h : ((swapAux L i).toAlgHom.comp (swapAux L (i + 1)).toAlgHom).comp (swapAux L i).toAlgHom
      = ((swapAux L (i + 1)).toAlgHom.comp (swapAux L i).toAlgHom).comp
          (swapAux L (i + 1)).toAlgHom := by
    refine MvPolynomial.algHom_ext fun n => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, swapAux_X, hsucc]
    rw [key]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) h

/-! ### The `S_3` braid relation -/

/-- **The ring identity behind `HJO.Sweep.braid_braid`, with the operators stripped out.** Every
hypothesis is one instance of `HJO.Sweep.sub_mul_braid` — the division-free form of `T_i` — or one
instance of it transported by `s_i` or `s_{i+1}`; the conclusion is the braid relation multiplied by
`(v-u)²(w-v)²(w-u)`.

Six knowns (`F` and its five images under `S_3`) and seven unknowns a side. Separating it from the
operators is what makes it checkable: with the operators gone it is a polynomial identity in `24`
indeterminates, and `linear_combination` verifies it by `ring`. -/
theorem braid_relation_aux {R : Type*} [CommRing R]
    (u v w c Q F sF tF stF tsF stsF P sP tP stP Qm sQ Rm P' tP' sP' tsP' Qm' tQ' Rm' : R)
    (hc : c = Q - 1)
    (hP : (v - u) * P = c * u * F + (v - Q * u) * sF)
    (hsP : (v - u) * sP = (Q * v - u) * F - c * v * sF)
    (htP : (w - u) * tP = c * u * tF + (w - Q * u) * tsF)
    (hstP : (w - v) * stP = c * v * stF + (w - Q * v) * stsF)
    (hQm : (w - v) * Qm = c * v * P + (w - Q * v) * tP)
    (hsQ : (w - u) * sQ = c * u * sP + (w - Q * u) * stP)
    (hRm : (v - u) * Rm = c * u * Qm + (v - Q * u) * sQ)
    (hP' : (w - v) * P' = c * v * F + (w - Q * v) * tF)
    (htP' : (w - v) * tP' = (Q * w - v) * F - c * w * tF)
    (hsP' : (w - u) * sP' = c * u * sF + (w - Q * u) * stF)
    (htsP' : (v - u) * tsP' = c * u * tsF + (v - Q * u) * stsF)
    (hQm' : (v - u) * Qm' = c * u * P' + (v - Q * u) * sP')
    (htQ' : (w - u) * tQ' = c * u * tP' + (w - Q * u) * tsP')
    (hRm' : (w - v) * Rm' = c * v * Qm' + (w - Q * v) * tQ') :
    (v - u) ^ 2 * (w - v) ^ 2 * (w - u) * Rm
      = (v - u) ^ 2 * (w - v) ^ 2 * (w - u) * Rm' := by
  subst hc
  linear_combination ((v - u) * (w - v) ^ 2 * (w - u)) * hRm
    + ((Q - 1) * u * (v - u) * (w - v) * (w - u)) * hQm
    + ((Q - 1) ^ 2 * u * v * (w - v) * (w - u)) * hP
    + ((Q - 1) * u * (w - Q * v) * (v - u) * (w - v)) * htP
    + ((v - Q * u) * (v - u) * (w - v) ^ 2) * hsQ
    + ((Q - 1) * u * (v - Q * u) * (w - v) ^ 2) * hsP
    + ((v - Q * u) * (w - Q * u) * (v - u) * (w - v)) * hstP
    - ((v - u) ^ 2 * (w - v) * (w - u)) * hRm'
    - ((Q - 1) * v * (v - u) * (w - v) * (w - u)) * hQm'
    - ((Q - 1) ^ 2 * u * v * (v - u) * (w - u)) * hP'
    - ((Q - 1) * v * (v - Q * u) * (v - u) * (w - v)) * hsP'
    - ((w - Q * v) * (v - u) ^ 2 * (w - v)) * htQ'
    - ((Q - 1) * u * (w - Q * v) * (v - u) ^ 2) * htP'
    - ((w - Q * v) * (w - Q * u) * (v - u) * (w - v)) * htsP'

/-- `HJO.Sweep.sub_mul_braid` at the index `i + 1`, with `i + 1 - 1` normalised to `i`. -/
theorem sub_mul_braid_succ (q : L) (i : ℕ) (G : Total L) :
    (MvPolynomial.X (i + 1) - MvPolynomial.X i : Total L) * braid q (i + 1) G
      = scal (q - 1) * MvPolynomial.X i * G
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X i) * swapAux L (i + 1) G := by
  have h := sub_mul_braid q (i + 1) G
  rwa [Nat.add_sub_cancel] at h

/-- **The `S_3` braid relation for the braid operators**, `HJO.Sweep.braid_braid`:
`T_i T_{i+1} T_i = T_{i+1} T_i T_{i+1}`.

The route is the one `HJO.Sweep.sub_mul_braid` exists for. Each of the two three-fold composites is
pinned by three instances of that division-free identity, and each instance is transported by `s_i`
or `s_{i+1}` to reach the images of `F` under the six elements of `S_3` — where
`HJO.Sweep.swapAux_braid` is what identifies `s_is_{i+1}s_i` with `s_{i+1}s_is_{i+1}`, so that the
six images really are six and not seven. Multiplying through by
`(y_{i+1}-y_i)²(y_{i+2}-y_{i+1})² (y_{i+2}-y_i)` clears every denominator,
`HJO.Sweep.braid_relation_aux` is the resulting polynomial identity, and the factor cancels because
`HJO.Sweep.Total L` is a domain. -/
@[hjo "lem_cm_demazure_braid"]
theorem braid_braid (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    braid q i (braid q (i + 1) (braid q i F))
      = braid q (i + 1) (braid q i (braid q (i + 1) F)) := by
  -- the action of the two transpositions on the three variables in play
  have hsu : swapAux L i (MvPolynomial.X (i - 1) : Total L) = MvPolynomial.X i := by
    rw [swapAux_X, Equiv.swap_apply_left]
  have hsv : swapAux L i (MvPolynomial.X i : Total L) = MvPolynomial.X (i - 1) := by
    rw [swapAux_X, Equiv.swap_apply_right]
  have hsw : swapAux L i (MvPolynomial.X (i + 1) : Total L) = MvPolynomial.X (i + 1) :=
    swapAux_X_of_ne_of_ne (by omega) (by omega)
  have htu : swapAux L (i + 1) (MvPolynomial.X (i - 1) : Total L) = MvPolynomial.X (i - 1) :=
    swapAux_X_of_ne_of_ne (by omega) (by omega)
  have htv : swapAux L (i + 1) (MvPolynomial.X i : Total L) = MvPolynomial.X (i + 1) := by
    rw [swapAux_X, Nat.add_sub_cancel, Equiv.swap_apply_left]
  have htw : swapAux L (i + 1) (MvPolynomial.X (i + 1) : Total L) = MvPolynomial.X i := by
    rw [swapAux_X, Nat.add_sub_cancel, Equiv.swap_apply_right]
  -- the left-hand chain
  have hP := sub_mul_braid q i F
  have hsP : (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) *
      swapAux L i (braid q i F)
      = (scal q * MvPolynomial.X i - MvPolynomial.X (i - 1)) * F
        - scal (q - 1) * MvPolynomial.X i * swapAux L i F := by
    have h := congrArg (swapAux L i) hP
    simp only [map_mul, map_add, map_sub, swapAux_scal, hsu, hsv, swapAux_swapAux] at h
    linear_combination -h
  have htP : (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1) : Total L) *
      swapAux L (i + 1) (braid q i F)
      = scal (q - 1) * MvPolynomial.X (i - 1) * swapAux L (i + 1) F
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X (i - 1)) *
            swapAux L (i + 1) (swapAux L i F) := by
    have h := congrArg (swapAux L (i + 1)) hP
    simp only [map_mul, map_add, map_sub, swapAux_scal, htu, htv] at h
    linear_combination h
  have hstP : (MvPolynomial.X (i + 1) - MvPolynomial.X i : Total L) *
      swapAux L i (swapAux L (i + 1) (braid q i F))
      = scal (q - 1) * MvPolynomial.X i * swapAux L i (swapAux L (i + 1) F)
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X i) *
            swapAux L i (swapAux L (i + 1) (swapAux L i F)) := by
    have h := congrArg (swapAux L i) htP
    simp only [map_mul, map_add, map_sub, swapAux_scal, hsu, hsw] at h
    linear_combination h
  have hQm := sub_mul_braid_succ q i (braid q i F)
  have hsQ : (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1) : Total L) *
      swapAux L i (braid q (i + 1) (braid q i F))
      = scal (q - 1) * MvPolynomial.X (i - 1) * swapAux L i (braid q i F)
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X (i - 1)) *
            swapAux L i (swapAux L (i + 1) (braid q i F)) := by
    have h := congrArg (swapAux L i) hQm
    simp only [map_mul, map_add, map_sub, swapAux_scal, hsv, hsw] at h
    linear_combination h
  have hRm := sub_mul_braid q i (braid q (i + 1) (braid q i F))
  -- the right-hand chain
  have hP' := sub_mul_braid_succ q i F
  have htP' : (MvPolynomial.X (i + 1) - MvPolynomial.X i : Total L) *
      swapAux L (i + 1) (braid q (i + 1) F)
      = (scal q * MvPolynomial.X (i + 1) - MvPolynomial.X i) * F
        - scal (q - 1) * MvPolynomial.X (i + 1) * swapAux L (i + 1) F := by
    have h := congrArg (swapAux L (i + 1)) hP'
    simp only [map_mul, map_add, map_sub, swapAux_scal, htv, htw, swapAux_swapAux] at h
    linear_combination -h
  have hsP' : (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1) : Total L) *
      swapAux L i (braid q (i + 1) F)
      = scal (q - 1) * MvPolynomial.X (i - 1) * swapAux L i F
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X (i - 1)) *
            swapAux L i (swapAux L (i + 1) F) := by
    have h := congrArg (swapAux L i) hP'
    simp only [map_mul, map_add, map_sub, swapAux_scal, hsv, hsw] at h
    linear_combination h
  have htsP' : (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) *
      swapAux L (i + 1) (swapAux L i (braid q (i + 1) F))
      = scal (q - 1) * MvPolynomial.X (i - 1) * swapAux L (i + 1) (swapAux L i F)
        + (MvPolynomial.X i - scal q * MvPolynomial.X (i - 1)) *
            swapAux L i (swapAux L (i + 1) (swapAux L i F)) := by
    have h := congrArg (swapAux L (i + 1)) hsP'
    simp only [map_mul, map_add, map_sub, swapAux_scal, htu, htw] at h
    rw [← swapAux_braid i hi F] at h
    linear_combination h
  have hQm' := sub_mul_braid q i (braid q (i + 1) F)
  have htQ' : (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1) : Total L) *
      swapAux L (i + 1) (braid q i (braid q (i + 1) F))
      = scal (q - 1) * MvPolynomial.X (i - 1) * swapAux L (i + 1) (braid q (i + 1) F)
        + (MvPolynomial.X (i + 1) - scal q * MvPolynomial.X (i - 1)) *
            swapAux L (i + 1) (swapAux L i (braid q (i + 1) F)) := by
    have h := congrArg (swapAux L (i + 1)) hQm'
    simp only [map_mul, map_add, map_sub, swapAux_scal, htu, htv] at h
    linear_combination h
  have hRm' := sub_mul_braid_succ q i (braid q i (braid q (i + 1) F))
  -- the cleared identity, and the cancellation
  have hne1 : (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) ≠ 0 :=
    auxVar_sub_ne_zero hi
  have hne2 : (MvPolynomial.X (i + 1) - MvPolynomial.X i : Total L) ≠ 0 := by
    have h := auxVar_sub_ne_zero (L := L) (show 1 ≤ i + 1 by omega)
    rwa [Nat.add_sub_cancel] at h
  have hne3 : (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1) : Total L) ≠ 0 := by
    refine sub_ne_zero.2 fun h => ?_
    have := MvPolynomial.X_injective (R := Sym.Lambda L) h
    omega
  refine mul_left_cancel₀ (a := (MvPolynomial.X i - MvPolynomial.X (i - 1) : Total L) ^ 2 *
    (MvPolynomial.X (i + 1) - MvPolynomial.X i) ^ 2 *
      (MvPolynomial.X (i + 1) - MvPolynomial.X (i - 1)))
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hne1) (pow_ne_zero 2 hne2)) hne3) ?_
  exact braid_relation_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by rw [← scal_one (L := L), ← scal_sub]) hP hsP htP hstP hQm hsQ hRm hP' htP' hsP' htsP'
    hQm' htQ' hRm'

/-! ### Two distant braid operators commute -/

/-- **Two braid operators at distant indices commute**,
`HJO.Sweep.braid_comm`: expanding `T_i = s_i + (q-1)y_i∂_i` on both sides gives four terms each,
matched by `HJO.Sweep.swapAux_comm`, `HJO.Sweep.swapAux_dividedDiff_comm_lt`,
`HJO.Sweep.swapAux_dividedDiff_comm_gt`, `HJO.Sweep.dividedDiff_auxVar_mul_of_ne` and
`HJO.Sweep.dividedDiff_comm`. -/
@[hjo "lem_cm_demazure_commute"]
theorem braid_comm (q : L) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    braid q i (braid q j F) = braid q j (braid q i F) := by
  have hj : 1 ≤ j := by omega
  have expand : ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
      swapAux L a (auxVar b : Total L) = auxVar b →
      swapAux L a (dividedDiff b F) = dividedDiff b (swapAux L a F) →
      dividedDiff a (auxVar b * dividedDiff b F) = (auxVar b : Total L) * dividedDiff a
        (dividedDiff b F) →
      braid q a (braid q b F)
        = swapAux L a (swapAux L b F)
          + scal (q - 1) * auxVar b * dividedDiff b (swapAux L a F)
          + scal (q - 1) * auxVar a * dividedDiff a (swapAux L b F)
          + scal (q - 1) * scal (q - 1) * auxVar a * auxVar b
              * dividedDiff a (dividedDiff b F) := by
    intro a b _ _ hfix hcomm hlin
    have hstep : dividedDiff a (scal (q - 1) * auxVar b * dividedDiff b F)
        = scal (q - 1) * auxVar b * dividedDiff a (dividedDiff b F) := by
      rw [mul_assoc, dividedDiff_scal_mul, hlin]
      ring
    rw [braid_apply, braid_apply, map_add, map_mul, map_mul, swapAux_scal, hfix, hcomm,
      dividedDiff_add, hstep]
    ring
  rw [expand i j hi hj (swapAux_auxVar_of_ne hj (by omega) (by omega))
      (swapAux_dividedDiff_comm_gt hi hij F)
      (dividedDiff_auxVar_mul_of_ne hi hj (by omega) (by omega) _),
    expand j i hj hi (swapAux_auxVar_of_ne hi (by omega) (by omega))
      (swapAux_dividedDiff_comm_lt hi hij F)
      (dividedDiff_auxVar_mul_of_ne hj hi (by omega) (by omega) _),
    swapAux_comm hi hij, dividedDiff_comm hi hij]
  ring

/-! ### The letter substitution commutes with a distant transposition -/

/-- `τ_{k,m}` fixes a scalar of `𝕜`, being an `𝕜`-algebra map. -/
@[simp]
theorem qshift_scal (q : L) (m : ℕ) (x : L) : qshift q m (scal x : Total L) = scal x := by
  rw [scal_eq_algebraMap, AlgHom.commutes]

/-- `τ_{k,m}` fixes every auxiliary variable, being a `𝕜[y]`-algebra map. -/
@[simp]
theorem qshift_auxVar_apply (q : L) (m j : ℕ) : qshift q m (auxVar j : Total L) = auxVar j :=
  qshift_auxVar q m (j - 1)

/-- **`τ_{k,m}` commutes with a distant transposition.** Both composites are `𝕜`-algebra
endomorphisms of `Total L = MvPolynomial ℕ Λ`, so `MvPolynomial.algHom_ext'` reduces the claim to
the auxiliary variables — which `τ_{k,m}` fixes — and the power sums, where `s_i` fixes `p_r` and
`τ_{k,m}` adds `(q^r-1)y_m^r`, a term `s_i` fixes exactly because `m ∉ {i, i+1}`. -/
theorem qshift_swapAux (q : L) {i m : ℕ} (hm : 1 ≤ m) (h1 : m ≠ i) (h2 : m ≠ i + 1) (F : Total L) :
    qshift q m (swapAux L i F) = swapAux L i (qshift q m F) := by
  have hfix : swapAux L i (auxVar m : Total L) = auxVar m := swapAux_auxVar_of_ne hm h1 h2
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : (qshift q m).comp A = A.comp (qshift q m) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, hAapp, swapAux_C,
        qshift_powerSum, map_add, map_mul, map_pow, swapAux_scal, hfix]
    · simp only [AlgHom.comp_apply, hAapp, swapAux_X, qshift_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **`τ_{k,m}` commutes with a distant divided difference.** -/
theorem qshift_dividedDiff (q : L) {i m : ℕ} (hi : 1 ≤ i) (hm : 1 ≤ m) (h1 : m ≠ i)
    (h2 : m ≠ i + 1) (F : Total L) :
    qshift q m (dividedDiff i F) = dividedDiff i (qshift q m F) := by
  refine dividedDiff_unique hi ?_
  have h := congrArg (qshift q m) (dividedDiff_spec i F)
  rw [map_mul, map_sub, qshift_auxVar, qshift_auxVar, map_sub,
    qshift_swapAux q hm h1 h2] at h
  exact h

/-- **The letter substitution commutes with a distant braid operator.** This is
`HJO.Sweep.qshift_braid`: for `m ∉ {i, i+1}`, `τ_{k,m}(T_iF) = T_i(τ_{k,m}F)`.

Stated on the total space, so the `k ≥ 2`, `i ≤ k-1` and `m ≤ k` carry no content; `i`
is unrestricted because `T_0` is the identity, and `1 ≤ m` is live because `HJO.Sweep.auxVar` reads
`y_0` as `y_1`. -/
@[hjo "lem_cm_qshift_commute_braid"]
theorem qshift_braid (q : L) {i m : ℕ} (hm : 1 ≤ m) (h1 : m ≠ i) (h2 : m ≠ i + 1) (F : Total L) :
    qshift q m (braid q i (F : Total L)) = braid q i (qshift q m F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [braid_zero_index, braid_zero_index]
  rw [braid_apply, braid_apply, map_add, map_mul, map_mul, qshift_scal, qshift_auxVar_apply,
    qshift_dividedDiff q hi hm h1 h2, qshift_swapAux q hm h1 h2]

/-- The same for `τ^-_{k,m}`: the two substitutions differ only in the sign of the added letter, and
the argument reads neither the sign nor the letter beyond `s_i` fixing `y_m`. -/
theorem qshiftNeg_swapAux (q : L) {i m : ℕ} (hm : 1 ≤ m) (h1 : m ≠ i) (h2 : m ≠ i + 1)
    (F : Total L) : qshiftNeg q m (swapAux L i F) = swapAux L i (qshiftNeg q m F) := by
  have hfix : swapAux L i (auxVar m : Total L) = auxVar m := swapAux_auxVar_of_ne hm h1 h2
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : (qshiftNeg q m).comp A = A.comp (qshiftNeg q m) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, hAapp, swapAux_C,
        qshiftNeg_powerSum, map_sub, map_mul, map_pow, swapAux_scal, hfix]
    · simp only [AlgHom.comp_apply, hAapp, swapAux_X, qshiftNeg_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-! ### The two relations in the endomorphism monoid -/

/-- **The `S_3` relation in the endomorphism monoid**, `HJO.Sweep.braid_braid` composed rather than
applied. This and `HJO.Sweep.braidEnd_comm` are the two relations of a braid system that hold for
**every** `q`; the two inverse laws are what needs `q ≠ 0`. -/
theorem braidEnd_braid (q : L) {i : ℕ} (hi : 1 ≤ i) :
    braidEnd q i * braidEnd q (i + 1) * braidEnd q i
      = braidEnd q (i + 1) * braidEnd q i * braidEnd q (i + 1) := by
  refine LinearMap.ext fun F => ?_
  simpa [braidEnd] using braid_braid q hi F

/-- **Far commutation in the endomorphism monoid**, `HJO.Sweep.braid_comm` composed rather than
applied. -/
theorem braidEnd_comm (q : L) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) :
    braidEnd q i * braidEnd q j = braidEnd q j * braidEnd q i := by
  refine LinearMap.ext fun F => ?_
  simpa [braidEnd] using braid_comm q hi hij F

/-! ### `HJO.Braid.IsBraidSystem` for the braid operators, reduced to the `S_3` relation -/

/-- **The braid operators form a braid system, with the `S_3` relation as a hypothesis.** The four
fields of `HJO.Braid.IsBraidSystem` are a right inverse, a left inverse, the braid relation and far
commutation. Three are discharged here — `HJO.Sweep.braidEnd_mul_braidInvEnd`,
`HJO.Sweep.braidInvEnd_mul_braidEnd` (both off the Hecke relation `HJO.Sweep.braid_braid_apply`,
which is where `q ≠ 0` is spent) and `HJO.Sweep.braid_comm` — leaving `hbraid`, which is
`HJO.Sweep.braid_braid`. `HJO.Sweep.isBraidSystem_braidEnd` supplies it. -/
theorem isBraidSystem_braidEnd_of_braid (q : L) (hq : q ≠ 0) (k : ℕ)
    (hbraid : ∀ i, 1 ≤ i → i + 2 ≤ k →
      braidEnd q i * braidEnd q (i + 1) * braidEnd q i
        = braidEnd q (i + 1) * braidEnd q i * braidEnd q (i + 1)) :
    Braid.IsBraidSystem k (braidEnd q) (braidInvEnd q) where
  mul_inv i _ _ := braidEnd_mul_braidInvEnd q hq i
  inv_mul i _ _ := braidInvEnd_mul_braidEnd q hq i
  braid := hbraid
  far_comm _ _ hi hij _ := braidEnd_comm q hi hij

/-- **The braid operators form a braid system**, `HJO.Sweep.isBraidSystem_braidEnd`. The
`S_3` relation is `HJO.Sweep.braid_braid`, far commutation is `HJO.Sweep.braid_comm`, and the two
inverses come off the Hecke relation, where `q ≠ 0` is spent.

The braid system is exhibited in the monoid of `𝕜`-linear endomorphisms of `HJO.Sweep.Total L`,
rather than in the endomorphisms of `V_k`. That is the one-total-space convention used
throughout and not a weakening: each `T_i` maps `V_k` to `V_k` for `1 ≤ i ≤ k-1`
(`HJO.Sweep.braid_mem_piece`), so the tuple restricts to the braid system on `V_k`, and
the total-space monoid is where `HJO.Braid.trainUp` and `HJO.Braid.trainDown` actually read it —
`HJO.Sweep.trainUpEnd` and `HJO.Sweep.trainDownEnd` are words in these very elements. -/
@[hjo "lem_mellit_braid_system"]
theorem isBraidSystem_braidEnd (q : L) (hq : q ≠ 0) (k : ℕ) :
    Braid.IsBraidSystem k (braidEnd q) (braidInvEnd q) :=
  isBraidSystem_braidEnd_of_braid q hq k fun i hi _ => by
    refine LinearMap.ext fun F => ?_
    simpa [braidEnd] using braid_braid q hi F

/-! ### The ascending braid word `HJO.Sweep.cmAscWord` -/

/-- An ascending train below its turning point is the plain ascending word. -/
theorem trainUpEnd_eq_ascendingWord (q : L) {a b : ℕ} (hab : a ≤ b) :
    trainUpEnd q a b = Braid.ascendingWord (braidEnd q) a b := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs
  rfl

/-- **The ascending braid word `T_{[a,b]}`**, `HJO.Sweep.cmAscWord`: the composite
`T_a ∘ T_{a+1} ∘ ⋯ ∘ T_b`, with `T_{[a,a-1]}` the identity.

It is **not** a new object. It is `HJO.Braid.trainUp` at the upper index `b + 1`, and it is written
that way rather than as a second recursion so that the whole train algebra of
`HJO/Shuffle/BraidTrainRelations.lean` applies to it verbatim — the half-open
convention `T_{[a,a-1]} = 1` is `HJO.Braid.trainUp_self`, and the composite form is
`HJO.Sweep.cmAscWord_succ_left`. The range condition `1 ≤ a`, `b ≤ k-1`, `b ≥ a-1`
carries no content here, the trains being total; it reappears wherever a relation of the braid
system is read. -/
@[hjo "def_cm_ascword"]
noncomputable def cmAscWord (q : L) (a b : ℕ) : Module.End L (Total L) := trainUpEnd q a (b + 1)

/-- **The empty convention of `HJO.Sweep.cmAscWord`**: `T_{[a,a-1]} = 1`, written without truncated
subtraction as `T_{[b+1,b]} = 1`. -/
@[simp]
theorem cmAscWord_self_pred (q : L) (b : ℕ) : cmAscWord q (b + 1) b = 1 :=
  Braid.trainUp_self _ _ _

/-- **One letter**: `T_{[a,a]} = T_a`. -/
@[simp]
theorem cmAscWord_self (q : L) (a : ℕ) : cmAscWord q a a = braidEnd q a := by
  rw [cmAscWord, trainUpEnd_eq_ascendingWord q (by omega), Braid.ascendingWord_succ_self]

/-- **The composite form of `HJO.Sweep.cmAscWord`**: `T_{[a,b]} = T_a T_{[a+1,b]}`, which unwinds to
`T_a ∘ T_{a+1} ∘ ⋯ ∘ T_b` and is the display. -/
theorem cmAscWord_succ_left (q : L) {a b : ℕ} (hab : a ≤ b) :
    cmAscWord q a b = braidEnd q a * cmAscWord q (a + 1) b := by
  rw [cmAscWord, cmAscWord, trainUpEnd_eq_ascendingWord q (by omega),
    trainUpEnd_eq_ascendingWord q (by omega), ← Braid.ascendingWord_succ_self (braidEnd q) a,
    Braid.ascendingWord_mul (braidEnd q) (by omega) (by omega)]

/-- **`T_{[a,b]}` applied to an element**,
`T_{[a,b]}(F) = T_a(T_{a+1}(⋯T_b(F)⋯))`, read one step at a time. -/
theorem cmAscWord_apply_succ_left (q : L) {a b : ℕ} (hab : a ≤ b) (F : Total L) :
    cmAscWord q a b F = braid q a (cmAscWord q (a + 1) b F) := by
  rw [cmAscWord_succ_left q hab]
  rfl

end Distant

end HJO.Sweep

end
