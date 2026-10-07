/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmCommutator
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CMStructure.VmodYMultiplication
public import HJO.SweepBlocks.Transport

/-! # The corner operator in closed form, at every width

`HJO.Sweep.corner` is `(q-1)^{-1}` times a commutator of the *sweep* pair of
generators `d^♭_±` (`HJO.Sweep.dminus`, `HJO.Sweep.dplus`). The commutator of that pair is already
proved at every width — it is `HJO.Sweep.dplus_dminus_sub_dminus_dplus` — so dividing by `q - 1`
gives the corner outright:

**`Δ^{(k)}F = -T_{1↑k}(y_kF)` for every `k ≥ 1` and every `F ∈ V_k`, whenever `q ∉ {0, 1}`.**

That is `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`. The two values of the corner proved
independently of this file are the width-1 closed form `Δ^{(1)}(y_1F) = -y_1^2F` and the single
width-2 computation `Δ^{(2)}(y_1y_2) = -qy_1^2y_2`, and both are re-derived here from the general
formula as consistency checks — `HJO.Sweep.corner_one_auxVar_mul_of_general` and
`HJO.Sweep.corner_two_X_zero_mul_X_one_of_general`, the latter's conclusion being verbatim that of
`HJO.Sweep.corner_two_X_zero_mul_X_one`.

## Which lowering operator

Everything here is about `HJO.Sweep.dminus`, the *sweep* convention, which
pairs `F_j` with `e_j`. `HJO.Sweep.dminusCM` (`HJO.Sweep.dminusCM`, pairing `F_j` with `e_{j+1}`)
appears only inside the proof of the transported statement, where
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` is quoted; it never occurs in a statement of this
file. `HJO.Sweep.corner` is built from the sweep pair, so the sweep pair is the one whose commutator
the corner is.

## Main results

* `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` — `Δ^{(k)}F = -T_{1↑k}(y_kF)` on `V_k`, for
  `q ≠ 0` and `q ≠ 1`.
* `HJO.Sweep.corner_auxVar_mul` — the same read at `y_kF`, the shape that generalises
  `HJO.Sweep.corner_one_auxVar_mul`.
* `HJO.Sweep.corner_transport_eq` — `Δ^{(k)}(Y_kF) = -Y_kT_{1↑k}(y_kF)` on the transport
  `Y_kV_k ⊆ V_k`, for `q ≠ 1` *only*. This is the generalisation of
  `HJO.Sweep.corner_one_transport` and it is the sharper statement where it applies.
* `HJO.Sweep.dminus_dplus_sub_dplus_dminus_transport` — its numerator,
  `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` carried across the transport, generalising
  `HJO.Sweep.dminus_dplus_sub_dplus_dminus_transport_one`.

## Genericity: exactly what is needed, and where the two routes differ

`q ≠ 1` is unavoidable in every statement: `HJO.Sweep.corner` carries the literal factor
`(q-1)^{-1}`, and at `q = 1` a field's `0^{-1} = 0` makes `HJO.Sweep.corner 1 k` the zero map
(the same collapse `HJO.Sweep.cmCorner_one_eq_zero` records for the unmodified corner), while
`-T_{1↑k}(y_kF)` is not zero. So the formula is false at `q = 1`, not merely unproved.

`q ≠ 0` is read by the route through `HJO.Sweep.dplus_dminus_sub_dminus_dplus`, and only by that
route. It enters through `HJO.Sweep.dplus_eq_neg_cmAscWord_cmDPlus`, which writes `d^♭_+`
in terms of the unmodified `d_+` using the *inverted* braid letters `T_i^{-1}`, and those exist only
for `q ≠ 0` (`HJO.Sweep.trainUpEnd_star_mul_cmAscWord`). Whether the conclusion itself survives at
`q = 0` is left open here: no statement of this file mentions an inverse of `q`, so nothing forces
its failure, but no proof is offered either.

What is offered instead is the observation that on the transport `Y_kV_k` the hypothesis is not
needed at all. `HJO.Sweep.corner_transport_eq` goes through
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` and
`HJO.Sweep.dminus_transport`/`HJO.Sweep.dplus_transport`, none of which reads `q ≠ 0`, and it is
exactly the width-1 situation generalised: `Y_1 = -y_1`, so `Y_1V_1 = y_1V_1` and
`HJO.Sweep.corner_one_transport` needs only `q ≠ 1`. For `k ≥ 2` the transport `Y_kV_k = y_1⋯y_kV_k`
is a proper submodule of `V_k`, so the two statements are genuinely different reaches: the general
one covers all of `V_k` at the cost of `q ≠ 0`, the transported one covers a submodule for free.

**`u` does not occur.** The corner operator is built from `d^♭_±` alone; the unit `u` enters the
sweep only through `HJO.Sweep.cycleShift` and `HJO.Sweep.zop`, neither of which is read here. So no
statement of this file needs `u ≠ 0`, and the `u ≠ 0` that
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_u_zero` forces on `HJO.Mellit.SweepAppend` is not a
condition on the corner.

**This costs nothing in the applications.** Both `hzero` instances at which a width-2 corner
actually occurs already assume `q ≠ 0`: `HJO.Mellit.sweepAppend_nil_two_three_one` and
`HJO.Mellit.sweepAppend_nil_one_two_two` are both stated with `q ≠ 0`, `u ≠ 0`, `q ≠ 1`, and
`HJO.Mellit.not_sweepAppend_nil_two_three_one_of_q_zero` shows the first of those cannot drop it.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Scalars

variable {L : Type*} [Field L]

/-- `x • F = (scal x)F`, the conversion the corner's `(q-1)^{-1} •` needs. A local copy:
`HJO.Sweep.smul_eq_scal_mul` lives in `HJO/Shuffle/SweepAppendWidth.lean`, which this file
deliberately does not import. -/
private theorem smul_eq_scal_mul' (x : L) (F : Total L) : x • F = scal x * F := by
  rw [scal_eq_algebraMap, Algebra.smul_def]

end Scalars

section Main

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The closed form on all of `V_k` -/

/-- **`Δ^{(k)}F = -T_{1↑k}(y_kF)` for every `k ≥ 1` and every `F ∈ V_k`**, whenever `q ≠ 0` and
`q ≠ 1`: the corner operator of `HJO.Sweep.corner` at every width, in closed form.

Read at `k = m + 1`, so the ascending word is `T_{1↑m+1}` of `HJO.Sweep.cmAscWord` with nothing
truncated and the empty word at `m = 0` (`HJO.Sweep.cmAscWord_one_zero`).

This is `HJO.Sweep.dplus_dminus_sub_dminus_dplus` divided by `q - 1`,
and nothing else: that theorem already states the commutator of the *sweep* pair
`d^♭_± = HJO.Sweep.dminus, HJO.Sweep.dplus` at general width, and `HJO.Sweep.corner` is
`(q-1)^{-1}` times that commutator with the opposite sign, so the `q - 1` of that theorem cancels
the `(q-1)^{-1}` of the definition and leaves the sign. `q ≠ 0` comes from that theorem,
`q ≠ 1` from the inverse. -/
theorem corner_eq_neg_cmAscWord_auxVar_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    corner q (m + 1) F = -(cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)) := by
  have hs : (scal ((q - 1)⁻¹) : Total L) * scal (q - 1) = 1 := by
    rw [← scal_mul, inv_mul_cancel₀ (sub_ne_zero.2 hq1), scal_one]
  have hcom := dplus_dminus_sub_dminus_dplus q hq0 m hF
  rw [corner_of_pos q (show m + 1 ≠ 0 by omega), LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show m + 1 + 1 = m + 2 from rfl,
    show m + 1 - 1 = m from rfl, smul_eq_scal_mul']
  linear_combination (-(scal ((q - 1)⁻¹) : Total L)) * hcom
    + (-(cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))) * hs

/-- **`Δ^{(k)}(y_kF) = -T_{1↑k}(y_k^2F)` for `F ∈ V_k`**, whenever `q ≠ 0` and `q ≠ 1`: the shape
`HJO.Sweep.corner_one_auxVar_mul` has at width `1`, at every width.
`HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` read at `y_kF`, which lies in `V_k` with `F`. -/
theorem corner_auxVar_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    corner q (m + 1) ((auxVar (m + 1) : Total L) * F)
      = -(cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ 2 * F)) := by
  have hmem : (auxVar (m + 1) : Total L) * F ∈ piece L (m + 1) :=
    Subalgebra.mul_mem _ (auxVar_mem_piece (by omega) le_rfl) hF
  rw [corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 m hmem,
    show (auxVar (m + 1) : Total L) * ((auxVar (m + 1) : Total L) * F)
      = (auxVar (m + 1) : Total L) ^ 2 * F from by ring]

/-- **`Δ^{(k)}(y_k^{n+1}G) = -T_{1↑k}(y_k^{n+2}G)` for `G ∈ V_k`**, the generalisation in the second
index of `HJO.Sweep.corner_one_auxVar_pow`: `HJO.Sweep.corner_auxVar_mul` at `F = y_k^nG`. -/
theorem corner_auxVar_pow_mul (hq0 : q ≠ 0) (hq1 : q ≠ 1) (m n : ℕ) {G : Total L}
    (hG : G ∈ piece L (m + 1)) :
    corner q (m + 1) ((auxVar (m + 1) : Total L) ^ (n + 1) * G)
      = -(cmAscWord q 1 m ((auxVar (m + 1) : Total L) ^ (n + 2) * G)) := by
  have hmem : (auxVar (m + 1) : Total L) ^ n * G ∈ piece L (m + 1) :=
    Subalgebra.mul_mem _ (pow_mem (auxVar_mem_piece (by omega) le_rfl) n) hG
  have h := corner_auxVar_mul hq0 hq1 m hmem
  rw [show (auxVar (m + 1) : Total L) * ((auxVar (m + 1) : Total L) ^ n * G)
      = (auxVar (m + 1) : Total L) ^ (n + 1) * G from by ring,
    show (auxVar (m + 1) : Total L) ^ 2 * ((auxVar (m + 1) : Total L) ^ n * G)
      = (auxVar (m + 1) : Total L) ^ (n + 2) * G from by ring] at h
  exact h

/-! ### The closed form on the transport, with no condition on `q` beyond `q ≠ 1` -/

/-- **The numerator of `HJO.Sweep.corner` at every width, on the transport of `V_k`.** This is
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` read at `k = m + 1` and carried from the
Carlsson--Mellit pair of generators to the sweep pair by `HJO.Sweep.dplus_transport` and
`HJO.Sweep.dminus_transport`:

`(d^♭_-d^♭_+ - d^♭_+d^♭_-)(Y_kF) = (1-q)Y_kT_{1↑k}(y_kF)` for `F ∈ V_k`.

The generalisation in the width of `HJO.Sweep.dminus_dplus_sub_dplus_dminus_transport_one`, whose
proof is this one with the word `T_{1↑1}` the identity. Nothing here reads `q ≠ 0`: the transport is
multiplication by a ring element and `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` is
unconditional in `q`. -/
theorem dminus_dplus_sub_dplus_dminus_transport (q : L) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    dminus q (m + 2) (dplus q (m + 1) (transport L (m + 1) F))
        - dplus q m (dminus q (m + 1) (transport L (m + 1) F))
      = scal (1 - q) * (transportScalar L (m + 1)
          * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)) := by
  have hcom := dminusCM_cmDPlus_sub_cmDPlus_dminusCM q m hF
  change dminus q (m + 1 + 1) (dplus q (m + 1) (transport L (m + 1) F))
      - dplus q m (dminus q (m + 1) (transport L (m + 1) F))
    = scal (1 - q) * (transportScalar L (m + 1)
        * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F))
  have hL : dminus q (m + 1 + 1) (dplus q (m + 1) (transport L (m + 1) F))
      = transport L (m + 1) (dminusCM q (m + 1 + 1) (cmDPlus q (m + 1) F)) := by
    rw [dplus_transport q (m + 1) F, dminus_transport q (m + 1) (cmDPlus q (m + 1) F)]
  have hR : dplus q m (dminus q (m + 1) (transport L (m + 1) F))
      = transport L (m + 1) (cmDPlus q m (dminusCM q (m + 1) F)) := by
    rw [dminus_transport q m F, dplus_transport q m (dminusCM q (m + 1) F)]
  rw [hL, hR, ← map_sub, show m + 1 + 1 = m + 2 from rfl, hcom, transport_apply]
  ring

/-- **`Δ^{(k)}(Y_kF) = -Y_kT_{1↑k}(y_kF)` for every `k ≥ 1` and every `F ∈ V_k`**, for every
`q ≠ 1` — with **no** hypothesis `q ≠ 0`.

The generalisation in the width of `HJO.Sweep.corner_one_transport`, and the sharper of the two
closed forms where it applies: `Y_k = (-1)^ky_1⋯y_k`, so its reach is the submodule
`Y_kV_k = y_1⋯y_kV_k` of `V_k`, which at `k = 1` is all of `y_1V_1` and for `k ≥ 2` is proper. On
that submodule `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` says the same thing (the transport
scalar is symmetric in `y_1, …, y_k` by `HJO.Sweep.swapAux_transportScalar`, hence passes the word),
but only for `q ≠ 0`. -/
theorem corner_transport_eq (hq : q ≠ 1) (m : ℕ) {F : Total L} (hF : F ∈ piece L (m + 1)) :
    corner q (m + 1) (transport L (m + 1) F)
      = -(transportScalar L (m + 1) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F)) := by
  have hscal : (q - 1)⁻¹ * (1 - q) = -1 := by
    have hq' : q - 1 ≠ 0 := sub_ne_zero.2 hq
    field_simp
    ring
  rw [corner_of_pos q (show m + 1 ≠ 0 by omega), LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply, show m + 1 + 1 = m + 2 from rfl,
    show m + 1 - 1 = m from rfl, dminus_dplus_sub_dplus_dminus_transport q m hF,
    ← smul_eq_scal_mul', smul_smul, hscal, neg_one_smul]

end Main

/-! ### The two known values, re-derived from the general formula

These are the two values of `HJO.Sweep.corner` computed independently of this file. Both are
recovered from `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`, which is what pins its scalar: the
general formula carries no free constant, and a wrong sign or a stray power of `q` would break one
of the two. -/

section Checks

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-- **Check at width `1`: `Δ^{(1)}(y_1F) = -y_1(y_1F)` for `F ∈ V_1`**, the conclusion of
`HJO.Sweep.corner_one_auxVar_mul`, obtained from `HJO.Sweep.corner_auxVar_mul` at `m = 0` where the
ascending word `T_{1↑1}` is the identity (`HJO.Sweep.cmAscWord_one_zero`).

The general formula is therefore consistent with the width-1 closed form. It is *weaker* in one
respect at this width: `HJO.Sweep.corner_one_auxVar_mul` needs only `q ≠ 1`, because it goes through
the transport, and `y_1V_1 = Y_1V_1` exactly at `k = 1`. -/
theorem corner_one_auxVar_mul_of_general (hq0 : q ≠ 0) (hq1 : q ≠ 1) {F : Total L}
    (hF : F ∈ piece L 1) :
    corner q 1 ((auxVar 1 : Total L) * F)
      = -((auxVar 1 : Total L) * ((auxVar 1 : Total L) * F)) := by
  have hF' : F ∈ piece L (0 + 1) := by rwa [Nat.zero_add]
  have h := corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 0
    (F := (auxVar (0 + 1) : Total L) * F)
    (Subalgebra.mul_mem _ (auxVar_mem_piece (by omega) le_rfl) hF')
  rw [cmAscWord_one_zero, Module.End.one_apply, Nat.zero_add] at h
  exact h

omit [Algebra ℚ L] in
private theorem dividedDiff_one_auxVar_one_mul_auxVar_two_sq :
    dividedDiff 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 ^ 2)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 := by
  refine (dividedDiff_unique (i := 1) le_rfl ?_).symm
  rw [map_mul, map_pow, swapAux_X, swapAux_X]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
  ring

omit [Algebra ℚ L] in
/-- **`T_1(y_1y_2^2) = qy_1^2y_2`.** A local copy of
`HJO.Sweep.braid_one_X_zero_mul_X_one_sq`, whose file this one deliberately does not import. -/
private theorem braid_one_auxVar_one_mul_auxVar_two_sq (q : L) :
    braid q 1 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 ^ 2)
      = scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1) := by
  have hq : (scal q : Total L) = 1 + scal (q - 1) := by
    rw [← scal_one (L := L), ← scal_add]
    congr 1
    ring
  have hav : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  rw [braid_apply, dividedDiff_one_auxVar_one_mul_auxVar_two_sq, map_mul, map_pow, swapAux_X,
    swapAux_X]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Nat.sub_self]
  rw [hav, hq]
  ring

/-- **Check at width `2`: `Δ^{(2)}(y_1y_2) = -qy_1^2y_2`.** The conclusion is verbatim that of
`HJO.Sweep.corner_two_X_zero_mul_X_one`, which was computed by hand from `HJO.Sweep.corner`;
here it is `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` at `m = 1`, where the ascending word
`T_{1↑2}` is the single letter `T_1` (`HJO.Sweep.cmAscWord_self`) and
`T_1(y_2 · y_1y_2) = T_1(y_1y_2^2) = qy_1^2y_2`.

This is the data point that pins the factor of `q`: the general formula puts `y_k` *inside* the
word, so the word acts on `y_1y_2^2` rather than on `y_1y_2`, and it is the braid operator — not the
corner — that produces the `q`. Had the word been placed outside, the value would have been
`-y_1y_2^2`, and this check would fail. -/
theorem corner_two_X_zero_mul_X_one_of_general (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = -(scal q * ((MvPolynomial.X 0 : Total L) ^ 2 * MvPolynomial.X 1)) := by
  have hav1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hav2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  have hmem : ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1) ∈ piece L (1 + 1) := by
    refine Subalgebra.mul_mem _ ?_ ?_
    · rw [← hav1]; exact auxVar_mem_piece (by omega) (by omega)
    · rw [← hav2]; exact auxVar_mem_piece (by omega) (by omega)
  have h := corner_eq_neg_cmAscWord_auxVar_mul hq0 hq1 1 hmem
  have hbe : ∀ G : Total L, braidEnd q 1 G = braid q 1 G := fun _ => rfl
  rw [show (1 : ℕ) + 1 = 2 from rfl, hav2,
    show (MvPolynomial.X 1 : Total L) * ((MvPolynomial.X 0 : Total L) * MvPolynomial.X 1)
      = (MvPolynomial.X 0 : Total L) * MvPolynomial.X 1 ^ 2 from by ring,
    cmAscWord_self, hbe, braid_one_auxVar_one_mul_auxVar_two_sq] at h
  exact h

end Checks

end HJO.Sweep

end
