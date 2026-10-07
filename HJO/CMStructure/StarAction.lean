/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.CmReplemma
public import HJO.CMStructure.StarConjRel1
public import HJO.CMStructure.StarConjRel2
public meta import HJO.Attr

/-! # Carlsson and Mellit's starred action

`HJO.Sweep.exists_isDpaAction_star`: the operators `T_i^{-1}`, `d_-`, `d^*_+` and the projections
onto the summands define an action of the starred copy of the Dyck path algebra on `V_*`, and they
satisfy the three mixed relations `z_{i+1}d_+ = d_+z_i`, `y_{i+1}d^*_+ = d^*_+y_i` and
`z_1d_+ = -uq^{k+1}y_1d^*_+`.

The starred copy of `HJO.Dyck.Aq` is that definition with `q` replaced by `q^{-1}`, so as an algebra
it is `HJO.Dyck.AqInv`'s `𝔸_{q^{-1}}` — the algebra `HJO.Dyck.Aq L q⁻¹`, which is
`HJO.Dyck.AqInv L q` at the instance `invertibleOfNonzero`. What is starred is the *assignment*: the
loops go to the inverted Demazure--Lusztig operators, the lowering arrow to `d_-` of
`HJO.Sweep.dminusCM` and the raising arrow to `d^*_+` of `HJO.Sweep.dplusStar`.

## Main definitions

* `HJO.Sweep.braidInvModPiece` — `T_{i+1}^{-1}` on the graded piece `V_k`, and `0` when the quiver
  has no such loop. This is the loop family of the starred assignment, as
  `HJO.Sweep.braidModPiece` is of the two unstarred ones.

## Main results

* `HJO.Sweep.exists_isDpaAction_star` — the starred action of `𝔸_{q^{-1}}` on `V_*`.
* `HJO.Sweep.exists_isDpaAction_starInv` — the same over `HJO.Dyck.AqInv L q`, the shape
  `HJO.Sweep.IsIntertwinedPair` reads.
* `HJO.Sweep.mixed_relations_star` — the three mixed relations.
* `HJO.Sweep.isDpaOperators_star` — Carlsson and Mellit's nine relations for the starred operators.

## The nine relations, and how many really transfer

The construction is `HJO.Sweep.IsDpaOperators.exists_isDpaAction`, shared with
`HJO.Sweep.exists_isDpaAction_cm` and `HJO.Sweep.exists_isDpaAction_mod`; this file is its third
instance, and the whole of the path-algebra plumbing is done there. So what remains is Carlsson and
Mellit's nine relations, read at the scalar `q^{-1}` and in the starred operators.

One might expect six of the nine to hold "for the same reasons as before" and three to
involve `d^*_+` essentially. **The split is really five and four**, and the assignment of lemmas
says so: `HJO.Sweep.dplusStar_braidInv` covers the two relations between `d^*_+` and the loops,
`HJO.Sweep.dminusCM_starCommCM_braidInv` the one with `d_-` on the left and
`HJO.Sweep.braidInv_starCommCM_dplusStar` the one with `d^*_+` on the right, which is four; the five
that never mention the raising arrow are `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid`,
`HJO.Sweep.braid_comm`, `HJO.Sweep.dminusCM_braid` and `HJO.Sweep.dminusCM_dminusCM_braid`.

**And those five do not transfer for free either.** `T_{i+1}^{-1}` is a different operator from
`T_{i+1}`, so each of the five is a small separate argument, done here:

* `HJO.Sweep.braidInv_braidInv_apply` — the Hecke relation at `q^{-1}`. This is the substitution
  that `HJO.Sweep.braid_braid_apply` carries, and it is a real computation:
  `T^{-2} = q^{-1} + (1-q^{-1})T^{-1}` follows from `T^2 = (1-q)T + q` by multiplying by `T^{-2}`,
  and `q^{-1}(q-1) = 1 - q^{-1}` is where the substitution happens.
* `HJO.Sweep.braidInv_braidInv_braid` — the braid relation for the inverses. The word is a
  palindrome, so inverting it reverses nothing; the proof cancels `T` against `T^{-1}` six times.
* `HJO.Sweep.braidInv_comm` — two distant inverses commute, by expanding both as
  `q^{-1}(T + (q-1))` and using `HJO.Sweep.braid_comm` on the single cross term.
* `HJO.Sweep.dminusCM_braidInv` — `T_{i+1}^{-1}d_- = d_-T_{i+1}^{-1}`, the same expansion.
* `d_-^2T_{k-1}^{-1} = d_-^2` — `HJO.Sweep.dminusCM_dminusCM_braid` read at `T_{k-1}^{-1}F`, which
  lies in `V_k` because `T_{k-1}^{-1}` does not leave it.

## The hypotheses, and which are forced

`q ≠ 0` is unavoidable: the operators of the statement are the inverses `T_i^{-1}`, which do not
exist otherwise, and the scalar `q^{-1}` of the starred relations is `0` at `q = 0` in Lean rather
than undefined. `HJO.Sweep.exists_isDpaAction_cm` needs no such hypothesis and
`HJO.Sweep.exists_isDpaAction_mod` needs exactly this one.

`q + 1 ≠ 0` is inherited from `HJO.Sweep.dminusCM_starCommCM_braidInv`, which supplies the relation
with `d_-` on the left. The step "the claim is equivalent to `A(T_{k-1}+q) = 0`" holds only up to a
factor `1 + q`, and at `q = -1` the reduced form gives nothing: there `T_{k-1}` is unipotent and the
two subspaces the operator is known to kill do not span `V_k`. The reduced form
`HJO.Sweep.starConj1_braid_add_q` is itself unconditional; the hypothesis is the price of that
route, not of the statement.

**No `q ≠ 1`.** The two sides of the first mixed relation carry the same prefactor
`q^{k+1-i}/(1-q)` — `q^{-i}q^{k+1}` on the left against `q^{1-i}q^k` on the right — so it cancels
and is left off both sides below. Since Lean makes `x/0 = 0`, a surviving `1/(1-q)` would have made
the statement silently false at `q = 1` rather than ill-typed, which is why it is worth saying that
none survives.

Every use instantiates it at parameters algebraically independent over `ℤ`, where `q ≠ 0`,
`q + 1 ≠ 0` and `q ≠ 1` all hold.

## The third mixed relation is stated in Carlsson and Mellit's convention

The third mixed relation as usually written pairs `HJO.Sweep.zop`'s `z_1`, which is built on the
*modified* lowering operator, with `HJO.Sweep.cmDPlus`'s `d_+`; mixed that way the relation is
false, and the evaluation point `F = 1` is a witness. The defect is recorded in full at
`HJO/CMStructure/StarZrelOne.lean`, which proves both *matched* readings — they reduce to the
one computation, Mellit's operators being Carlsson and Mellit's displaced by the last letter, and
the displacements cancelling in the composite `z_1d_+`.

The convention taken here is **all-Carlsson--Mellit**, throughout: `d_-` is `HJO.Sweep.dminusCM`,
`d_+` is `HJO.Sweep.cmDPlus`, `d^*_+` is `HJO.Sweep.dplusStar` and the starred commutator is
`HJO.Sweep.starCommCM`. That is the convention of the action built here, of
`HJO.Sweep.starCommCM_cmDPlus` and of `HJO.Sweep.dminusCM_starCommCM_braidInv`; the reading of the
third mixed relation used below is therefore `HJO.Sweep.starCommCM_trainUpEnd_star_cmDPlus`, not the
Mellit-convention `HJO.Sweep.zopOneStar_dplus`, and no second lowering or raising operator enters.
`HJO.Sweep.starComm` — Mellit's `d^♭_-` in the same expression — appears nowhere here.

**The prefactors of `z_1` and `z_{i+1}` are left off**, as in the two lemmas that supply them.
Reinstating them would need a second `z` operator in the library, `HJO.Sweep.zop`'s formula read
with `HJO.Sweep.dminusCM` in place of `HJO.Sweep.dminus`, which is a genuinely different operator
from `HJO.Sweep.zopOneStar`. What is stated is the part with content: at the first index
the relation is `[d^*_+, d_-](T^*_{k+1↓1}d_+F) = (q-1)uy_1d^*_+F`, and multiplying by
`q^{k+1}/(1-q)` turns it into `z_1d_+ = -uq^{k+1}y_1d^*_+` verbatim.

`HJO.Sweep.braid_one_dplusStar_cmDPlus`, the relation `T_1d^*_+d_+ = d_+d^*_+` between the two
raising arrows, is **not** used here: it is what carries `HJO.Sweep.starCommCM_cmDPlus`, and this
file needs it only through that lemma.

## References

E. Carlsson and A.
Mellit, *A proof of the shuffle conjecture*, §5, and A. Mellit, *Toric braids and `(m, n)`-parking
functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The inverted loops -/

section BraidInv

variable {L : Type*} [Field L]

/-- **`T_{i+1}^{-1}` as an endomorphism of the graded piece `V_k`**, and `0` when the quiver has no
such loop, that is when `k ≤ i + 1`. The index shift is `HJO.Dyck.Aq`'s, as for
`HJO.Sweep.braidModPiece`: the generator `Tg k i` is Carlsson and Mellit's `T_{i+1}` at the vertex
`k`, and the starred assignment sends it to the inverse. -/
noncomputable def braidInvModPiece (q : L) (k i : ℕ) : pieceSub L k →ₗ[L] pieceSub L k :=
  if h : i + 2 ≤ k then
    ((braidInv q (i + 1)).restrictScalars L).restrict
      fun _ hx => braidInv_mem_piece q (by omega) hx
  else 0

theorem coe_braidInvModPiece (q : L) {k i : ℕ} (h : i + 2 ≤ k) (F : pieceSub L k) :
    (braidInvModPiece q k i F : Total L) = braidInv q (i + 1) F := by
  rw [braidInvModPiece]
  simp only [h, ↓reduceDIte]
  rfl

theorem braidInvModPiece_of_le (q : L) {k i : ℕ} (h : k ≤ i + 1) :
    braidInvModPiece q k i = 0 := by
  rw [braidInvModPiece]
  simp only [show ¬(i + 2 ≤ k) from by omega, ↓reduceDIte]

/-- **The Hecke relation at `q^{-1}`**: `T_i^{-2} = (1-q^{-1})T_i^{-1} + q^{-1}`, which is
`HJO.Sweep.braid_braid_apply` read after the substitution the starred copy of `HJO.Dyck.Aq` makes.
Multiplying `T_i^2 = (1-q)T_i + q` by `T_i^{-2}` gives `1 = (1-q)T_i^{-1} + qT_i^{-2}`, and the
substitution is the single scalar identity `q^{-1}(q-1) = 1 - q^{-1}`. -/
theorem braidInv_braidInv_apply (q : L) (hq : q ≠ 0) (i : ℕ) (F : Total L) :
    braidInv q i (braidInv q i F)
      = scal (1 - q⁻¹) * braidInv q i F + scal q⁻¹ * F := by
  have hq' : q⁻¹ * (q - 1) = 1 - q⁻¹ := by
    rw [mul_sub, inv_mul_cancel₀ hq, mul_one]
  have hc : (scal q⁻¹ : Total L) * scal (q - 1) = scal (1 - q⁻¹) := by
    rw [← scal_mul, hq']
  rw [braidInv_apply q i (braidInv q i F), braid_braidInv q hq i]
  linear_combination (braidInv q i F : Total L) * hc

/-- **The braid relation for the inverted loops**, `HJO.Sweep.braid_braid` read in the starred
generators. The word `T_iT_{i+1}T_i` is a palindrome, so inverting the relation leaves the two sides
in the same order; the proof is six cancellations of `T` against `T^{-1}`. -/
theorem braidInv_braidInv_braid (q : L) (hq : q ≠ 0) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    braidInv q i (braidInv q (i + 1) (braidInv q i F))
      = braidInv q (i + 1) (braidInv q i (braidInv q (i + 1) F)) := by
  have hAa : ∀ G : Total L, braid q i (braidInv q i G) = G := braid_braidInv q hq i
  have hBb : ∀ G : Total L, braid q (i + 1) (braidInv q (i + 1) G) = G :=
    braid_braidInv q hq (i + 1)
  have haA : ∀ G : Total L, braidInv q i (braid q i G) = G := braidInv_braid q hq i
  have hbB : ∀ G : Total L, braidInv q (i + 1) (braid q (i + 1) G) = G :=
    braidInv_braid q hq (i + 1)
  have key : braid q i (braid q (i + 1) (braid q i
      (braidInv q (i + 1) (braidInv q i (braidInv q (i + 1) F))))) = F := by
    rw [braid_braid q hi, hBb, hAa, hBb]
  have h : braidInv q i (braidInv q (i + 1) (braidInv q i
        (braid q i (braid q (i + 1) (braid q i
          (braidInv q (i + 1) (braidInv q i (braidInv q (i + 1) F))))))))
      = braidInv q (i + 1) (braidInv q i (braidInv q (i + 1) F)) := by
    rw [haA, hbB, haA]
  rw [key] at h
  exact h

/-- **Two distant inverted loops commute**, `HJO.Sweep.braid_comm` read in the starred
generators. Expanding `T_i^{-1} = q^{-1}(T_i + (q-1))` on both sides leaves one cross term
`T_iT_j`, and that is `HJO.Sweep.braid_comm`. -/
theorem braidInv_comm (q : L) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (F : Total L) :
    braidInv q i (braidInv q j F) = braidInv q j (braidInv q i F) := by
  have e : ∀ a b : ℕ, braidInv q a (braidInv q b F)
      = scal q⁻¹ * scal q⁻¹ * (braid q a (braid q b F) + scal (q - 1) * braid q a F
          + scal (q - 1) * braid q b F + scal (q - 1) * scal (q - 1) * F) := by
    intro a b
    rw [braidInv_apply q b F, braidInv_apply q a (scal q⁻¹ * (braid q b F + scal (q - 1) * F)),
      braid_scal_mul, map_add, braid_scal_mul]
    ring
  rw [e i j, e j i, braid_comm q hi hij]
  ring

end BraidInv

/-! ### The lowering operator against the inverted loops -/

section Lower

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-` commutes with the inverted loops** at the indices at which it commutes with the loops
themselves, `HJO.Sweep.dminusCM_braid` read in the starred generators: `T_i^{-1}` is a
`𝕜`-combination of `T_i` and the identity, and `d_-` is `𝕜`-linear. -/
theorem dminusCM_braidInv (q : L) {k i : ℕ} (hik : i ≤ k) (F : Total L) :
    dminusCM q (k + 2) (braidInv q i F) = braidInv q i (dminusCM q (k + 2) F) := by
  rw [braidInv_apply q i F, braidInv_apply q i (dminusCM q (k + 2) F), dminusCM_scal_mul,
    map_add, dminusCM_braid q hik, dminusCM_scal_mul]

/-- **`d_-^2T_{k-1}^{-1} = d_-^2` on `V_k`**, `HJO.Sweep.dminusCM_dminusCM_braid` read in the
starred generators. `T_{k-1}^{-1}` is an endomorphism of `V_k`, so
`HJO.Sweep.dminusCM_dminusCM_braid` applies to `T_{k-1}^{-1}F` and `T_{k-1}T_{k-1}^{-1} = 1`
finishes. -/
theorem dminusCM_dminusCM_braidInv (q : L) (hq : q ≠ 0) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 2)) :
    dminusCM q (m + 1) (dminusCM q (m + 2) (braidInv q (m + 1) F))
      = dminusCM q (m + 1) (dminusCM q (m + 2) F) := by
  have hmem : braidInv q (m + 1) F ∈ piece L (m + 2) :=
    braidInv_mem_piece q (by omega) hF
  have h := dminusCM_dminusCM_braid q m hmem
  rw [braid_braidInv q hq (m + 1)] at h
  exact h.symm

end Lower

/-! ### The nine relations -/

section Star

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The starred operators satisfy Carlsson and Mellit's nine relations at the scalar `q^{-1}`.**
Field by field: the first family is `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and
`HJO.Sweep.braid_comm` read in the inverted loops; the second `HJO.Sweep.dminusCM_braid` and
`HJO.Sweep.dminusCM_dminusCM_braid`, likewise; the third `HJO.Sweep.dplusStar_braidInv`, in both its
clauses about the raising arrow; and the pair `HJO.Sweep.dminusCM_starCommCM_braidInv`,
`HJO.Sweep.braidInv_starCommCM_dplusStar`. -/
theorem isDpaOperators_star (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    IsDpaOperators q⁻¹ (braidInvModPiece q) (dminusPiece q) (dplusStarPiece q u) where
  loop_eq_zero h := braidInvModPiece_of_le q h
  quadratic := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [AddMemClass.coe_add, SetLike.val_smul, coe_braidInvModPiece q hik,
      smul_eq_scal_mul]
    exact braidInv_braidInv_apply q hq (i + 1) _
  braid := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q (show i + 2 ≤ k from by omega),
      coe_braidInvModPiece q (show i + 1 + 2 ≤ k from by omega)]
    exact braidInv_braidInv_braid q hq (show 1 ≤ i + 1 from by omega) _
  comm := by
    intro k i j hi hj hij F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q hi, coe_braidInvModPiece q hj]
    exact braidInv_comm q (show 1 ≤ i + 1 from by omega)
      (show i + 1 + 2 ≤ j + 1 from by omega) _
  loop_lower := by
    intro m i him F
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q him, coe_dminusPiece,
      coe_braidInvModPiece q (show i + 2 ≤ n + 2 + 1 from by omega)]
    exact (dminusCM_braidInv q (k := n + 1) (show i + 1 ≤ n + 1 from by omega) _).symm
  lower_sq := by
    intro m F
    refine Subtype.ext ?_
    simp only [coe_dminusPiece, coe_braidInvModPiece q (show m + 2 ≤ m + 2 from le_rfl)]
    exact dminusCM_dminusCM_braidInv q hq m F.2
  raise_loop := by
    intro k i hik F
    refine Subtype.ext ?_
    simp only [coe_dplusStarPiece, coe_braidInvModPiece q hik,
      coe_braidInvModPiece q (show i + 1 + 2 ≤ k + 1 from by omega)]
    exact dplusStar_braidInv q u hq (show 1 ≤ i + 1 from by omega)
      (show i + 1 < k from by omega) _
  raise_sq := by
    intro k F
    refine Subtype.ext ?_
    simp only [coe_braidInvModPiece q (show 0 + 2 ≤ k + 2 from by omega), coe_dplusStarPiece]
    exact braidInv_one_dplusStar_dplusStar q u hq F.2
  extra_lower := by
    intro j F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusPiece, coe_dplusStarPiece,
      coe_braidInvModPiece q (show j + 2 ≤ j + 2 from le_rfl)]
    have h := dminusCM_starCommCM_braidInv q u hq hq1 (k := j) F.2
    rw [starCommCM_succ_apply, starCommCM_succ_apply] at h
    exact h
  extra_raise := by
    intro m F
    refine Subtype.ext ?_
    simp only [AddSubgroupClass.coe_sub, SetLike.val_smul, coe_dminusPiece, coe_dplusStarPiece,
      coe_braidInvModPiece q (show 0 + 2 ≤ m + 2 from by omega)]
    have h := braidInv_starCommCM_dplusStar q u hq (k := m) F.2
    simp only [map_sub] at h ⊢
    exact h

/-! ### The action -/

/-- **Carlsson--Mellit, the starred action**, the action half of
`HJO.Sweep.exists_isDpaAction_star`: the operators `T_i^{-1}`, `d_-`, `d^*_+` and the projections
onto the summands define an action of the starred copy of the Dyck path algebra on `V_*`.

The starred copy of `HJO.Dyck.Aq` is that definition with `q` replaced by `q^{-1}`, which is
`HJO.Dyck.AqInv`'s `𝔸_{q^{-1}}`; `HJO.Dyck.Aq` being a presentation, "the operators define an
action" is the statement that the assignment of its generators to them descends to an algebra
homomorphism out of that algebra, and here it is one satisfying `HJO.Sweep.IsDpaAction` as well.

The proof. The assignment extends to the path algebra, composability being respected;
by `HJO.Sweep.IsDpaAction` it then suffices that the images of the generators of the defining ideal
vanish, and that is `HJO.Sweep.isDpaOperators_star` fed to
`HJO.Sweep.IsDpaOperators.exists_isDpaAction`, which also discharges the nine relations of the
path-algebra structure. `HJO.Sweep.coe_braidInvModPiece`, `HJO.Sweep.coe_dminusPiece` and
`HJO.Sweep.coe_dplusStarPiece` read the three operator families off as
`HJO.Sweep.braidInv`, `HJO.Sweep.dminusCM` and `HJO.Sweep.dplusStar`.

The three mixed relations are the other half of the statement and are
`HJO.Sweep.mixed_relations_star`. `q ≠ 0` and `q + 1 ≠ 0` are accounted for in the file header. -/
@[hjo "lem_cm_astarthm"]
theorem exists_isDpaAction_star (q u : L) (hq : q ≠ 0) (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Aq L q⁻¹ →ₐ[L] Module.End L (Vstar L), IsDpaAction q⁻¹ ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q⁻¹ k i) = loopVstar (braidInvModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q⁻¹ k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q⁻¹ k) = raiseVstar (dplusStarPiece q u) k) :=
  (isDpaOperators_star q u hq hq1).exists_isDpaAction

/-- `HJO.Sweep.exists_isDpaAction_star` over `HJO.Dyck.AqInv L q`, which is `HJO.Dyck.Aq L ⅟q` by
`HJO.Dyck.AqInv`. This is the shape `HJO.Sweep.IsIntertwinedPair` reads,
`HJO.Sweep.IsDpaIntertwined` taking its second action out of that algebra; at the instance
`invertibleOfNonzero` the two statements are the same one, `⅟q` being `q⁻¹` there. -/
theorem exists_isDpaAction_starInv (q u : L) [Invertible q] (hq1 : q + 1 ≠ 0) :
    ∃ ρ : Dyck.Aq L (⅟q) →ₐ[L] Module.End L (Vstar L), IsDpaAction (⅟q) ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L (⅟q) k i) = loopVstar (braidInvModPiece q) k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L (⅟q) k) = lowerVstar (dminusPiece q) k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L (⅟q) k) = raiseVstar (dplusStarPiece q u) k) := by
  rw [invOf_eq_inv]
  exact exists_isDpaAction_star q u (Invertible.ne_zero q) hq1

/-! ### The three mixed relations -/

/-- **The three mixed relations of `HJO.Dyck.Tilde.Atilde`, for the operators**, the other half of
`HJO.Sweep.exists_isDpaAction_star`: `z_{i+1}d_+ = d_+z_i`,
`y_{i+1}d^*_+ = d^*_+y_i` and `z_1d_+ = -uq^{k+1}y_1d^*_+`, each in the all-Carlsson--Mellit
convention of the action above and with the common prefactors of `z` removed; see the file header
for both points.

The first clause is `HJO.Sweep.starCommCM_cmDPlus`
(`HJO.Sweep.trainDown_starCommCM_trainUp_cmDPlus`), which unwinds `HJO.Dyck.Tilde.Atilde`'s
recursion `z_i = qT_i^{-1}z_{i+1}T_i^{-1}` into the conjugation of `z_1` by the two braid trains,
exact at both ends of `1 ≤ i ≤ k`. The second is the third clause of `HJO.Sweep.dplusStar_braidInv`
(`HJO.Sweep.dplusStar_auxVar_mul`), the corner element acting as multiplication by its variable and
the cyclic shift inside `d^*_+` raising its index. The third is `HJO.Sweep.zopOneStar_dplus` in its
all-Carlsson--Mellit reading (`HJO.Sweep.starCommCM_trainUpEnd_star_cmDPlus`), where the train of
`z_1` undoes the train of `d_+` and what is left is one commutator computation. -/
@[hjo "lem_cm_astarthm"]
theorem mixed_relations_star (q u : L) (hq : q ≠ 0) :
    (∀ (k i : ℕ), 1 ≤ i → i ≤ k → ∀ F : Total L, F ∈ piece L k →
        trainDownEnd q (i + 1) 1 (starCommCM q u (k + 1)
            (trainUpEnd q (k + 1) 1 (trainUpEnd q 1 (i + 1) (cmDPlus q k F))))
          = cmDPlus q k (trainDownEnd q i 1 (starCommCM q u k
              (trainUpEnd q k 1 (trainUpEnd q 1 i F)))))
      ∧ (∀ (k i : ℕ), 1 ≤ i → i ≤ k → ∀ F : Total L,
          dplusStar q u k ((auxVar i : Total L) * F)
            = (auxVar (i + 1) : Total L) * dplusStar q u k F)
      ∧ (∀ (k : ℕ) (F : Total L), F ∈ piece L k →
          dplusStar q u k (dminusCM q (k + 1) (trainUpEnd q (k + 1) 1 (cmDPlus q k F)))
              - dminusCM q (k + 1 + 1)
                  (dplusStar q u (k + 1) (trainUpEnd q (k + 1) 1 (cmDPlus q k F)))
            = scal ((q - 1) * u) * (auxVar 1 : Total L) * dplusStar q u k F) :=
  ⟨fun _ _ hi hik _ hF => trainDown_starCommCM_trainUp_cmDPlus q u hq hi hik hF,
   fun _ _ hi hik F => dplusStar_auxVar_mul q u hi hik F,
   fun _ _ hF => starCommCM_trainUpEnd_star_cmDPlus q u hq hF⟩

end Star

end HJO.Sweep

end
