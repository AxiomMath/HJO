/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidMonoid
public import HJO.Shuffle.BraidRelations
public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # The braid representation

Mellit's Proposition 5.3 sends the generators of `𝔹_k^+(𝕋_0)` to operators on `V_k`:
`T_i ↦ q^{-1/2}T_i`, `T̄_i ↦ q^{1/2}T_i^{-1}`, `y_1 ↦ -y_1` and `z_1 ↦ (qu)^{-1}z_1`. This
file builds the assignment and descends it to the quotient. Well-definedness is a hypothesis
here; `HJO/CMStructure/BraidRepReduce.lean` reduces it to one clause of that proposition,
`HJO.Sweep.BraidRepResidual`, and `HJO.Sweep.braidRepRespects_mellit`
(`HJO/CMStructure/MellitBraidRep.lean`) discharges it at generic `q`.

## The codomain is the graded piece, and that is not a detail

`HJO.Sweep.braidRep`'s codomain is `End(V_k ⊗_𝕜 𝕜[q^{1/2}])` — endomorphisms of **one graded
piece** — and `HJO.Sweep.braidRep` below is typed at `Module.End L (pieceSub L k)`
accordingly. Typing the whole layer at `Module.End L (Total L)`, the one-total-space convention
used elsewhere, is **impossible**: `HJO.Sweep.braidRepRespectsTotal_two_false` in
`HJO/CMStructure/BraidRepNotTotal.lean` proves there is no rank-`2` instance of it,
because `HJO.Sweep.zop_two_not_comm` makes `z_1z_2 ≠ z_2z_1` on `y_3`, the first auxiliary
variable *outside* `V_2`. The operators are defined between graded pieces; extending them to
the whole total space and then asking them to commute there asks for more than Mellit's
proposition says.

The total-space layer is kept, under the names `HJO.Sweep.braidRepLetterTotal`,
`HJO.Sweep.braidRepFreeTotal`, `HJO.Sweep.yRepTotal`, `HJO.Sweep.zRepTotal`,
`HJO.Sweep.BraidRepRespectsTotal` and `HJO.Sweep.braidRepTotal`, for three reasons: every
closed form downstream (`HJO/CMStructure/YBraid.lean`,
`HJO/CMStructure/ZBraid.lean`, `HJO/CMStructure/ZyMixed.lean`) is proved there and
each such identity *descends*; the refutation has to have something to be a refutation of; and
at rank `1` the total-space representation exists outright, which is the typing
`HJO.Sweep.slopeOperator` is written in.

`HJO.Sweep.zop_mem_piece` is what makes the typing on the graded piece well posed: `z_i` carries
`V_k` into itself for `1 ≤ i ≤ k`. At `i = 1`, which is all this file needs, that is
`HJO.Sweep.zopOneStar_mem_piece`, and the same holds for every other letter —
`HJO.Sweep.braid_mem_piece`, `HJO.Sweep.braidInv_mem_piece`, `HJO.Sweep.auxVar_mem_piece` — so
`HJO.Sweep.braidRepLetterTotal_mem_piece` holds for *every* letter, in rank or out of it, and the
piece-level assignment is the restriction of the total-space one with no guard of its own.

The bridge between the two layers is `HJO.Sweep.braidRepFree_coe`, from which
`HJO.Sweep.braidRepFree_eq_of_total` follows: any identity between words proved on the total
space holds on the graded piece. That single implication is what lets the reduction in
`HJO/CMStructure/BraidRepReduce.lean` keep all nine discharged relation families at the
total-space level while the one residual clause is asked only on `V_k`.

## Which `d_-` this layer speaks

Mellit's, throughout. `HJO.Sweep.zop` is built on `HJO.Sweep.zopOneStar`, which is built on
`HJO.Sweep.starComm` and hence on `HJO.Sweep.dminus` — the modified lowering operator `d^♭_-`, which
pairs `F_j` with `e_j`. It is **not** `HJO.Sweep.dminusCM`, which pairs `F_j` with `e_{j+1}` and is
the operator the starred action `HJO.Sweep.exists_isDpaAction_star` sends `d_-` to. The choice of
codomain does not affect this: the two conventions are related by the displacement
`HJO.Sweep.dminusCM_eq_neg_dminus_auxVar_mul` by the last letter, and carrying that displacement
through the commutator and both trains of `z_1` is a separate bridge, not given here. Any
identification of these operators' `z_i` with a `ρ^*(y_i)` of the starred action must supply it.

## Main definitions

* `HJO.Sweep.braidRepLetterTotal`, `HJO.Sweep.braidRepFreeTotal` — the assignment on letters
  and the homomorphism it induces on the *free* monoid, on the total space, which needs no
  relation at all.
* `HJO.Sweep.braidRepLetter`, `HJO.Sweep.braidRepFree` — the same two on the graded piece,
  restrictions of the above.
* `HJO.Sweep.yRepTotal`, `HJO.Sweep.zRepTotal`, `HJO.Sweep.yRep`, `HJO.Sweep.zRep` — the
  operators the words `𝗒_i`, `𝗓_i` are sent to, on the total space and on the piece.
* `HJO.Sweep.BraidRepRespectsTotal`, `HJO.Sweep.BraidRepRespects` — the assignment kills the
  relations, on the total space and on the piece. The first is false at `k = 2`.
* `HJO.Sweep.braidRep`, given that hypothesis;
  `HJO.Sweep.braidRepTotal` — its total-space shadow.

## Main results

* `HJO.Sweep.braidRepFree_coe`, `HJO.Sweep.braidRepFree_eq_of_total` — the bridge.
* `HJO.Sweep.braidRep_T`, `HJO.Sweep.braidRep_Tbar`, `HJO.Sweep.braidRep_y`,
  `HJO.Sweep.braidRep_z` — the values on the generators.
* `HJO.Sweep.braidRep_zero` — at `k = 0` the representation is the unique homomorphism out of
  the trivial monoid, as it must be.
* `HJO.Sweep.yRepTotal_succ`, `HJO.Sweep.zRepTotal_succ` — what the `q^{1/2}` normalisation
  costs: the operator recursions are `y_{i+1} = q·T_i^{-1}y_iT_i^{-1}` and
  `z_{i+1} = q^{-1}T_iz_iT_i`.

## Implementation notes

### `HJO.Sweep.braidRep` is not a bare definition: it carries its well-definedness

`HJO.Sweep.braidRep` names "the monoid homomorphism induced by" an assignment on the generators of
a *presented* monoid. Such a homomorphism exists exactly when the assignment respects the relations,
and that is Mellit's Proposition 5.3 — a theorem, not a convention. It is stated as
`HJO.Sweep.braidRep_unique`, and it is not proved in this file, so this file cannot define
`HJO.Sweep.braidRep` as a bare `def`.

What it does instead is carry the well-definedness hypothesis. `HJO.Sweep.braidRepFree` is the
assignment on the free monoid, which is unconditional; `HJO.Sweep.BraidRepRespects` says it
kills the relations; and `HJO.Sweep.braidRep` takes that as an argument.

**The reduction of that hypothesis is not in this file.** Proposition 5.3's five clauses are

* `y_i T_j = T_j y_i` and `z_i T_j = T_j z_i` for `i ∉ {j, j+1}`,
* `y_iy_j = y_jy_i` and `z_iz_j = z_jz_i`,
* `z_1T_1y_1T_1^{-1} = T_1^{-1}y_1T_1^{-1}z_1`,

read on the operators, and four of them are theorems — `HJO.Sweep.yRepTotal_mul_braidEnd` and
`HJO.Sweep.yRepTotal_mul_comm` in `HJO/CMStructure/YBraid.lean`, `HJO.Sweep.zRepTotal_mul_braidEnd`
in `HJO/CMStructure/ZBraid.lean`, and the mixed one in `HJO/CMStructure/ZyMixed.lean`. All of those
files import this one, so a residue stated here would have to keep all five clauses and would carry
as hypotheses four things that are theorems. The residue and the reduction therefore live
downstream, in `HJO/CMStructure/BraidRepReduce.lean`, where `HJO.Sweep.BraidRepResidual` is the one
clause left: `z_iz_j = z_jz_i`, **on the graded piece**, proved as
`HJO.Sweep.braidRepResidual_mellit`. This file carries only the unconditional part — the assignment,
the free homomorphisms, the operator recursions, the bridge, and `HJO.Sweep.braidRep` itself.

### `q^{1/2}` is a designated square root in the base field, not a base change

The target is the monoid of `𝕜[q^{1/2}]`-linear endomorphisms of
`V_k ⊗_𝕜 𝕜[q^{1/2}]`. Building that base change would add a layer whose only purpose is to
name a square root of `q`; instead this file takes a parameter `r : L` with `r * r = q`, the
base field `L` of the one-total-space convention already being arbitrary. Every
statement about the target is recovered by instantiating `L := 𝕜(q^{1/2})` and
`r := q^{1/2}`, and no statement is lost, `V_k ⊗_𝕜 𝕜[q^{1/2}]` being
`HJO.Sweep.pieceSub L k` over that `L` — which, by `HJO.Sweep.pieceTensorAlgEquiv`, is the
tensor product itself and not merely a module containing a copy of it.

The normalisation is not cosmetic and the two places it shows are recorded:
`HJO.Sweep.yRepTotal_succ` — `y_{i+1} = q·T_i^{-1}y_iT_i^{-1}` for the operators, because
`𝗒_{i+1}` carries two `T̄` letters and each contributes `r` — and the mixed relation of
`HJO/CMStructure/ZyMixed.lean`, which acquires a factor `q` on one side for the same
reason.

### Out-of-rank letters go to the identity

`HJO.Braid.BraidRel` trivialises the letters outside the rank, which is what cuts the free
monoid on the whole of `HJO.Braid.Letter` down to the `F_k`. The assignment must
therefore do the same, and `HJO.Sweep.braidRepLetterTotal` guards every clause with
`HJO.Braid.Letter.InRank`. **Dropping the guard would make the assignment fail to descend**:
`HJO.Sweep.braidEnd q 0` is the identity operator, so the unguarded `T_0 ↦ q^{-1/2}T_0` sends
a letter that the monoid has killed to the scalar `q^{-1/2}`, which is `1` only when `q = 1`.

The guard also makes the `k = 0` clause a theorem: every letter is out of rank
there, so `HJO.Sweep.braidRep_zero` says `π_0` sends everything to the identity.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, Proposition 5.3.
-/

@[expose] public section

namespace HJO.Sweep

open Braid

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem ite_of_pos {P : Prop} [Decidable P] {α : Sort*} (h : P) (a b : α) :
    (if P then a else b) = a := by simp [h]

private theorem ite_of_neg {P : Prop} [Decidable P] {α : Sort*} (h : ¬ P) (a b : α) :
    (if P then a else b) = b := by simp [h]

/-! ### The assignment on letters, on the total space -/

/-- **The assignment of `HJO.Sweep.braidRep` on the letters**: `T_i ↦ q^{-1/2}T_i`,
`T̄_i ↦ q^{1/2}T_i^{-1}`, `y_1 ↦ -y_1` (multiplication by `-y_1`) and `z_1 ↦ (qu)^{-1}z_1`,
with `r` standing for `q^{1/2}`.

A letter outside the rank goes to the identity, matching `HJO.Braid.BraidRel.out_of_rank`; see
the module docstring on why the guard cannot be dropped. -/
noncomputable def braidRepLetterRaw (q u r : L) (k : ℕ) : Letter → Module.End L (Total L)
  | Letter.T i => r⁻¹ • braidEnd q i
  | Letter.Tbar i => r • braidInvEnd q i
  | Letter.y1 => -LinearMap.mulLeft L (auxVar 1 : Total L)
  | Letter.z1 => (q * u)⁻¹ • zop q u k 1

/-- The assignment itself, with the out-of-rank letters sent to the identity. -/
noncomputable def braidRepLetterTotal (q u r : L) (k : ℕ) (c : Letter) : Module.End L (Total L) :=
  if Letter.InRank k c then braidRepLetterRaw q u r k c else 1

theorem braidRepLetterTotal_T (q u r : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    braidRepLetterTotal q u r k (Letter.T i) = r⁻¹ • braidEnd q i := by
  rw [braidRepLetterTotal, ite_of_pos (show Letter.InRank k (Letter.T i) from ⟨hi, hik⟩)]
  rfl

theorem braidRepLetterTotal_Tbar (q u r : L) {k i : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    braidRepLetterTotal q u r k (Letter.Tbar i) = r • braidInvEnd q i := by
  rw [braidRepLetterTotal, ite_of_pos (show Letter.InRank k (Letter.Tbar i) from ⟨hi, hik⟩)]
  rfl

theorem braidRepLetterTotal_y1 (q u r : L) {k : ℕ} (hk : 1 ≤ k) :
    braidRepLetterTotal q u r k Letter.y1 = -LinearMap.mulLeft L (auxVar 1 : Total L) := by
  rw [braidRepLetterTotal, ite_of_pos (show Letter.InRank k Letter.y1 from hk)]
  rfl

theorem braidRepLetterTotal_z1 (q u r : L) {k : ℕ} (hk : 1 ≤ k) :
    braidRepLetterTotal q u r k Letter.z1 = (q * u)⁻¹ • zop q u k 1 := by
  rw [braidRepLetterTotal, ite_of_pos (show Letter.InRank k Letter.z1 from hk)]
  rfl

theorem braidRepLetterTotal_of_not_inRank (q u r : L) {k : ℕ} {c : Letter}
    (h : ¬ Letter.InRank k c) : braidRepLetterTotal q u r k c = 1 := by
  rw [braidRepLetterTotal, ite_of_neg h]

/-- **The assignment on the free monoid**, which needs no relation: this is unconditionally a
monoid homomorphism, and the whole content of `HJO.Sweep.braidRep` is whether it descends. -/
noncomputable def braidRepFreeTotal (q u r : L) (k : ℕ) :
    FreeMonoid Letter →* Module.End L (Total L) :=
  FreeMonoid.lift (braidRepLetterTotal q u r k)

@[simp]
theorem braidRepFreeTotal_of (q u r : L) (k : ℕ) (c : Letter) :
    braidRepFreeTotal q u r k (FreeMonoid.of c) = braidRepLetterTotal q u r k c := rfl

/-! ### The images of the `y`- and `z`-words, on the total space -/

/-- The operator the word `𝗒_i` of `HJO.Braid.yWord` is sent to, on the total space. -/
noncomputable def yRepTotal (q u r : L) (k i : ℕ) : Module.End L (Total L) :=
  braidRepFreeTotal q u r k (yWord i)

/-- The operator the word `𝗓_i` of `HJO.Braid.zWord` is sent to, on the total space. -/
noncomputable def zRepTotal (q u r : L) (k i : ℕ) : Module.End L (Total L) :=
  braidRepFreeTotal q u r k (zWord i)

theorem yRepTotal_def (q u r : L) (k i : ℕ) :
    yRepTotal q u r k i = braidRepFreeTotal q u r k (yWord i) := rfl

theorem zRepTotal_def (q u r : L) (k i : ℕ) :
    zRepTotal q u r k i = braidRepFreeTotal q u r k (zWord i) := rfl

theorem yRepTotal_one (q u r : L) {k : ℕ} (hk : 1 ≤ k) :
    yRepTotal q u r k 1 = -LinearMap.mulLeft L (auxVar 1 : Total L) := by
  rw [yRepTotal, yWord_one, braidRepFreeTotal_of, braidRepLetterTotal_y1 q u r hk]

theorem zRepTotal_one (q u r : L) {k : ℕ} (hk : 1 ≤ k) :
    zRepTotal q u r k 1 = (q * u)⁻¹ • zop q u k 1 := by
  rw [zRepTotal, zWord_one, braidRepFreeTotal_of, braidRepLetterTotal_z1 q u r hk]

/-- **What the `q^{1/2}` normalisation costs on the `y` side.** The word
`𝗒_{i+1} = T̄_i 𝗒_i T̄_i` carries two `T̄` letters and each is scaled by `r`, so the operator
recursion is `y_{i+1} = q · T_i^{-1} y_i T_i^{-1}` — the unnormalised
`y_{i+1} = T_i^{-1}y_iT_i^{-1}` with a factor `q`, which is the price of the half-integral
normalisation of the braid letters. -/
theorem yRepTotal_succ (q u : L) {r : L} (hr : r * r = q) {k i : ℕ} (hik : i + 2 ≤ k) :
    yRepTotal q u r k (i + 2)
      = q • (braidInvEnd q (i + 1) * yRepTotal q u r k (i + 1) * braidInvEnd q (i + 1)) := by
  rw [yRepTotal, yWord_succ, map_mul, map_mul, braidRepFreeTotal_of,
    braidRepLetterTotal_Tbar q u r (show 1 ≤ i + 1 by omega) (show i + 1 + 1 ≤ k by omega),
    ← yRepTotal_def]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hr]

/-- **And on the `z` side.** The word `𝗓_{i+1} = T_i 𝗓_i T_i` carries two `T` letters, each
scaled by `r^{-1}`, so the operator recursion is `z_{i+1} = q^{-1}T_iz_iT_i` — which is
`HJO.Sweep.zop`'s own recursion, on the nose. The `y` and `z` normalisations are inverse to one
another, and that asymmetry is already in the presentation of `HJO.Braid.BraidMonoid`. -/
theorem zRepTotal_succ (q u : L) {r : L} (hr : r * r = q) {k i : ℕ} (hik : i + 2 ≤ k) :
    zRepTotal q u r k (i + 2)
      = q⁻¹ • (braidEnd q (i + 1) * zRepTotal q u r k (i + 1) * braidEnd q (i + 1)) := by
  rw [zRepTotal, zWord_succ, map_mul, map_mul, braidRepFreeTotal_of,
    braidRepLetterTotal_T q u r (show 1 ≤ i + 1 by omega) (show i + 1 + 1 ≤ k by omega),
    ← zRepTotal_def]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_inv, hr]

/-! ### Every letter preserves the graded piece

The well-posedness half of the typing on the graded piece: each of the four operators the assignment
names carries `V_k` into itself, so the assignment restricts to `V_k` with no guard beyond the one
it already has. -/

/-- **Every letter of the assignment is an endomorphism of `V_k`.** In rank the four clauses
are `HJO.Sweep.braid_mem_piece`, `HJO.Sweep.braidInv_mem_piece`, `HJO.Sweep.auxVar_mem_piece`
(`V_k` being a subalgebra) and `HJO.Sweep.zopOneStar_mem_piece`, each at exactly the index
range `HJO.Braid.Letter.InRank` supplies; out of rank the letter goes to the identity and there
is nothing to prove. The `z` clause is the `i = 1` case of `HJO.Sweep.zop_mem_piece`, which is
all the assignment reads. -/
theorem braidRepLetterTotal_mem_piece (q u r : L) (k : ℕ) (c : Letter) {F : Total L}
    (hF : F ∈ piece L k) : braidRepLetterTotal q u r k c F ∈ piece L k := by
  cases c with
  | T i =>
    by_cases hc : Letter.InRank k (Letter.T i)
    · obtain ⟨hi, hik⟩ := hc
      rw [braidRepLetterTotal_T q u r hi hik, LinearMap.smul_apply]
      exact smul_mem_piece (braid_mem_piece q hi (by omega) hF)
    · rw [braidRepLetterTotal_of_not_inRank q u r hc]
      exact hF
  | Tbar i =>
    by_cases hc : Letter.InRank k (Letter.Tbar i)
    · obtain ⟨hi, hik⟩ := hc
      rw [braidRepLetterTotal_Tbar q u r hi hik, LinearMap.smul_apply]
      exact smul_mem_piece (braidInv_mem_piece q (show i < k by omega) hF)
    · rw [braidRepLetterTotal_of_not_inRank q u r hc]
      exact hF
  | y1 =>
    by_cases hc : Letter.InRank k Letter.y1
    · rw [braidRepLetterTotal_y1 q u r hc, LinearMap.neg_apply, LinearMap.mulLeft_apply]
      exact neg_mem (mul_mem (auxVar_mem_piece le_rfl hc) hF)
    · rw [braidRepLetterTotal_of_not_inRank q u r hc]
      exact hF
  | z1 =>
    by_cases hc : Letter.InRank k Letter.z1
    · rw [braidRepLetterTotal_z1 q u r hc, LinearMap.smul_apply, zop_one]
      exact smul_mem_piece (zopOneStar_mem_piece q u hc hF)
    · rw [braidRepLetterTotal_of_not_inRank q u r hc]
      exact hF

/-! ### The assignment on the graded piece -/

/-- **The assignment of `HJO.Sweep.braidRep` on the letters, at the codomain**: the
restriction of `HJO.Sweep.braidRepLetterTotal` to `V_k`, well defined by
`HJO.Sweep.braidRepLetterTotal_mem_piece`. -/
noncomputable def braidRepLetter (q u r : L) (k : ℕ) (c : Letter) :
    Module.End L (pieceSub L k) :=
  (braidRepLetterTotal q u r k c).restrict fun _ hx =>
    braidRepLetterTotal_mem_piece q u r k c hx

@[simp]
theorem coe_braidRepLetter (q u r : L) (k : ℕ) (c : Letter) (x : pieceSub L k) :
    (braidRepLetter q u r k c x : Total L) = braidRepLetterTotal q u r k c x := rfl

/-- **The assignment on the free monoid, at the codomain.** Unconditionally a
monoid homomorphism; the whole content of `HJO.Sweep.braidRep` is whether it descends to
`𝔹_k^+(𝕋_0)`. -/
noncomputable def braidRepFree (q u r : L) (k : ℕ) :
    FreeMonoid Letter →* Module.End L (pieceSub L k) :=
  FreeMonoid.lift (braidRepLetter q u r k)

@[simp]
theorem braidRepFree_of (q u r : L) (k : ℕ) (c : Letter) :
    braidRepFree q u r k (FreeMonoid.of c) = braidRepLetter q u r k c := rfl

/-- **The bridge between the two layers**: the piece-level free representation is the
restriction of the total-space one, word by word. -/
theorem braidRepFree_coe (q u r : L) (k : ℕ) (w : FreeMonoid Letter) (x : pieceSub L k) :
    (braidRepFree q u r k w x : Total L) = braidRepFreeTotal q u r k w x := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [map_one, Module.End.one_apply]
  | of_mul c w ih =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, braidRepFree_of,
      coe_braidRepLetter, ih, braidRepFreeTotal_of]

/-- **Any identity between words proved on the total space descends to the graded piece.**
This is the one implication the typing on the graded piece needs: the nine relation families that
`HJO/CMStructure/BraidRepReduce.lean` discharges are all proved at the total-space level,
where the closed forms live, and only the residual clause has to be asked on `V_k`. The
converse fails — that is exactly `HJO.Sweep.zop_two_not_comm`. -/
theorem braidRepFree_eq_of_total (q u r : L) (k : ℕ) {x y : FreeMonoid Letter}
    (h : braidRepFreeTotal q u r k x = braidRepFreeTotal q u r k y) :
    braidRepFree q u r k x = braidRepFree q u r k y := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [braidRepFree_coe, braidRepFree_coe, h]

/-! ### The images of the `y`- and `z`-words on the graded piece -/

/-- The operator the word `𝗒_i` of `HJO.Braid.yWord` is sent to, on `V_k`. -/
noncomputable def yRep (q u r : L) (k i : ℕ) : Module.End L (pieceSub L k) :=
  braidRepFree q u r k (yWord i)

/-- The operator the word `𝗓_i` of `HJO.Braid.zWord` is sent to, on `V_k`. -/
noncomputable def zRep (q u r : L) (k i : ℕ) : Module.End L (pieceSub L k) :=
  braidRepFree q u r k (zWord i)

theorem yRep_def (q u r : L) (k i : ℕ) : yRep q u r k i = braidRepFree q u r k (yWord i) := rfl

theorem zRep_def (q u r : L) (k i : ℕ) : zRep q u r k i = braidRepFree q u r k (zWord i) := rfl

@[simp]
theorem coe_yRep (q u r : L) (k i : ℕ) (x : pieceSub L k) :
    (yRep q u r k i x : Total L) = yRepTotal q u r k i x :=
  braidRepFree_coe q u r k (yWord i) x

@[simp]
theorem coe_zRep (q u r : L) (k i : ℕ) (x : pieceSub L k) :
    (zRep q u r k i x : Total L) = zRepTotal q u r k i x :=
  braidRepFree_coe q u r k (zWord i) x

/-! ### Well-definedness -/

/-- **The assignment respects the relations of `HJO.Braid.BraidMonoid`, on the total space.** This
is the hypothesis the total-space shadow `HJO.Sweep.braidRepTotal` needs, and
`HJO.Sweep.braidRepRespectsTotal_two_false` proves it cannot be supplied at `k = 2`. It is kept
because it is what that refutation refutes, and because at `k = 1` it holds outright. -/
def BraidRepRespectsTotal (q u r : L) (k : ℕ) : Prop :=
  ∀ x y : FreeMonoid Letter, BraidRel k x y →
    braidRepFreeTotal q u r k x = braidRepFreeTotal q u r k y

/-- **The assignment respects the relations of `HJO.Braid.BraidMonoid`, on `V_k`.** This is the
hypothesis `HJO.Sweep.braidRep` needs;
`HJO.Sweep.braidRepRespects_of_residual`, downstream in
`HJO/CMStructure/BraidRepReduce.lean`, reduces it to the one clause
`HJO.Sweep.BraidRepResidual`, which `HJO.Sweep.braidRepResidual_mellit` proves. It is weaker than
`HJO.Sweep.BraidRepRespectsTotal`: the total-space form implies it by
`HJO.Sweep.braidRepFree_eq_of_total`, and the total-space form is refuted at `k = 2` by
`HJO.Sweep.braidRepRespectsTotal_two_false` while this one is not. -/
def BraidRepRespects (q u r : L) (k : ℕ) : Prop :=
  ∀ x y : FreeMonoid Letter, BraidRel k x y → braidRepFree q u r k x = braidRepFree q u r k y

/-- The total-space hypothesis implies the one on the graded piece. -/
theorem braidRepRespects_of_total (q u r : L) (k : ℕ) (h : BraidRepRespectsTotal q u r k) :
    BraidRepRespects q u r k :=
  fun x y hxy => braidRepFree_eq_of_total q u r k (h x y hxy)

/-! ### The representation -/

/-- **The braid representation `π_k`**, `HJO.Sweep.braidRep`: the monoid
homomorphism `𝔹_k^+(𝕋_0) → End(V_k ⊗_𝕜 𝕜[q^{1/2}])` induced by `T_i ↦ q^{-1/2}T_i`,
`T̄_i ↦ q^{1/2}T_i^{-1}`, `y_1 ↦ -y_1` and `z_1 ↦ (qu)^{-1}z_1`, with `r` for `q^{1/2}`.

**The codomain is the graded piece.** The total-space typing
is refuted; see `HJO.Sweep.braidRepRespectsTotal_two_false` and the module docstring.

**It takes the well-definedness hypothesis as an argument**, because discharging it
is a theorem in its own right: a homomorphism out of a presented monoid exists exactly when the
assignment respects the presentation, and that is Mellit's Proposition 5.3, proved downstream as
`HJO.Sweep.braidRepRespects_mellit`. `HJO.Sweep.braidRepRespects_of_residual` reduces the
hypothesis to one clause of that proposition, and `HJO.Braid.monoidHom_ext` says
there is at most one such homomorphism, so the hypothesis is the only thing between this
definition and a bare `def`. -/
@[hjo "def_braid_rep"]
noncomputable def braidRep (q u r : L) (k : ℕ) (h : BraidRepRespects q u r k) :
    BraidMonoid k →* Module.End L (pieceSub L k) :=
  Con.lift _ (braidRepFree q u r k)
    (Con.conGen_le.2 fun x y hxy => (Con.ker_rel _).2 (h x y hxy))

/-- **The total-space shadow of the representation**, the one-total-space convention applied to
`π_k`. It exists only under `HJO.Sweep.BraidRepRespectsTotal`, which
`HJO.Sweep.braidRepRespectsTotal_two_false` refutes at `k = 2`; at `k = 1` it exists outright,
and that is the typing `HJO.Sweep.slopeOperator` is written in. -/
noncomputable def braidRepTotal (q u r : L) (k : ℕ) (h : BraidRepRespectsTotal q u r k) :
    BraidMonoid k →* Module.End L (Total L) :=
  Con.lift _ (braidRepFreeTotal q u r k)
    (Con.conGen_le.2 fun x y hxy => (Con.ker_rel _).2 (h x y hxy))

/-- The representation reads a word through the assignment it was built from. -/
@[simp]
theorem braidRep_apply (q u r : L) (k : ℕ) (h : BraidRepRespects q u r k)
    (x : FreeMonoid Letter) :
    braidRep q u r k h (toBraidMonoid k x) = braidRepFree q u r k x :=
  Con.lift_coe _ _

@[simp]
theorem braidRepTotal_apply (q u r : L) (k : ℕ) (h : BraidRepRespectsTotal q u r k)
    (x : FreeMonoid Letter) :
    braidRepTotal q u r k h (toBraidMonoid k x) = braidRepFreeTotal q u r k x :=
  Con.lift_coe _ _

/-- **The two layers agree**: where both exist, `π_k` on `V_k` is the restriction of its
total-space shadow. -/
theorem coe_braidRep (q u r : L) (k : ℕ) (h : BraidRepRespects q u r k)
    (h' : BraidRepRespectsTotal q u r k) (B : BraidMonoid k) (x : pieceSub L k) :
    (braidRep q u r k h B x : Total L) = braidRepTotal q u r k h' B x := by
  obtain ⟨w, rfl⟩ := toBraidMonoid_surjective k B
  rw [braidRep_apply, braidRepTotal_apply, braidRepFree_coe]

theorem braidRep_T (q u r : L) {k : ℕ} (h : BraidRepRespects q u r k) (i : ℕ) :
    braidRep q u r k h (braidGenT k i) = braidRepLetter q u r k (Letter.T i) := by
  rw [braidGenT, braidRep_apply, braidRepFree_of]

theorem braidRep_Tbar (q u r : L) {k : ℕ} (h : BraidRepRespects q u r k) (i : ℕ) :
    braidRep q u r k h (braidGenTinv k i) = braidRepLetter q u r k (Letter.Tbar i) := by
  rw [braidGenTinv, braidRep_apply, braidRepFree_of]

/-- The value of `π_k(T_i)` on `V_k`: `q^{-1/2}T_i`, read through the inclusion. -/
theorem coe_braidRep_T (q u r : L) {k i : ℕ} (h : BraidRepRespects q u r k) (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) (x : pieceSub L k) :
    (braidRep q u r k h (braidGenT k i) x : Total L) = r⁻¹ • braidEnd q i x := by
  rw [braidRep_T q u r h i, coe_braidRepLetter, braidRepLetterTotal_T q u r hi hik,
    LinearMap.smul_apply]

/-- The value of `π_k(T̄_i)` on `V_k`: `q^{1/2}T_i^{-1}`. -/
theorem coe_braidRep_Tbar (q u r : L) {k i : ℕ} (h : BraidRepRespects q u r k) (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) (x : pieceSub L k) :
    (braidRep q u r k h (braidGenTinv k i) x : Total L) = r • braidInvEnd q i x := by
  rw [braidRep_Tbar q u r h i, coe_braidRepLetter, braidRepLetterTotal_Tbar q u r hi hik,
    LinearMap.smul_apply]

theorem braidRepTotal_T (q u r : L) {k i : ℕ} (h : BraidRepRespectsTotal q u r k) (hi : 1 ≤ i)
    (hik : i + 1 ≤ k) : braidRepTotal q u r k h (braidGenT k i) = r⁻¹ • braidEnd q i := by
  rw [braidGenT, braidRepTotal_apply, braidRepFreeTotal_of, braidRepLetterTotal_T q u r hi hik]

theorem braidRepTotal_Tbar (q u r : L) {k i : ℕ} (h : BraidRepRespectsTotal q u r k)
    (hi : 1 ≤ i) (hik : i + 1 ≤ k) :
    braidRepTotal q u r k h (braidGenTinv k i) = r • braidInvEnd q i := by
  rw [braidGenTinv, braidRepTotal_apply, braidRepFreeTotal_of,
    braidRepLetterTotal_Tbar q u r hi hik]

/-- The generator `y_i` goes to `HJO.Sweep.yRep`, and at `i = 1` to
multiplication by `-y_1`. -/
theorem braidRep_y (q u r : L) {k : ℕ} (h : BraidRepRespects q u r k) (i : ℕ) :
    braidRep q u r k h (braidGenY k i) = yRep q u r k i := by
  rw [braidGenY, braidRep_apply, yRep]

/-- The generator `z_i` goes to `HJO.Sweep.zRep`, and at `i = 1` to
`(qu)^{-1}z_1`. -/
theorem braidRep_z (q u r : L) {k : ℕ} (h : BraidRepRespects q u r k) (i : ℕ) :
    braidRep q u r k h (braidGenZ k i) = zRep q u r k i := by
  rw [braidGenZ, braidRep_apply, zRep]

theorem braidRepTotal_y (q u r : L) {k : ℕ} (h : BraidRepRespectsTotal q u r k) (i : ℕ) :
    braidRepTotal q u r k h (braidGenY k i) = yRepTotal q u r k i := by
  rw [braidGenY, braidRepTotal_apply, yRepTotal]

theorem braidRepTotal_z (q u r : L) {k : ℕ} (h : BraidRepRespectsTotal q u r k) (i : ℕ) :
    braidRepTotal q u r k h (braidGenZ k i) = zRepTotal q u r k i := by
  rw [braidGenZ, braidRepTotal_apply, zRepTotal]

/-- **At rank `0` the representation is the unique homomorphism out of the trivial monoid**,
as it must be: at `k = 0` there are no generators and `π_0` sends the identity to the
identity of `V_0 ⊗_𝕜 𝕜[q^{1/2}]`. Here it is a theorem,
`𝔹_0^+(𝕋_0)` being trivial by `HJO.Braid.braidMonoid_zero`. -/
theorem braidRep_zero (q u r : L) (h : BraidRepRespects q u r 0) (x : BraidMonoid 0) :
    braidRep q u r 0 h x = 1 := by
  rw [braidMonoid_zero x, map_one]

theorem braidRepTotal_zero (q u r : L) (h : BraidRepRespectsTotal q u r 0) (x : BraidMonoid 0) :
    braidRepTotal q u r 0 h x = 1 := by
  rw [braidMonoid_zero x, map_one]

/-- **At rank `0` the hypothesis is free**: every letter is out of rank, so the assignment is
constantly the identity and every relation is satisfied. So `π_0` exists outright. -/
theorem braidRepRespectsTotal_zero (q u r : L) : BraidRepRespectsTotal q u r 0 := by
  intro x y hrel
  have hconst : ∀ w : FreeMonoid Letter, braidRepFreeTotal q u r 0 w = 1 := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => exact map_one _
    | of_mul c w ih =>
      rw [map_mul, ih, mul_one, braidRepFreeTotal_of,
        braidRepLetterTotal_of_not_inRank q u r (not_inRank_zero c)]
  rw [hconst x, hconst y]

theorem braidRepRespects_zero (q u r : L) : BraidRepRespects q u r 0 :=
  braidRepRespects_of_total q u r 0 (braidRepRespectsTotal_zero q u r)

/-! ### Rank one -/

/-- At rank one `π_1(y_1)` is multiplication by `-y_1`, the `y` letter of
`HJO.Sweep.slopeOperator`. -/
theorem coe_braidRep_one_y1 (q u r : L) (h : BraidRepRespects q u r 1) (x : pieceSub L 1) :
    (braidRep q u r 1 h (braidGenY 1 1) x : Total L) = -((auxVar 1 : Total L) * x) := by
  rw [braidRep_y, coe_yRep, yRepTotal_one q u r le_rfl, LinearMap.neg_apply,
    LinearMap.mulLeft_apply]

/-- At rank one `π_1(z_1)` is `(qu)^{-1}z_1`, the `z` letter of
`HJO.Sweep.slopeOperator`. -/
theorem coe_braidRep_one_z1 (q u r : L) (h : BraidRepRespects q u r 1) (x : pieceSub L 1) :
    (braidRep q u r 1 h (braidGenZ 1 1) x : Total L) = (q * u)⁻¹ • zop q u 1 1 x := by
  rw [braidRep_z, coe_zRep, zRepTotal_one q u r le_rfl, LinearMap.smul_apply]

theorem braidRepTotal_one_y1 (q u r : L) (h : BraidRepRespectsTotal q u r 1) :
    braidRepTotal q u r 1 h (braidGenY 1 1) = -LinearMap.mulLeft L (auxVar 1 : Total L) := by
  rw [braidRepTotal_y, yRepTotal_one q u r le_rfl]

theorem braidRepTotal_one_z1 (q u r : L) (h : BraidRepRespectsTotal q u r 1) :
    braidRepTotal q u r 1 h (braidGenZ 1 1) = (q * u)⁻¹ • zop q u 1 1 := by
  rw [braidRepTotal_z, zRepTotal_one q u r le_rfl]

/-- **The representation is the only homomorphism with these values**, which is what "induced
by the assignment on the generators" asserts. This is the uniqueness half of
`HJO.Sweep.braidRep_unique` — "so the homomorphism `π_k` exists and is unique" — the existence half
being `HJO.Sweep.braidRepRespects_mellit`. -/
@[hjo "lem_braid_rep_respects"]
theorem braidRep_unique (q u r : L) {k : ℕ} (h : BraidRepRespects q u r k)
    {f : BraidMonoid k →* Module.End L (pieceSub L k)}
    (hf : ∀ c : Letter, f (toBraidMonoid k (FreeMonoid.of c)) = braidRepLetter q u r k c) :
    f = braidRep q u r k h := by
  refine Braid.monoidHom_ext fun c => ?_
  rw [hf c, braidRep_apply, braidRepFree_of]

theorem braidRepTotal_unique (q u r : L) {k : ℕ} (h : BraidRepRespectsTotal q u r k)
    {f : BraidMonoid k →* Module.End L (Total L)}
    (hf : ∀ c : Letter,
      f (toBraidMonoid k (FreeMonoid.of c)) = braidRepLetterTotal q u r k c) :
    f = braidRepTotal q u r k h := by
  refine Braid.monoidHom_ext fun c => ?_
  rw [hf c, braidRepTotal_apply, braidRepFreeTotal_of]

end HJO.Sweep
