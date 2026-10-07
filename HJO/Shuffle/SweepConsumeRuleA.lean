/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepBoundaryConsume
public import HJO.Shuffle.SweepShiftConjugate
public meta import HJO.Attr

/-!
# Rule `A` consumes the staircase too — at an offset one lower than rule `C`'s

`HJO.Sweep.corner_stairWord_consume_of_mem_piece` absorbs an arriving staircase into the scalar
`q^m` at rule `C`. `HJO.Sweep.not_dplus_stairWord_consume` is read as saying that rule `A` cannot do
the same. **It does not say that.** It refutes

`d^♭_+{}^{(2)}(S_{0,1}v) = x·d^♭_+{}^{(1)}(v)`

— the staircase at offset `0` against the index pair `(2,1)` — and that is the pair the *corner*
consumes at, not the pair rule `A` consumes at. This file proves that rule `A` has its own consuming
identity, one offset higher, and that the vector-level hypothesis it needs is exactly the property
`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` isolates.

## Why the offsets differ, and it is one line of definitions

On its own graded piece the corner is the ascending word times the top variable, with **no
substitution**: `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` reads

`Δ^{(n+1)}(w) = -T_{[1,n]}(y_{n+1}w)` for `w ∈ V_{n+1}`.

The raising operator is the *same* word and the *same* variable, with the substitution in front
(`HJO.Sweep.dplus_apply`):

`d^♭_+{}^{(n)}(F) = -T_{[1,n]}(y_{n+1}τ_{n+1,n+1}(F))`.

So the single absorption mechanism — `HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`, which
eats `S_{c,m}` against `T_{[1,c+m]}y_{c+m+1}·` and lands on `T_{[1,c]}y_{c+1}·` — serves
`Δ^{(c+m+1)} ↦ Δ^{(c+1)}` and `d^♭_+{}^{(c+m)} ↦ d^♭_+{}^{(c)}`. **The index pair is shifted by
one, so the staircase offset the two rules can absorb is shifted by one as well.** Rule `C` at width
`k` absorbs the staircase of offset `k - 1`; rule `A` at width `k` absorbs the staircase of offset
`k`.

`HJO.Sweep.consume_offsets_differ_by_one` is that statement at one vector, with all four halves
machine-checked: at the index pair `(2,1)` and the vector `y_1`, rule `C` consumes the offset-`0`
staircase, rule `A` does **not** consume it at any scalar, rule `A` **does** consume the offset-`1`
staircase, and rule `B` consumes neither, at any offset.

## The vector-level hypothesis, and what it is

`HJO.Sweep.dplus_consume_of_qshift_eq` is the identity in full: no hypothesis on `q`, and the only
hypothesis is

`τ_{c+m+1,c+m+1}(F) = S_{c,m}(τ_{c+1,c+1}(H))`,

which for `F = S_{c,m}H` says that the staircase **intertwines the two substitutions** — the one at
the raised index with the one at the base index. That is not a commutation of operators: the two
substitutions read different variables, and `HJO.Sweep.qshift_braid` covers neither of the letters
involved. It is a condition on the vector, and the condition is *precisely* the one
`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` identifies — **the `q`-shift
must be invisible.**

* It holds on the `Λ`-free vectors, `HJO.Sweep.auxSubalg`, where every `τ` is the identity
  (`HJO.Sweep.dplus_stairWord_consume_of_mem_auxSubalg`) — in particular at the vacuum, at every
  offset and height (`HJO.Sweep.dplus_stairWord_consume_one`), and at `y_1`
  (`HJO.Sweep.dplus_stairWord_consume_X_zero` and
  `HJO.Sweep.dplus_stairWord_consume_X_zero_offset_one`).
* It **fails**, and so does the identity, at `F = Ce_1`:
  `HJO.Sweep.not_dplus_stairWord_consume_C_powerSum` refutes rule-`A` consumption at *its own*
  offset and index pair, for every scalar, with discrepancy `(q-1)^2y_1y_2` — the residue of
  `HJO.Sweep.dplus_apply_powerSum_not_mem_piece`. `Ce_1` is the same witness that refutes the
  operator reading of the append clause, and `(q-1)` divides the discrepancy for the same reason.

## What this leaves

The absorbing class is the `Λ`-free vectors, and **rule `B` leaves it**:
`HJO.Sweep.dminus_auxVar_pow` is `d^♭_-{}^{(k+1)}(y_{k+1}^m) = (-1)^me_m`, an element of `Λ`. So
the property cannot be carried through a layer that contains a type-`B` event, and at the first
`Λ`-generator it meets, rule `A`'s consumption is already false. Nothing here is a statement about
a rectangle: no `a`, no `b`, no `A` occurs, so none of it is confined to `a = 1` and all of it is
in force inside `1 < a < b`.

Rule `B` has no ascending word at all, and correspondingly no consuming identity at any offset:
`HJO.Sweep.not_dminus_stairWord_consume_offset` refutes every offset at the vector `y_1`, extending
`HJO.Sweep.not_dminus_stairWord_consume`, which is the offset-`0` case. `d^♭_-{}^{(n)}` reads `y_n`,
and a staircase strictly below `n` simply commutes out (`HJO.Sweep.dminus_stairWord`), leaving the
index where it was.

`HJO.Sweep.not_forall_mem_piece_exists_dplus_stairWord_consume` and its `d^♭_-` twin record that the
two refutations were already **vector-level** in the sense of
`HJO.Sweep.corner_stairWord_consume_of_mem_piece`: their witness `y_1` lies in `V_1`
(`HJO.Sweep.auxVar_mem_piece`), which is that theorem's hypothesis. So no hypothesis of the form
`v ∈ V_{c+1}` can rescue either rule at the corner's offset.

## References

This file builds on `HJO.Sweep.dplus`, `HJO.Sweep.dminus`, `HJO.Sweep.corner`,
`HJO.Sweep.stairWord`, `HJO.Sweep.qshift`, `HJO.Sweep.braid_auxVar_succ_mul_braid`. Transcribing A.
Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### The raising operator as the corner's word with a substitution in front -/

omit [Algebra ℚ L] in
/-- **`d^♭_+{}^{(k)} = -T_{[1,k]}∘y_{k+1}·∘τ_{k+1,k+1}`**, `HJO.Sweep.dplus_apply` with the
ascending train named as the word `HJO.Sweep.cmAscWord` that the absorption relation
`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` is stated in.

Read against `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul`, which is `-T_{[1,k]}∘y_{k+1}·` with no
substitution and is the corner at index `k + 1`: the same word and the same variable serve rule `A`
at width `k` and rule `C` at width `k + 1`. That one-unit offset is the whole content of this
file. -/
theorem dplus_eq_cmAscWord' (q : L) (k : ℕ) (F : Total L) :
    dplus q k F = -cmAscWord q 1 k ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) :=
  dplus_apply q k F

/-! ### THE RULE-`A` CONSUMING IDENTITY -/

omit [Algebra ℚ L] in
/-- **RULE `A` CONSUMES THE STAIRCASE, at the index pair one below the corner's.** For every `c` and
`m`, and every pair `F`, `H` with

`τ_{c+m+1,c+m+1}(F) = S_{c,m}(τ_{c+1,c+1}(H))`,

one has `d^♭_+{}^{(c+m)}(F) = q^m·d^♭_+{}^{(c)}(H)`. **No hypothesis on `q`.**

The mechanism is the one relation `HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord`,
which is also the whole content of `HJO.Sweep.corner_stairWord_consume`: the staircase is eaten
letter by letter against the ascending word of the closed form, and the operator comes out at an
index lowered by exactly the staircase's height. What differs from the corner is *where* that word
sits. `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` puts `T_{[1,n]}y_{n+1}·` in front of
`Δ^{(n+1)}`; `HJO.Sweep.dplus_eq_cmAscWord'` puts the same thing in front of `d^♭_+{}^{(n)}`. Hence
the index pair `(c+m, c)` here against the corner's `(c+m+1, c+1)`.

The hypothesis is the *only* thing asked, and it is a statement about the vector, not the word: it
says the staircase carries the substitution at the raised index to the substitution at the base
index. The two substitutions read different variables (`y_{c+m+1}` and `y_{c+1}`), so this is not
`HJO.Sweep.qshift_braid`, which needs the substitution's variable to miss both letters of the braid
and misses neither here. -/
theorem dplus_consume_of_qshift_eq (q : L) (c m : ℕ) {F H : Total L}
    (h : qshift q (c + m + 1) F = stairWord q 1 c m (qshift q (c + 1) H)) :
    dplus q (c + m) F = q ^ m • dplus q c H := by
  have hword := congrArg (fun T : Module.End L (Total L) => T (qshift q (c + 1) H))
    (cmAscWord_mul_mulLeft_auxVar_mul_stairWord q c m)
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply] at hword
  rw [dplus_eq_cmAscWord' q (c + m) F, h, hword, dplus_eq_cmAscWord' q c H, smul_neg]

omit [Algebra ℚ L] in
/-- **`HJO.Sweep.dplus_consume_of_qshift_eq` at `F = S_{c,m}H`**, where the hypothesis becomes the
intertwining

`τ_{c+m+1,c+m+1}∘S_{c,m} = S_{c,m}∘τ_{c+1,c+1}` at `H`,

i.e. **the `q`-shift is invisible to the staircase at `H`**. This is the property
`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` isolates as the reason the
append identity holds at the vacuum and nowhere else, appearing here as the exact hypothesis of the
rule-`A` absorption. -/
theorem dplus_stairWord_consume_of_qshift_comm (q : L) (c m : ℕ) {H : Total L}
    (h : qshift q (c + m + 1) (stairWord q 1 c m H) = stairWord q 1 c m (qshift q (c + 1) H)) :
    dplus q (c + m) (stairWord q 1 c m H) = q ^ m • dplus q c H :=
  dplus_consume_of_qshift_eq q c m h

omit [Algebra ℚ L] in
/-- **RULE `A` CONSUMES THE STAIRCASE ON EVERY `Λ`-FREE VECTOR.** For `H` and `S_{c,m}H` both in
`HJO.Sweep.auxSubalg` — the `𝕜`-subalgebra generated by the auxiliary variables — every
substitution `τ_{k,i}` fixes them (`HJO.Sweep.qshift_of_mem_auxSubalg`), so the intertwining is
trivial and

`d^♭_+{}^{(c+m)}(S_{c,m}H) = q^m·d^♭_+{}^{(c)}(H)`.

No hypothesis on `q`. The second membership is a side condition on the instance, not on the
mathematics: the braid operators are built from a variable interchange and a divided difference in
the variables, both of which keep a `𝕜`-polynomial in the `y` a `𝕜`-polynomial in the `y`; it is
discharged by computation at each use below.

The class of `Λ`-free vectors is where this identity lives, and `HJO.Sweep.dminus_auxVar_pow` is
where it is lost: `d^♭_-{}^{(k+1)}(y_{k+1}^m) = (-1)^me_m` puts a generator of `Λ` into the vector,
and `HJO.Sweep.not_dplus_stairWord_consume_C_powerSum` shows the identity is false at the first such
generator. -/
theorem dplus_stairWord_consume_of_mem_auxSubalg (q : L) (c m : ℕ) {H : Total L}
    (hH : H ∈ auxSubalg L) (hS : stairWord q 1 c m H ∈ auxSubalg L) :
    dplus q (c + m) (stairWord q 1 c m H) = q ^ m • dplus q c H := by
  refine dplus_stairWord_consume_of_qshift_comm q c m ?_
  rw [qshift_of_mem_auxSubalg q _ hS, qshift_of_mem_auxSubalg q _ hH]

/-! ### The vacuum: every offset, every height -/

omit [Algebra ℚ L] in
/-- **The staircase at `δ = 1` fixes the vacuum**, at every offset and height. Each block of
`HJO.Sweep.stairWord` at `δ = 1` is the single letter `T_{c+m+1}`
(`HJO.Sweep.cmAscWord_self`), and a braid letter fixes anything its interchange fixes
(`HJO.Sweep.braid_of_swapAux_eq`). -/
theorem stairWord_one_apply_one (q : L) (c : ℕ) :
    ∀ m : ℕ, stairWord q 1 c m (1 : Total L) = 1
  | 0 => by simp
  | m + 1 => by
      rw [stairWord_succ_apply, stairWord_one_apply_one q c m, cmAscWord_self]
      exact braid_of_swapAux_eq q (map_one _)

omit [Algebra ℚ L] in
/-- **Rule `A` consumes the staircase at the vacuum, at every offset and height**, with the same
scalar `q^m` the corner absorbs it into. Both substitutions fix `1`, being algebra maps, so the
intertwining of `HJO.Sweep.dplus_stairWord_consume_of_qshift_comm` is immediate. Read with
`HJO.Sweep.not_dplus_stairWord_consume_C_powerSum`: the vacuum is inside the absorbing class and
`Ce_1` is outside it. -/
theorem dplus_stairWord_consume_one (q : L) (c m : ℕ) :
    dplus q (c + m) (stairWord q 1 c m (1 : Total L)) = q ^ m • dplus q c (1 : Total L) := by
  refine dplus_stairWord_consume_of_qshift_comm q c m ?_
  rw [stairWord_one_apply_one, map_one, map_one, stairWord_one_apply_one]

/-! ### The two instances at the point where the refutation lives -/

omit [Algebra ℚ L] in
/-- `T_1y_1 = y_2 + (1-q)y_1` is `Λ`-free, the side condition of
`HJO.Sweep.dplus_stairWord_consume_of_mem_auxSubalg` discharged at the smallest witness. -/
theorem braid_one_X_zero_mem_auxSubalg (q : L) :
    braid q 1 (MvPolynomial.X 0 : Total L) ∈ auxSubalg L := by
  rw [braid_one_X_zero]
  refine add_mem (auxVar_mem_auxSubalg (L := L) 2) (mul_mem ?_ (auxVar_mem_auxSubalg (L := L) 1))
  rw [scal_eq_algebraMap]
  exact (auxSubalg L).algebraMap_mem _

omit [Algebra ℚ L] in
/-- **Rule `A` consumes the offset-`0` staircase at the index pair `(1,0)`**, at the very vector
`y_1` where `HJO.Sweep.not_dplus_stairWord_consume` refutes it at the pair `(2,1)`:

`d^♭_+{}^{(1)}(T_1y_1) = q·d^♭_+{}^{(0)}(y_1)`.

Both sides are `-qy_1^2`. So that refutation is not about rule `A`'s inability to eat a
staircase; it is about the index pair it was asked at. -/
theorem dplus_stairWord_consume_X_zero (q : L) :
    dplus q 1 (stairWord q 1 0 1 (MvPolynomial.X 0 : Total L))
      = q • dplus q 0 (MvPolynomial.X 0 : Total L) := by
  have hS : stairWord q 1 0 1 (MvPolynomial.X 0 : Total L) ∈ auxSubalg L := by
    rw [stairWord_one, Nat.zero_add, cmAscWord_self]
    exact braid_one_X_zero_mem_auxSubalg q
  have h := dplus_stairWord_consume_of_mem_auxSubalg q 0 1
    (auxVar_mem_auxSubalg (L := L) 1) hS
  rwa [Nat.zero_add, pow_one] at h

omit [Algebra ℚ L] in
/-- **`T_{c+2}` fixes `y_1`**: its interchange swaps `y_{c+1}` and `y_{c+2}`, neither of which is
`y_1`. -/
theorem braid_succ_succ_X_zero (q : L) (c : ℕ) :
    braid q (c + 2) (MvPolynomial.X 0 : Total L) = MvPolynomial.X 0 := by
  refine braid_of_swapAux_eq q ?_
  rw [swapAux_X, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

omit [Algebra ℚ L] in
/-- **Rule `A` consumes the offset-`1` staircase at the index pair `(2,1)` — the pair the
refutation uses.** At the same vector `y_1`,

`d^♭_+{}^{(2)}(T_2y_1) = q·d^♭_+{}^{(1)}(y_1)`,

both sides being `-qy_1y_2`, while `HJO.Sweep.not_dplus_stairWord_consume` shows
`d^♭_+{}^{(2)}(T_1y_1) = x·d^♭_+{}^{(1)}(y_1)` is false for every `x`. Same rule, same widths, same
vector: **only the offset of the arriving staircase differs**, `1` here against `0` there. -/
theorem dplus_stairWord_consume_X_zero_offset_one (q : L) :
    dplus q 2 (stairWord q 1 1 1 (MvPolynomial.X 0 : Total L))
      = q • dplus q 1 (MvPolynomial.X 0 : Total L) := by
  have hfix : stairWord q 1 1 1 (MvPolynomial.X 0 : Total L) = MvPolynomial.X 0 := by
    rw [stairWord_one, cmAscWord_self]
    exact braid_succ_succ_X_zero q 0
  have h := dplus_stairWord_consume_of_mem_auxSubalg q 1 1
    (H := (MvPolynomial.X 0 : Total L)) (auxVar_mem_auxSubalg (L := L) 1)
    (by rw [hfix]; exact auxVar_mem_auxSubalg (L := L) 1)
  rwa [pow_one] at h

/-! ### THE WALL, at rule `A`'s own offset: the `q`-shift becomes visible at `Λ` -/

omit [Algebra ℚ L] in
/-- A braid letter fixes a symmetric function: the interchange fixes it and the divided difference
kills it. `HJO.Sweep.braid_C_mul` at `F = 1`. -/
theorem braid_apply_C (q : L) (i : ℕ) (c : Sym.Lambda L) :
    braid q i (MvPolynomial.C c : Total L) = MvPolynomial.C c := by
  have h := braid_C_mul q i c (1 : Total L)
  rwa [mul_one, braid_of_swapAux_eq q (map_one _), mul_one] at h

/-- **RULE `A` DOES NOT CONSUME THE STAIRCASE AT `Ce_1`, at its own offset and its own index pair,
for every scalar.** For every `q ≠ 1` and every `x`,

`d^♭_+{}^{(1)}(S_{0,1}Ce_1) ≠ x·d^♭_+{}^{(0)}(Ce_1)`.

The staircase does not even move the vector — a braid letter fixes a symmetric function
(`HJO.Sweep.braid_apply_C`) — so this is a statement about the two indices alone: `d^♭_+{}^{(0)}`
carries `V_0` into `V_1` (`HJO.Sweep.dplus_mem_piece`) and `d^♭_+{}^{(1)}` does not
(`HJO.Sweep.dplus_apply_powerSum_not_mem_piece`), the residue being `(q-1)^2y_1y_2`. No scalar
multiple of an element of `V_1` leaves `V_1`.

**This is the wall, and it is the same witness and the same divisibility as the operator
refutation.** `Ce_1` is what
`HJO.Mellit.not_forall_sum_partialSweepWord_eq_sum_stageTotal_one_two` evaluates at, `(q-1)` divides
both discrepancies, and the reason is one reason: the substitution `τ` adds a multiple of an
auxiliary variable to every power sum, so it is invisible on a scalar and visible on every other
element of `Λ`. The intertwining hypothesis of
`HJO.Sweep.dplus_stairWord_consume_of_qshift_comm` fails here for the same cause — at `H = Ce_1` it
reduces to `S_{c,m}(y_{c+1}) = y_{c+m+1}`, and `T_{c+1}y_{c+1} = y_{c+2} + (1-q)y_{c+1}` already
refutes it.

So the absorbing class of rule `A` is bounded away from `Λ`, and `HJO.Sweep.dminus_auxVar_pow` says
rule `B` puts the vector into `Λ`. A vector-level hypothesis strong enough for rule `A` therefore
cannot survive a type-`B` event. -/
theorem not_dplus_stairWord_consume_C_powerSum (hq : q ≠ 1) (x : L) :
    dplus q 1 (stairWord q 1 0 1 (MvPolynomial.C (Sym.powerSum L 1) : Total L))
      ≠ x • dplus q 0 (MvPolynomial.C (Sym.powerSum L 1) : Total L) := by
  have hfix : stairWord q 1 0 1 (MvPolynomial.C (Sym.powerSum L 1) : Total L)
      = MvPolynomial.C (Sym.powerSum L 1) := by
    rw [stairWord_one, Nat.zero_add, cmAscWord_self]
    exact braid_apply_C q 1 _
  have h0 : (MvPolynomial.C (Sym.powerSum L 1) : Total L) ∈ piece L 0 := by
    rw [MvPolynomial.C_eq_algebraMap]
    exact (piece L 0).algebraMap_mem _
  rw [hfix]
  intro h
  refine dplus_apply_powerSum_not_mem_piece hq ?_
  rw [h, smul_eq_scal_mul]
  exact mul_mem (scal_mem_piece x 1) (dplus_mem_piece q 0 h0)

/-! ### The two refutations were already vector-level -/

omit [Algebra ℚ L] in
/-- **No hypothesis of the corner's shape rescues rule `A` at the corner's offset.** The
vector-level hypothesis of `HJO.Sweep.corner_stairWord_consume_of_mem_piece` is `v ∈ V_{c+1}`; its
witness `y_1` lies in `V_1` (`HJO.Sweep.auxVar_mem_piece`), so
`HJO.Sweep.not_dplus_stairWord_consume` refutes the rule-`A` statement *with that hypothesis in
place*, and with the absorbing scalar existentially quantified rather than fixed. The two
statements are the same statement: writing the quantifiers out, the refutation is
`∀ q ≠ 0, ∀ x, ¬(… y_1 …)` at a vector satisfying the hypothesis, which contradicts
`∀ v ∈ V_1, ∃ x, …`.

What rescues rule `A` is not a stronger hypothesis on the vector but the correct offset:
`HJO.Sweep.dplus_stairWord_consume_X_zero_offset_one`. -/
theorem not_forall_mem_piece_exists_dplus_stairWord_consume (hq : q ≠ 0) :
    ¬ ∀ v ∈ piece L 1, ∃ x : L,
        dplus q 2 (stairWord q 1 0 1 v) = x • dplus q 1 v := by
  intro h
  obtain ⟨x, hx⟩ := h (MvPolynomial.X 0) (auxVar_mem_piece (i := 1) le_rfl le_rfl)
  exact not_dplus_stairWord_consume hq x hx

/-- **The same for rule `B`**, from `HJO.Sweep.not_dminus_stairWord_consume`. -/
theorem not_forall_mem_piece_exists_dminus_stairWord_consume (hq : q ≠ 1) :
    ¬ ∀ v ∈ piece L 1, ∃ x : L,
        dminus q 2 (stairWord q 1 0 1 v) = x • dminus q 1 v := by
  intro h
  obtain ⟨x, hx⟩ := h (MvPolynomial.X 0) (auxVar_mem_piece (i := 1) le_rfl le_rfl)
  exact not_dminus_stairWord_consume hq x hx

/-! ### Rule `B`: no offset repairs it -/

/-- **RULE `B` CONSUMES NO STAIRCASE, AT ANY OFFSET.** For every `q ≠ 1`, every offset `c` and every
scalar `x`,

`d^♭_-{}^{(2)}(S_{c,1}y_1) ≠ x·d^♭_-{}^{(1)}(y_1)`.

`HJO.Sweep.not_dminus_stairWord_consume` is the case `c = 0`, where the arriving letter `T_1` moves
`y_1` and the left side keeps a monomial in it. At every higher offset the letter `T_{c+2}` does not
touch `y_1` at all (`HJO.Sweep.braid_succ_succ_X_zero`), so the left side is
`d^♭_-{}^{(2)}(y_1) = y_1` while the right side is a multiple of `e_1` — an element of `Λ`, which
`y_1` is not.

The reason is structural and is why no offset can help: `d^♭_-` is a coefficient extraction with
**no ascending word**, so there is nothing for a staircase to be eaten against, and the mechanism
`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` — the whole content of the rule-`A` and
rule-`C` absorptions — has no rule-`B` analogue. What rule `B` does have is commutation,
`HJO.Sweep.dminus_stairWord`, valid for `c + m + δ + 1 ≤ n`; that leaves the index where it was and
so cannot lower a raised width. -/
theorem not_dminus_stairWord_consume_offset (hq : q ≠ 1) (c : ℕ) (x : L) :
    dminus q 2 (stairWord q 1 c 1 (MvPolynomial.X 0 : Total L))
      ≠ x • dminus q 1 (MvPolynomial.X 0 : Total L) := by
  match c with
  | 0 => exact not_dminus_stairWord_consume hq x
  | (c + 1) =>
    rw [stairWord_one, cmAscWord_self, show c + 1 + 1 = c + 2 from rfl]
    change dminus q 2 (braid q (c + 2) (MvPolynomial.X 0 : Total L)) ≠ _
    rw [braid_succ_succ_X_zero, dminus_two_X_zero q, dminus_one_X_zero]
    intro h
    have hne : ¬ ((0 : ℕ →₀ ℕ) = Finsupp.single 0 1) := by
      intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 0) hh) (by simp)
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
    rw [show (MvPolynomial.X 0 : Total L)
          = MvPolynomial.monomial (Finsupp.single 0 1) 1 from
        (monomial_single_one_eq_X (L := L) 0).symm] at hc
    simp only [MvPolynomial.coeff_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_neg,
      MvPolynomial.coeff_C, hne, ite_true, ite_false, neg_zero, smul_zero] at hc
    exact one_ne_zero hc

/-! ### The four halves in one statement -/

/-- **THE OFFSET OF AN ABSORBABLE STAIRCASE IS DECIDED BY THE RULE, AND RULES `A` AND `C`
DISAGREE BY ONE.** At the index pair `(2,1)` and the vector `y_1`, for every `q ≠ 0` and `q ≠ 1`:

1. rule `C` consumes the offset-`0` staircase, `Δ^{(2)}(T_1y_1) = qΔ^{(1)}(y_1)`;
2. rule `A` does **not** consume it, at any scalar;
3. rule `A` consumes the offset-`1` staircase, `d^♭_+{}^{(2)}(T_2y_1) = qd^♭_+{}^{(1)}(y_1)`;
4. rule `B` consumes neither, at any offset and any scalar.

Clauses 1 and 3 are the same absorption mechanism read through two closed forms whose ascending
words sit at indices differing by one: `HJO.Sweep.corner_eq_neg_cmAscWord_auxVar_mul` at `n + 1`
against `HJO.Sweep.dplus_eq_cmAscWord'` at `n`. Clause 2 is
`HJO.Sweep.not_dplus_stairWord_consume`, here identified as the refutation of rule `A` **at rule
`C`'s offset**. Clause 4 is `HJO.Sweep.not_dminus_stairWord_consume_offset`.

For the round boundary this replaces one question by a sharper one. The arriving staircase has a
single offset `c`; a type-`C` point of width `k` absorbs it only if `c = k - 1`, a type-`A` point of
width `k` only if `c = k`, and a type-`B` point never. So a layer can absorb its arriving staircase
only if its type-`A` points sit exactly one width below its type-`C` points and it has no type-`B`
point at all — an arithmetic condition on the two rectangles, of the same kind as the one
`HJO.Sweep.corner_stairWord_consume`'s module docstring already names as the remaining obstruction,
and now with a definite numerical content per rule. -/
theorem consume_offsets_differ_by_one (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    corner q 2 (stairWord q 1 0 1 (MvPolynomial.X 0 : Total L))
        = q • corner q 1 (MvPolynomial.X 0 : Total L)
      ∧ (∀ x : L, dplus q 2 (stairWord q 1 0 1 (MvPolynomial.X 0 : Total L))
          ≠ x • dplus q 1 (MvPolynomial.X 0 : Total L))
      ∧ dplus q 2 (stairWord q 1 1 1 (MvPolynomial.X 0 : Total L))
          = q • dplus q 1 (MvPolynomial.X 0 : Total L)
      ∧ (∀ (c : ℕ) (x : L), dminus q 2 (stairWord q 1 c 1 (MvPolynomial.X 0 : Total L))
          ≠ x • dminus q 1 (MvPolynomial.X 0 : Total L)) := by
  refine ⟨?_, fun x => not_dplus_stairWord_consume hq0 x,
    dplus_stairWord_consume_X_zero_offset_one q,
    fun c x => not_dminus_stairWord_consume_offset hq1 c x⟩
  have h := corner_stairWord_consume_of_mem_piece hq0 hq1 0 1
    (v := (MvPolynomial.X 0 : Total L)) (auxVar_mem_piece (i := 1) le_rfl le_rfl)
  rwa [Nat.zero_add, pow_one] at h

end HJO.Sweep

end
