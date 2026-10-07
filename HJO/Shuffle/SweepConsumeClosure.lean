/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepConsumeRuleA
public import HJO.Shuffle.SweepBoundaryWidthSharp
public meta import HJO.Attr

/-!
# The consumption route is closed: no class carries it, and the shift it needs is `δ = 1`

`HJO.Sweep.consume_offsets_differ_by_one` establishes that rules `A` and `C` absorb an arriving
staircase at offsets differing by one, and that rule `B` absorbs none. Two questions were left, and
this file answers both **negatively**, which closes the route.

## The absorbing class cannot be closed under the sweep

The absorbing class of rule `A` is bounded away from `Λ`
(`HJO.Sweep.not_dplus_stairWord_consume_C_powerSum`) and rule `B` puts `Λ` into the vector
(`HJO.Sweep.dminus_auxVar_pow`). This file makes that into a theorem about *every* candidate class,
with no linearity, no convexity and no closure under negation assumed:

`HJO.Sweep.not_exists_consuming_class` — **there is no set of vectors containing the vacuum, closed
under rule `A` and rule `B`, on which rule `A`'s consumption holds at offset `0` and height `1`.**

The proof is two events long. `HJO.Sweep.dminus_dplus_vacuum` computes

`d^♭_-{}^{(1)}(d^♭_+{}^{(0)}(1)) = Ce_1 = Cp_1`,

so **the wall is reached from the vacuum by one type-`A` event at width `0` followed by one type-`B`
event at width `1`** — the shortest event sequence a layer can have. No hypothesis of closure under
rule `C` is used, so the statement covers a fortiori every class closed under all three rules
(`HJO.Sweep.not_exists_consuming_class_three_rules`). The consumption asked of the class is the
single instance `(c, m) = (0, 1)`, which is the offset and height the round-boundary failure
`HJO.Mellit.not_tailRoundWord_stairWord_bound` actually presents; asking it at every `(c, m)` only
weakens the theorem.

This is why the vacuum result `HJO.Sweep.dplus_stairWord_consume_one` is no evidence: the two
vectors the vacuum reaches in two steps already leave the class.

## The absorption is a one-letter braid sandwich, so it lives only at `δ = 1`

`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` is stated at `δ = 1`, and that is not a
choice of generality. The mechanism is `HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd`,
the single relation `T_iy_{i+1}T_i = qy_i`, which eats **one** letter. A block of the staircase at
shift `δ` is the ascending word `T_{[c+i+1,c+i+δ]}`, of `δ` letters, and the sandwich reaches only
its lowest letter. `HJO.Sweep.cmAscWord_mulLeft_auxVar_stairWord_shift` computes what is left at
height `1`:

`T_{[1,c+1]}·y_{c+2}·S^δ_{c,1} = q·(T_{[1,c]}·y_{c+1}·T_{[c+2,c+δ]})`,

with the **residual ascending word `T_{[c+2,c+δ]}`** standing where the `δ = 1` identity has nothing
(`HJO.Sweep.cmAscWord_residual_one`). And the residual cannot be dropped:
`HJO.Sweep.not_dplus_stairWord_consume_shift_two` refutes rule `A`'s consumption at `δ = 2`, for
every scalar, at the `Λ`-free vector `y_2` — so the failure is **not** the `Λ` obstruction above but
a second, independent one, living entirely inside the absorbing class.

## And the geometry supplies `δ ≥ 2` inside `1 < a`

`HJO.Paths.tailLiveSteps` is a window `a` levels wide (`HJO.Paths.mem_tailLiveSteps_iff_Ioc`), so
`δ_e = #(tailLiveSteps w e)` exceeds `1` as soon as two of the tail's north steps fall in one
window, which at `a ≥ 2` is the rule rather than the exception.
`HJO.Mellit.not_tailRoundWord_stairWord_bound_shift_two` exhibits it on the smallest rectangle in
range, `(a, b) = (2, 3)` with `N = A = 1`: the base `HJO.Mellit.baseTwoThreeB` and the tail
`HJO.Mellit.tailTwoThreeA` give a staircase of shift `2` and height `1` emitted at round `2` and
arriving at offset `0` at the tail layer of round `1`, which is the single point `(1,2)` — a
**type-`B`** event read at index `3`, where passing needs `4`. Rule `B` passes nothing at that width
and absorbs nothing — at any offset at shift `1`
(`HJO.Sweep.not_dminus_stairWord_consume_offset`) and at offset `0` at shift `2`
(`HJO.Sweep.not_dminus_stairWord_consume_shift_two`), which is the instance this witness presents —
and at `δ = 2` neither of the other two rules has an absorption to offer either.

Everything here is at `a = 2`, inside `1 < a < b`, and no genericity in `q` or `u` is used beyond
`q ≠ 0` and `q ≠ 1`.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections
4 and 6.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L}

/-! ### Two events from the vacuum to the wall -/

/-- **The vacuum reaches `Cp_1` in two events, one of type `A` and one of type `B`.**
`HJO.Sweep.dplus_zero_one` is `d^♭_+{}^{(0)}(1) = -y_1` and `HJO.Sweep.dminus_one_X_zero` is
`d^♭_-{}^{(1)}(y_1) = -Ce_1`, so the two signs cancel and no closure under negation is needed to
get from the vacuum to the vector at which rule `A`'s consumption is false
(`HJO.Sweep.not_dplus_stairWord_consume_C_powerSum`).

Read against `HJO.Paths.card_tailLiveSteps_succ_add_card_roundEvents_A`: a type-`A` event raises the
graded index and a type-`B` event lowers it, so this pair is the shortest excursion a layer can make
and return from, and it already leaves the absorbing class. -/
theorem dminus_dplus_vacuum (q : L) :
    dminus q 1 (dplus q 0 (1 : Total L)) = MvPolynomial.C (Sym.powerSum L 1) := by
  rw [dplus_zero_one, map_neg, dminus_one_X_zero, neg_neg, Sym.elemSymm_one_eq_powerSum]

/-! ### THERE IS NO CONSUMING CLASS -/

/-- **NO CLASS OF VECTORS CLOSED UNDER RULES `A` AND `B` CARRIES RULE `A`'S CONSUMPTION.** For every
`q ≠ 1` there is no set `S` of vectors with

* `1 ∈ S`,
* `d^♭_+{}^{(n)}(S) ⊆ S` for every `n`,
* `d^♭_-{}^{(n)}(S) ⊆ S` for every `n`,
* `d^♭_+{}^{(1)}(S_{0,1}v) = q·d^♭_+{}^{(0)}(v)` for every `v ∈ S`.

`S` is an arbitrary `Set`: no linearity, no closure under scalars or negation, no membership in a
graded piece. The hypothesis is therefore as weak as the question allows, and the conclusion is that
the absorbing class of `HJO.Sweep.dplus_stairWord_consume_of_mem_auxSubalg` — the `Λ`-free vectors —
has no closed enlargement at all.

The proof is `HJO.Sweep.dminus_dplus_vacuum` followed by
`HJO.Sweep.not_dplus_stairWord_consume_C_powerSum`: the vacuum is forced into `S`, two applications
of the closure hypotheses put `Cp_1` into `S`, and the consumption hypothesis at `Cp_1` is false.

Nothing here is a statement about a rectangle — no `a`, no `b`, no `A` occurs — so it holds inside
`1 < a < b` as it stands. -/
theorem not_exists_consuming_class (hq : q ≠ 1) :
    ¬ ∃ S : Set (Total L), (1 : Total L) ∈ S
      ∧ (∀ (n : ℕ) (v : Total L), v ∈ S → dplus q n v ∈ S)
      ∧ (∀ (n : ℕ) (v : Total L), v ∈ S → dminus q n v ∈ S)
      ∧ ∀ v ∈ S, dplus q 1 (stairWord q 1 0 1 v) = q • dplus q 0 v := by
  rintro ⟨S, h1, hA, hB, hcons⟩
  have hmem : (MvPolynomial.C (Sym.powerSum L 1) : Total L) ∈ S := by
    rw [← dminus_dplus_vacuum q]
    exact hB 1 _ (hA 0 _ h1)
  exact not_dplus_stairWord_consume_C_powerSum hq q (hcons _ hmem)

/-- **The same with closure under rule `C` and consumption at every offset and height.** This is the
question "is there any class of vectors closed under all three rules on which consumption holds at
the required offsets?" verbatim, and the answer is no. It is *weaker* than
`HJO.Sweep.not_exists_consuming_class`, which asks neither the rule-`C` closure nor any instance of
the consumption beyond `(c, m) = (0, 1)`. -/
theorem not_exists_consuming_class_three_rules (hq : q ≠ 1) :
    ¬ ∃ S : Set (Total L), (1 : Total L) ∈ S
      ∧ (∀ (n : ℕ) (v : Total L), v ∈ S → dplus q n v ∈ S)
      ∧ (∀ (n : ℕ) (v : Total L), v ∈ S → dminus q n v ∈ S)
      ∧ (∀ (n : ℕ) (v : Total L), v ∈ S → corner q n v ∈ S)
      ∧ ∀ (c m : ℕ), ∀ v ∈ S, dplus q (c + m) (stairWord q 1 c m v) = q ^ m • dplus q c v := by
  rintro ⟨S, h1, hA, hB, _, hcons⟩
  refine not_exists_consuming_class hq ⟨S, h1, hA, hB, fun v hv => ?_⟩
  have h := hcons 0 1 v hv
  rwa [Nat.zero_add, pow_one] at h

/-! ### THE SHIFT: the sandwich eats one letter, and a residual word is left -/

omit [Algebra ℚ L] in
/-- **THE ABSORPTION AT SHIFT `δ` LEAVES THE RESIDUAL ASCENDING WORD `T_{[c+2,c+δ]}`.** At height
`1`, for every `δ ≥ 1`,

`T_{[1,c+1]}·y_{c+2}·S^δ_{c,1} = q·(T_{[1,c]}·y_{c+1}·T_{[c+2,c+δ]})`.

`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` is the case `δ = 1`, where the residual is
the empty word (`HJO.Sweep.cmAscWord_residual_one`). For `δ ≥ 2` it is not, and the whole reason is
visible in the proof: the mechanism is
`HJO.Sweep.braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd`, the relation `T_iy_{i+1}T_i = qy_i`,
which is a sandwich around **one** letter. The staircase's block at shift `δ` is the ascending word
`T_{[c+1,c+δ]}` of `δ` letters (`HJO.Sweep.stairWord_one`), the sandwich reaches its lowest letter
`T_{c+1}`, and `HJO.Sweep.cmAscWord_split` peels that letter off and leaves the rest standing.

No hypothesis on `q`. -/
@[hjo "lem_sweep_stair_absorb_residual"]
theorem cmAscWord_mulLeft_auxVar_stairWord_shift (q : L) (c : ℕ) {δ : ℕ} (hδ : 1 ≤ δ) :
    cmAscWord q 1 (c + 1) * LinearMap.mulLeft L (auxVar (c + 2) : Total L) * stairWord q δ c 1
      = q • (cmAscWord q 1 c * LinearMap.mulLeft L (auxVar (c + 1) : Total L)
          * cmAscWord q (c + 2) (c + δ)) := by
  have hstair : stairWord q δ c 1 = braidEnd q (c + 1) * cmAscWord q (c + 2) (c + δ) := by
    rw [stairWord_one, cmAscWord_split q (a := c + 1) (b := c + δ) (c := c + 1) (by omega)
      (by omega), cmAscWord_self]
  have htrain : cmAscWord q 1 (c + 1) = cmAscWord q 1 c * braidEnd q (c + 1) := by
    rw [cmAscWord_split q (a := 1) (b := c + 1) (c := c) (by omega) (by omega), cmAscWord_self]
  have hsand : braidEnd q (c + 1) * LinearMap.mulLeft L (auxVar (c + 2) : Total L)
      * braidEnd q (c + 1) = q • LinearMap.mulLeft L (auxVar (c + 1) : Total L) := by
    have h := braidEnd_mul_mulLeft_auxVar_succ_mul_braidEnd q (i := c + 1) (by omega)
    rwa [show c + 1 + 1 = c + 2 from rfl] at h
  calc cmAscWord q 1 (c + 1) * LinearMap.mulLeft L (auxVar (c + 2) : Total L) * stairWord q δ c 1
      = cmAscWord q 1 c * (braidEnd q (c + 1) * LinearMap.mulLeft L (auxVar (c + 2) : Total L)
          * braidEnd q (c + 1)) * cmAscWord q (c + 2) (c + δ) := by
        rw [htrain, hstair]; noncomm_ring
    _ = cmAscWord q 1 c * (q • LinearMap.mulLeft L (auxVar (c + 1) : Total L))
          * cmAscWord q (c + 2) (c + δ) := by rw [hsand]
    _ = q • (cmAscWord q 1 c * LinearMap.mulLeft L (auxVar (c + 1) : Total L)
          * cmAscWord q (c + 2) (c + δ)) := by
        rw [mul_smul_comm, smul_mul_assoc]

omit [Algebra ℚ L] in
/-- **At `δ = 1` the residual word is empty**, which is why
`HJO.Sweep.cmAscWord_mul_mulLeft_auxVar_mul_stairWord` is an absorption and not a rewriting:
`T_{[c+2,c+1]} = 1`. -/
@[hjo "lem_sweep_stair_absorb_residual"]
theorem cmAscWord_residual_one (q : L) (c : ℕ) : cmAscWord q (c + 2) (c + 1) = 1 :=
  cmAscWord_self_pred q (c + 1)

/-! ### THE WALL AT `δ = 2`, inside the absorbing class -/

omit [Algebra ℚ L] in
/-- `T_i(y_i) = y_{i+1} + (1-q)y_i`, `HJO.Sweep.braid_auxVar_pow` at `n = 1`. -/
theorem braid_auxVar_self (q : L) {i : ℕ} (hi : 1 ≤ i) :
    braid q i (auxVar i : Total L) = (auxVar (i + 1) : Total L) + scal (1 - q) * auxVar i := by
  have h := braid_auxVar_pow q hi 1
  rw [pow_one] at h
  simpa [Finset.sum_range_one] using h

omit [Algebra ℚ L] in
/-- `T_1` fixes `y_3`: its interchange swaps `y_1` and `y_2`. -/
theorem braid_one_X_two (q : L) :
    braid q 1 (MvPolynomial.X 2 : Total L) = MvPolynomial.X 2 := by
  refine braid_of_swapAux_eq q ?_
  rw [swapAux_X, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

omit [Algebra ℚ L] in
/-- **The shift-`2` staircase at offset `0` and height `1`, evaluated at `y_2`**:
`T_1T_2(y_2) = y_3 + q(1-q)y_1`. Both letters act: `T_2` sends `y_2` to `y_3 + (1-q)y_2`
(`HJO.Sweep.braid_auxVar_self`), and `T_1` then fixes `y_3`
(`HJO.Sweep.braid_one_X_two`) and sends `y_2` to `qy_1` (`HJO.Sweep.braid_one_X_one`). -/
theorem stairWord_two_zero_one_X_one (q : L) :
    stairWord q 2 0 1 (MvPolynomial.X 1 : Total L)
      = MvPolynomial.X 2 + scal ((1 - q) * q) * MvPolynomial.X 0 := by
  have hav2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  have hav3 : (auxVar 3 : Total L) = MvPolynomial.X 2 := by norm_num [auxVar]
  have h2 : braid q 2 (MvPolynomial.X 1 : Total L)
      = MvPolynomial.X 2 + scal (1 - q) * MvPolynomial.X 1 := by
    have h := braid_auxVar_self q (i := 2) (by omega)
    rwa [hav2, hav3] at h
  have hsplit : stairWord q 2 0 1 (MvPolynomial.X 1 : Total L)
      = braid q 1 (braid q 2 (MvPolynomial.X 1 : Total L)) := by
    rw [stairWord_one, Nat.zero_add,
      cmAscWord_split q (a := 1) (b := 2) (c := 1) (by omega) (by omega), cmAscWord_self,
      cmAscWord_self]
    rfl
  rw [hsplit, h2, map_add, braid_one_X_two, braid_scal_mul, braid_one_X_one, ← mul_assoc,
    ← scal_mul]

omit [Algebra ℚ L] in
/-- `T_1T_2(y_2)` is `Λ`-free, the side condition of
`HJO.Sweep.dplus_stairWord_shift_two_of_mem_auxSubalg` at the witness. -/
theorem stairWord_two_zero_one_X_one_mem_auxSubalg (q : L) :
    stairWord q 2 0 1 (MvPolynomial.X 1 : Total L) ∈ auxSubalg L := by
  rw [stairWord_two_zero_one_X_one]
  refine add_mem (auxVar_mem_auxSubalg (L := L) 3) (mul_mem ?_ (auxVar_mem_auxSubalg (L := L) 1))
  rw [scal_eq_algebraMap]
  exact (auxSubalg L).algebraMap_mem _

omit [Algebra ℚ L] in
/-- **RULE `A` AT SHIFT `2` DOES NOT ABSORB — IT REWRITES.** Whenever the shift-`2` staircase image
of `F` is `Λ`-free,

`d^♭_+{}^{(1)}(S^2_{0,1}F) = -q·y_1T_2(F)`,

against `d^♭_+{}^{(0)}(F) = -y_1F` for `Λ`-free `F`
(`HJO.Sweep.dplus_zero_of_mem_auxSubalg`). The residual letter `T_2` of
`HJO.Sweep.cmAscWord_mulLeft_auxVar_stairWord_shift` stands between the two, and no scalar can
remove it unless `T_2` fixes `F`. -/
theorem dplus_stairWord_shift_two_of_mem_auxSubalg (q : L) {F : Total L}
    (hS : stairWord q 2 0 1 F ∈ auxSubalg L) :
    dplus q 1 (stairWord q 2 0 1 F)
      = -(q • ((auxVar 1 : Total L) * braid q 2 F)) := by
  have hword := congrArg (fun T : Module.End L (Total L) => T F)
    (cmAscWord_mulLeft_auxVar_stairWord_shift q 0 (δ := 2) (by omega))
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply] at hword
  rw [dplus_eq_cmAscWord' q 1 _, qshift_of_mem_auxSubalg q _ hS]
  rw [show (1 : ℕ) + 1 = 2 from rfl] at hword ⊢
  rw [show cmAscWord q 1 0 = 1 from cmAscWord_self_pred q 0] at hword
  simp only [Module.End.one_apply] at hword
  rw [show cmAscWord q (0 + 2) (0 + 2) = braidEnd q 2 from by norm_num [cmAscWord_self]] at hword
  rw [hword]
  rfl

omit [Algebra ℚ L] in
/-- `d^♭_+{}^{(0)}` on a `Λ`-free vector is just `-y_1·`. -/
theorem dplus_zero_of_mem_auxSubalg (q : L) {F : Total L} (hF : F ∈ auxSubalg L) :
    dplus q 0 F = -((auxVar 1 : Total L) * F) := by
  rw [dplus_eq_cmAscWord' q 0 F, qshift_of_mem_auxSubalg q _ hF,
    show cmAscWord q 1 0 = 1 from cmAscWord_self_pred q 0]
  rfl

omit [Algebra ℚ L] in
/-- **RULE `A`'S CONSUMPTION IS FALSE AT SHIFT `δ = 2`, FOR EVERY SCALAR, AT A `Λ`-FREE VECTOR.**
For every `q ≠ 0` and every `x`,

`d^♭_+{}^{(1)}(S^2_{0,1}y_2) ≠ x·d^♭_+{}^{(0)}(y_2)`.

The left side is `-q(y_1y_3 + (1-q)y_1y_2)` and the right side is `-xy_1y_2`; the monomial `y_1y_3`
occurs on the left with coefficient `-q ≠ 0` and not at all on the right.

**This is a second obstruction, independent of the `Λ` one.** `y_2` is `Λ`-free, so it lies in the
class on which `HJO.Sweep.dplus_stairWord_consume_of_mem_auxSubalg` holds — at `δ = 1`. The failure
here is the residual letter `T_2` of
`HJO.Sweep.cmAscWord_mulLeft_auxVar_stairWord_shift`, and it is present for every `δ ≥ 2`. So
enlarging the class cannot help: at `δ ≥ 2` there is nothing to enlarge it to. -/
theorem not_dplus_stairWord_consume_shift_two (hq : q ≠ 0) (x : L) :
    dplus q 1 (stairWord q 2 0 1 (MvPolynomial.X 1 : Total L))
      ≠ x • dplus q 0 (MvPolynomial.X 1 : Total L) := by
  have hav1 : (auxVar 1 : Total L) = MvPolynomial.X 0 := rfl
  have hav2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  have hmem : (MvPolynomial.X 1 : Total L) ∈ auxSubalg L := by
    rw [← hav2]; exact auxVar_mem_auxSubalg (L := L) 2
  have hb2 : braid q 2 (MvPolynomial.X 1 : Total L)
      = MvPolynomial.X 2 + scal (1 - q) * MvPolynomial.X 1 := by
    have h := braid_auxVar_self q (i := 2) (by omega)
    rwa [hav2, show (auxVar 3 : Total L) = MvPolynomial.X 2 from by norm_num [auxVar]] at h
  rw [dplus_stairWord_shift_two_of_mem_auxSubalg q
      (stairWord_two_zero_one_X_one_mem_auxSubalg q),
    dplus_zero_of_mem_auxSubalg q hmem, hb2, hav1]
  intro h
  have hmm : ∀ i j : ℕ, (MvPolynomial.X i * MvPolynomial.X j : Total L)
      = MvPolynomial.monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := fun i j => by
    rw [← monomial_single_one_eq_X (L := L) i, ← monomial_single_one_eq_X (L := L) j,
      MvPolynomial.monomial_mul, mul_one]
  have hkey : (MvPolynomial.X 0 * (MvPolynomial.X 2 + scal (1 - q) * MvPolynomial.X 1) : Total L)
      = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 2 1) 1
        + MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1)
            (MvPolynomial.C (1 - q)) := by
    rw [mul_add, hmm 0 2, show (MvPolynomial.X 0 * (scal (1 - q) * MvPolynomial.X 1) : Total L)
        = scal (1 - q) * (MvPolynomial.X 0 * MvPolynomial.X 1) from by ring, hmm 0 1, scal,
      MvPolynomial.C_mul_monomial, mul_one]
  have hne : (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ)
      ≠ Finsupp.single 0 1 + Finsupp.single 2 1 := by
    intro hh
    have h2 := congrArg (fun f : ℕ →₀ ℕ => f 2) hh
    simp at h2
  rw [hkey, hmm 0 1] at h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) h
  simp only [MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, MvPolynomial.coeff_add,
    MvPolynomial.coeff_monomial, hne, reduceIte, add_zero, smul_zero, neg_zero] at hc
  exact hq (by simpa using hc)

/-! ### Rule `B` absorbs nothing at shift `2` either, offset `0` included -/

omit [Algebra ℚ L] in
/-- **The shift-`2` staircase at offset `0` and height `1`, evaluated at `y_1`**:
`T_1T_2(y_1) = y_2 + (1-q)y_1`. The upper letter `T_2` does not touch `y_1`
(`HJO.Sweep.braid_succ_succ_X_zero`) and the lower one is
`HJO.Sweep.braid_one_X_zero`. -/
theorem stairWord_two_zero_one_X_zero (q : L) :
    stairWord q 2 0 1 (MvPolynomial.X 0 : Total L)
      = MvPolynomial.X 1 + scal (1 - q) * MvPolynomial.X 0 := by
  have hsplit : stairWord q 2 0 1 (MvPolynomial.X 0 : Total L)
      = braid q 1 (braid q 2 (MvPolynomial.X 0 : Total L)) := by
    rw [stairWord_one, Nat.zero_add,
      cmAscWord_split q (a := 1) (b := 2) (c := 1) (by omega) (by omega), cmAscWord_self,
      cmAscWord_self]
    rfl
  rw [hsplit, braid_succ_succ_X_zero q 0, braid_one_X_zero]

/-- **RULE `B` ABSORBS NOTHING AT SHIFT `2`, AT OFFSET `0`, FOR EVERY SCALAR.** For every `q ≠ 1`
and every `x`,

`d^♭_-{}^{(2)}(S^2_{0,1}y_1) ≠ x·d^♭_-{}^{(1)}(y_1)`.

`HJO.Sweep.not_dminus_stairWord_consume_offset` is the same at shift `1`, at every offset. This is
the instance the round-boundary witness
`HJO.Mellit.not_tailRoundWord_stairWord_bound_shift_two` needs: there the staircase arrives at
offset `0` with shift `2` at a type-`B` event, so neither that theorem's shift nor this one's offset
is a free choice.

The left side is `-e_1 + (1-q)y_1`, from `HJO.Sweep.stairWord_two_zero_one_X_zero` and
`HJO.Sweep.dminus_auxVar_pow`; the right side is `-xe_1`. The monomial `y_1` occurs on the left with
coefficient `1 - q ≠ 0` and not at all on the right. Structurally it is the same reason as at shift
`1`: `d^♭_-` is a coefficient extraction with no ascending word, so there is nothing for a staircase
block of any width to be eaten against. -/
theorem not_dminus_stairWord_consume_shift_two (hq : q ≠ 1) (x : L) :
    dminus q 2 (stairWord q 2 0 1 (MvPolynomial.X 0 : Total L))
      ≠ x • dminus q 1 (MvPolynomial.X 0 : Total L) := by
  have hav2 : (auxVar 2 : Total L) = MvPolynomial.X 1 := by norm_num [auxVar]
  have hd2 : dminus q 2 (MvPolynomial.X 1 : Total L)
      = -MvPolynomial.C (Sym.elemSymm L 1) := by
    have h := dminus_auxVar_pow q 1 1
    rw [pow_one, pow_one, hav2] at h
    rw [h]; ring
  rw [stairWord_two_zero_one_X_zero, map_add, hd2, dminus_one_X_zero, smul_eq_scal_mul,
    show (scal (1 - q) * MvPolynomial.X 0 : Total L) = (1 - q) • MvPolynomial.X 0 from
      (smul_eq_scal_mul _ _).symm, map_smul, dminus_two_X_zero]
  intro h
  have hne : ¬ ((0 : ℕ →₀ ℕ) = Finsupp.single 0 1) := by
    intro hh; exact absurd (congrArg (fun f : ℕ →₀ ℕ => f 0) hh) (by simp)
  have hrhs : (scal x * -MvPolynomial.C (Sym.elemSymm L 1) : Total L)
      = MvPolynomial.C (MvPolynomial.C x * -(Sym.elemSymm L 1)) := by
    rw [show (-MvPolynomial.C (Sym.elemSymm L 1) : Total L)
        = MvPolynomial.C (-(Sym.elemSymm L 1)) from
      (map_neg (MvPolynomial.C : Sym.Lambda L →+* Total L) _).symm, scal, ← MvPolynomial.C_mul]
  rw [hrhs] at h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single 0 1)) h
  rw [← monomial_single_one_eq_X (L := L) 0] at hc
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_C, MvPolynomial.coeff_monomial, hne, ite_true, ite_false, neg_zero,
    zero_add] at hc
  rcases smul_eq_zero.1 hc with h1 | h1
  · exact hq (sub_eq_zero.1 h1).symm
  · exact one_ne_zero h1

end HJO.Sweep

/-! ### The geometry supplies `δ = 2` at a type-`B` event, on the smallest rectangle in range -/

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset ParkingFunctions

/-- The above-diagonal path `ŷ = (0, 2, 3)` of the `2 × 3` rectangle, used as the **tail** against
the base `HJO.Mellit.baseTwoThreeB`. Its three north steps `(0,0)`, `(0,1)`, `(1,2)` have diagonal
excesses `0`, `2`, `1`, so two of them fall in the window `[0, 2)` of
`HJO.Paths.tailLiveSteps` at level `2` and the shift there is `2`, not `1`. -/
def tailTwoThreeA : Heights 2 3 1 :=
  fun r => if (r : ℕ) = 0 then 0 else if (r : ℕ) = 1 then 2 else 3

theorem isAboveDiagonal_tailTwoThreeA : IsAboveDiagonal tailTwoThreeA := by decide

/-- `HJO.Mellit.sweptAbove` at a separating level is a `decide`-able filter of the swept region, the
form every kernel computation below reads. -/
theorem sweptAbove_tailTwoThreeA :
    sweptAbove tailTwoThreeA (sepLevel 2 1)
      = {P ∈ sweptRegion tailTwoThreeA | 3 * P.1 < 2 * P.2} :=
  sweptAbove_eq_filter (separatesDiagonal_sepLevel (by norm_num)) _

/-- **The shift at level `2` is `2`.** Two of the tail's north steps, `(0,0)` of excess `0` and
`(1,2)` of excess `1`, lie in the window `[0, 2)`. This is where `a` enters: the window is `a`
levels wide (`HJO.Paths.mem_tailLiveSteps_iff_Ioc`), and at `a = 2` it catches two steps. -/
theorem card_tailLiveSteps_tailTwoThreeA_two : #(tailLiveSteps tailTwoThreeA 2) = 2 := by decide

/-- **The height of the staircase emitted at round `2` is `1`**: the base layer of round `2` of
`HJO.Mellit.baseTwoThreeB` is the single type-`C` point `(0,1)`. -/
theorem card_baseRound_ac_baseTwoThreeB_two :
    #{P ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 P = 2 ∧
        (eventType baseTwoThreeB P = EventType.A ∨
          eventType baseTwoThreeB P = EventType.C)} = 1 := by
  rw [sweptAbove_baseTwoThreeB]; decide

/-- **The arrival point.** The tail layer of round `1` of `HJO.Mellit.tailTwoThreeA` is the single
point `(1,2)`, a **type-`B`** event, and the index its raised operator is read at — its own width
plus `β_1 = #(HJO.Paths.baseLiveSteps baseTwoThreeB 1)` — is `3`. -/
theorem tailRound_one_tailTwoThreeA :
    {p ∈ sweptAbove tailTwoThreeA (sepLevel 2 1) | diagExcess 2 3 p = 1} = {(1, 2)} ∧
      eventType tailTwoThreeA ((1, 2) : ℕ × ℕ) = EventType.B ∧
      sweepWidth tailTwoThreeA ((1, 2) : ℕ × ℕ) + #(baseLiveSteps baseTwoThreeB 1) = 3 := by
  refine ⟨?_, by decide, by decide⟩
  rw [sweptAbove_tailTwoThreeA]; decide

/-- **THE PASS BOUND FAILS AT SHIFT `2`, AT A TYPE-`B` EVENT, AND NO ABSORPTION REPLACES IT.** The
side condition of `HJO.Mellit.tailRoundWord_stairWord` fails at round `1` of the pair
`z = HJO.Mellit.baseTwoThreeB`, `w = HJO.Mellit.tailTwoThreeA` for the staircase the base layer of
round `2` emits — height `m = 1` by `HJO.Mellit.card_baseRound_ac_baseTwoThreeB_two`, shift
`δ = 2` by `HJO.Mellit.card_tailLiveSteps_tailTwoThreeA_two`, offset `0`, the layer between them
being `HJO.Mellit.tailRound_one_tailTwoThreeA`'s single point.

Passing needs `0 + 0 + 1 + 2 + 1 = 4` and the index is `3`, so the staircase does not commute. And
nothing absorbs it either: the event is of type `B`, which absorbs at no offset at shift `1`
(`HJO.Sweep.not_dminus_stairWord_consume_offset`) and not at offset `0` at shift `2` either
(`HJO.Sweep.not_dminus_stairWord_consume_shift_two`, the instance this witness presents), and at
`δ = 2` neither rule `A` nor rule `C` has an absorption to offer
(`HJO.Sweep.not_dplus_stairWord_consume_shift_two`,
`HJO.Sweep.cmAscWord_mulLeft_auxVar_stairWord_shift`).

This differs from `HJO.Mellit.not_tailRoundWord_stairWord_bound` in the one respect that matters:
there the arriving staircase had `δ = 1` and the arrival point was of type `C`, where
`HJO.Sweep.corner_stairWord_consume_of_mem_piece` **does** absorb at exactly the offset
`HJO.Sweep.consume_offsets_differ_by_one` predicts. Here it is type `B` and `δ = 2`, and there is no
candidate identity at all. Nothing is assumed of `q` or `u`: this is a fact about the two paths, and
both lie in the `2 × 3` rectangle, so `a = 2` and the witness is inside `1 < a < b`. -/
theorem not_tailRoundWord_stairWord_bound_shift_two :
    ¬ ∀ p ∈ sortByRank 2 3 1
          {p ∈ sweptAbove tailTwoThreeA (sepLevel 2 1) | diagExcess 2 3 p = 1},
        0 + acCount tailTwoThreeA (sortByRank 2 3 1
              {p ∈ sweptAbove tailTwoThreeA (sepLevel 2 1) | diagExcess 2 3 p = 1})
            + 1 + 2 + 1 ≤ sweepWidth tailTwoThreeA p + #(baseLiveSteps baseTwoThreeB 1) := by
  intro h
  have hmem : ((1, 2) : ℕ × ℕ) ∈ sortByRank 2 3 1
      {p ∈ sweptAbove tailTwoThreeA (sepLevel 2 1) | diagExcess 2 3 p = 1} :=
    mem_sortByRank.2 (by rw [sweptAbove_tailTwoThreeA]; decide)
  have hgrad : sweepWidth tailTwoThreeA ((1, 2) : ℕ × ℕ)
      + #(baseLiveSteps baseTwoThreeB 1) = 3 := by decide
  have := h _ hmem
  omega

/-! ### The thresholds, as arithmetic -/

/-- **THE COMMUTATION AND ABSORPTION THRESHOLDS ARE COMPLEMENTARY AT `δ = 1`, AND RULE `B` LEAVES A
ONE-UNIT HOLE.** At shift `δ = 1`, for an arriving staircase of offset `c` and height `m` read
against an operator of index `n`:

1. **rule `A`** commutes for `c + m + 1 ≤ n` (`HJO.Sweep.dplus_stairWord`) and absorbs at
   `n = c + m` (`HJO.Sweep.dplus_stairWord_consume_of_mem_auxSubalg`), and the two together are
   exactly `c + m ≤ n`;
2. **rule `C`** commutes for `c + m + 2 ≤ n` (`HJO.Sweep.corner_stairWord`) and absorbs at
   `n = c + m + 1` (`HJO.Sweep.corner_stairWord_consume`), and the two together are exactly
   `c + m + 1 ≤ n`;
3. **rule `B`** commutes for `c + m + 2 ≤ n` and absorbs nowhere
   (`HJO.Sweep.not_dminus_stairWord_consume_offset`), so the index `n = c + m + 1` is covered by
   neither.

So the absorptions of `HJO.Sweep.consume_offsets_differ_by_one` extend each rule's reach by exactly
one unit and no more, and rule `B`'s reach is not extended at all. The hole at clause 3 is where the
consumption route has to be checked against the geometry, and
`HJO.Mellit.not_tailRoundWord_stairWord_bound_shift_two` is an instance of a type-`B` event below
its threshold. -/
theorem consume_commute_thresholds (c m n : ℕ) :
    (c + m + 1 ≤ n ∨ n = c + m ↔ c + m ≤ n)
      ∧ (c + m + 2 ≤ n ∨ n = c + m + 1 ↔ c + m + 1 ≤ n)
      ∧ ¬ c + m + 2 ≤ c + m + 1 := by
  omega

end HJO.Mellit

end
