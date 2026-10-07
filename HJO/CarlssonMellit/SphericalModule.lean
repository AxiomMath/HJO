/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AlgBasis
public import HJO.CMStructure.CmYMultiplication
public import HJO.CMStructure.StarEasy
public import HJO.CMStructure.HeckeStraighten
public import HJO.CarlssonMellit.ArrowWords
public import HJO.CarlssonMellit.BopModule
public import HJO.CarlssonMellit.CornerPairs
public import HJO.CarlssonMellit.CornerRaising
public import HJO.CarlssonMellit.CornerTransport
public meta import HJO.Attr

/-! # The spherical module of the Dyck path algebra

Carlsson and Mellit's spherical module is the left ideal `𝔸_q𝟏_0` of the Dyck path algebra
`HJO.Dyck.Aq`, and their Theorem 5.2 says that the evaluation map `f𝟏_0 ↦ f(1)` is an isomorphism of
`𝔸_q`-modules onto the graded module `V_*` of `HJO.Sweep.Vstar`, carrying `𝟏_k𝔸_q𝟏_0` onto `V_k`.

This file builds the left ideal, builds the evaluation map out of the action of
`HJO.Sweep.exists_isDpaAction_cm`, proves that the map is `𝔸_q`-equivariant, that it carries `𝟏_0`
to `1 ∈ V_0`, that it carries `𝟏_k𝔸_q𝟏_0` *into* `V_k` and *onto* `V_k`, hence `𝔸_q𝟏_0` onto `V_*`;
and it proves the normal form for the left ideal off which the reverse inequality — injectivity — is
to be read.

Surjectivity is proved by exhibiting, for each basis vector of
`HJO.Sweep.exists_basis_vstar_prod_bop`, one word of the algebra that evaluates to it. The basis
vector indexed by `k`, by exponents `a_1, …, a_k` and by a list `r_1, …, r_m` is

`y_1^{a_1} ⋯ y_k^{a_k}·B_{r_1+1}(B_{r_2+1}(⋯ B_{r_m+1}(1)⋯)) ∈ V_k`,

and the word is read off it from the outside in. The innermost `1` is `d_+^{k+m}𝟏_0`, since `d_+`
fixes `1` at every vertex. A single Hall--Littlewood operator is one lowering arrow applied to one
power of the last variable, by `HJO.Sweep.dminusCM_auxVar_pow_mul`: `d_-(y_{j+1}^{r}F) = -B_{r+1}F`
for `F ∈ V_j`. Since `B_{r+1}F` again lies in `Λ = V_0 ⊆ V_j`, the identity may be applied again one
vertex lower, and `m` applications descend from the vertex `k + m` to the vertex `k`, producing the
nested word up to the sign `(-1)^m`. The head `y_1^{a_1} ⋯ y_k^{a_k}` is then the corner elements
`HJO.Dyck.Aq.yElt` acting, which they do by multiplication by the variables. So the word

`y_1^{a_1} ⋯ y_k^{a_k}·(d_-y_{k+1}^{r_1})(d_-y_{k+2}^{r_2}) ⋯ (d_-y_{k+m}^{r_m})·d_+^{k+m}𝟏_0`

of `𝟏_k𝔸_q𝟏_0` evaluates to `(-1)^m` times the basis vector, and the image, being a submodule
containing every basis vector, is all of `V_k`.

The normal form is Carlsson and Mellit's: every path from the vertex `0` to the vertex `k` is a
`𝕜`-combination of the words

`d_-^m y_1^{b_1} ⋯ y_{k+m}^{b_{k+m}}d_+^{k+m}𝟏_0`,   `b_{k+1} ≥ b_{k+2} ≥ ⋯ ≥ b_{k+m}`,

every lowering arrow collected on the left and a single corner monomial at the top vertex `k + m`.
It is reached in two steps, and neither runs the iteration of two competing moves.

That the span of these words with *no* condition on the exponents already contains `𝔸_q𝟏_0` is a
structural induction on a word in the generators, with no measure at all. A loop at the bottom
vertex travels rightwards past the whole lowering block by `T_id_- = d_-T_i`, is absorbed into the
corner monomial by `HJO.Dyck.Aq.Tg_mul_yMon_mem_span`, and whatever loop that rule leaves on the
right dies on the raising block by `HJO.Dyck.Aq.Tg_mul_dPlusPow`. A corner element travels
rightwards by `HJO.Dyck.Aq.yElt_mul_dMinus` and merges into the monomial. A lowering arrow lengthens
the block. The raising arrow is the only generator needing an induction, and it is an induction on
the *length of the lowering block*: `HJO.Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt` turns a leading
`d_+d_-` into `d_-d_+` plus a loop word times a corner element — both already covered — and at
length zero `HJO.Dyck.Aq.dPlus_mul_yElt` carries `d_+` past the corner monomial at the cost of loops
and corner elements at the vertex above, which the previous clauses absorb. So `d_+` never has to
travel past a corner element that a later step reintroduces to its left, which is what the second
move does and what refutes its measure.

That the sorted words suffice is a second induction, on the weight `∑_s s·b_s` of the corner
monomial. For `k < j < k + m` the relation `d_-^mT_j = d_-^m` of `HJO.Dyck.Aq.dMinusPow_mul_Tg`
inserts `T_j` to the left of the monomial for free, and when `b_j < b_{j+1}` the Hecke commutation
`HJO.Dyck.Aq.Tg_mul_yElt_succ` and the pair commutation `HJO.Dyck.Aq.Tg_mul_yElt_pair` rewrite
`T_jy_1^{b_1} ⋯ y_{k+m}^{b_{k+m}}`
into monomials, with or without `T_j` on the right, every one of strictly smaller weight: peeling
`y_jy_{j+1}` off the front while `b_j > 0` is a commutation, and the first peeled `y_{j+1}` with
`b_j = 0` trades a factor of weight `j + 1` for one of weight `j`. The weight is a measure on the
*exponents*, where the measure of `HJO.Dyck.straightenMeasure` is on the letters, which is why the
counterexample of `HJO.Dyck.straightenMeasure_lt_moveTwo` does not reach it.

## Main definitions

* `HJO.Dyck.Aq.e0Ideal`: the left ideal `𝔸_q𝟏_0`.
* `HJO.Dyck.Aq.cornerE0`: the summand `𝟏_k𝔸_q𝟏_0` of it, the paths from the vertex `0` to the
  vertex `k`.
* `HJO.Sweep.evalOneAq`: the evaluation map `f ↦ f(1)`, of which the map `f𝟏_0 ↦ f(1)`
  is the restriction to `𝔸_q𝟏_0`.
* `HJO.Dyck.Aq.normalWord`: the word `d_-^my_1^{b_1} ⋯ y_{k+m}^{b_{k+m}}d_+^{k+m}𝟏_0`, and
  `HJO.Dyck.Aq.normalSpan`, `HJO.Dyck.Aq.sortedNormalSpan`: the span of these words, and of those
  whose exponents above the vertex `k` are weakly decreasing.
* `HJO.Dyck.Aq.yMonWt`: the weight `∑_s s·b_s` of a corner monomial, the measure the sort falls on.
* `HJO.Dyck.Aq.lowerStraightenSet`: the words a weight-lowering straightening step produces.

## Main results

* `HJO.Sweep.evalOneAq_mul` and `HJO.Sweep.evalOneAq_e_zero`: the evaluation map is
  `𝔸_q`-equivariant and sends `𝟏_0` to `1 ∈ V_0`.
* `HJO.Sweep.map_evalOneAq_cornerE0_eq`: it carries `𝟏_k𝔸_q𝟏_0` onto `V_k`.
* `HJO.Sweep.map_evalOneAq_e0Ideal_eq_top`: it carries `𝔸_q𝟏_0` onto `V_*`.
* `HJO.Dyck.Aq.e0Ideal_le_iSup_sortedNormalSpan` and
  `HJO.Dyck.Aq.cornerE0_le_sortedNormalSpan`: the normal form, for `𝔸_q𝟏_0` and for each
  `𝟏_k𝔸_q𝟏_0`.
* `HJO.Dyck.Aq.dPlus_mul_mem_normalSpan`: the raising arrow carries the span of the unsorted normal
  forms at the vertex `k` into the one at `k + 1`, the one clause of the closure that is not a
  single relation.
* `HJO.Dyck.Aq.Tg_mul_yMon_mem_span_lowerStraightenSet`: the weight-lowering straightening, the
  stopping rule of the sort.
* `HJO.Sweep.exists_linearEquiv_e0Ideal_of_injOn`: the isomorphism of `𝔸_q`-modules, given that the
  evaluation map is injective on `𝔸_q𝟏_0`.

## Implementation notes

**Injectivity is a hypothesis.** Surjectivity needs one word per basis vector and nothing
else. Injectivity is an upper bound on `𝔸_q𝟏_0`, and an upper bound is a normal form; the normal
form is proved here, and what is still missing is one equation. The sorted words of the introduction
are indexed by exactly the data indexing the basis of `HJO.Sweep.exists_basis_vstar_prod_bop` at the
vertex `k` — the unconstrained exponents `b_1, …, b_k` and the weakly decreasing list
`b_{k+1} ≥ ⋯ ≥ b_{k+m}` — and what remains is that the evaluation map sends the word at `(k, b, m)`
to `(-1)^m` times the basis vector at the same index. Given that equation the sorted words are a
spanning family carried bijectively onto a basis, so the evaluation map precomposed with the linear
combination along that family is injective, and injectivity on `𝔸_q𝟏_0` follows from the injectivity
of a composite. The equation is not an estimate: `HJO.Dyck.Aq.yElt_mul_dMinus` carries the corner
elements of index `≤ k + t` leftwards through the `t`-th lowering arrow, turning the normal form
into the interleaved word of the introduction, and then `HJO.Sweep.dminusCM_auxVar_pow_mul` read
through `HJO.Sweep.bopExt` computes each arrow exactly, where the surjectivity argument of this file
needs only a membership. As it is not proved here, `HJO.Sweep.exists_linearEquiv_e0Ideal_of_injOn`
carries injectivity as a hypothesis, in the same shape in which
`HJO.Sweep.atildeE0_inf_ker_eq_kernelIdealE0_of_injOn` already carries it.

**The stopping rule is not repaired but replaced, and in two places.** The straightening
argument one would write by hand reduces a path word by four moves with the second and the fourth
iterated, and measures the iteration by `HJO.Dyck.straightenMeasure`, which the second move raises —
`HJO.Dyck.straightenMeasure_lt_moveTwo`. Here the closure of the span under the generators carries
no measure at all: it is an induction on the word, with the raising arrow's clause an induction on
the length of the lowering block, so that the raising arrow is dealt with once and for all rather
than competing with the straightening. The straightening then appears only inside the sort, where it
is run against the weight `∑_s s·b_s` of the exponents; and it is run only when `b_j < b_{j+1}`,
which makes it strictly lowering. Neither the closure nor the sort consults an order on the letters.

**The weight-lowering straightening is not a special case of `HJO.Dyck.Aq.Tg_mul_yMon_mem_span`.**
That rule preserves the total degree `∑_s b_s` and says nothing about `∑_s s·b_s`, and it cannot:
for `b` with `b_j = b_{j+1}` the loop simply commutes past the monomial, at constant weight. The
hypothesis `b_j < b_{j+1}` is therefore part of
`HJO.Dyck.Aq.Tg_mul_yMon_mem_span_lowerStraightenSet`, and it is available exactly where the sort
needs it. Its proof is the same peeling induction as the one behind
`HJO.Dyck.Aq.Tg_mul_yMon_mem_span`, on `b_j + b_{j+1}`, with the bookkeeping changed from the degree
to the weight.

**The evaluation map is defined on all of `𝔸_q`, not on the ideal.** Since `ρ(𝟏_0)` is the
projection onto `V_0` and fixes `1`, the map `x ↦ ρ(x)(1)` restricts on `𝔸_q𝟏_0` to the map
`f𝟏_0 ↦ f(1)`, by `HJO.Sweep.evalOneAq_mul` and `HJO.Sweep.evalOneAq_e_zero`; having it on `𝔸_q`
is what makes the images of the submodules `𝟏_k𝔸_q𝟏_0` readable as `Submodule.map`. This is the
convention `HJO.Sweep.evalOne` already uses for the extended algebra.

**`V_k` is named as a submodule of `V_*` by the range of its inclusion.** `V_*` is the external
direct sum of the `HJO.Sweep.pieceSub`, so "the image is `V_k`" is the equation
`Submodule.map (evalOneAq ρ) (cornerE0 L q k) = LinearMap.range (ofPiece L k)`, and the statement
that `V_*` is exhausted is that these ranges sum to `⊤`, which is the direct-sum decomposition
rather than anything about the algebra.

**The surjectivity induction runs over an arbitrary list, not a partition.** The basis of
`HJO.Sweep.exists_basis_vstar_prod_bop` is indexed by weakly decreasing lists, because that is what
makes the Hall--Littlewood words a *basis*; the recursion producing a word for a Hall--Littlewood
monomial needs no order on the list, so `HJO.Sweep.ofPiece_mem_map_evalOneAq_cornerE0` is stated for
every list and the order enters only where the basis is consumed.

**The corner elements of the algebra carry the head of the monomial.** The step is
`HJO.Sweep.map_yElt_eq_auxMulPiece_cm`, that `ρ(y_i)` is multiplication by `y_i` on `V_k`; this is
usually left as a remark after the construction of the action in `HJO.Sweep.exists_isDpaAction_cm`,
without a separate statement, and it is what lets the head `y_1^{a_1} ⋯ y_k^{a_k}` of a basis vector
be produced inside the one corner `𝟏_k𝔸_q𝟏_k` instead of being carried along the descent.

## References

This file formalises the lemma `HJO.Sweep.exists_linearEquiv_e0Ideal`, using
`HJO.Dyck.Aq`, `HJO.Sweep.Vstar`, `HJO.Sweep.piece`, `HJO.Dyck.Aq.yElt` and `HJO.Sweep.bopExt`, and
proved here from `HJO.Sweep.exists_isDpaAction_cm`, `HJO.Sweep.exists_basis_vstar_prod_bop` and
`HJO.Sweep.dminusCM_auxVar_pow_mul`; the normal form from `HJO.Dyck.Aq.Tg_mul_yMon_mem_span`,
`HJO.Dyck.Aq.Tg_mul_dPlusPow`, `HJO.Dyck.Aq.dMinusPow_mul_Tg`, `HJO.Dyck.Aq.yElt_mul_dMinus`,
`HJO.Dyck.Aq.dPlus_mul_yElt`, `HJO.Dyck.Aq.Delta_eq_smul_tSegUp_mul_yElt`,
`HJO.Dyck.Aq.Tg_mul_yElt_succ`, `HJO.Dyck.Aq.Tg_mul_yElt_pair` and `HJO.Dyck.Aq.yElt_comm`. The
refutation of the termination measure is `HJO.Dyck.straightenMeasure_lt_of_step` read against
`HJO.Dyck.straightenMeasure_lt_moveTwo`. Transcribing E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, Theorem 5.2 and its Lemma 5.4.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K}

/-! ### The left ideal `𝔸_q𝟏_0` -/

/-- **The left ideal `𝔸_q𝟏_0`** of the Dyck path algebra: the paths that begin at the vertex `0`.
This is the domain of the isomorphism of `HJO.Sweep.exists_linearEquiv_e0Ideal`. -/
noncomputable def e0Ideal (K : Type*) [CommRing K] (q : K) : Submodule K (Aq K q) :=
  LinearMap.range (LinearMap.mulRight K (e K q 0))

theorem mem_e0Ideal_iff {x : Aq K q} : x ∈ e0Ideal K q ↔ ∃ y : Aq K q, y * e K q 0 = x := Iff.rfl

theorem mul_e_zero_mem_e0Ideal (x : Aq K q) : x * e K q 0 ∈ e0Ideal K q :=
  mem_e0Ideal_iff.2 ⟨x, rfl⟩

theorem e_zero_mem_e0Ideal : e K q 0 ∈ e0Ideal K q := mem_e0Ideal_iff.2 ⟨1, one_mul _⟩

/-- **`𝔸_q𝟏_0` is a left ideal**, which is what makes it a module over the algebra and so the
domain of a map of `𝔸_q`-modules. -/
theorem mul_mem_e0Ideal (a : Aq K q) {x : Aq K q} (hx : x ∈ e0Ideal K q) : a * x ∈ e0Ideal K q := by
  obtain ⟨y, rfl⟩ := mem_e0Ideal_iff.1 hx
  exact mem_e0Ideal_iff.2 ⟨a * y, mul_assoc a y (e K q 0)⟩

/-- **The summand `𝟏_k𝔸_q𝟏_0`**: the paths from the vertex `0` to the vertex `k`. -/
noncomputable def cornerE0 (K : Type*) [CommRing K] (q : K) (k : ℕ) : Submodule K (Aq K q) :=
  LinearMap.range ((LinearMap.mulLeft K (e K q k)).comp (LinearMap.mulRight K (e K q 0)))

theorem mem_cornerE0_iff {k : ℕ} {x : Aq K q} :
    x ∈ cornerE0 K q k ↔ ∃ y : Aq K q, e K q k * y * e K q 0 = x := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, by rw [mul_assoc]; exact hy⟩
  · obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← mul_assoc]
    exact hy

theorem cornerE0_le_e0Ideal (k : ℕ) : cornerE0 K q k ≤ e0Ideal K q := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_cornerE0_iff.1 hx
  exact mem_e0Ideal_iff.2 ⟨e K q k * y, hy⟩

/-- **A path from `k` to `j` carries `𝟏_k𝔸_q𝟏_0` into `𝟏_j𝔸_q𝟏_0`**: this is the grading by
vertex, and it is what makes the evaluation map of `HJO.Sweep.exists_linearEquiv_e0Ideal` graded. -/
theorem mul_mem_cornerE0 {j k : ℕ} {a x : Aq K q} (ha : e K q j * a * e K q k = a)
    (hx : x ∈ cornerE0 K q k) : a * x ∈ cornerE0 K q j := by
  obtain ⟨y, hy⟩ := mem_cornerE0_iff.1 hx
  have hleft : e K q j * a = a := by
    calc e K q j * a = e K q j * (e K q j * a * e K q k) := by rw [ha]
      _ = e K q j * e K q j * a * e K q k := by simp only [mul_assoc]
      _ = a := by rw [e_mul_self, ha]
  have hright : a * e K q k = a := by
    calc a * e K q k = e K q j * a * e K q k * e K q k := by rw [ha]
      _ = e K q j * a * (e K q k * e K q k) := by simp only [mul_assoc]
      _ = a := by rw [e_mul_self, ha]
  refine mem_cornerE0_iff.2 ⟨a * y, ?_⟩
  rw [← hy]
  calc e K q j * (a * y) * e K q 0 = e K q j * a * (y * e K q 0) := by simp only [mul_assoc]
    _ = a * (y * e K q 0) := by rw [hleft]
    _ = a * e K q k * (y * e K q 0) := by rw [hright]
    _ = a * (e K q k * y * e K q 0) := by simp only [mul_assoc]

/-! ### The word of raising arrows out of the vertex `0` -/

theorem e_mul_dPlusPow (n : ℕ) : e K q n * dPlusPow K q n = dPlusPow K q n := by
  induction n with
  | zero => exact e_mul_self 0
  | succ n _ => rw [dPlusPow_succ, ← mul_assoc, e_mul_dPlus]

theorem dPlusPow_mul_e_zero (n : ℕ) : dPlusPow K q n * e K q 0 = dPlusPow K q n := by
  induction n with
  | zero => exact e_mul_self 0
  | succ n ih => rw [dPlusPow_succ, mul_assoc, ih]

/-- **`d_+^n𝟏_0` is a path from the vertex `0` to the vertex `n`.** -/
theorem dPlusPow_mem_cornerE0 (n : ℕ) : dPlusPow K q n ∈ cornerE0 K q n :=
  mem_cornerE0_iff.2 ⟨dPlusPow K q n, by rw [e_mul_dPlusPow, dPlusPow_mul_e_zero]⟩

theorem dMinusPow_zero (k : ℕ) : dMinusPow K q k 0 = e K q k := rfl

theorem e_mul_dMinusPow (k m : ℕ) : e K q k * dMinusPow K q k m = dMinusPow K q k m := by
  induction m with
  | zero => exact e_mul_self k
  | succ m ih => rw [dMinusPow_succ, ← mul_assoc, ih]

theorem dMinusPow_succ_left (k m : ℕ) :
    dMinusPow K q k (m + 1) = dMinus K q k * dMinusPow K q (k + 1) m := by
  induction m with
  | zero => rw [dMinusPow_succ, dMinusPow_zero, dMinusPow_zero, Nat.add_zero, e_mul_dMinus,
      dMinus_mul_e]
  | succ m ih =>
    have hidx : k + 1 + m = k + (m + 1) := by omega
    rw [dMinusPow_succ, ih, dMinusPow_succ, hidx, mul_assoc]

theorem Tg_mul_dMinusPow {k i : ℕ} (h : i + 2 ≤ k) (m : ℕ) :
    Tg K q k i * dMinusPow K q k m = dMinusPow K q k m * Tg K q (k + m) i := by
  induction m with
  | zero => rw [dMinusPow_zero, Nat.add_zero, Tg_mul_e, e_mul_Tg]
  | succ m ih =>
    rw [show k + (m + 1) = k + m + 1 from (Nat.add_assoc k m 1).symm, dMinusPow_succ,
      ← mul_assoc, ih, mul_assoc, Tg_mul_dMinus (by omega : i + 2 ≤ k + m), ← mul_assoc,
      ← dMinusPow_succ]

variable [Invertible q] [Invertible (q - 1)]

theorem yElt_mul_dMinusPow {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (m : ℕ) :
    yElt K q k i * dMinusPow K q k m = dMinusPow K q k m * yElt K q (k + m) i := by
  induction m with
  | zero => rw [dMinusPow_zero, Nat.add_zero, yElt_mul_e, e_mul_yElt]
  | succ m ih =>
    rw [show k + (m + 1) = k + m + 1 from (Nat.add_assoc k m 1).symm, dMinusPow_succ,
      ← mul_assoc, ih, mul_assoc, yElt_mul_dMinus h1 (by omega : i ≤ k + m), ← mul_assoc,
      ← dMinusPow_succ]

theorem yProd_zero (k : ℕ) (l : List ℕ) : yProd K q k (fun _ => 0) l = 1 := by
  induction l with
  | nil => rfl
  | cons s t ih => rw [yProd_cons, ih, mul_one, pow_zero]

theorem yMon_zero (k : ℕ) : yMon K q k (fun _ => 0) = 1 := yProd_zero k _

/-! ### The normal-form words -/

/-- The normal-form word. -/
noncomputable def normalWord (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k m : ℕ) (b : ℕ → ℕ) : Aq K q :=
  dMinusPow K q k m * yMon K q (k + m) b * dPlusPow K q (k + m)

/-- The span of the normal-form words. -/
noncomputable def normalSpan (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) : Submodule K (Aq K q) :=
  Submodule.span K {x | ∃ m b, x = normalWord K q k m b}

theorem normalWord_eq (k m : ℕ) (b : ℕ → ℕ) :
    normalWord K q k m b
      = dMinusPow K q k m * (yMon K q (k + m) b * dPlusPow K q (k + m)) :=
  mul_assoc _ _ _

theorem normalWord_mem_normalSpan (k m : ℕ) (b : ℕ → ℕ) :
    normalWord K q k m b ∈ normalSpan K q k :=
  Submodule.subset_span ⟨m, b, rfl⟩

theorem dPlusPow_mem_normalSpan (k : ℕ) : dPlusPow K q k ∈ normalSpan K q k := by
  have h := normalWord_mem_normalSpan (K := K) (q := q) k 0 (fun _ => 0)
  rwa [normalWord, dMinusPow_zero, Nat.add_zero, yMon_zero, mul_one, e_mul_dPlusPow] at h

theorem e_zero_mem_normalSpan_zero : e K q 0 ∈ normalSpan K q 0 :=
  dPlusPow_mem_normalSpan 0

/-! ### The idempotents against a normal-form word -/

theorem e_mul_normalWord (k m : ℕ) (b : ℕ → ℕ) :
    e K q k * normalWord K q k m b = normalWord K q k m b := by
  rw [normalWord, ← mul_assoc, ← mul_assoc, e_mul_dMinusPow]

theorem e_mul_normalWord_of_ne {j k : ℕ} (h : j ≠ k) (m : ℕ) (b : ℕ → ℕ) :
    e K q j * normalWord K q k m b = 0 := by
  rw [← e_mul_normalWord (K := K) (q := q) k m b, ← mul_assoc, e_mul_e_of_ne h, zero_mul]

theorem e_mul_eq_self_of_mem_normalSpan {k : ℕ} {z : Aq K q} (hz : z ∈ normalSpan K q k) :
    e K q k * z = z := by
  refine Submodule.span_induction (p := fun w _ => e K q k * w = w) ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, b, rfl⟩; exact e_mul_normalWord k m b
  · rw [mul_zero]
  · intro x y _ _ hx hy; rw [mul_add, hx, hy]
  · intro c x _ hx; rw [mul_smul_comm, hx]

theorem e_mul_eq_zero_of_mem_normalSpan {j k : ℕ} (h : j ≠ k) {z : Aq K q}
    (hz : z ∈ normalSpan K q k) : e K q j * z = 0 := by
  refine Submodule.span_induction (p := fun w _ => e K q j * w = 0) ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, b, rfl⟩; exact e_mul_normalWord_of_ne h m b
  · rw [mul_zero]
  · intro x y _ _ hx hy; rw [mul_add, hx, hy, add_zero]
  · intro c x _ hx; rw [mul_smul_comm, hx, smul_zero]

theorem e_mul_mem_normalSpan (j : ℕ) {k : ℕ} {z : Aq K q} (hz : z ∈ normalSpan K q k) :
    e K q j * z ∈ normalSpan K q k := by
  rcases eq_or_ne j k with rfl | hjk
  · rw [e_mul_eq_self_of_mem_normalSpan hz]; exact hz
  · rw [e_mul_eq_zero_of_mem_normalSpan hjk hz]; exact zero_mem _

/-! ### Closure under products -/

theorem mul_mul_mem_normalSpan {k : ℕ} {A B : Aq K q}
    (hA : ∀ z ∈ normalSpan K q k, A * z ∈ normalSpan K q k)
    (hB : ∀ z ∈ normalSpan K q k, B * z ∈ normalSpan K q k) :
    ∀ z ∈ normalSpan K q k, A * B * z ∈ normalSpan K q k :=
  fun z hz => by rw [mul_assoc]; exact hA _ (hB z hz)

theorem pow_mul_mem_normalSpan {k : ℕ} {A : Aq K q}
    (hA : ∀ z ∈ normalSpan K q k, A * z ∈ normalSpan K q k) :
    ∀ (n : ℕ) {z : Aq K q}, z ∈ normalSpan K q k → A ^ n * z ∈ normalSpan K q k := by
  intro n
  induction n with
  | zero => intro z hz; rwa [pow_zero, one_mul]
  | succ n ih => intro z hz; rw [pow_succ', mul_assoc]; exact hA _ (ih hz)

/-! ### A loop and a corner element against a normal-form word -/

theorem straighten_mul_mem_normalSpan {k m j n : ℕ} (hj : j + 2 ≤ k) {x : Aq K q}
    (hx : x ∈ Submodule.span K (straightenSet K q (k + m) (j + 1) n)) :
    dMinusPow K q k m * (x * dPlusPow K q (k + m)) ∈ normalSpan K q k := by
  refine Submodule.span_induction
    (p := fun w _ => dMinusPow K q k m * (w * dPlusPow K q (k + m)) ∈ normalSpan K q k)
    ?_ ?_ ?_ ?_ hx
  · rintro w ⟨b, -, hw | hw⟩
    · rw [hw, Nat.add_sub_cancel, mul_assoc, Tg_mul_dPlusPow j (k + m) (by omega),
        ← normalWord_eq]
      exact normalWord_mem_normalSpan k m b
    · rw [hw, ← normalWord_eq]
      exact normalWord_mem_normalSpan k m b
  · rw [zero_mul, mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [add_mul, mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem Tg_mul_mem_normalSpan (j : ℕ) {k : ℕ} {z : Aq K q} (hz : z ∈ normalSpan K q k) :
    Tg K q k j * z ∈ normalSpan K q k := by
  rcases Nat.lt_or_ge (j + 1) k with hjk | hjk
  · refine Submodule.span_induction (p := fun w _ => Tg K q k j * w ∈ normalSpan K q k)
      ?_ ?_ ?_ ?_ hz
    · rintro w ⟨m, b, rfl⟩
      rw [normalWord_eq, ← mul_assoc, Tg_mul_dMinusPow (by omega) m, mul_assoc,
        ← mul_assoc (Tg K q (k + m) j)]
      exact straighten_mul_mem_normalSpan (K := K) (q := q) (k := k) (m := m) (j := j)
        (n := yMonDeg (k + m) b) (by omega)
        (Tg_mul_yMon_mem_span (k := k + m) (i := j + 1) (by omega) (by omega) b)
    · rw [mul_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
    · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  · rw [Tg_eq_zero (by omega), zero_mul]; exact zero_mem _

theorem yElt_mul_mem_normalSpan {k r : ℕ} (h1 : 1 ≤ r) (hrk : r ≤ k) {z : Aq K q}
    (hz : z ∈ normalSpan K q k) : yElt K q k r * z ∈ normalSpan K q k := by
  refine Submodule.span_induction (p := fun w _ => yElt K q k r * w ∈ normalSpan K q k)
    ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, b, rfl⟩
    rw [normalWord_eq, ← mul_assoc, yElt_mul_dMinusPow h1 hrk m, mul_assoc,
      ← mul_assoc (yElt K q (k + m) r),
      ← yMon_of_succ (K := K) (q := q) h1 (by omega : r ≤ k + m)
        (b' := Function.update b r (b r + 1)) (Function.update_self r (b r + 1) b)
        (fun s hs => Function.update_of_ne hs (b r + 1) b),
      ← normalWord_eq]
    exact normalWord_mem_normalSpan k m _
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem Tinv_mul_mem_normalSpan (j : ℕ) {k : ℕ} {z : Aq K q} (hz : z ∈ normalSpan K q k) :
    Tinv K q k j * z ∈ normalSpan K q k := by
  rw [Tinv_eq, smul_mul_assoc, add_mul, smul_mul_assoc]
  exact Submodule.smul_mem _ _
    (add_mem (Tg_mul_mem_normalSpan j hz) (Submodule.smul_mem _ _ (e_mul_mem_normalSpan k hz)))

theorem tSegUp_mul_mem_normalSpan (k a : ℕ) :
    ∀ (n : ℕ) {z : Aq K q}, z ∈ normalSpan K q k → tSegUp K q k a n * z ∈ normalSpan K q k := by
  intro n
  induction n with
  | zero => intro z hz; rw [tSegUp_zero]; exact e_mul_mem_normalSpan k hz
  | succ n ih => intro z hz; rw [tSegUp_succ, mul_assoc]; exact ih (Tg_mul_mem_normalSpan _ hz)

theorem tinvWord_mul_mem_normalSpan (k : ℕ) :
    ∀ (n : ℕ) {z : Aq K q}, z ∈ normalSpan K q k → tinvWord K q k n * z ∈ normalSpan K q k := by
  intro n
  induction n with
  | zero => intro z hz; rw [tinvWord_zero]; exact e_mul_mem_normalSpan k hz
  | succ n ih => intro z hz; rw [tinvWord_succ, mul_assoc]; exact Tinv_mul_mem_normalSpan _ (ih hz)

/-! ### The lowering arrow -/

theorem dMinus_mul_normalWord (k m : ℕ) (b : ℕ → ℕ) :
    dMinus K q k * normalWord K q (k + 1) m b = normalWord K q k (m + 1) b := by
  have hidx : k + 1 + m = k + (m + 1) := by omega
  rw [normalWord_eq, normalWord_eq, ← mul_assoc, ← dMinusPow_succ_left, hidx]

theorem dMinus_mul_mem_normalSpan (k : ℕ) {z : Aq K q} (hz : z ∈ normalSpan K q (k + 1)) :
    dMinus K q k * z ∈ normalSpan K q k := by
  refine Submodule.span_induction (p := fun w _ => dMinus K q k * w ∈ normalSpan K q k)
    ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, b, rfl⟩
    rw [dMinus_mul_normalWord]
    exact normalWord_mem_normalSpan k (m + 1) b
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-! ### The raising arrow -/

theorem dPlus_mul_yElt_pow {k r : ℕ} (h1 : 1 ≤ r) (hrk : r ≤ k) (n : ℕ) :
    dPlus K q k * yElt K q k r ^ n
      = (tSegUp K q (k + 1) 0 r * yElt K q (k + 1) r * tinvWord K q (k + 1) r) ^ n
        * dPlus K q k := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
  | succ n ih =>
    rw [pow_succ' (yElt K q k r), ← mul_assoc, dPlus_mul_yElt r h1 hrk, mul_assoc, ih,
      pow_succ']
    simp only [mul_assoc]

theorem exists_dPlus_mul_yProd (k : ℕ) (b : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) →
      ∃ X : Aq K q, (∀ z ∈ normalSpan K q (k + 1), X * z ∈ normalSpan K q (k + 1)) ∧
        dPlus K q k * yProd K q k b l = X * dPlus K q k := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨1, fun z hz => by rwa [one_mul], by rw [yProd_nil, mul_one, one_mul]⟩
  | cons s t ih =>
    intro hl
    obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
    obtain ⟨X, hX, hXeq⟩ := ih fun r hr => hl r (List.mem_cons_of_mem _ hr)
    have hA : ∀ z ∈ normalSpan K q (k + 1),
        tSegUp K q (k + 1) 0 s * yElt K q (k + 1) s * tinvWord K q (k + 1) s * z
          ∈ normalSpan K q (k + 1) :=
      mul_mul_mem_normalSpan
        (mul_mul_mem_normalSpan (fun z hz => tSegUp_mul_mem_normalSpan (k + 1) 0 s hz)
          (fun z hz => yElt_mul_mem_normalSpan hs1 (by omega) hz))
        (fun z hz => tinvWord_mul_mem_normalSpan (k + 1) s hz)
    refine ⟨(tSegUp K q (k + 1) 0 s * yElt K q (k + 1) s * tinvWord K q (k + 1) s) ^ b s * X,
      fun z hz => ?_, ?_⟩
    · rw [mul_assoc]
      exact pow_mul_mem_normalSpan hA (b s) (hX z hz)
    · rw [yProd_cons, ← mul_assoc, dPlus_mul_yElt_pow hs1 hsk, mul_assoc, hXeq, ← mul_assoc]

theorem dPlus_mul_normalWord_mem_normalSpan :
    ∀ (m k : ℕ) (b : ℕ → ℕ),
      dPlus K q k * normalWord K q k m b ∈ normalSpan K q (k + 1) := by
  intro m
  induction m with
  | zero =>
    intro k b
    obtain ⟨X, hX, hXeq⟩ := exists_dPlus_mul_yProd (K := K) (q := q) k b (List.range' 1 k)
      fun s hs => mem_range'_one_bounds hs
    have hstep : dPlus K q k * normalWord K q k 0 b = X * dPlusPow K q (k + 1) := by
      rw [normalWord_eq, dMinusPow_zero, Nat.add_zero, ← mul_assoc, dPlus_mul_e, ← mul_assoc,
        yMon, hXeq, mul_assoc, ← dPlusPow_succ]
    rw [hstep]
    exact hX _ (dPlusPow_mem_normalSpan (k + 1))
  | succ m ih =>
    intro k b
    have hcomm : dPlus K q k * dMinus K q k
        = Delta K q k + dMinus K q (k + 1) * dPlus K q (k + 1) := by
      rw [Delta_eq]; abel
    have hDelta : Delta K q k
        = (q - 1) • (tSegUp K q (k + 1) 0 k * yElt K q (k + 1) (k + 1)) := by
      have h := Delta_eq_smul_tSegUp_mul_yElt (K := K) (q := q) (k := k + 1) (by omega)
      rwa [Nat.add_sub_cancel] at h
    rw [← dMinus_mul_normalWord, ← mul_assoc, hcomm, add_mul, hDelta, smul_mul_assoc]
    refine add_mem (Submodule.smul_mem _ _ ?_) ?_
    · exact mul_mul_mem_normalSpan (fun z hz => tSegUp_mul_mem_normalSpan (k + 1) 0 k hz)
        (fun z hz => yElt_mul_mem_normalSpan (by omega) le_rfl hz) _
        (normalWord_mem_normalSpan (k + 1) m b)
    · rw [mul_assoc]
      exact dMinus_mul_mem_normalSpan (k + 1) (ih (k + 1) b)

theorem dPlus_mul_mem_normalSpan (k : ℕ) {z : Aq K q} (hz : z ∈ normalSpan K q k) :
    dPlus K q k * z ∈ normalSpan K q (k + 1) := by
  refine Submodule.span_induction (p := fun w _ => dPlus K q k * w ∈ normalSpan K q (k + 1))
    ?_ ?_ ?_ ?_ hz
  · rintro w ⟨m, b, rfl⟩; exact dPlus_mul_normalWord_mem_normalSpan m k b
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-! ### Every path from the vertex `0` is a combination of normal-form words -/

theorem gen_mul_mem_iSup_normalSpan (g : Gen) {z : Aq K q} (hz : z ∈ ⨆ k, normalSpan K q k) :
    mk K q (FreeAlgebra.ι K g) * z ∈ ⨆ k, normalSpan K q k := by
  refine Submodule.iSup_induction (normalSpan K q)
    (motive := fun w => mk K q (FreeAlgebra.ι K g) * w ∈ ⨆ k, normalSpan K q k) hz ?_ ?_ ?_
  · intro j y hy
    cases g with
    | vertex l =>
      change e K q l * y ∈ ⨆ k, normalSpan K q k
      exact Submodule.mem_iSup_of_mem j (e_mul_mem_normalSpan l hy)
    | up l =>
      change dPlus K q l * y ∈ ⨆ k, normalSpan K q k
      rcases eq_or_ne l j with rfl | hlj
      · exact Submodule.mem_iSup_of_mem (l + 1) (dPlus_mul_mem_normalSpan l hy)
      · rw [← dPlus_mul_e l, mul_assoc, e_mul_eq_zero_of_mem_normalSpan hlj hy, mul_zero]
        exact zero_mem _
    | down l =>
      change dMinus K q l * y ∈ ⨆ k, normalSpan K q k
      rcases eq_or_ne (l + 1) j with rfl | hlj
      · exact Submodule.mem_iSup_of_mem l (dMinus_mul_mem_normalSpan l hy)
      · rw [← dMinus_mul_e l, mul_assoc, e_mul_eq_zero_of_mem_normalSpan hlj hy, mul_zero]
        exact zero_mem _
    | braid l i =>
      change Tg K q l i * y ∈ ⨆ k, normalSpan K q k
      rcases eq_or_ne l j with rfl | hlj
      · exact Submodule.mem_iSup_of_mem l (Tg_mul_mem_normalSpan i hy)
      · rw [← Tg_mul_e l i, mul_assoc, e_mul_eq_zero_of_mem_normalSpan hlj hy, mul_zero]
        exact zero_mem _
  · rw [mul_zero]; exact zero_mem _
  · intro x y hx hy; rw [mul_add]; exact add_mem hx hy

theorem mk_mul_mem_iSup_normalSpan (y : FreeAlgebra K Gen) {z : Aq K q}
    (hz : z ∈ ⨆ k, normalSpan K q k) : mk K q y * z ∈ ⨆ k, normalSpan K q k := by
  induction y using FreeAlgebra.induction generalizing z with
  | grade0 r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ r hz
  | grade1 g => exact gen_mul_mem_iSup_normalSpan g hz
  | mul a b ha hb => rw [map_mul, mul_assoc]; exact ha (hb hz)
  | add a b ha hb => rw [map_add, add_mul]; exact add_mem (ha hz) (hb hz)

theorem e_mul_mem_normalSpan_of_mem_iSup (k : ℕ) {w : Aq K q}
    (hw : w ∈ ⨆ j, normalSpan K q j) : e K q k * w ∈ normalSpan K q k := by
  refine Submodule.iSup_induction (normalSpan K q)
    (motive := fun w => e K q k * w ∈ normalSpan K q k) hw ?_ ?_ ?_
  · intro j y hy
    rcases eq_or_ne k j with rfl | hkj
    · rw [e_mul_eq_self_of_mem_normalSpan hy]; exact hy
    · rw [e_mul_eq_zero_of_mem_normalSpan hkj hy]; exact zero_mem _
  · rw [mul_zero]; exact zero_mem _
  · intro x y hx hy; rw [mul_add]; exact add_mem hx hy

theorem e_mul_mul_e_zero_mem_normalSpan (k : ℕ) (x : Aq K q) :
    e K q k * x * e K q 0 ∈ normalSpan K q k := by
  obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective K (Rel K q) x
  rw [mul_assoc]
  refine e_mul_mem_normalSpan_of_mem_iSup k ?_
  change mk K q y * e K q 0 ∈ _
  exact mk_mul_mem_iSup_normalSpan y (Submodule.mem_iSup_of_mem 0 e_zero_mem_normalSpan_zero)

/-! ### The weight of a corner monomial -/

/-- The weight `∑_s s·b_s` of a corner monomial. -/
def yMonWt (n : ℕ) (b : ℕ → ℕ) : ℕ := ∑ s ∈ Finset.Icc 1 n, s * b s

theorem yMonWt_update_succ {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) (b : ℕ → ℕ) :
    yMonWt n (Function.update b r (b r + 1)) = yMonWt n b + r := by
  have hr : r ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hr1, hrn⟩
  have htail : ∑ s ∈ (Finset.Icc 1 n).erase r, s * Function.update b r (b r + 1) s
      = ∑ s ∈ (Finset.Icc 1 n).erase r, s * b s :=
    Finset.sum_congr rfl fun s hs => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  rw [yMonWt, yMonWt, ← Finset.add_sum_erase _ _ hr, ← Finset.add_sum_erase _ _ hr,
    Function.update_self, htail]
  ring

theorem yMonWt_peel {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {b : ℕ → ℕ} (h : 1 ≤ b r) :
    yMonWt n b = yMonWt n (Function.update b r (b r - 1)) + r := by
  have hc : Function.update (Function.update b r (b r - 1)) r
      (Function.update b r (b r - 1) r + 1) = b := by
    funext s
    by_cases hs : s = r
    · subst hs; rw [Function.update_self, Function.update_self]; omega
    · rw [Function.update_of_ne hs, Function.update_of_ne hs]
  have hstep := yMonWt_update_succ (n := n) hr1 hrn (Function.update b r (b r - 1))
  rwa [hc] at hstep

theorem yMon_peel {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) {b : ℕ → ℕ} (h : 1 ≤ b r) :
    yMon K q n b = yElt K q n r * yMon K q n (Function.update b r (b r - 1)) :=
  yMon_of_succ hr1 hrn (by rw [Function.update_self]; omega)
    (fun s hs => (Function.update_of_ne hs _ _).symm)

theorem yMon_push {n r : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n) (b : ℕ → ℕ) :
    yElt K q n r * yMon K q n b = yMon K q n (Function.update b r (b r + 1)) :=
  (yMon_of_succ hr1 hrn (Function.update_self r (b r + 1) b)
    (fun _ hs => Function.update_of_ne hs (b r + 1) b)).symm

/-! ### The straightening that strictly lowers the weight -/

/-- The words a weight-lowering straightening step may produce: a corner monomial of weight below
`w`, with or without the loop `T_i` on the right. -/
noncomputable def lowerStraightenSet (K : Type*) [CommRing K] (q : K) [Invertible q]
    [Invertible (q - 1)] (n i w : ℕ) : Set (Aq K q) :=
  {x | ∃ b : ℕ → ℕ, yMonWt n b < w ∧
    (x = yMon K q n b * Tg K q n (i - 1) ∨ x = yMon K q n b)}

theorem span_lowerStraightenSet_mono {n i w w' : ℕ} (h : w ≤ w') :
    Submodule.span K (lowerStraightenSet K q n i w)
      ≤ Submodule.span K (lowerStraightenSet K q n i w') :=
  Submodule.span_mono fun _ ⟨b, hb, hx⟩ => ⟨b, lt_of_lt_of_le hb h, hx⟩

theorem yElt_mul_mem_span_lowerStraightenSet {n i r w : ℕ} (hr1 : 1 ≤ r) (hrn : r ≤ n)
    {x : Aq K q} (hx : x ∈ Submodule.span K (lowerStraightenSet K q n i w)) :
    yElt K q n r * x ∈ Submodule.span K (lowerStraightenSet K q n i (w + r)) := by
  refine Submodule.span_induction
    (p := fun y _ => yElt K q n r * y
      ∈ Submodule.span K (lowerStraightenSet K q n i (w + r))) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨b, hb, hy | hy⟩
    · rw [hy, ← mul_assoc, yMon_push hr1 hrn]
      exact Submodule.subset_span
        ⟨_, by rw [yMonWt_update_succ hr1 hrn]; omega, Or.inl rfl⟩
    · rw [hy, yMon_push hr1 hrn]
      exact Submodule.subset_span
        ⟨_, by rw [yMonWt_update_succ hr1 hrn]; omega, Or.inr rfl⟩
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

/-- **A loop against a corner monomial whose exponents rise across the loop.** When
`b_i < b_{i+1}` the straightening of `HJO.Dyck.Aq.Tg_mul_yMon_mem_span` may be run so that every
monomial it produces has strictly smaller weight `∑ s·b_s`: the swap `b_i ↔ b_{i+1}` lowers the
weight by `b_{i+1} - b_i` and each Hecke correction lowers it by at least one. -/
theorem Tg_mul_yMon_mem_span_lowerStraightenSet {n i : ℕ} (h1 : 1 ≤ i) (hin : i < n) :
    ∀ (N : ℕ) (b : ℕ → ℕ), b i + b (i + 1) ≤ N → b i < b (i + 1) →
      Tg K q n (i - 1) * yMon K q n b
        ∈ Submodule.span K (lowerStraightenSet K q n i (yMonWt n b)) := by
  intro N
  induction N with
  | zero => intro b hN hlt; omega
  | succ N ih =>
    intro b hN hlt
    rcases Nat.eq_zero_or_pos (b i) with hbi | hbi
    · -- `y_i` is absent: peel one `y_{i+1}`.
      set c := Function.update b (i + 1) (b (i + 1) - 1) with hcdef
      have hci : c i = b i := Function.update_of_ne (by omega) _ _
      have hci1 : c (i + 1) = b (i + 1) - 1 := Function.update_self _ _ _
      have hsplit : yMon K q n b = yElt K q n (i + 1) * yMon K q n c :=
        yMon_peel (by omega) (by omega) (by omega)
      have hwt : yMonWt n b = yMonWt n c + (i + 1) :=
        yMonWt_peel (by omega) (by omega) (by omega)
      have hd : yMonWt n (Function.update c i (c i + 1)) = yMonWt n c + i :=
        yMonWt_update_succ h1 (by omega) c
      have key : Tg K q n (i - 1) * yMon K q n b
          = yElt K q n i * (Tg K q n (i - 1) * yMon K q n c)
            + (q - 1) • (yElt K q n i * yMon K q n c) := by
        rw [hsplit, ← mul_assoc (Tg K q n (i - 1)) (yElt K q n (i + 1)) (yMon K q n c),
          Tg_mul_yElt_succ h1 hin, add_mul, smul_mul_assoc]
        simp only [mul_assoc]
      rw [key]
      refine add_mem ?_ (Submodule.smul_mem _ _ ?_)
      · rcases Nat.lt_or_ge 1 (b (i + 1)) with hb2 | hb2
        · have hinner := ih c (by omega) (by omega)
          refine span_lowerStraightenSet_mono (by omega)
            (yElt_mul_mem_span_lowerStraightenSet h1 (by omega) hinner)
        · have hcomm : Commute (Tg K q n (i - 1)) (yMon K q n c) :=
            commute_Tg_yProd h1 hin (by omega) (by omega) _
              fun _ hs => mem_range'_one_bounds hs
          rw [hcomm.eq, ← mul_assoc, yMon_push h1 (by omega)]
          exact Submodule.subset_span ⟨_, by omega, Or.inl rfl⟩
      · rw [yMon_push h1 (by omega)]
        exact Submodule.subset_span ⟨_, by omega, Or.inr rfl⟩
    · -- `y_i` is present: peel the pair `y_iy_{i+1}`, which the loop commutes with.
      set c1 := Function.update b i (b i - 1) with hc1def
      have hc1i : c1 i = b i - 1 := Function.update_self _ _ _
      have hc1i1 : c1 (i + 1) = b (i + 1) := Function.update_of_ne (by omega) _ _
      set c := Function.update c1 (i + 1) (c1 (i + 1) - 1) with hcdef
      have hci : c i = b i - 1 := by rw [hcdef, Function.update_of_ne (by omega), hc1i]
      have hci1 : c (i + 1) = b (i + 1) - 1 := by
        rw [hcdef, Function.update_self, hc1i1]
      have hsplit1 : yMon K q n b = yElt K q n i * yMon K q n c1 :=
        yMon_peel h1 (by omega) (by omega)
      have hsplit2 : yMon K q n c1 = yElt K q n (i + 1) * yMon K q n c :=
        yMon_peel (by omega) (by omega) (by omega)
      have hwt1 : yMonWt n b = yMonWt n c1 + i := yMonWt_peel h1 (by omega) (by omega)
      have hwt2 : yMonWt n c1 = yMonWt n c + (i + 1) :=
        yMonWt_peel (by omega) (by omega) (by omega)
      have hpair : Commute (Tg K q n (i - 1)) (yElt K q n i * yElt K q n (i + 1)) :=
        Tg_mul_yElt_pair h1 hin
      have key : Tg K q n (i - 1) * yMon K q n b
          = yElt K q n i * (yElt K q n (i + 1) * (Tg K q n (i - 1) * yMon K q n c)) := by
        rw [hsplit1, hsplit2,
          show yElt K q n i * (yElt K q n (i + 1) * yMon K q n c)
            = yElt K q n i * yElt K q n (i + 1) * yMon K q n c from (mul_assoc _ _ _).symm,
          ← mul_assoc, hpair.eq]
        simp only [mul_assoc]
      rw [key, hwt1, hwt2]
      have hinner := ih c (by omega) (by omega)
      exact yElt_mul_mem_span_lowerStraightenSet h1 (by omega)
        (yElt_mul_mem_span_lowerStraightenSet (by omega) (by omega) hinner)

/-! ### The sorted normal-form words span -/

/-- The span of the normal-form words whose corner exponents above the vertex `k` are weakly
decreasing. -/
noncomputable def sortedNormalSpan (K : Type*) [CommRing K] (q : K) [Invertible q]
    [Invertible (q - 1)] (k : ℕ) : Submodule K (Aq K q) :=
  Submodule.span K {x | ∃ m b, (∀ j, k + 1 ≤ j → j + 1 ≤ k + m → b (j + 1) ≤ b j) ∧
    x = normalWord K q k m b}

theorem lowerStraighten_mul_mem_span {k m j w : ℕ} (hj0 : 1 ≤ j) (hj : j + 1 ≤ k + m)
    {x : Aq K q}
    (hx : x ∈ Submodule.span K (lowerStraightenSet K q (k + m) j w)) :
    dMinusPow K q k m * (x * dPlusPow K q (k + m))
      ∈ Submodule.span K {y | ∃ b', yMonWt (k + m) b' < w ∧ y = normalWord K q k m b'} := by
  refine Submodule.span_induction
    (p := fun z _ => dMinusPow K q k m * (z * dPlusPow K q (k + m))
      ∈ Submodule.span K {y | ∃ b', yMonWt (k + m) b' < w ∧ y = normalWord K q k m b'})
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨b, hb, hz | hz⟩
    · rw [hz, mul_assoc, Tg_mul_dPlusPow (j - 1) (k + m) (by omega), ← normalWord_eq]
      exact Submodule.subset_span ⟨b, hb, rfl⟩
    · rw [hz, ← normalWord_eq]
      exact Submodule.subset_span ⟨b, hb, rfl⟩
  · rw [zero_mul, mul_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [add_mul, mul_add]; exact add_mem hx hy
  · intro c x _ hx; rw [smul_mul_assoc, mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem normalWord_mem_span_lower {k m j : ℕ} (hj1 : k + 1 ≤ j) (hj2 : j + 1 ≤ k + m)
    (b : ℕ → ℕ) (hlt : b j < b (j + 1)) :
    normalWord K q k m b
      ∈ Submodule.span K {y | ∃ b', yMonWt (k + m) b' < yMonWt (k + m) b
          ∧ y = normalWord K q k m b'} := by
  have hTg : dMinusPow K q k m * Tg K q (k + m) (j - 1) = dMinusPow K q k m :=
    dMinusPow_mul_Tg (by omega) m (by omega)
  have hkey : normalWord K q k m b
      = dMinusPow K q k m * ((Tg K q (k + m) (j - 1) * yMon K q (k + m) b)
          * dPlusPow K q (k + m)) := by
    conv_lhs => rw [normalWord_eq, ← hTg]
    simp only [mul_assoc]
  rw [hkey]
  exact lowerStraighten_mul_mem_span (j := j) (by omega) (by omega)
    (Tg_mul_yMon_mem_span_lowerStraightenSet (n := k + m) (i := j) (by omega) (by omega)
      (b j + b (j + 1)) b le_rfl hlt)

/-- **Every normal-form word is a combination of sorted ones.** The measure is the weight
`∑ s·b_s` of the corner monomial: the exchange inside `d₋^m(-)d₊^{k+m}𝟏_0`, available because
`d₋^mT_j = d₋^m`, replaces an ascending pair of exponents by monomials of strictly smaller
weight. -/
theorem normalWord_mem_sortedNormalSpan (k m : ℕ) :
    ∀ (w : ℕ) (b : ℕ → ℕ), yMonWt (k + m) b ≤ w →
      normalWord K q k m b ∈ sortedNormalSpan K q k := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b hb
    by_cases hsorted : ∀ j, k + 1 ≤ j → j + 1 ≤ k + m → b (j + 1) ≤ b j
    · exact Submodule.subset_span ⟨m, b, hsorted, rfl⟩
    · push Not at hsorted
      obtain ⟨j, hj1, hj2, hjlt⟩ := hsorted
      refine Submodule.span_le.2 ?_ (normalWord_mem_span_lower hj1 hj2 b hjlt)
      rintro y ⟨b', hb', rfl⟩
      exact ih (yMonWt (k + m) b') (lt_of_lt_of_le hb' hb) b' le_rfl

theorem normalSpan_le_sortedNormalSpan (k : ℕ) : normalSpan K q k ≤ sortedNormalSpan K q k := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, b, rfl⟩
  exact normalWord_mem_sortedNormalSpan k m (yMonWt (k + m) b) b le_rfl

/-- **Every path from the vertex `0` to the vertex `k` is a combination of sorted normal-form
words.** -/
theorem e_mul_mul_e_zero_mem_sortedNormalSpan (k : ℕ) (x : Aq K q) :
    e K q k * x * e K q 0 ∈ sortedNormalSpan K q k :=
  normalSpan_le_sortedNormalSpan k (e_mul_mul_e_zero_mem_normalSpan k x)

/-! ### The left ideal and the corners, read against the normal forms -/

/-- **`𝔸_q𝟏_0` is spanned by the normal-form words.** -/
theorem e0Ideal_le_iSup_normalSpan : e0Ideal K q ≤ ⨆ k, normalSpan K q k := by
  rintro x hx
  obtain ⟨y, rfl⟩ := mem_e0Ideal_iff.1 hx
  obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective K (Rel K q) y
  change mk K q z * e K q 0 ∈ _
  exact mk_mul_mem_iSup_normalSpan z (Submodule.mem_iSup_of_mem 0 e_zero_mem_normalSpan_zero)

/-- **`𝔸_q𝟏_0` is spanned by the sorted normal-form words**, the normal form of Carlsson and
Mellit's Lemma 5.4. -/
theorem e0Ideal_le_iSup_sortedNormalSpan : e0Ideal K q ≤ ⨆ k, sortedNormalSpan K q k :=
  le_trans e0Ideal_le_iSup_normalSpan (iSup_mono normalSpan_le_sortedNormalSpan)

/-- **`𝟏_k𝔸_q𝟏_0` is spanned by the sorted normal-form words at the vertex `k`.** -/
theorem cornerE0_le_sortedNormalSpan (k : ℕ) : cornerE0 K q k ≤ sortedNormalSpan K q k := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_cornerE0_iff.1 hx
  exact e_mul_mul_e_zero_mem_sortedNormalSpan k y

end HJO.Dyck.Aq

namespace HJO.Sweep

/-! ### The evaluation map -/

section Eval

variable {L : Type*} [Field L] {q : L} (ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L))

/-- **The evaluation map `f ↦ f(1)`**, of which the map `f𝟏_0 ↦ f(1)` is the restriction
to `𝔸_q𝟏_0`: since `ρ(𝟏_0)` fixes `1 ∈ V_0`, the two agree there. -/
noncomputable def evalOneAq : Dyck.Aq L q →ₗ[L] Vstar L where
  toFun x := ρ x (oneVstar L)
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

@[simp]
theorem evalOneAq_apply (x : Dyck.Aq L q) : evalOneAq ρ x = ρ x (oneVstar L) := rfl

/-- **The evaluation map is `𝔸_q`-equivariant.** -/
theorem evalOneAq_mul (x y : Dyck.Aq L q) : evalOneAq ρ (x * y) = ρ x (evalOneAq ρ y) := by
  rw [evalOneAq_apply, map_mul]
  rfl

/-- **The evaluation map sends `𝟏_0` to `1 ∈ V_0`.** -/
theorem evalOneAq_e_zero (hact : IsDpaAction q ρ) : evalOneAq ρ (Dyck.Aq.e L q 0) = oneVstar L := by
  rw [evalOneAq_apply, hact.map_e]
  exact pieceProj_ofPiece 0 _

end Eval

/-! ### The unit of a summand, and elementary memberships -/

section Unit

variable {L : Type*} [Field L]

/-- **`1 ∈ V_k`, read in the `k`-th summand of `V_*`.** -/
noncomputable def oneAtPiece (L : Type*) [Field L] (k : ℕ) : pieceSub L k :=
  ⟨1, one_mem (piece L k)⟩

@[simp]
theorem coe_oneAtPiece (k : ℕ) : (oneAtPiece L k : Total L) = 1 := rfl

theorem oneVstar_eq_ofPiece : oneVstar L = ofPiece L 0 (oneAtPiece L 0) := rfl

/-- **An element of `Λ`, read as a constant, lies in every graded piece.** -/
theorem algebraMap_mem_piece (f : Sym.Lambda L) (k : ℕ) :
    algebraMap (Sym.Lambda L) (Total L) f ∈ piece L k :=
  piece_mono (Nat.zero_le k) ((piece L 0).algebraMap_mem f)

/-- **A monomial in the variables `y_1, …, y_k` lies in `V_k`.** -/
theorem prod_auxVar_mem_piece {k : ℕ} (a : Fin k →₀ ℕ) :
    (a.prod fun j n => (auxVar ((j : ℕ) + 1) : Total L) ^ n) ∈ piece L k := by
  rw [Finsupp.prod]
  exact prod_mem fun j _ => pow_mem (auxVar_mem_piece (Nat.le_add_left 1 _) j.2) _

theorem auxVar_pow_mul_mem_piece {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (n : ℕ) {G : Total L}
    (hG : G ∈ piece L k) : (auxVar i : Total L) ^ n * G ∈ piece L k :=
  mul_mem (pow_mem (auxVar_mem_piece h1 hik) n) hG

/-- **The projection onto `V_k` lands in `V_k`.** -/
theorem pieceProj_mem_range_ofPiece (k : ℕ) (v : Vstar L) :
    pieceProj L k v ∈ LinearMap.range (ofPiece L k) :=
  ⟨toPiece L k v, (pieceProj_apply k v).symm⟩

end Unit

/-! ### Transporting the image along a path -/

section Transport

variable {L : Type*} [Field L] {q : L} {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)}
  (hact : IsDpaAction q ρ)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)

include hact hU in
/-- **`d_+^k𝟏_0` evaluates to `1 ∈ V_k`**, the raising operator of `HJO.Sweep.cmDPlus` fixing `1` at
every vertex by `HJO.Sweep.cmDPlus_map_one`. -/
theorem evalOneAq_dPlusPow (k : ℕ) :
    evalOneAq ρ (Dyck.Aq.dPlusPow L q k) = ofPiece L k (oneAtPiece L k) := by
  induction k with
  | zero =>
    rw [show Dyck.Aq.dPlusPow L q 0 = Dyck.Aq.e L q 0 from rfl, evalOneAq_e_zero ρ hact,
      oneVstar_eq_ofPiece]
  | succ k ih =>
    rw [Dyck.Aq.dPlusPow_succ, evalOneAq_mul, ih, hU, raiseVstar_ofPiece]
    congr 1
    exact Subtype.ext (by simp only [coe_cmDPlusPiece, coe_oneAtPiece, cmDPlus_map_one])

/-- **A path from `k` to `j` carries the image of `𝟏_k𝔸_q𝟏_0` into the image of `𝟏_j𝔸_q𝟏_0`.** -/
theorem mem_map_evalOneAq_cornerE0 {j k : ℕ} {a : Dyck.Aq L q}
    (ha : Dyck.Aq.e L q j * a * Dyck.Aq.e L q k = a) {v : Vstar L}
    (hv : v ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k)) :
    ρ a v ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q j) := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨a * x, Dyck.Aq.mul_mem_cornerE0 ha hx, evalOneAq_mul ρ a x⟩

include hact in
/-- **The evaluation map carries `𝟏_k𝔸_q𝟏_0` into `V_k`**, which is the grading by vertex of
`HJO.Sweep.IsDpaAction`. -/
theorem map_evalOneAq_cornerE0_le (k : ℕ) :
    Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) ≤ LinearMap.range (ofPiece L k) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := Dyck.Aq.mem_cornerE0_iff.1 hx
  have hval : evalOneAq ρ x = pieceProj L k (ρ (y * Dyck.Aq.e L q 0) (oneVstar L)) := by
    rw [evalOneAq_apply, ← hy, mul_assoc, map_mul, hact.map_e]
    rfl
  rw [hval]
  exact pieceProj_mem_range_ofPiece k _

end Transport

/-! ### Every monomial of `HJO.Sweep.exists_basis_vstar_prod_bop` is in the image -/

section Image

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)} (hact : IsDpaAction q ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)

include hact hT hD hU in
/-- **Multiplication by `y_i` preserves the image of `𝟏_k𝔸_q𝟏_0`**, the corner element `y_i` of
`HJO.Dyck.Aq.yElt` being a path from `k` to `k` which acts by multiplication by the variable. -/
theorem auxMulPiece_mem_map_evalOneAq_cornerE0 {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k)
    {F : pieceSub L k}
    (hF : ofPiece L k F ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k)) :
    ofPiece L k (auxMulPiece L k i F)
      ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  have h := mem_map_evalOneAq_cornerE0 (a := Dyck.Aq.yElt L q k i)
    (Dyck.Aq.e_mul_yElt_mul_e k i) hF
  rwa [map_yElt_eq_auxMulPiece_cm hact hT hD hU h1 hik, loopVstar_ofPiece] at h

omit [Invertible q] [Invertible (q - 1)] in
include hD in
/-- **The lowering arrow carries the image of `𝟏_{k+1}𝔸_q𝟏_0` into the image of
`𝟏_k𝔸_q𝟏_0`.** -/
theorem dminusPiece_mem_map_evalOneAq_cornerE0 {k : ℕ} {F : pieceSub L (k + 1)}
    (hF : ofPiece L (k + 1) F ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q (k + 1))) :
    ofPiece L k (dminusPiece q k F)
      ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  have h := mem_map_evalOneAq_cornerE0 (a := Dyck.Aq.dMinus L q k)
    (by rw [Dyck.Aq.e_mul_dMinus, Dyck.Aq.dMinus_mul_e]) hF
  rwa [hD, lowerVstar_ofPiece] at h

include hact hT hD hU in
/-- **A power of one variable times an element of the image is in the image.** -/
theorem auxVar_pow_mul_mem_map_evalOneAq_cornerE0 {k i : ℕ} (h1 : 1 ≤ i) (hik : i ≤ k) (n : ℕ)
    (G : pieceSub L k)
    (hG : ofPiece L k G ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k)) :
    ∀ F : pieceSub L k, (F : Total L) = (auxVar i : Total L) ^ n * G →
      ofPiece L k F ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  induction n with
  | zero =>
    intro F hF
    rw [pow_zero, one_mul] at hF
    rwa [Subtype.ext hF]
  | succ n ih =>
    intro F hF
    have hmem : (auxVar i : Total L) ^ n * (G : Total L) ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece
        (auxVar_pow_mul_mem_piece h1 hik n (mem_piece_of_mem_pieceSub G.2))
    have h := ih ⟨_, hmem⟩ rfl
    have hF' : F = auxMulPiece L k i ⟨(auxVar i : Total L) ^ n * (G : Total L), hmem⟩ := by
      refine Subtype.ext ?_
      rw [coe_auxMulPiece h1 hik, hF, pow_succ',
        mul_assoc (auxVar i : Total L) ((auxVar i : Total L) ^ n) (G : Total L)]
    rw [hF']
    exact auxMulPiece_mem_map_evalOneAq_cornerE0 hact hT hD hU h1 hik h

include hact hT hD hU in
/-- **A monomial in the variables times an element of the image is in the image**: the head
`y_1^{a_1} ⋯ y_k^{a_k}` of a basis vector of `HJO.Sweep.exists_basis_vstar_prod_bop` is produced
inside the corner `𝟏_k𝔸_q𝟏_k`. -/
theorem prod_auxVar_mul_mem_map_evalOneAq_cornerE0 {k : ℕ} (a : Fin k →₀ ℕ) :
    ∀ F G : pieceSub L k,
      ofPiece L k G ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) →
      (F : Total L) = (a.prod fun j n => (auxVar ((j : ℕ) + 1) : Total L) ^ n) * G →
      ofPiece L k F ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  refine Finsupp.induction a ?_ ?_
  · intro F G hG hF
    rw [Finsupp.prod_zero_index, one_mul] at hF
    rwa [Subtype.ext hF]
  · intro i n b _ _ ih F G hG hF
    have hprod : ((Finsupp.single i n + b).prod
          fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
        = (auxVar ((i : ℕ) + 1) : Total L) ^ n *
          (b.prod fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m) := by
      rw [Finsupp.prod_add_index'
          (h := fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
          (fun j => pow_zero _) (fun j m₁ m₂ => pow_add _ m₁ m₂),
        Finsupp.prod_single_index
          (h := fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m) (pow_zero _)]
    have hmem : (b.prod fun j m => (auxVar ((j : ℕ) + 1) : Total L) ^ m) * (G : Total L)
        ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece
        (mul_mem (prod_auxVar_mem_piece b) (mem_piece_of_mem_pieceSub G.2))
    refine auxVar_pow_mul_mem_map_evalOneAq_cornerE0 hact hT hD hU (Nat.le_add_left 1 _) i.2 n
      ⟨_, hmem⟩ (ih _ G hG rfl) F ?_
    rw [hF, hprod, mul_assoc]

include hact hT hD hU in
/-- **Every Hall--Littlewood monomial of `HJO.Sweep.exists_basis_vstar_prod_bop` is in the image of
`𝟏_k𝔸_q𝟏_0`.** The induction is on the list, which raises the vertex by one at each step: the
innermost `1` is the word `d_+^j𝟏_0` at the vertex `j = k + m` the descent starts from, by
`HJO.Sweep.evalOneAq_dPlusPow`; one Hall--Littlewood operator is one lowering arrow applied to one
power of the last variable, by `HJO.Sweep.dminusCM_auxVar_pow_mul`; and the head monomial is the
corner elements acting. -/
theorem ofPiece_mem_map_evalOneAq_cornerE0 :
    ∀ (l : List ℕ) (k : ℕ) (a : Fin k →₀ ℕ) (F : pieceSub L k),
      (F : Total L) = (a.prod fun j n => (auxVar ((j : ℕ) + 1) : Total L) ^ n) *
        algebraMap (Sym.Lambda L) (Total L)
          (((l.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1) →
      ofPiece L k F ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  intro l
  induction l with
  | nil =>
    intro k a F hF
    refine prod_auxVar_mul_mem_map_evalOneAq_cornerE0 hact hT hD hU a F (oneAtPiece L k)
      ⟨Dyck.Aq.dPlusPow L q k, Dyck.Aq.dPlusPow_mem_cornerE0 k,
        evalOneAq_dPlusPow hact hU k⟩ ?_
    rw [hF, coe_oneAtPiece, mul_one]
    simp
  | cons r l ih =>
    intro k a F hF
    obtain ⟨g, hg⟩ : ∃ g : Sym.Lambda L,
        ((l.map (· + 1)).map fun s : ℕ => Sym.Bop q (s : ℤ)).prod 1 = g := ⟨_, rfl⟩
    rw [hg] at ih
    have hcast : ((r + 1 : ℕ) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
    have hhead : ((((r :: l).map (· + 1)).map fun s : ℕ => Sym.Bop q (s : ℤ)).prod 1
        : Sym.Lambda L) = Sym.Bop q ((r : ℤ) + 1) g := by
      rw [List.map_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, hcast, hg]
    -- the element `y_{k+1}^r·g` of `V_{k+1}`, and its image under the lowering arrow
    have hmem : (auxVar (k + 1) : Total L) ^ r * algebraMap (Sym.Lambda L) (Total L) g
        ∈ pieceSub L (k + 1) :=
      mem_pieceSub_of_mem_piece
        (auxVar_pow_mul_mem_piece (Nat.le_add_left 1 k) le_rfl r (algebraMap_mem_piece g (k + 1)))
    have hmem2 : algebraMap (Sym.Lambda L) (Total L) (Sym.Bop q ((r : ℤ) + 1) g) ∈ pieceSub L k :=
      mem_pieceSub_of_mem_piece (algebraMap_mem_piece _ k)
    have hstep : ofPiece L (k + 1) ⟨_, hmem⟩
        ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q (k + 1)) := by
      refine ih (k + 1) (Finsupp.single (Fin.last k) r) ⟨_, hmem⟩ ?_
      rw [Finsupp.prod_single_index
        (h := fun (j : Fin (k + 1)) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
        (pow_zero _), Fin.val_last]
    have hlower := dminusPiece_mem_map_evalOneAq_cornerE0 hD hstep
    have hBopval : (dminusPiece q k ⟨_, hmem⟩ : Total L)
        = -algebraMap (Sym.Lambda L) (Total L) (Sym.Bop q ((r : ℤ) + 1) g) := by
      rw [coe_dminusPiece, dminusCM_auxVar_pow_mul q k r (algebraMap_mem_piece g k)]
      congr 1
      rw [MvPolynomial.algebraMap_eq, bopExt_C]
    have hBop : dminusPiece q k ⟨_, hmem⟩ = -(⟨_, hmem2⟩ : pieceSub L k) :=
      Subtype.ext (by rw [NegMemClass.coe_neg]; exact hBopval)
    rw [hBop, map_neg] at hlower
    have hpos : ofPiece L k ⟨_, hmem2⟩
        ∈ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
      have h := neg_mem hlower
      rwa [neg_neg] at h
    refine prod_auxVar_mul_mem_map_evalOneAq_cornerE0 hact hT hD hU a F ⟨_, hmem2⟩ hpos ?_
    rw [hF, hhead]

end Image

/-! ### The image of `𝟏_k𝔸_q𝟏_0` is `V_k` -/

section Onto

variable {L : Type*} [Field L] [Algebra ℚ L] {q : L} [Invertible q] [Invertible (q - 1)]
  {ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L)} (hact : IsDpaAction q ρ)
  (hT : ∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar (braidModPiece q) k i)
  (hD : ∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar (dminusPiece q) k)
  (hU : ∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar (cmDPlusPiece q) k)

include hact hT hD hU in
/-- **The evaluation map carries `𝟏_k𝔸_q𝟏_0` onto `V_k`**: every basis vector of
`HJO.Sweep.exists_basis_vstar_prod_bop` lying in `V_k` is in the image by
`HJO.Sweep.ofPiece_mem_map_evalOneAq_cornerE0`, and a submodule containing a basis of `V_k`
is `V_k`. -/
theorem range_ofPiece_le_map_evalOneAq_cornerE0 (k : ℕ) :
    LinearMap.range (ofPiece L k) ≤ Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) := by
  classical
  obtain ⟨bLam, hbLam⟩ := Sym.exists_basis_prod_bop_one (K := L) q
  set b : Module.Basis {l : List ℕ // l.SortedGE} L (Sym.Lambda L) :=
    bLam.reindex Sym.sortedPartitionEquiv.symm with hb
  have hbval : ∀ l : {l : List ℕ // l.SortedGE},
      b l = ((l.1.map (· + 1)).map fun r : ℕ => Sym.Bop q (r : ℤ)).prod 1 := by
    intro l
    rw [hb, Module.Basis.reindex_apply, Equiv.symm_symm, hbLam,
      Sym.sort_parts_sortedPartitionEquiv]
  have hle : Submodule.span L (Set.range (pieceSubBasis k b))
      ≤ (Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k)).comap (ofPiece L k) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨a, l⟩, rfl⟩
    refine ofPiece_mem_map_evalOneAq_cornerE0 hact hT hD hU l.1 k a _ ?_
    rw [coe_pieceSubBasis_eq_prod, hbval,
      Finsupp.prod_fintype _ (fun (j : Fin k) (m : ℕ) => (auxVar ((j : ℕ) + 1) : Total L) ^ m)
        fun j => pow_zero _]
  rintro _ ⟨F, rfl⟩
  exact hle (by rw [(pieceSubBasis k b).span_eq]; exact Submodule.mem_top)

include hact hT hD hU in
/-- **The evaluation map carries `𝟏_k𝔸_q𝟏_0` onto `V_k`**, the surjectivity clause of
`HJO.Sweep.exists_linearEquiv_e0Ideal` in its graded form. -/
theorem map_evalOneAq_cornerE0_eq (k : ℕ) :
    Submodule.map (evalOneAq ρ) (Dyck.Aq.cornerE0 L q k) = LinearMap.range (ofPiece L k) :=
  le_antisymm (map_evalOneAq_cornerE0_le hact k)
    (range_ofPiece_le_map_evalOneAq_cornerE0 hact hT hD hU k)

include hact hT hD hU in
/-- **The evaluation map carries `𝔸_q𝟏_0` onto `V_*`**: the summands generate the direct sum, and
each is in the image of one `𝟏_k𝔸_q𝟏_0`. -/
theorem map_evalOneAq_e0Ideal_eq_top :
    Submodule.map (evalOneAq ρ) (Dyck.Aq.e0Ideal L q) = ⊤ := by
  classical
  refine top_unique fun x _ => ?_
  refine DirectSum.induction_on x (zero_mem _) (fun k F => ?_) fun x y hx hy => add_mem hx hy
  rw [← DirectSum.lof_eq_of L]
  exact Submodule.map_mono (Dyck.Aq.cornerE0_le_e0Ideal k)
    (range_ofPiece_le_map_evalOneAq_cornerE0 hact hT hD hU k
      (LinearMap.mem_range_self (ofPiece L k) F))

/-! ### The isomorphism, given injectivity -/

include hact hT hD hU in
/-- **`HJO.Sweep.exists_linearEquiv_e0Ideal` given that the evaluation map is injective on
`𝔸_q𝟏_0`**: an isomorphism of `𝔸_q`-modules from `𝔸_q𝟏_0` to `V_*` carrying `𝟏_0` to `1 ∈ V_0` and
`𝟏_k𝔸_q𝟏_0` onto `V_k` for every `k ≥ 0`, where `V_*` carries the action of
`HJO.Sweep.exists_isDpaAction_cm`.

The hypothesis `hinj` is all that separates this from `HJO.Sweep.exists_linearEquiv_e0Ideal`. The
route to it is a normal form for a path word, whose naive termination measure fails by
`HJO.Dyck.straightenMeasure_lt_moveTwo`; the surjectivity, the equivariance and the grading are
unconditional. -/
theorem exists_linearEquiv_e0Ideal_of_injOn
    (hinj : ∀ x ∈ Dyck.Aq.e0Ideal L q, evalOneAq ρ x = 0 → x = 0) :
    ∃ f : Dyck.Aq.e0Ideal L q ≃ₗ[L] Vstar L,
      (∀ x : Dyck.Aq.e0Ideal L q, f x = evalOneAq ρ (x : Dyck.Aq L q)) ∧
      (∀ (a : Dyck.Aq L q) (x : Dyck.Aq.e0Ideal L q),
        f ⟨a * (x : Dyck.Aq L q), Dyck.Aq.mul_mem_e0Ideal a x.2⟩ = ρ a (f x)) ∧
      f ⟨Dyck.Aq.e L q 0, Dyck.Aq.e_zero_mem_e0Ideal⟩ = oneVstar L ∧
      ∀ k : ℕ, Submodule.map (f : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L)
          ((Dyck.Aq.cornerE0 L q k).comap (Dyck.Aq.e0Ideal L q).subtype)
        = LinearMap.range (ofPiece L k) := by
  set g : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L :=
    (evalOneAq ρ).comp (Dyck.Aq.e0Ideal L q).subtype with hgdef
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hmap : Submodule.map g ⊤ = ⊤ := by
    rw [hgdef, Submodule.map_comp, Submodule.map_top, Submodule.range_subtype,
      map_evalOneAq_e0Ideal_eq_top hact hT hD hU]
  have hgsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, ← Submodule.map_top]
    exact hmap
  refine ⟨LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩, fun x => rfl,
    fun a x => evalOneAq_mul ρ a (x : Dyck.Aq L q), evalOneAq_e_zero ρ hact, fun k => ?_⟩
  rw [show ((LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩ :
      Dyck.Aq.e0Ideal L q ≃ₗ[L] Vstar L) : Dyck.Aq.e0Ideal L q →ₗ[L] Vstar L) = g from rfl,
    hgdef, Submodule.map_comp, Submodule.map_comap_subtype,
    inf_eq_right.2 (Dyck.Aq.cornerE0_le_e0Ideal k),
    map_evalOneAq_cornerE0_eq hact hT hD hU k]

end Onto

end HJO.Sweep

end
