/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BopLinear
public import HJO.Classical.PartitionDiagram
public import HJO.Collinear.GradedBasis
public import HJO.Macdonald.LexAddPart
public meta import HJO.Attr

/-! # A word of Hall--Littlewood operators is triangular

`HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span`: for a partition `lam` of `d`, applying the
Hall--Littlewood operators `HJO.Sym.Bop` along the parts of `lam` in nonincreasing order, starting
from `1`, gives an element of `Λ` which differs from `(-1)^d e_lam` by a `𝕜`-linear combination of
the elementary monomials `e_mu` with `mu` a partition of `d` lexicographically greater than `lam`.

## Main definitions

* `HJO.Sym.listDiagram`: the diagram of a list of parts, built by repeated insertion. It is the
  bookkeeping of the induction below and not a new notion of partition: it lands in
  `YoungDiagram`, and `HJO.Sym.listDiagram_sort` identifies it with `HJO.Sym.partitionDiagram`.
* `HJO.Sym.emonSpanAbove`: the `𝕜`-span of the `e_mu` with `mu` a diagram of `d` cells
  lexicographically above a given one -- the span the statement asserts membership in, in the
  form the induction carries it.

## Main results

* `HJO.Sym.foldr_bop_sub_smul_elemSymmMonomial_mem_span`.
* `HJO.Sym.foldr_bop_sub_mul_elemSymmMonomial_mem_emonSpanAbove`: the same statement for an
  arbitrary weakly decreasing list of positive parts, which is the shape the induction runs in.
* `HJO.Sym.elemSymmMonomial_mem_lambdaComp`: `e_mu` is homogeneous of degree the sum of `mu`.
* `HJO.Sym.mem_span_elemSymmMonomial_rowLens`: `HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`
  read as a spanning statement indexed by diagrams rather than by `Nat.Partition`.

## Implementation notes

**The induction runs on the list of parts, not on the partition.** The proof as usually written
inducts on the number `m` of parts with `lam' = (lam_2, …, lam_m)`; a `YoungDiagram` has no such
tail, so the recursion is carried by a list and the diagram of the list is rebuilt at each step by
`HJO.Sym.insertPart`, which is exactly what `HJO.Sym.listDiagram` does. Then
`listDiagram (a :: l) = insertPart a (listDiagram l)` holds by definition, which is what makes the
two clauses of `HJO.Sym.insertPart` and `HJO.Sym.partitionLex_insertPart` applicable with no
bridging.

**The `n := d - lam_1` does not appear.** Truncated subtraction is avoided by running
the induction over the list, where the degree of the tail is `l.sum` and the degree of the whole is
`a + l.sum` by construction; `d` is recovered only at the top, where `Nat.Partition.parts_sum`
supplies `(lam.parts.sort (· ≥ ·)).sum = d`. The one subtraction left is the `n + r - s` of
`HJO.Sym.bop_leading`, which is honest on `Finset.Icc (r+1) (r+n)`.

**Two conventions for a partition meet here, and both are in use in this library.** The order
`HJO.Sym.partitionLex` and the insertion `HJO.Sym.insertPart` are stated on `YoungDiagram`, while
the elementary monomial basis `HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial` is indexed by
`Nat.Partition d`; `HJO.Sym.partitionDiagram` is the existing bridge. The induction is run on the
diagram side, where the order lives, and the conclusion is stated on the `Nat.Partition d` side,
where the basis and its finiteness live -- that is the side the consumer
`HJO.Sym.exists_basis_lambdaComp_prod_bop_one` needs, since
`HJO.Sym.exists_basis_of_triangular_of_sto` wants a finite index type carrying a strict total order,
and `HJO.Sym.partitionLt` is that order, by definition the relation used here. No third
representation is introduced.

**The diagonal term is a scalar action, `(-1)^d • e_lam` with `(-1)^d : K`**, which is the form
`Module.Basis.exists_basis_of_triangular` asks for; `HJO.Sym.neg_one_pow_mul_eq_smul` is the
identification with the product `(-1 : Λ)^d * e_lam` that the induction computes with.

**Neither `HJO.Sym.isLinearMap_bop` nor `HJO.Sym.bop_one` is spent.** One usually expands the tail
`g` in the elementary monomial basis and treats `B_{lam_1}(e_nu)` term by term, which needs the
linearity of `B_{lam_1}`; here `HJO.Sym.bop_leading` is applied to `g` itself, since all that
lemma asks of its argument is that it be homogeneous, and the homogeneity of `g` follows from the
inductive hypothesis. For the same reason the induction needs only the base case `m = 0`, where
the element is `1 - 1`: the second base case `m = 1` is the ordinary step at
`g = 1 ∈ Λ_0`, where the correction sum over `Finset.Icc (r+1) (r+0)` is empty -- which is exactly
how `HJO.Sym.bop_one` is itself proved. The elementary monomial basis is still spent, on the
cofactors `g_s` of the correction terms.

The explicit `fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f` is not decoration: with the binder
types left to the elaborator the ascription `(a : ℤ)` makes `a` an integer and the list of
natural-number parts is silently lifted to a `List ℤ` through the monadic coercion, so the word
reads as a fold over a coerced list.

## References

E. Carlsson and A. Mellit, *A proof of the
shuffle conjecture*, J. Amer. Math. Soc. **31** (2018) 661--697, arXiv:1508.06239, Section 3.
-/

@[expose] public section

namespace YoungDiagram

/-- **The empty diagram has no rows.** Its list of row lengths is read over
`List.range (colLen 0)`, and the empty diagram has no cell in column `0`. -/
theorem rowLens_bot : (⊥ : YoungDiagram).rowLens = [] := by
  rw [YoungDiagram.rowLens]
  simp [YoungDiagram.colLen]

end YoungDiagram

namespace HJO.Sym

/-! ### Scalars, homogeneity and the two readings of a partition -/

/-- **A sign in `Λ` is a sign in `𝕜`**: `(-1)^n` times an element of `Λ` is the scalar `(-1)^n`
acting on it. The induction below computes with the product, while the statement it proves and the
consumer `Module.Basis.exists_basis_of_triangular` are phrased with the action. -/
theorem neg_one_pow_mul_eq_smul {K : Type*} [CommRing K] (n : ℕ) (x : Lambda K) :
    (-1 : Lambda K) ^ n * x = (-1 : K) ^ n • x := by
  rw [Algebra.smul_def, map_pow, map_neg, map_one]

/-- **Multiplying a span into a submodule**: if `x * y` lies in `N` for every generator `y` of a
span, then `x * f` lies in `N` for every `f` in that span. Multiplication by `x` is `𝕜`-linear, so
the three closure clauses of `Submodule.span_induction` are the three clauses of a submodule. -/
theorem mul_mem_of_mem_span {K : Type*} [CommRing K] {x : Lambda K} {S : Set (Lambda K)}
    {N : Submodule K (Lambda K)} (hS : ∀ y ∈ S, x * y ∈ N) {f : Lambda K}
    (hf : f ∈ Submodule.span K S) : x * f ∈ N := by
  induction hf using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact N.smul_mem c hy

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- **The elementary monomial of a multiset of parts is homogeneous of degree their sum.** Each
factor `e_a` lies in `Λ_a` by `HJO.Sym.elemSymm_mem_lambdaComp` and the components multiply. No
positivity of the parts is needed: `e_0 = 1` lies in `Λ_0`. -/
theorem elemSymmMonomial_mem_lambdaComp (K : Type*) [CommRing K] [Algebra ℚ K] (mu : Multiset ℕ) :
    elemSymmMonomial K mu ∈ LambdaComp K mu.sum := by
  induction mu using Multiset.induction_on with
  | empty => simpa using one_mem_lambdaComp K
  | cons a s ih =>
    rw [elemSymmMonomial_cons, Multiset.sum_cons]
    exact mul_mem_lambdaComp (elemSymm_mem_lambdaComp K a) ih

/-- **The elementary monomial of a diagram with `d` cells lies in `Λ_d`.** The parts are the rows
and the number of cells is their sum. -/
theorem elemSymmMonomial_rowLens_mem_lambdaComp (K : Type*) [CommRing K] [Algebra ℚ K]
    {mu : YoungDiagram} {d : ℕ} (h : mu.card = d) :
    elemSymmMonomial K (mu.rowLens : Multiset ℕ) ∈ LambdaComp K d := by
  have hm := elemSymmMonomial_mem_lambdaComp K (mu.rowLens : Multiset ℕ)
  rwa [Multiset.sum_coe, ← YoungDiagram.card_eq_sum_rowLens, h] at hm

/-- **The rows of `D_lam` are the parts of `lam`, as a list.** The unindexed form of
`HJO.Sym.rowLen_partitionDiagram`: `YoungDiagram.ofRowLens` returns the list it was given,
the parts of a partition being positive. -/
theorem rowLens_partitionDiagram {d : ℕ} (p : Nat.Partition d) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) :=
  YoungDiagram.rowLens_ofRowLens_eq_self fun _ hx => pos_of_mem_sort p hx

/-- **Sorting an already weakly decreasing list changes nothing.** Two weakly decreasing lists
that are permutations of one another are equal, and `Multiset.sort` produces a permutation. This is
the half of the bridge between the two readings of a partition that goes from a diagram to a
`Nat.Partition`: the parts of the latter are the rows of the former, already in order. -/
theorem sort_coe_of_sortedGE {l : List ℕ} (hl : l.SortedGE) :
    (l : Multiset ℕ).sort (· ≥ ·) = l :=
  List.Perm.eq_of_sortedGE (Multiset.pairwise_sort _ _).sortedGE hl
    (Multiset.coe_eq_coe.1 (Multiset.sort_eq (l : Multiset ℕ) (· ≥ ·)))

/-! ### The diagram of a list of parts -/

/-- **The diagram of a list of parts**, built by inserting the parts one at a time from the right.
For a weakly decreasing list of positive parts its rows are the list itself
(`HJO.Sym.rowLens_listDiagram`) and it is the diagram of the corresponding partition
(`HJO.Sym.listDiagram_sort`), so this is not a second notion of partition but the recursive
presentation of one: `listDiagram (a :: l) = insertPart a (listDiagram l)` holds by definition,
which is what lets the induction below step with `HJO.Sym.insertPart` and
`HJO.Sym.partitionLex_insertPart`. -/
def listDiagram : List ℕ → YoungDiagram
  | [] => ⊥
  | a :: l => insertPart a (listDiagram l)

/-- **A diagram whose rows are bounded by `a` has first row at most `a`.** Row `0` is the first
entry of the list of rows, read as `0` when the list is empty. -/
theorem rowLen_zero_le_of_rowLens_eq {mu : YoungDiagram} {l : List ℕ} (h : mu.rowLens = l) {a : ℕ}
    (ha : ∀ b ∈ l, b ≤ a) : mu.rowLen 0 ≤ a := by
  rw [YoungDiagram.rowLen_eq_getD, h]
  match l with
  | [] => simp
  | b :: l' => exact ha b (by simp)

/-- **The rows of the diagram of a list are the list**, for a weakly decreasing list of positive
parts. Each insertion stops at the front, the part inserted being at least the largest row of what
has been built so far. -/
theorem rowLens_listDiagram {l : List ℕ} (hpos : ∀ a ∈ l, 0 < a) (hs : l.SortedGE) :
    (listDiagram l).rowLens = l := by
  induction l with
  | nil => exact YoungDiagram.rowLens_bot
  | cons a l ih =>
    obtain ⟨hab, hsl⟩ := List.pairwise_cons.1 hs.pairwise
    have hposl : ∀ b ∈ l, 0 < b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
    have hrow : (listDiagram l).rowLens = l := ih hposl hsl.sortedGE
    change (insertPart a (listDiagram l)).rowLens = a :: l
    rw [rowLens_insertPart_of_rowLen_zero_le (hpos a List.mem_cons_self)
      (rowLen_zero_le_of_rowLens_eq hrow fun b hb => hab b hb), hrow]

/-- **The diagram of the parts of a partition is its diagram**: `HJO.Sym.listDiagram` of the
nonincreasing listing of the parts is `HJO.Sym.partitionDiagram`. Both are `ofRowLens` of that
listing, one of them after the previous lemma. -/
theorem listDiagram_sort {d : ℕ} (p : Nat.Partition d) :
    listDiagram (p.parts.sort (· ≥ ·)) = partitionDiagram p := by
  have hpos : ∀ a ∈ p.parts.sort (· ≥ ·), 0 < a := fun a ha => pos_of_mem_sort p ha
  have hs : (p.parts.sort (· ≥ ·)).SortedGE := (Multiset.pairwise_sort _ _).sortedGE
  rw [partitionDiagram]
  exact ((YoungDiagram.ofRowLens_congr (rowLens_listDiagram hpos hs).symm).trans
    YoungDiagram.ofRowLens_to_rowLens_eq_self).symm

/-! ### The span of the elementary monomials above a partition -/

/-- **`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial` as a spanning statement indexed by
diagrams.** A homogeneous symmetric function of degree `m` is a `𝕜`-combination of the elementary
monomials of the diagrams with `m` cells. The basis is indexed by `Nat.Partition m`;
`HJO.Sym.partitionDiagram` carries each index to a diagram with the same parts. -/
theorem mem_span_elemSymmMonomial_rowLens {m : ℕ} {f : Lambda K} (hf : f ∈ LambdaComp K m) :
    f ∈ Submodule.span K
      {x | ∃ nu : YoungDiagram, nu.card = m ∧
        x = elemSymmMonomial K (nu.rowLens : Multiset ℕ)} := by
  obtain ⟨B, hB⟩ := exists_basis_lambdaComp_elemSymmMonomial K m
  have h2 : f ∈ Submodule.map (LambdaComp K m).subtype (Submodule.span K (Set.range B)) :=
    ⟨⟨f, hf⟩, B.mem_span _, rfl⟩
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro x ⟨y, ⟨p, rfl⟩, rfl⟩
  refine ⟨partitionDiagram p, card_partitionDiagram p, (hB p).trans ?_⟩
  rw [rowLens_partitionDiagram, Multiset.sort_eq]

/-- **The `𝕜`-span of the `e_mu` with `mu` a diagram of `d` cells lexicographically above
`lam`.** This is the span "the `𝕜`-linear span of the `e_mu` with `mu` a partition of `d`
satisfying `mu > lam`", read on the side where the order lives; the main statement below is its
translation to `Nat.Partition d`, and `HJO.Sym.emonSpanAbove_le_span_partition` is that
translation. -/
noncomputable def emonSpanAbove (K : Type*) [CommRing K] [Algebra ℚ K] (d : ℕ)
    (lam : YoungDiagram) : Submodule K (Lambda K) :=
  Submodule.span K {x | ∃ mu : YoungDiagram, mu.card = d ∧ partitionLex lam mu ∧
    x = elemSymmMonomial K (mu.rowLens : Multiset ℕ)}

/-- An elementary monomial above `lam` lies in the span of those above `lam`. -/
theorem elemSymmMonomial_mem_emonSpanAbove {d : ℕ} {lam mu : YoungDiagram} (hcard : mu.card = d)
    (hlex : partitionLex lam mu) :
    elemSymmMonomial K (mu.rowLens : Multiset ℕ) ∈ emonSpanAbove K d lam :=
  Submodule.subset_span ⟨mu, hcard, hlex, rfl⟩

/-- **The span sits inside the graded piece**, every generator being homogeneous of degree `d`.
This is how the induction learns that the word on the tail is homogeneous, which is the hypothesis
`HJO.Sym.bop_leading` asks of it. -/
theorem emonSpanAbove_le_lambdaComp (d : ℕ) (lam : YoungDiagram) :
    emonSpanAbove K d lam ≤ LambdaComp K d := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨mu, hcard, -, rfl⟩
  exact elemSymmMonomial_rowLens_mem_lambdaComp K hcard

/-- **The span, translated to partitions of `d`.** Every diagram with `d` cells is the diagram of
a partition of `d`, namely of the multiset of its rows, so the span over diagrams above `D_lam` is
contained in the span over the partitions of `d` above `lam`. -/
theorem emonSpanAbove_le_span_partition {d : ℕ} (lam : Nat.Partition d) :
    emonSpanAbove K d (partitionDiagram lam) ≤ Submodule.span K
      ((fun mu : Nat.Partition d => elemSymmMonomial K mu.parts) ''
        {mu | partitionLex (partitionDiagram lam) (partitionDiagram mu)}) := by
  rw [emonSpanAbove]
  refine Submodule.span_le.2 ?_
  rintro x ⟨mu, hcard, hlex, rfl⟩
  have hsum : (mu.rowLens : Multiset ℕ).sum = d := by
    rw [Multiset.sum_coe, ← YoungDiagram.card_eq_sum_rowLens, hcard]
  set p : Nat.Partition d := ⟨(mu.rowLens : Multiset ℕ),
    fun hi => mu.pos_of_mem_rowLens _ (Multiset.mem_coe.1 hi), hsum⟩ with hp
  have hpd : partitionDiagram p = mu := by
    rw [partitionDiagram]
    refine (YoungDiagram.ofRowLens_congr ?_).trans YoungDiagram.ofRowLens_to_rowLens_eq_self
    show p.parts.sort (· ≥ ·) = mu.rowLens
    rw [hp]
    exact sort_coe_of_sortedGE mu.rowLens_sorted
  exact Submodule.subset_span ⟨p, by rw [Set.mem_ofPred_eq, hpd]; exact hlex, rfl⟩

/-! ### Triangularity of a word of Hall--Littlewood operators -/

/-- **A word of Hall--Littlewood operators is triangular, for a list of parts.** For a weakly
decreasing list `l` of positive integers, applying the operators along `l` to `1` gives an element
differing from `(-1)^{|l|} e_l` by a combination of the `e_mu` with `mu` a diagram of `|l|` cells
lexicographically above the diagram of `l`. This is the shape the induction on the
number of parts runs in.

The step at `a :: l`: the word `g` on the tail is homogeneous of degree `n = |l|`, by the
inductive hypothesis together with `HJO.Sym.emonSpanAbove_le_lambdaComp`, so
`HJO.Sym.bop_leading` writes `B_a g` as `(-1)^a e_a g` plus corrections `(-1)^s e_s g_s` with
`s > a` and `g_s` in `Λ_{n+a-s}`. Substituting `g = (-1)^n e_l + h` with `h` above the tail turns
the leading term into `(-1)^{a+n} e_{a :: l}` plus `(-1)^a e_a h`, and `e_a h` is above
`a ∪ l` by `HJO.Sym.partitionLex_insertPart`, the insertion stopping at the front because `a` is at
least every part of `l`. Each correction is a combination of `e_s e_rho = e_{s ∪ rho}` by
`HJO.Sym.exists_basis_lambdaComp_elemSymmMonomial`, whose first part is at least `s > a`, so row `0`
already witnesses the comparison with `a ∪ l`. -/
theorem foldr_bop_sub_mul_elemSymmMonomial_mem_emonSpanAbove (q : K) {l : List ℕ}
    (hpos : ∀ a ∈ l, 0 < a) (hs : l.SortedGE) :
    l.foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1
        - (-1 : Lambda K) ^ l.sum * elemSymmMonomial K (l : Multiset ℕ)
      ∈ emonSpanAbove K l.sum (listDiagram l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hab, hsl⟩ := List.pairwise_cons.1 hs.pairwise
    have ha : 0 < a := hpos a List.mem_cons_self
    have hposl : ∀ b ∈ l, 0 < b := fun b hb => hpos b (List.mem_cons_of_mem a hb)
    have hle : (listDiagram l).rowLen 0 ≤ a :=
      rowLen_zero_le_of_rowLens_eq (rowLens_listDiagram hposl hsl.sortedGE) fun b hb => hab b hb
    have ihl := ih hposl hsl.sortedGE
    set n := l.sum with hn
    set g := l.foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1 with hgdef
    set h := g - (-1 : Lambda K) ^ n * elemSymmMonomial K (l : Multiset ℕ) with hhdef
    have hgn : g ∈ LambdaComp K n := by
      have h1 : h ∈ LambdaComp K n := emonSpanAbove_le_lambdaComp n (listDiagram l) ihl
      have h2 : elemSymmMonomial K (l : Multiset ℕ) ∈ LambdaComp K n := by
        have hm := elemSymmMonomial_mem_lambdaComp K (l : Multiset ℕ)
        rwa [Multiset.sum_coe] at hm
      have hgeq : g = h + (-1 : Lambda K) ^ n * elemSymmMonomial K (l : Multiset ℕ) := by
        rw [hhdef]; ring
      rw [hgeq]
      exact Submodule.add_mem _ h1
        (by rw [neg_one_pow_mul_eq_smul]; exact Submodule.smul_mem _ _ h2)
    obtain ⟨G, hG, hBop⟩ := bop_leading q n a hgn
    have hkey : (a :: l).foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1
          - (-1 : Lambda K) ^ (a :: l).sum * elemSymmMonomial K ((a :: l : List ℕ) : Multiset ℕ)
        = (-1 : Lambda K) ^ a * elemSymm K a * h
          + ∑ s ∈ Finset.Icc (a + 1) (a + n), (-1 : Lambda K) ^ s * elemSymm K s * G s := by
      have hcons : ((a :: l : List ℕ) : Multiset ℕ) = a ::ₘ (l : Multiset ℕ) := rfl
      rw [List.foldr_cons, List.sum_cons, hcons, elemSymmMonomial_cons, ← hgdef, hBop, hhdef]
      ring
    rw [hkey]
    change _ ∈ emonSpanAbove K (a + n) (insertPart a (listDiagram l))
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun s hsmem => ?_)
    · refine mul_mem_of_mem_span ?_ ihl
      rintro y ⟨mu, hcard, hlex, rfl⟩
      rw [mul_assoc, ← elemSymmMonomial_cons, ← rowLens_insertPart_toMultiset ha,
        neg_one_pow_mul_eq_smul]
      refine Submodule.smul_mem _ _ (elemSymmMonomial_mem_emonSpanAbove ?_
        (partitionLex_insertPart hlex ha hle))
      rw [card_insertPart ha, hcard]
      omega
    · rw [Finset.mem_Icc] at hsmem
      refine mul_mem_of_mem_span ?_ (mem_span_elemSymmMonomial_rowLens (hG s (by
        rw [Finset.mem_Icc]; omega)))
      rintro y ⟨nu, hcard, rfl⟩
      rw [mul_assoc, ← elemSymmMonomial_cons, ← rowLens_insertPart_toMultiset (by omega),
        neg_one_pow_mul_eq_smul]
      refine Submodule.smul_mem _ _ (elemSymmMonomial_mem_emonSpanAbove ?_ ⟨0, ?_, ?_⟩)
      · rw [card_insertPart (by omega), hcard]
        omega
      · omega
      · rw [rowLen_insertPart_zero ha hle]
        exact lt_of_lt_of_le (by omega) (le_rowLen_insertPart_zero (by omega : 0 < s) nu)

/-- **A word of Hall--Littlewood operators is triangular.** For every
`d` and every partition `lam` of `d`, the element
`B_{lam_1}(B_{lam_2}(⋯ B_{lam_m}(1) ⋯)) - (-1)^d e_lam` lies in the `𝕜`-linear span of the
elementary monomials `e_mu` with `mu` a partition of `d` satisfying `mu > lam` in the
lexicographic order of `HJO.Sym.partitionLex`.

The word is the fold of `HJO.Sym.Bop q` along the parts of `lam` read in nonincreasing order,
outermost part first, and `e_lam` is `HJO.Sym.elemSymmMonomial` of the parts. The statement is
`HJO.Sym.foldr_bop_sub_mul_elemSymmMonomial_mem_emonSpanAbove` at the list of parts, with the sign
read as a scalar action and the span re-indexed by the partitions of `d`. -/
@[hjo "lem_cm_bword_triangular"]
theorem foldr_bop_sub_smul_elemSymmMonomial_mem_span (q : K) {d : ℕ} (lam : Nat.Partition d) :
    ((lam.parts.sort (· ≥ ·)).foldr (fun (a : ℕ) (f : Lambda K) => Bop q (a : ℤ) f) 1
        - (-1 : K) ^ d • elemSymmMonomial K lam.parts)
      ∈ Submodule.span K ((fun mu : Nat.Partition d => elemSymmMonomial K mu.parts) ''
          {mu | partitionLex (partitionDiagram lam) (partitionDiagram mu)}) := by
  have hpos : ∀ a ∈ lam.parts.sort (· ≥ ·), 0 < a := fun a ha => pos_of_mem_sort lam ha
  have hs : (lam.parts.sort (· ≥ ·)).SortedGE := (Multiset.pairwise_sort _ _).sortedGE
  have hcoe : ((lam.parts.sort (· ≥ ·) : List ℕ) : Multiset ℕ) = lam.parts := Multiset.sort_eq _ _
  have hsum : (lam.parts.sort (· ≥ ·)).sum = d := by
    rw [← Multiset.sum_coe, hcoe, lam.parts_sum]
  have hmain := foldr_bop_sub_mul_elemSymmMonomial_mem_emonSpanAbove q hpos hs
  rw [hsum, hcoe, listDiagram_sort, neg_one_pow_mul_eq_smul] at hmain
  exact emonSpanAbove_le_span_partition lam hmain

end HJO.Sym
