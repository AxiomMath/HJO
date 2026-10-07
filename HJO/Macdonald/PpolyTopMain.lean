/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Macdonald.EigenbasisFamily
public import HJO.Macdonald.PpolyBasis
public import HJO.Macdonald.PpolyTopSum
public meta import HJO.Attr

/-! # `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`: the coefficient of `x_n^{λ_1}` in `P_λ[X_n]` is
`P_κ[X_{n-1}]`

Steps 4 and 5 of the proof, and the lemma itself. Step 3
(`HJO/Macdonald/PpolyTopSum.lean`) has already exhibited `g`, the coefficient of `x_t^{λ_1}`
in `P_λ[X_n]`, as an eigenvector of Macdonald's operator in the small alphabet with the eigenvalue
of `λ` with its first row removed. What is left is to normalise it.

## `κ` is a hypothesis, not a construction

The proof says "let `κ` be the sequence whose `i`th entry is `λ_{i+1}`". That is exactly
`HJO.Sym.shiftRows` on diagrams, so the lemma carries `κ` as an argument together with
`partDiagram σ' κ = HJO.Sym.shiftRows (partDiagram σ μ)`, in the style of
`HJO.Mac.macdonaldEigenvalue_partDiagram_add_onesExp`. `HJO.Mac.exists_partDiagram_eq_shiftRows`
says such a `κ` exists, so nothing is vacuous, and a consumer that already has its `κ` in hand — as
`HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero` does — does not have to match a construction.

## The normalisation, and why it is a statement about multisets

Step 4 of the usual proof compares `g` with `m_κ[X_{n-1}]` modulo lower monomial symmetric
polynomials. That is not what is done here. Macdonald's polynomials are a basis of `𝒮_{n-1,d-r}`
(`HJO.Mac.exists_basis_macPpoly`) consisting of eigenvectors of `D^{(n-1)}_1` with pairwise distinct
eigenvalues (`HJO.Mac.macdonaldEigenvalue_partDiagram_ne_of_ne`), so an eigenvector at `E_{n-1}(κ)`
is a *scalar multiple* of `P_κ[X_{n-1}]` (`Module.Basis.exists_smul_of_apply_eq_smul`), and the
whole of Step 4 collapses to pinning that one scalar. One coefficient does it: the coefficient of
`x^{\bar\kappa}`, which is `1` in `P_κ[X_{n-1}]` (`HJO.Mac.coeff_partExp_macPpoly`).

Reading that coefficient off `g` is the one genuinely combinatorial step. By
`HJO.Mac.splitAt_coeff_coeff` it is the coefficient of `x^{\bar\kappa}x_t^{λ_1}` in `P_λ[X_n]`, and
`P_λ[X_n]` is symmetric, so what has to be checked is that the exponent vector
`\bar\kappa + λ_1 e_t` is a *rearrangement* of `\bar\lambda` — a statement about the multiset of
entries, not about their order. That is `HJO.Mac.map_univ_val_mapDomain_add_single`: on the left
the multiset splits at `t`, on the right it splits at the least letter `i_0`, and the two
remainders are both the row lengths of `λ` from the first row on, which is what the hypothesis on
`κ` says.

The lexicographic comparison of the `\bar\nu` is thereby avoided altogether. It would
have needed the fact that inserting the largest part at the front of a weakly decreasing sequence
preserves the lexicographic order, which is true and is not cheap.

## Main results

* `HJO.Mac.map_univ_val_eq_map_range`, `HJO.Mac.map_univ_val_eq_cons`: the multiset of entries of
  an exponent vector, read along the increasing listing of the alphabet and split at one letter.
* `HJO.Mac.map_univ_val_mapDomain_add_single`: `\bar\kappa + λ_1 e_t` rearranges `\bar\lambda`.
* `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq_one`: the normalisation, `[x^{\bar\kappa}]g = 1`.
* `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`.
* `HJO.Mac.exists_partDiagram_eq_shiftRows`: the `κ` exists.

## References

The file proves `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq`, on `HJO.Sym.rowLenSeq`,
`HJO.Mac.msymmMem`, `Finsupp.lex_lt_iff_isLeast` and `HJO.Mac.macPpoly`, using
`HJO.Mac.existsUnique_isMonicEigen`; it is used by `HJO.Mac.rowLen_succ_eq_of_coeff_ne_zero`.
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mac

/-! ### The multiset of entries of an exponent vector -/

section Entries

variable {τ : Type*} [Fintype τ] [LinearOrder τ]

/-- **The entries of an exponent vector, read along the increasing listing of the alphabet.** The
row-length sequence `HJO.Mac.rowLenSeqOf` lists them in weakly decreasing order when the vector is
weakly decreasing, and in any case lists exactly them. -/
theorem map_univ_val_eq_map_range (α : τ →₀ ℕ) :
    Multiset.map α (univ : Finset τ).val
      = Multiset.map (rowLenSeqOf τ α) (Multiset.range (Fintype.card τ)) := by
  have hletters : Multiset.map (letterEquiv τ) (univ : Finset (Fin (Fintype.card τ))).val
      = (univ : Finset τ).val := by
    conv_rhs => rw [← Finset.map_univ_equiv (letterEquiv τ).toEquiv]
    rfl
  have hrange : Multiset.map (Fin.val) (univ : Finset (Fin (Fintype.card τ))).val
      = Multiset.range (Fintype.card τ) := by
    have hval : (Finset.range (Fintype.card τ)).val = Multiset.range (Fintype.card τ) := rfl
    rw [← hval, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val]
    rfl
  rw [← hletters, ← hrange, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  rw [rowLenSeqOf_of_lt k.2]

/-- **The entries of an exponent vector, split off at one letter.** -/
theorem map_univ_val_eq_cons (α : τ →₀ ℕ) (a : τ) :
    Multiset.map α (univ : Finset τ).val
      = α a ::ₘ Multiset.map α ((univ : Finset τ).erase a).val := by
  conv_lhs => rw [← Multiset.cons_erase (show a ∈ (univ : Finset τ).val by simp)]
  rw [Multiset.map_cons, Finset.erase_val]

omit [LinearOrder τ] in
/-- The total degree of an exponent vector is the sum of its entries over the whole alphabet: the
letters outside the support contribute `0`. -/
theorem degree_eq_sum_univ (α : τ →₀ ℕ) : α.degree = ∑ i : τ, α i := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.mp hi

/-- The naturals below `n+1` are `0` together with the successors of the naturals below `n`. -/
theorem multiset_range_succ_eq_map (n : ℕ) :
    Multiset.range (n + 1) = 0 ::ₘ Multiset.map (· + 1) (Multiset.range n) := by
  rw [Multiset.range, Multiset.range, List.range_succ_eq_map]
  rfl

end Entries

/-! ### The `κ` exists -/

section Shift

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {d : ℕ}

/-- **The row lengths of `μ` sum to `d`.** The row of index `k` is the entry of `\bar\mu` at the
`k`-th letter, and `\bar\mu` has total degree `d`. -/
theorem sum_range_rowLenSeqOf (μ : PartIdx σ d) :
    ∑ k ∈ Finset.range (Fintype.card σ), rowLenSeqOf σ (partExp σ μ) k = d := by
  rw [← Fin.sum_univ_eq_sum_range,
    show (∑ k : Fin (Fintype.card σ), rowLenSeqOf σ (partExp σ μ) k) = ∑ i : σ, partExp σ μ i from
      Fintype.sum_equiv (letterEquiv σ).toEquiv _ _ fun k => by
        rw [rowLenSeqOf_of_lt k.2]; rfl,
    ← degree_eq_sum_univ, degree_partExp]

/-- **The `κ` exists**: there is an index of the monomial symmetric basis of
`𝒮_{n-1,d-λ_1}` whose diagram is the diagram of `μ` with its first row removed.

Its exponent vector is read off directly: the entry at the `k`-th letter of the small alphabet is
the row of index `k+1` of the diagram of `μ`. That vector is weakly decreasing because the row
lengths are, and its total degree is `d - λ_1` because the rows of `μ` sum to `d`
(`sum_range_rowLenSeqOf`) and the row of index `0` is `λ_1`
(`HJO.Mac.rowLen_partDiagram_zero`). `HJO.Mac.eq_partExp` then identifies it with `\bar\kappa`, and
two diagrams with the same rows are equal. -/
theorem exists_partDiagram_eq_shiftRows (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀) (t : σ) :
    ∃ κ : PartIdx {b : σ // b ≠ t} (d - partExp σ μ i₀),
      partDiagram {b : σ // b ≠ t} κ = HJO.Sym.shiftRows (partDiagram σ μ) := by
  set w : {b : σ // b ≠ t} →₀ ℕ := Finsupp.onFinset Finset.univ
    (fun b => rowLenSeqOf σ (partExp σ μ) (((letterEquiv {b : σ // b ≠ t}).symm b : ℕ) + 1))
    (fun _ _ => Finset.mem_univ _) with hwdef
  have hw : ∀ b, w b
      = rowLenSeqOf σ (partExp σ μ) (((letterEquiv {b : σ // b ≠ t}).symm b : ℕ) + 1) :=
    fun _ => rfl
  -- the row lengths of `μ`, shifted by one, are still weakly decreasing
  have hanti : Antitone w := fun b c hbc => by
    rw [hw, hw]
    exact antitone_rowLenSeqOf (antitone_partExp μ)
      (Nat.succ_le_succ (Fin.le_def.1 ((letterEquiv {b : σ // b ≠ t}).symm.monotone hbc)))
  -- and they sum to `d - λ_1`
  have hdeg : w.degree = d - partExp σ μ i₀ := by
    have hsplit := Finset.sum_range_succ' (rowLenSeqOf σ (partExp σ μ))
      (Fintype.card {b : σ // b ≠ t})
    rw [card_subtype_ne_add_one t, sum_range_rowLenSeqOf μ,
      show rowLenSeqOf σ (partExp σ μ) 0 = partExp σ μ i₀ by
        rw [← rowLen_partDiagram, rowLen_partDiagram_zero μ hi₀]] at hsplit
    rw [degree_eq_sum_univ,
      show (∑ b : {b : σ // b ≠ t}, w b)
        = ∑ k : Fin (Fintype.card {b : σ // b ≠ t}),
            rowLenSeqOf σ (partExp σ μ) ((k : ℕ) + 1) from
        (Fintype.sum_equiv (letterEquiv {b : σ // b ≠ t}).toEquiv _ _ fun k => by
          rw [hw]; simp).symm,
      Fin.sum_univ_eq_sum_range (fun m => rowLenSeqOf σ (partExp σ μ) (m + 1))
        (Fintype.card {b : σ // b ≠ t})]
    omega
  obtain ⟨a, ha⟩ := degree_eq_iff_exists_sym.mp hdeg
  refine ⟨⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩, ?_⟩
  have hkappa : w = partExp {b : σ // b ≠ t} ⟨Nat.Partition.ofSym a,
      Nat.Partition.parts_card_le a⟩ := ha ▸ eq_partExp rfl (ha ▸ hanti)
  have hrow : ∀ k : ℕ, rowLenSeqOf {b : σ // b ≠ t}
      (partExp {b : σ // b ≠ t} ⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩) k
      = rowLenSeqOf σ (partExp σ μ) (k + 1) := fun k => by
    rw [← hkappa]
    rcases Nat.lt_or_ge k (Fintype.card {b : σ // b ≠ t}) with hk | hk
    · rw [rowLenSeqOf_of_lt hk, hw]
      simp
    · rw [rowLenSeqOf_of_le hk, rowLenSeqOf_of_le (by rw [← card_subtype_ne_add_one t]; omega)]
  exact YoungDiagram.ext (Finset.ext fun c => by
    rw [YoungDiagram.mem_cells c, YoungDiagram.mem_cells c, YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen, rowLen_partDiagram, HJO.Sym.rowLen_shiftRows,
      rowLen_partDiagram, hrow c.1])

end Shift

/-! ### The lifted exponent vector of `κ` rearranges `\bar\lambda` -/

section Rearrange

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {d : ℕ} {t : σ}

/-- **`\bar\kappa + λ_1 e_t` is a rearrangement of `\bar\lambda`.** The two multisets of entries
are compared by splitting each off at one letter: the left-hand one at `t`, whose entry is `λ_1`
because that is how the vector was built, and the right-hand one at the least letter `i_0`, whose
entry is `λ_1` because the least letter carries the first row (`HJO.Mac.rowLen_partDiagram_zero`).
What is left on either side is the list of row lengths of `λ` from the first row on: on the right
by `HJO.Mac.map_univ_val_eq_map_range` and `multiset_range_succ_eq_map`, on the left by the same
lemma in the small alphabet together with the hypothesis on `κ`. -/
theorem map_univ_val_mapDomain_add_single (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀)
    (κ : PartIdx {b : σ // b ≠ t} (d - partExp σ μ i₀))
    (hκ : partDiagram {b : σ // b ≠ t} κ = HJO.Sym.shiftRows (partDiagram σ μ)) :
    Multiset.map (Finsupp.mapDomain Subtype.val (partExp {b : σ // b ≠ t} κ)
          + Finsupp.single t (partExp σ μ i₀)) (univ : Finset σ).val
      = Multiset.map (partExp σ μ) (univ : Finset σ).val := by
  have hrow : ∀ k : ℕ, rowLenSeqOf {b : σ // b ≠ t} (partExp {b : σ // b ≠ t} κ) k
      = rowLenSeqOf σ (partExp σ μ) (k + 1) := fun k => by
    rw [← rowLen_partDiagram, ← rowLen_partDiagram, hκ, HJO.Sym.rowLen_shiftRows]
  -- the value of the lifted vector at `t`, and at every other letter
  have hat : (Finsupp.mapDomain Subtype.val (partExp {b : σ // b ≠ t} κ)
      + Finsupp.single t (partExp σ μ i₀)) t = partExp σ μ i₀ := by
    rw [Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ (by simp),
      Finsupp.single_eq_same, zero_add]
  have hval : ∀ b : {b : σ // b ≠ t}, (Finsupp.mapDomain Subtype.val
      (partExp {b : σ // b ≠ t} κ) + Finsupp.single t (partExp σ μ i₀)) b.1
        = partExp {b : σ // b ≠ t} κ b := fun b => by
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply Subtype.val_injective,
      Finsupp.single_eq_of_ne b.2, add_zero]
  have hcomp : Multiset.map ((Finsupp.mapDomain Subtype.val (partExp {b : σ // b ≠ t} κ)
        + Finsupp.single t (partExp σ μ i₀)) ∘ Subtype.val) (univ : Finset {b : σ // b ≠ t}).val
      = Multiset.map (partExp {b : σ // b ≠ t} κ) (univ : Finset {b : σ // b ≠ t}).val :=
    Multiset.map_congr rfl fun b _ => hval b
  -- the left-hand side, split off at `t`
  rw [map_univ_val_eq_cons _ t, hat, univ_erase_top_eq_image t,
    Finset.image_val_of_injOn Subtype.val_injective.injOn, Multiset.map_map, hcomp,
    map_univ_val_eq_map_range]
  -- the right-hand side, split off at `i₀`
  rw [map_univ_val_eq_map_range, ← card_subtype_ne_add_one t, multiset_range_succ_eq_map,
    Multiset.map_cons, Multiset.map_map]
  refine congrArg₂ _ ?_ (Multiset.map_congr rfl fun k _ => hrow k)
  rw [← rowLen_partDiagram, rowLen_partDiagram_zero μ hi₀]

end Rearrange

/-! ### The normalisation, and `HJO.Mac.coeff_partExp_splitAt_macPpoly_eq` -/

section Main

variable {σ : Type*} [LinearOrder σ] [Fintype σ] {K : Type*} [Field K] [Algebra ℚ K] {q : Kˣ}
  {u : K} {d : ℕ} {t : σ}

/-- **The normalisation: `[x^{\bar\kappa}]g = 1`.** By `HJO.Mac.splitAt_coeff_coeff` this is the
coefficient of `x^{\bar\kappa}x_t^{λ_1}` in `P_λ[X_n]`, whose exponent vector rearranges
`\bar\lambda` (`HJO.Mac.map_univ_val_mapDomain_add_single`); `P_λ[X_n]` is symmetric, so that
coefficient is the coefficient at `\bar\lambda`, which is `1` (`HJO.Mac.coeff_partExp_macPpoly`). -/
theorem coeff_partExp_splitAt_macPpoly_eq_one (hqu : AlgebraicIndependent ℤ ![(q : K), u])
    (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀)
    (κ : PartIdx {b : σ // b ≠ t} (d - partExp σ μ i₀))
    (hκ : partDiagram {b : σ // b ≠ t} κ = HJO.Sym.shiftRows (partDiagram σ μ)) :
    coeff (partExp {b : σ // b ≠ t} κ)
        (Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀))
      = 1 := by
  have hmap := map_univ_val_mapDomain_add_single μ hi₀ κ hκ
  -- the lifted vector has total degree `d`, being a rearrangement of `\bar\mu`
  have hdeg : (Finsupp.mapDomain Subtype.val (partExp {b : σ // b ≠ t} κ)
      + Finsupp.single t (partExp σ μ i₀)).degree = d := by
    rw [degree_eq_sum_univ,
      show (∑ i : σ, (Finsupp.mapDomain Subtype.val (partExp {b : σ // b ≠ t} κ)
            + Finsupp.single t (partExp σ μ i₀)) i) = ∑ i : σ, partExp σ μ i from
        congrArg Multiset.sum hmap,
      ← degree_eq_sum_univ, degree_partExp]
  obtain ⟨a, ha⟩ := degree_eq_iff_exists_sym.mp hdeg
  -- the partition that the lifted vector names is `μ`
  have hrho : (⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩ : PartIdx σ d) = μ := by
    refine partExp_injective (eq_of_antitone (antitone_partExp μ) (antitone_partExp _) ?_)
    rw [partExp, map_toFinsupp_univ_val_eq_of_ofSym_eq
      (a := a) (b := partSym σ ⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩)
      (ofSym_partSym ⟨Nat.Partition.ofSym a, Nat.Partition.parts_card_le a⟩).symm, ha]
    exact hmap
  have hsymm : (macPpoly hqu μ : MvPolynomial σ K).IsSymmetric :=
    (mem_symmetricHomogeneousSubmodule.1 (macPpoly hqu μ).2).1
  rw [splitAt_coeff_coeff, ← ha,
    coeff_eq_of_ofSym_eq hsymm (a := a) (b := partSym σ μ)
      (by rw [ofSym_partSym, ← hrho]),
    ← partExp, coeff_partExp_macPpoly]

/-- **The coefficient of `x_n^{λ_1}` in `P_λ[X_n]` is `P_κ[X_{n-1}]`**, where
`κ` is `λ` with its first row removed.

Step 3 (`HJO.Mac.macOpComp_coeff_partExp_splitAt_macPpoly`) makes `g` an eigenvector of
`D^{(n-1)}_1` at `E_{n-1}(κ)` and `HJO.Mac.coeff_partExp_splitAt_macPpoly_ne_zero` makes it
nonzero, so `Module.Basis.exists_smul_of_apply_eq_smul` against the eigenbasis
`HJO.Mac.exists_basis_macPpoly` — whose eigenvalues are pairwise distinct at generic parameters —
makes it a nonzero multiple of `P_κ[X_{n-1}]`. The coefficient at `x^{\bar\kappa}` is `1` on both
sides, so the multiple is `1`.

The genericity is the `hqu` that naming `HJO.Mac.macPpoly` already costs, spent through
`HJO.Mac.macdonaldEigenvalue_partDiagram_ne_of_ne`; nothing here asks more of `q` and `u`, and in
particular the `n ≥ 2` is not needed. -/
@[hjo "lem_dua_ppoly_top"]
theorem coeff_partExp_splitAt_macPpoly_eq (ht : IsTop t)
    (hqu : AlgebraicIndependent ℤ ![(q : K), u]) (μ : PartIdx σ d) {i₀ : σ} (hi₀ : IsBot i₀)
    (κ : PartIdx {b : σ // b ≠ t} (d - partExp σ μ i₀))
    (hκ : partDiagram {b : σ // b ≠ t} κ = HJO.Sym.shiftRows (partDiagram σ μ)) :
    Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀)
      = (macPpoly hqu κ : MvPolynomial {b : σ // b ≠ t} K) := by
  obtain ⟨B, hB⟩ := exists_basis_macPpoly (σ := {b : σ // b ≠ t}) (K := K) (q := q) (u := u)
    (d := d - partExp σ μ i₀) hqu
  have hdiag : ∀ ϖ, macOpComp q u (d - partExp σ μ i₀) (B ϖ)
      = HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card {b : σ // b ≠ t})
          (partDiagram {b : σ // b ≠ t} ϖ) • B ϖ := fun ϖ => by
    rw [hB]
    exact macOpComp_macPpoly hqu ϖ
  have hEinj : Function.Injective fun ϖ : PartIdx {b : σ // b ≠ t} (d - partExp σ μ i₀) =>
      HJO.Sym.macdonaldEigenvalue (q : K) u (Fintype.card {b : σ // b ≠ t})
        (partDiagram {b : σ // b ≠ t} ϖ) := fun ϖ ρ h => by
    by_contra hne
    exact macdonaldEigenvalue_partDiagram_ne_of_ne hqu hne h
  have hne0 : (⟨Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K))
      (partExp σ μ i₀), coeff_partExp_splitAt_macPpoly_mem hqu μ i₀ t⟩ :
        symmetricHomogeneousSubmodule {b : σ // b ≠ t} K (d - partExp σ μ i₀)) ≠ 0 := fun h =>
    coeff_partExp_splitAt_macPpoly_ne_zero hqu μ hi₀ t (congrArg Subtype.val h)
  have heig := macOpComp_coeff_partExp_splitAt_macPpoly ht hqu μ hi₀
  rw [← hκ] at heig
  obtain ⟨c, -, hc⟩ := B.exists_smul_of_apply_eq_smul hdiag hEinj (i := κ) hne0 heig
  have hcoe := congrArg (Subtype.val (p := fun p =>
    p ∈ symmetricHomogeneousSubmodule {b : σ // b ≠ t} K (d - partExp σ μ i₀))) hc
  rw [hB, SetLike.val_smul] at hcoe
  have hone : coeff (partExp {b : σ // b ≠ t} κ)
      (Polynomial.coeff (splitAt t (macPpoly hqu μ : MvPolynomial σ K)) (partExp σ μ i₀)) = 1 :=
    coeff_partExp_splitAt_macPpoly_eq_one hqu μ hi₀ κ hκ
  have htwo : coeff (partExp {b : σ // b ≠ t} κ)
      (macPpoly hqu κ : MvPolynomial {b : σ // b ≠ t} K) = 1 := coeff_partExp_macPpoly hqu κ
  have hc1 : c = 1 := by
    have h := congrArg (coeff (partExp {b : σ // b ≠ t} κ)) hcoe
    rw [coeff_smul, htwo, smul_eq_mul, mul_one] at h
    exact (hone.symm.trans h).symm
  rw [hc1, one_smul] at hcoe
  exact hcoe

end Main

end HJO.Mac

end
