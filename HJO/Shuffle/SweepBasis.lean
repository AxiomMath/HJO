/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepModule
public import HJO.Shuffle.SweepPiece
public import Mathlib.RingTheory.AlgebraTower
public meta import HJO.Attr

/-! # A basis of the graded piece, and its symmetric elements

`HJO/Shuffle/SweepPiece.lean` exhibits `HJO.Sweep.piece L k` as Carlsson and Mellit's
`V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]`. This file reads two consequences of that description off, both of
which the Carlsson–Mellit argument uses as bookkeeping:

* a `𝕜`-basis of `V_k` built from any `𝕜`-basis `(f_i)` of `Λ`, namely the products
  `y_1^{a_1} ⋯ y_k^{a_k} f_i` (`HJO.Sweep.pieceBasis`);
* the description of an element of `V_k` fixed by `s_{k-1}` as a sum of *symmetrised* monomials
  `(y_{k-1}^a y_k^b + y_{k-1}^b y_k^a) H` with `H ∈ V_{k-2}` (`HJO.Sweep.exists_symmetrised_sum`).

## Main results

* `HJO.Sweep.pieceBasis`: from a `𝕜`-basis `b` of `Λ`, the `𝕜`-basis of `V_k` indexed by pairs
  `(a, i)`, with `HJO.Sweep.coe_pieceBasis_eq_prod` reading its value off as
  `y_1^{a_1} ⋯ y_k^{a_k} f_i`. `HJO.Sweep.pieceSubBasis` is the same basis on the submodule
  presentation `HJO.Sweep.pieceSub`.
* `HJO.Sweep.exists_symmetrised_sum`: an `s_{k-1}`-invariant `G ∈ V_k` is a finite sum
  `∑_t (y_{k-1}^{a_t} y_k^{b_t} + y_{k-1}^{b_t} y_k^{a_t}) H_t` with every `H_t ∈ V_{k-2}`.
* `HJO.Sweep.pieceEquivMv`: the `Λ`-algebra isomorphism `V_k ≃ₐ[Λ] Λ[y_1, …, y_k]`, the form of
  `HJO.Sweep.pieceTensorAlgEquiv` the basis is built from.

## Implementation notes

The basis is built over the tower `𝕜 → Λ → V_k` by `Module.Basis.smulTower` rather than through the
tensor product of `HJO.Sweep.pieceTensorAlgEquiv`: the `Λ`-basis of `V_k` by `y`-monomials is
`MvPolynomial.basisMonomials` transported along `HJO.Sweep.pieceEquivMv`, and a `𝕜`-basis of `Λ`
then splits each `Λ`-coefficient. The two routes give the same family, and this one keeps the basis
*value* a product in the total space, which is what the statement names and what
`HJO.Sweep.coe_pieceBasis_eq_prod` records.

The exponent tuple `a ∈ ℕ^k` is `Fin k →₀ ℕ`, Mathlib's index type for the
monomials of a polynomial ring in `k` variables (`MvPolynomial.basisMonomials`). On the finite type
`Fin k` every function is finitely supported, so this is the `ℕ^k` and not a subfamily
of it; the basis *value* is pinned by `HJO.Sweep.coe_pieceBasis_eq_prod` either way.

The proof of `HJO.Sweep.exists_symmetrised_sum` departs from the usual one and is shorter. The
usual proof writes `G = ∑_{a,b} c_{ab} y_{k-1}^a y_k^b` over `W = Λ ⊗ 𝕜[y_1, …, y_{k-2}]`, deduces
`c_{ab} = c_{ba}` by comparing coefficients, then splits the sum into the ranges `a < b` and
`a = b` and halves the diagonal terms. Here the coefficients are extracted the same way
(`HJO.Sweep.pairCoeff`, grouping `G.support` by the pair of exponents at `y_{k-1}` and `y_k`), but
no comparison of coefficients and no case split is made: since `s_{k-1}` fixes each coefficient and
interchanges the two variables, `G + s_{k-1}G` is *visibly* a sum of symmetrised monomials, and
`hsym` turns it into `2G`. So `H_{ab} = c_{ab}/2` works uniformly, and the hypothesis needed of the
base ring is only that `2` be invertible — here `ℚ ⊆ 𝕜`, which the operator layer already has.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5.
-/

@[expose] public section

open MvPolynomial

namespace HJO.Sweep

variable {L : Type*} [CommRing L]

/-! ### The graded piece as a polynomial ring in `k` variables over `Λ` -/

/-- Undoing `MvPolynomial.supportedEquivMvPolynomial`: the element of the total space underlying
`(supportedEquivMvPolynomial s).symm y` is `y` with its variables read back in `ℕ`. -/
theorem rename_supportedEquivMvPolynomial (s : Set ℕ)
    (x : MvPolynomial.supported (Sym.Lambda L) s) :
    rename Subtype.val (MvPolynomial.supportedEquivMvPolynomial s x) = (x : Total L) := by
  have hinj : Function.Injective (rename ((↑) : s → ℕ) : MvPolynomial s (Sym.Lambda L) → _) :=
    rename_injective _ Subtype.val_injective
  have h := congrArg (Subtype.val (p := fun z => z ∈ (rename ((↑) : s → ℕ)).range))
    ((AlgEquiv.ofInjective (rename ((↑) : s → ℕ)) hinj).apply_symm_apply
      ⟨(x : Total L), by rw [← MvPolynomial.supported_eq_range_rename]; exact x.2⟩)
  rw [AlgEquiv.ofInjective_apply] at h
  exact h

/-- **The graded piece is a polynomial ring in `k` variables over `Λ`.** The `Λ`-algebra
isomorphism `V_k ≃ₐ[Λ] Λ[y_1, …, y_k]`, the second reading of `HJO.Sweep.piece`: it is the tensor
product `HJO.Sweep.pieceTensorAlgEquiv` exhibits with the two factors multiplied out, and it is the
form in which the monomials `y_1^{a_1} ⋯ y_k^{a_k}` are a `Λ`-basis. -/
noncomputable def pieceEquivMv (k : ℕ) :
    piece L k ≃ₐ[Sym.Lambda L] MvPolynomial (Fin k) (Sym.Lambda L) :=
  (MvPolynomial.supportedEquivMvPolynomial (Set.Iio k)).trans
    (MvPolynomial.renameEquiv (Sym.Lambda L) (setIioEquivFin k))

theorem pieceEquivMv_apply {k : ℕ} (x : piece L k) :
    pieceEquivMv k x
      = rename (setIioEquivFin k) (MvPolynomial.supportedEquivMvPolynomial (Set.Iio k) x) := rfl

/-- `pieceEquivMv` only renames the variables: reading its value back in `ℕ` returns the original
element of the total space. -/
theorem rename_pieceEquivMv {k : ℕ} (x : piece L k) :
    rename (fun j : Fin k => (j : ℕ)) (pieceEquivMv k x) = (x : Total L) := by
  rw [pieceEquivMv_apply, rename_rename]
  exact rename_supportedEquivMvPolynomial _ _

/-- The inverse of `pieceEquivMv`, read in the total space: it is again a renaming of variables. -/
theorem coe_pieceEquivMv_symm {k : ℕ} (y : MvPolynomial (Fin k) (Sym.Lambda L)) :
    (((pieceEquivMv k).symm y : piece L k) : Total L) = rename (fun j : Fin k => (j : ℕ)) y := by
  conv_rhs => rw [show y = pieceEquivMv k ((pieceEquivMv k).symm y) from
    ((pieceEquivMv k).apply_symm_apply y).symm]
  rw [rename_pieceEquivMv]

/-! ### A basis of the graded piece -/

/-- The `Λ`-basis of `V_k` given by the monomials `y_1^{a_1} ⋯ y_k^{a_k}`: `basisMonomials`
transported along `HJO.Sweep.pieceEquivMv`. -/
noncomputable def pieceBasisLambda (k : ℕ) :
    Module.Basis (Fin k →₀ ℕ) (Sym.Lambda L) (piece L k) :=
  (MvPolynomial.basisMonomials (Fin k) (Sym.Lambda L)).map (pieceEquivMv k).symm.toLinearEquiv

/-- The `Λ`-basis `pieceBasisLambda` is the family of `y`-monomials, read in the total space. -/
theorem coe_pieceBasisLambda {k : ℕ} (a : Fin k →₀ ℕ) :
    ((pieceBasisLambda (L := L) k a : piece L k) : Total L)
      = MvPolynomial.monomial (a.mapDomain fun j : Fin k => (j : ℕ)) 1 := by
  rw [pieceBasisLambda, Module.Basis.map_apply,
    show (MvPolynomial.basisMonomials (Fin k) (Sym.Lambda L)) a = MvPolynomial.monomial a 1 from
      congrFun (MvPolynomial.coe_basisMonomials _ _) a,
    AlgEquiv.toLinearEquiv_apply, coe_pieceEquivMv_symm, MvPolynomial.rename_monomial]

variable {ι : Type*}

/-- **A basis of the graded module from a basis of the symmetric functions.** This is
`HJO.Sweep.pieceBasis`: for `k ≥ 0` and a `𝕜`-basis `(f_i)_{i ∈ I}` of `Λ`, the family
`y_1^{a_1} ⋯ y_k^{a_k} f_i`, indexed by the pairs `(a, i)` with `a ∈ ℕ^k` and `i ∈ I`, is a
`𝕜`-basis of `V_k`.

The exponent tuple `a ∈ ℕ^k` is `Fin k →₀ ℕ`, and the basis value is read off by
`HJO.Sweep.coe_pieceBasis_eq_prod`. The construction is the tower `𝕜 → Λ → V_k`: the `Λ`-basis of
`V_k` by `y`-monomials is `HJO.Sweep.pieceBasisLambda`, and `b` splits each `Λ`-coefficient. -/
@[hjo "lem_cm_vk_basis"]
noncomputable def pieceBasis (k : ℕ) (b : Module.Basis ι L (Sym.Lambda L)) :
    Module.Basis ((Fin k →₀ ℕ) × ι) L (piece L k) :=
  (b.smulTower (pieceBasisLambda k)).reindex (Equiv.prodComm ι (Fin k →₀ ℕ))

/-- The basis `pieceBasis` in monomial form: its value at `(a, i)` is the `y`-monomial with
exponents `a` and coefficient `f_i`. -/
theorem coe_pieceBasis {k : ℕ} (b : Module.Basis ι L (Sym.Lambda L)) (a : Fin k →₀ ℕ) (i : ι) :
    ((pieceBasis k b (a, i) : piece L k) : Total L)
      = MvPolynomial.monomial (a.mapDomain fun j : Fin k => (j : ℕ)) (b i) := by
  rw [pieceBasis, Module.Basis.reindex_apply,
    show (Equiv.prodComm ι (Fin k →₀ ℕ)).symm (a, i) = (i, a) from rfl,
    Module.Basis.smulTower_apply,
    show ((i, a) : ι × (Fin k →₀ ℕ)).1 = i from rfl,
    show ((i, a) : ι × (Fin k →₀ ℕ)).2 = a from rfl,
    Subalgebra.coe_smul, MvPolynomial.smul_eq_C_mul, coe_pieceBasisLambda,
    MvPolynomial.C_mul_monomial, mul_one]

/-- A product of powers of distinct variables is a monomial. -/
theorem prod_X_pow_eq_monomial_sum_single {κ : Type*} (s : Finset κ) (g : κ → ℕ) (f : κ → ℕ) :
    ∏ j ∈ s, (MvPolynomial.X (g j) : Total L) ^ f j
      = MvPolynomial.monomial (∑ j ∈ s, Finsupp.single (g j) (f j)) 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp [MvPolynomial.monomial_zero']
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul, one_mul]

/-- Reindexing a finitely supported function along a map out of a finite type is the sum of its
one-point pieces. -/
theorem mapDomain_eq_sum_single {κ : Type*} [Fintype κ] (g : κ → ℕ) (a : κ →₀ ℕ) :
    Finsupp.mapDomain g a = ∑ j : κ, Finsupp.single (g j) (a j) := by
  classical
  rw [Finsupp.mapDomain]
  exact Finsupp.sum_fintype _ _ fun i => Finsupp.single_zero _

/-- **The basis of `HJO.Sweep.pieceBasis` is the family.** The value of `pieceBasis` at
`(a, i)` is `y_1^{a_1} ⋯ y_k^{a_k} f_i`, a product of powers of the auxiliary variables with the
`i`-th basis vector of `Λ`. Without this the basis would be an unidentified family and the
intended statement would not have been proved. -/
@[hjo "lem_cm_vk_basis"]
theorem coe_pieceBasis_eq_prod {k : ℕ} (b : Module.Basis ι L (Sym.Lambda L)) (a : Fin k →₀ ℕ)
    (i : ι) :
    ((pieceBasis k b (a, i) : piece L k) : Total L)
      = (∏ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) ^ a j) *
        algebraMap (Sym.Lambda L) (Total L) (b i) := by
  rw [coe_pieceBasis]
  have hav : ∀ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) = MvPolynomial.X (j : ℕ) := fun j => by
    rw [auxVar, Nat.add_sub_cancel]
  have hprod : (∏ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) ^ a j)
      = MvPolynomial.monomial (Finsupp.mapDomain (fun j : Fin k => (j : ℕ)) a) 1 := by
    rw [mapDomain_eq_sum_single, ← prod_X_pow_eq_monomial_sum_single]
    exact Finset.prod_congr rfl fun j _ => by rw [hav j]
  rw [hprod, MvPolynomial.algebraMap_eq, mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-- **The basis of `HJO.Sweep.pieceBasis` on the submodule presentation of `V_k`.** The same family
as `HJO.Sweep.pieceBasis`, read on `HJO.Sweep.pieceSub`, which is the shape in which the operators
of the sweep state their domains and codomains. The underlying `L`-module is the same one, so the
transport is the identity. -/
@[hjo "lem_cm_vk_basis"]
noncomputable def pieceSubBasis (k : ℕ) (b : Module.Basis ι L (Sym.Lambda L)) :
    Module.Basis ((Fin k →₀ ℕ) × ι) L (pieceSub L k) :=
  (pieceBasis k b).map (LinearEquiv.refl L (piece L k))

/-- The value of `pieceSubBasis` at `(a, i)` is `y_1^{a_1} ⋯ y_k^{a_k} f_i`. -/
@[hjo "lem_cm_vk_basis"]
theorem coe_pieceSubBasis_eq_prod {k : ℕ} (b : Module.Basis ι L (Sym.Lambda L)) (a : Fin k →₀ ℕ)
    (i : ι) :
    ((pieceSubBasis k b (a, i) : pieceSub L k) : Total L)
      = (∏ j : Fin k, (auxVar ((j : ℕ) + 1) : Total L) ^ a j) *
        algebraMap (Sym.Lambda L) (Total L) (b i) :=
  coe_pieceBasis_eq_prod b a i

/-! ### Symmetric elements of the graded piece

`HJO.Sweep.exists_symmetrised_sum`: an element of `V_k` fixed by `s_{k-1}` is a sum of
symmetrised monomials in `y_{k-1}, y_k` with coefficients in `V_{k-2}`. -/

/-- A `y`-monomial whose exponents vanish from `y_{j+1}` on lies in `V_j`. -/
theorem monomial_mem_piece {j : ℕ} {e : ℕ →₀ ℕ} (h : ∀ n, e n ≠ 0 → n < j) (r : Sym.Lambda L) :
    (MvPolynomial.monomial e r : Total L) ∈ piece L j := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [map_zero]
    exact zero_mem _
  rw [piece, MvPolynomial.mem_supported, MvPolynomial.vars_monomial hr]
  intro n hn
  exact Set.mem_Iio.2 (h n (Finsupp.mem_support_iff.1 (by simpa using hn)))

/-- A transposition of two indices at which an exponent vector vanishes does not move it. -/
theorem mapDomain_swap_eq_self {p q : ℕ} {d : ℕ →₀ ℕ} (hp : d p = 0) (hq : d q = 0) :
    Finsupp.mapDomain (Equiv.swap p q) d = d := by
  refine Finsupp.ext fun n => ?_
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, Equiv.symm_swap]
  rcases eq_or_ne n p with rfl | h1
  · rw [Equiv.swap_apply_left, hp, hq]
  rcases eq_or_ne n q with rfl | h2
  · rw [Equiv.swap_apply_right, hp, hq]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **`s_i` fixes `V_j` pointwise once `j + 1 ≤ i`.** The two variables `y_i, y_{i+1}` that `s_i`
interchanges are then both unread by an element of `V_j`. This is the "`s_{k-1}` fixes
`W = Λ ⊗ 𝕜[y_1, …, y_{k-2}]` pointwise". -/
theorem swapAux_eq_self_of_mem_piece {i j : ℕ} (hij : j + 1 ≤ i) {A : Total L}
    (hA : A ∈ piece L j) : swapAux L i A = A := by
  have hz : ∀ d ∈ A.support, ∀ n, j ≤ n → d n = 0 := by
    intro d hd n hn
    by_contra hne
    have hv : n ∈ A.vars :=
      (MvPolynomial.mem_vars_iff_mem_support n).2 ⟨d, hd, Finsupp.mem_support_iff.2 hne⟩
    have hlt := MvPolynomial.mem_supported.1 hA hv
    simp only [Set.mem_Iio] at hlt
    omega
  conv_lhs => rw [A.as_sum]
  conv_rhs => rw [A.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hmd : Finsupp.mapDomain (Equiv.swap (i - 1) i) d = d :=
    mapDomain_swap_eq_self (hz d hd (i - 1) (by omega)) (hz d hd i (by omega))
  change MvPolynomial.rename (Equiv.swap (i - 1) i) (MvPolynomial.monomial d _) = _
  rw [MvPolynomial.rename_monomial, hmd]

variable (m : ℕ) (G : Total L)

/-- The coefficient `c_{ab}` of `G ∈ V_{m+2}` at the monomial `y_{m+1}^a y_{m+2}^b`:
the `y`-monomials of `G` whose exponents at those two variables are `a` and `b`, with those two
exponents deleted. -/
noncomputable def pairCoeff (m : ℕ) (G : Total L) (p : ℕ × ℕ) : Total L :=
  ∑ d ∈ G.support with (d m, d (m + 1)) = p,
    MvPolynomial.monomial (Finsupp.erase m (Finsupp.erase (m + 1) d)) (G.coeff d)

/-- **The coefficients lie in `V_m`**, the `c_{ab} ∈ W = Λ ⊗ 𝕜[y_1, …, y_{k-2}]`: the
two exponents that could reach `y_{m+1}` and `y_{m+2}` have been deleted, and `G ∈ V_{m+2}` bounds
the rest. -/
theorem pairCoeff_mem_piece (hG : G ∈ piece L (m + 2)) (p : ℕ × ℕ) :
    pairCoeff m G p ∈ piece L m := by
  have hz : ∀ d ∈ G.support, ∀ n, m + 2 ≤ n → d n = 0 := by
    intro d hd n hn
    by_contra hne
    have hv : n ∈ G.vars :=
      (MvPolynomial.mem_vars_iff_mem_support n).2 ⟨d, hd, Finsupp.mem_support_iff.2 hne⟩
    have hlt := MvPolynomial.mem_supported.1 hG hv
    simp only [Set.mem_Iio] at hlt
    omega
  refine sum_mem fun d hd => monomial_mem_piece (fun n hn => ?_) _
  simp only [Finset.mem_filter] at hd
  rcases eq_or_ne n m with rfl | h1
  · exact absurd (Finsupp.erase_same (a := n) (f := Finsupp.erase (n + 1) d)) hn
  rcases eq_or_ne n (m + 1) with rfl | h2
  · rw [Finsupp.erase_ne (by omega), Finsupp.erase_same] at hn
    exact absurd rfl hn
  · rw [Finsupp.erase_ne h1, Finsupp.erase_ne h2] at hn
    have := hz d hd.1 n
    omega

/-- **The expansion of `G ∈ V_{m+2}` in the last two variables**,
`G = ∑_{a,b} c_{ab} y_{k-1}^a y_k^b`: grouping the `y`-monomials of `G` by their pair of exponents
at `y_{m+1}` and `y_{m+2}` and factoring those two powers out. -/
theorem sum_pairCoeff (hG : G ∈ piece L (m + 2)) :
    G = ∑ p ∈ G.support.image fun d => (d m, d (m + 1)),
      (MvPolynomial.X m : Total L) ^ p.1 * MvPolynomial.X (m + 1) ^ p.2 * pairCoeff m G p := by
  conv_lhs => rw [G.as_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun d hd => Finset.mem_image_of_mem (fun d => (d m, d (m + 1))) hd)
    fun d => MvPolynomial.monomial d (G.coeff d)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pairCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter] at hd
  obtain ⟨hd1, hd2⟩ := hd
  have hp1 : p.1 = d m := by rw [← hd2]
  have hp2 : p.2 = d (m + 1) := by rw [← hd2]
  rw [hp1, hp2]
  have hsum : Finsupp.single m (d m) + Finsupp.single (m + 1) (d (m + 1))
      + Finsupp.erase m (Finsupp.erase (m + 1) d) = d := by
    refine Finsupp.ext fun n => ?_
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    rcases eq_or_ne n m with rfl | h1
    · rw [Finsupp.erase_same]
      simp
    rcases eq_or_ne n (m + 1) with rfl | h2
    · rw [Finsupp.erase_ne (by omega), Finsupp.erase_same]
      simp
    · rw [Finsupp.erase_ne h1, Finsupp.erase_ne h2]
      simp [Ne.symm h1, Ne.symm h2]
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.monomial_mul, one_mul, one_mul, hsum]

/-- `s_{m+1}` fixes each coefficient of the expansion, those lying in `V_m`. -/
theorem swapAux_pairCoeff (hG : G ∈ piece L (m + 2)) (p : ℕ × ℕ) :
    swapAux L (m + 1) (pairCoeff m G p) = pairCoeff m G p :=
  swapAux_eq_self_of_mem_piece le_rfl (pairCoeff_mem_piece m G hG p)

/-- **`s_{m+1}` interchanges the two exponents of the expansion**, that is,
`s_{k-1}(G) = ∑_{a,b} c_{ab} y_{k-1}^b y_k^a`. -/
theorem swapAux_eq_sum_pairCoeff (hG : G ∈ piece L (m + 2)) :
    swapAux L (m + 1) G = ∑ p ∈ G.support.image fun d => (d m, d (m + 1)),
      (MvPolynomial.X m : Total L) ^ p.2 * MvPolynomial.X (m + 1) ^ p.1 * pairCoeff m G p := by
  conv_lhs => rw [sum_pairCoeff m G hG]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, swapAux_pairCoeff m G hG, swapAux_X, swapAux_X,
    Nat.add_sub_cancel, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

section Half

variable [Algebra ℚ L]

/-- **A symmetric element as a sum of symmetrised monomials.** This is
`HJO.Sweep.exists_symmetrised_sum`: for `k ≥ 2` and `G ∈ V_k` with `s_{k-1}(G) = G` there are
finitely many triples `(a_t, b_t, H_t)` with `H_t ∈ Λ ⊗_𝕜 𝕜[y_1, …, y_{k-2}]` and
`G = ∑_t (y_{k-1}^{a_t} y_k^{b_t} + y_{k-1}^{b_t} y_k^{a_t}) H_t`.

The finitely many triples are packaged as a `Finset (ℕ × ℕ)` of exponent pairs together with a
coefficient for each pair, which is the indexing with the index set named.

The proof is shorter than the usual one. Expanding `G` in the last two variables
(`HJO.Sweep.sum_pairCoeff`) and applying `s_{k-1}`, which fixes the coefficients and interchanges
the two variables (`HJO.Sweep.swapAux_eq_sum_pairCoeff`), makes `G + s_{k-1}G` visibly a sum of
symmetrised monomials; `hsym` says that sum is `2G`. So `H_{ab} = c_{ab}/2` serves for every pair,
and the comparison of coefficients — the deduction `c_{ab} = c_{ba}` — and its case
split on `a < b` versus `a = b` are both unnecessary. All that is used of the base ring is that `2`
is invertible, which `ℚ ⊆ 𝕜` gives. -/
@[hjo "lem_cm_symmetric_span"]
theorem exists_symmetrised_sum {k : ℕ} (hk : 2 ≤ k) {G : Total L} (hG : G ∈ piece L k)
    (hsym : swapAux L (k - 1) G = G) :
    ∃ (s : Finset (ℕ × ℕ)) (H : ℕ × ℕ → Total L), (∀ p, H p ∈ piece L (k - 2)) ∧
      G = ∑ p ∈ s, ((auxVar (k - 1) : Total L) ^ p.1 * auxVar k ^ p.2
        + auxVar (k - 1) ^ p.2 * auxVar k ^ p.1) * H p := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hk1 : m + 2 - 1 = m + 1 := by omega
  have hk2 : m + 2 - 2 = m := by omega
  rw [hk1] at hsym
  rw [hk2]
  set half : L := algebraMap ℚ L 2⁻¹ with hhalfdef
  have hhalf : (MvPolynomial.C (MvPolynomial.C half) : Total L)
      + MvPolynomial.C (MvPolynomial.C half) = 1 := by
    rw [← map_add, ← map_add, hhalfdef, ← map_add]
    norm_num
  refine ⟨G.support.image fun d => (d m, d (m + 1)),
    fun p => MvPolynomial.C (MvPolynomial.C half) * pairCoeff m G p, fun p => ?_, ?_⟩
  · exact mul_mem ((piece L m).algebraMap_mem (MvPolynomial.C half))
      (pairCoeff_mem_piece m G hG p)
  have hav1 : (auxVar (m + 1) : Total L) = MvPolynomial.X m := by
    rw [auxVar, Nat.add_sub_cancel]
  have hav2 : (auxVar (m + 2) : Total L) = MvPolynomial.X (m + 1) := by
    rw [auxVar, hk1]
  rw [hk1, hav1, hav2]
  have hsplit : ∑ p ∈ G.support.image fun d => (d m, d (m + 1)),
      ((MvPolynomial.X m : Total L) ^ p.1 * MvPolynomial.X (m + 1) ^ p.2
        + MvPolynomial.X m ^ p.2 * MvPolynomial.X (m + 1) ^ p.1)
        * (MvPolynomial.C (MvPolynomial.C half) * pairCoeff m G p)
      = MvPolynomial.C (MvPolynomial.C half) *
        ((∑ p ∈ G.support.image fun d => (d m, d (m + 1)),
            (MvPolynomial.X m : Total L) ^ p.1 * MvPolynomial.X (m + 1) ^ p.2 * pairCoeff m G p)
          + ∑ p ∈ G.support.image fun d => (d m, d (m + 1)),
            (MvPolynomial.X m : Total L) ^ p.2 * MvPolynomial.X (m + 1) ^ p.1
              * pairCoeff m G p) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit, ← sum_pairCoeff m G hG, ← swapAux_eq_sum_pairCoeff m G hG, hsym]
  linear_combination (-G : Total L) * hhalf

end Half

end HJO.Sweep
