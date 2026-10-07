/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import HJO.CarlssonMellit.PowerRingDomain
public import HJO.CarlssonMellit.SeriesGrading
public meta import HJO.Attr

/-! # Vanishing on the diagonal is divisibility by the difference

A series in the graded part `P^gr_{k,d+1}` of `P°_k` that becomes `0` when the letter `x_j` is
substituted for the letter `x_i` is `(x_j - x_i)H` for a unique `H ∈ P^gr_{k,d}`. This is the lemma
that makes the lowering step's division legitimate: the divisor `x_j - x_i` is *not* invertible, and
what licenses the division is that the numerator vanishes on the diagonal.

The proof here is not the usual one, which groups the series by the monomials in the
letters other than `x_i` and `x_j` — that grouping is
`MvPowerSeries.IsHomogeneous.existsUnique_eq_monomialwiseFinsum_monomial_mul` of
`HJO.CarlssonMellit.HomogeneousSplit` — divides each two-variable block by `x_j - x_i` in the
polynomial ring, and reassembles. The quotient's coefficients are written down instead: the
coefficient of `H` at `ρ x_i^u x_j^v` is the partial sum
`∑_{u' + s = u}\,[\,ρ x_i^{u'} x_j^{\,v + s}\,]G`, which is the unique solution of the one-step
recursion that multiplying by `x_j - x_i` imposes. Both halves of the theorem are then coefficient
identities, no summable family and no block ring is needed, and the hypothesis is spent in exactly
one place: it says the *full* partial sum at `v = 0` vanishes, which is the boundary condition the
recursion needs at its far end.

## Main definitions

* `HJO.Sym.collapseVar`: the map of letters substituting `x_j` for `x_i`, so that
  `MvPowerSeries.rename (collapseVar i j)` is that substitution. It has finite fibres — the fibre
  over `x_j` is `{x_i, x_j}` and every other is a singleton or empty — so the substitution is
  defined on the whole series ring.
* `HJO.Sym.diffQuot`: the quotient `H`.

## Main results

* `HJO.Sym.coeff_rename_collapseVar`: the coefficients of the substituted series, as the finite sums
  over the fibres that they are. This is the usable form of the hypothesis.
* `HJO.Sym.isHomogeneous_and_eq_X_sub_X_mul_diffQuot`: existence, over any commutative ring.
* `HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`: the theorem in `P°_k`, which is
  `HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`.

## Implementation notes

*The degree is written `d + 1` and the quotient's `d`.* The paper asks `d ≥ 1` and puts the
quotient in `P^gr_{k,d-1}`; `ℕ`-subtraction would clip that to `0` at `d = 0`, where the statement
is false — the series `1` is homogeneous of degree `0`, is killed by no substitution, and
`x_j - x_i` does not divide it — so the successor form is used, as throughout.

*The letter type is arbitrary, and the specialisation to `ℕ` happens only in the last statement.*
The construction and both halves of the theorem are about `MvPowerSeries σ A` for an arbitrary `σ`,
because the merged alphabet of `HJO.Sym.IsZDelta` needs exactly this division with its letters
indexed by `Option ℕ` — the distinguished letter `y_k` together with the free variables — and
nothing in the argument looks at the letters beyond distinguishing two of them.
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`, which is
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul` in `P°_k`, is the instance at `σ = ℕ`, and
`HJO.Sym.zDeltaOn` of `HJO.CarlssonMellit.ZDeltaDefined` is the instance at `σ = Option ℕ`.

*The distinguished letters are `x_i` and `x_j` with `i ≠ j`, and the difference is `x_j - x_i`.*
The order matters only for the sign of `H`, and the `G = (x_j - x_i)H` is the order
kept. Distinctness is needed: at `i = j` the substitution is the identity, so the hypothesis says
`G = 0`, and the conclusion's uniqueness fails because `x_j - x_i = 0`.

*A monomial is decomposed by addition, not by truncated subtraction.* Every exponent vector is
`ρ + u·x_i + v·x_j` for a unique `ρ` free of `x_i` and `x_j`, which is
`HJO.Sym.eraseTwo_add_single_add_single`, and the total degree of that is `deg ρ + u + v` on the
nose, by `map_add` and
`Finsupp.degree_single`. Writing the same thing with `Finsupp.update` would put `deg α - α i` in
every degree computation.

*The hypothesis is `MvPowerSeries.rename (collapseVar i j) G = 0` and not a condition on
coefficients.* `MvPowerSeries.rename` needs the substitution to have finite fibres, which it has,
and it is the honest reading of "substituting `x_j` for `x_i` in `G` gives `0`"; the coefficient
form the proof uses is derived from it in `HJO.Sym.coeff_rename_collapseVar` rather than assumed.
Note that the substitution is *not* injective on monomials, so `MvPolynomial.rename`'s API does not
transfer: the coefficient of the substituted series at a monomial is a sum over a fibre with two or
more members, and that sum being `0` is strictly weaker than each of its terms being `0`. The whole
content of the lemma lives in that difference.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 4, where the division by `x_{r+1} - x_r` is performed without comment.
-/

@[expose] public section

namespace HJO.Sym

variable {σ : Type*}

/-! ### Substituting one letter for another -/

open scoped Classical in
/-- The map of letters substituting `x_j` for `x_i`: it carries `i` to `j` and fixes every other
letter. It is `noncomputable` only because the letter type carries no decidable equality: the
generality is what the merged alphabet of `HJO.Sym.IsZDelta` needs, its letters being indexed by
`Option ℕ` rather than by `ℕ`. -/
noncomputable def collapseVar (i j : σ) : σ → σ := fun l => if l = i then j else l

@[simp]
theorem collapseVar_self (i j : σ) : collapseVar i j i = j := by simp [collapseVar]

@[simp]
theorem collapseVar_of_ne {i j l : σ} (h : l ≠ i) : collapseVar i j l = l := by
  simp [collapseVar, h]

/-- The substituted-in letter is fixed, whether or not it is the substituted-for one. -/
@[simp]
theorem collapseVar_right (i j : σ) : collapseVar i j j = j := by
  rcases eq_or_ne j i with rfl | h
  · exact collapseVar_self j j
  · exact collapseVar_of_ne h

/-- The substitution has finite fibres: the fibre over `j` is contained in `{i, j}` and every other
fibre in a singleton. This is what makes `MvPowerSeries.rename` available, and it is the reason the
substitution is defined on the whole series ring rather than on polynomials only. -/
instance tendstoCofinite_collapseVar (i j : σ) : Filter.TendstoCofinite (collapseVar i j) := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro b
  refine Set.Finite.subset ((Set.finite_singleton b).insert i) fun l hl => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, collapseVar] at hl
  rcases eq_or_ne l i with rfl | h
  · exact Set.mem_insert _ _
  · rw [ite_eq_right h] at hl
    exact Set.mem_insert_of_mem _ hl

/-! ### Splitting a monomial off two letters -/

/-- A monomial with the exponents of `x_i` and `x_j` removed. -/
noncomputable def eraseTwo (i j : σ) (α : σ →₀ ℕ) : σ →₀ ℕ := (α.erase i).erase j

@[simp]
theorem eraseTwo_apply_left {i j : σ} (hij : i ≠ j) (α : σ →₀ ℕ) : eraseTwo i j α i = 0 := by
  rw [eraseTwo, Finsupp.erase_ne hij, Finsupp.erase_same]

@[simp]
theorem eraseTwo_apply_right (i j : σ) (α : σ →₀ ℕ) : eraseTwo i j α j = 0 := by
  rw [eraseTwo, Finsupp.erase_same]

theorem eraseTwo_apply_of_ne {i j l : σ} (hi : l ≠ i) (hj : l ≠ j) (α : σ →₀ ℕ) :
    eraseTwo i j α l = α l := by
  rw [eraseTwo, Finsupp.erase_ne hj, Finsupp.erase_ne hi]

/-- **Every monomial splits off two letters**: `α = ρ + u·x_i + v·x_j` with `ρ` free of `x_i` and
`x_j`. Addition, not truncated subtraction, so that the total degree splits on the nose. -/
theorem eraseTwo_add_single_add_single {i j : σ} (hij : i ≠ j) (α : σ →₀ ℕ) :
    eraseTwo i j α + Finsupp.single i (α i) + Finsupp.single j (α j) = α := by
  refine Finsupp.ext fun l => ?_
  rw [Finsupp.add_apply, Finsupp.add_apply]
  rcases eq_or_ne l i with rfl | hi
  · rw [eraseTwo_apply_left hij, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, zero_add,
      add_zero]
  rcases eq_or_ne l j with rfl | hj
  · rw [eraseTwo_apply_right, Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.single_eq_same,
      zero_add, zero_add]
  · rw [eraseTwo_apply_of_ne hi hj, Finsupp.single_eq_of_ne hi, Finsupp.single_eq_of_ne hj,
      add_zero, add_zero]

variable {i j : σ}

/-- The two distinguished exponents of a split monomial, on the left. -/
@[simp]
theorem add_single_add_single_apply_left (hij : i ≠ j) {ρ : σ →₀ ℕ} (hρ : ρ i = 0) (u v : ℕ) :
    (ρ + Finsupp.single i u + Finsupp.single j v) i = u := by
  rw [Finsupp.add_apply, Finsupp.add_apply, hρ, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hij, zero_add, add_zero]

/-- The two distinguished exponents of a split monomial, on the right. -/
@[simp]
theorem add_single_add_single_apply_right (hij : i ≠ j) {ρ : σ →₀ ℕ} (hρ : ρ j = 0) (u v : ℕ) :
    (ρ + Finsupp.single i u + Finsupp.single j v) j = v := by
  rw [Finsupp.add_apply, Finsupp.add_apply, hρ, Finsupp.single_eq_of_ne (Ne.symm hij),
    Finsupp.single_eq_same, zero_add, zero_add]

/-- The letter-free part of a split monomial is what it was split off. -/
theorem eraseTwo_add_single_add_single_eq (hij : i ≠ j) {ρ : σ →₀ ℕ} (hρi : ρ i = 0)
    (hρj : ρ j = 0) (u v : ℕ) :
    eraseTwo i j (ρ + Finsupp.single i u + Finsupp.single j v) = ρ := by
  refine Finsupp.ext fun l => ?_
  rcases eq_or_ne l i with rfl | hi
  · rw [eraseTwo_apply_left hij, hρi]
  rcases eq_or_ne l j with rfl | hj
  · rw [eraseTwo_apply_right, hρj]
  · rw [eraseTwo_apply_of_ne hi hj, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.single_eq_of_ne hi, Finsupp.single_eq_of_ne hj, add_zero, add_zero]

/-- The total degree of a split monomial. -/
theorem degree_add_single_add_single (ρ : σ →₀ ℕ) (u v : ℕ) :
    Finsupp.degree (ρ + Finsupp.single i u + Finsupp.single j v)
      = Finsupp.degree ρ + u + v := by
  rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- **The substitution on a monomial**: `x_j` replaces `x_i`, so the two exponents merge. -/
theorem mapDomain_collapseVar (hij : i ≠ j) (α : σ →₀ ℕ) :
    Finsupp.mapDomain (collapseVar i j) α
      = eraseTwo i j α + Finsupp.single j (α i + α j) := by
  conv_lhs => rw [← eraseTwo_add_single_add_single hij α]
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, collapseVar_self, collapseVar_of_ne (Ne.symm hij),
    Finsupp.mapDomain_congr (f := collapseVar i j) (g := id) (fun l hl => ?_), Finsupp.mapDomain_id,
    add_assoc, ← Finsupp.single_add]
  refine collapseVar_of_ne fun h => ?_
  rw [Finsupp.mem_support_iff, h, eraseTwo_apply_left hij] at hl
  exact hl rfl

/-- **The fibre of the substitution over a monomial free of `x_i`**: a monomial maps to
`ρ x_j^m` exactly when it is `ρ x_i^u x_j^v` with `u + v = m`. -/
theorem eraseTwo_eq_and_add_eq_of_mapDomain_collapseVar (hij : i ≠ j) {ρ : σ →₀ ℕ} (hρi : ρ i = 0)
    (hρj : ρ j = 0) {m : ℕ} {y : σ →₀ ℕ}
    (h : Finsupp.mapDomain (collapseVar i j) y = ρ + Finsupp.single j m) :
    eraseTwo i j y = ρ ∧ y i + y j = m := by
  rw [mapDomain_collapseVar hij] at h
  refine ⟨Finsupp.ext fun l => ?_, ?_⟩
  · rcases eq_or_ne l i with rfl | hi
    · rw [eraseTwo_apply_left hij, hρi]
    rcases eq_or_ne l j with rfl | hj
    · rw [eraseTwo_apply_right, hρj]
    · have hl := congrArg (fun f : σ →₀ ℕ => f l) h
      simpa [Finsupp.single_eq_of_ne hj] using hl
  · have hl := congrArg (fun f : σ →₀ ℕ => f j) h
    simpa [hρj] using hl

/-! ### The coefficients of a substituted series -/

variable {A : Type*} [CommRing A]

/-- **The coefficients of a substituted series**: the coefficient of `ρ x_j^m` in the series
obtained from `G` by substituting `x_j` for `x_i` is the sum over the `m + 1` ways of splitting `m`
between
`x_i` and `x_j`, of the coefficients of `G`. This is the usable form of the hypothesis of
`HJO.Sym.existsUnique_mem_pGraded_eq_X_sub_X_mul`, and it is where the non-injectivity of the
substitution shows: the fibre has `m + 1` members, and the vanishing of the sum does not make the
terms vanish. -/
theorem coeff_rename_collapseVar (hij : i ≠ j) (G : MvPowerSeries σ A) {ρ : σ →₀ ℕ}
    (hρi : ρ i = 0) (hρj : ρ j = 0) (m : ℕ) :
    MvPowerSeries.coeff (ρ + Finsupp.single j m) (MvPowerSeries.rename (collapseVar i j) G)
      = ∑ p ∈ Finset.antidiagonal m,
          MvPowerSeries.coeff (ρ + Finsupp.single i p.1 + Finsupp.single j p.2) G := by
  classical
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_nbij' (i := fun y : σ →₀ ℕ => (y i, y j))
    (j := fun p : ℕ × ℕ => ρ + Finsupp.single i p.1 + Finsupp.single j p.2) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    exact Finset.mem_antidiagonal.2
      (eraseTwo_eq_and_add_eq_of_mapDomain_collapseVar hij hρi hρj hy).2
  · intro p hp
    rw [Set.Finite.mem_toFinset]
    change Finsupp.mapDomain (collapseVar i j) _ = _
    rw [mapDomain_collapseVar hij, eraseTwo_add_single_add_single_eq hij hρi hρj,
      add_single_add_single_apply_left hij hρi, add_single_add_single_apply_right hij hρj,
      Finset.mem_antidiagonal.1 hp]
  · intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    rw [(eraseTwo_eq_and_add_eq_of_mapDomain_collapseVar hij hρi hρj hy).1.symm,
      eraseTwo_add_single_add_single hij]
  · intro p _
    rw [add_single_add_single_apply_left hij hρi, add_single_add_single_apply_right hij hρj]
  · intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    rw [(eraseTwo_eq_and_add_eq_of_mapDomain_collapseVar hij hρi hρj hy).1.symm,
      eraseTwo_add_single_add_single hij]

/-! ### The coefficient of a series multiplied by a letter -/

/-- The coefficient of `x_s φ` at a monomial divisible by `x_s`. -/
theorem coeff_X_mul_add (s : σ) (φ : MvPowerSeries σ A) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.single s 1 + m) (MvPowerSeries.X s * φ)
      = MvPowerSeries.coeff m φ := by
  classical
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single_of_mem (Finsupp.single s 1, m) (Finset.mem_antidiagonal.2 rfl) fun p hp hne
      => ?_]
  · rw [MvPowerSeries.coeff_X, ite_eq_left rfl, one_mul]
  · rw [MvPowerSeries.coeff_X, ite_eq_right ?_, zero_mul]
    intro hp1
    refine hne (Prod.ext hp1 ?_)
    have h := Finset.mem_antidiagonal.1 hp
    rw [hp1] at h
    exact add_left_cancel h

/-- The coefficient of `x_s φ` at a monomial not divisible by `x_s`. -/
theorem coeff_X_mul_eq_zero (s : σ) (φ : MvPowerSeries σ A) {α : σ →₀ ℕ} (h : α s = 0) :
    MvPowerSeries.coeff α (MvPowerSeries.X s * φ) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [MvPowerSeries.coeff_X, ite_eq_right ?_, zero_mul]
  intro hp1
  have hsum := Finset.mem_antidiagonal.1 hp
  have := congrArg (fun f : σ →₀ ℕ => f s) hsum
  simp only [Finsupp.add_apply, hp1, Finsupp.single_eq_same, h] at this
  omega

/-! ### The quotient -/

variable (i j : σ)

/-- The partial sums that are the quotient's coefficients: the coefficient of `H` at
`ρ x_i^u x_j^v` is `∑_{u' + s = u}\,[\,ρ x_i^{u'} x_j^{\,v + s}\,]G`. It is the unique solution of
the recursion `[\,ρ x_i^{u+1} x_j^{v}\,]G = W(u+1, v) - W(u, v+1)` that multiplying by `x_j - x_i`
imposes, with the boundary condition `W(u, 0) = 0` supplied by the hypothesis. -/
noncomputable def diffQuotSum (G : MvPowerSeries σ A) (ρ : σ →₀ ℕ) (u v : ℕ) : A :=
  ∑ p ∈ Finset.antidiagonal u,
    MvPowerSeries.coeff (ρ + Finsupp.single i p.1 + Finsupp.single j (v + p.2)) G

/-- **The quotient of a series vanishing on the diagonal by `x_j - x_i`**: the series whose
coefficient at `ρ x_i^u x_j^v` is the partial sum `HJO.Sym.diffQuotSum` at `(u, v + 1)`. -/
noncomputable def diffQuot (G : MvPowerSeries σ A) : MvPowerSeries σ A := fun α =>
  diffQuotSum i j G (eraseTwo i j α) (α i) (α j + 1)

variable {i j}

theorem diffQuotSum_apply (G : MvPowerSeries σ A) (ρ : σ →₀ ℕ) (u v : ℕ) :
    diffQuotSum i j G ρ u v = ∑ p ∈ Finset.antidiagonal u,
      MvPowerSeries.coeff (ρ + Finsupp.single i p.1 + Finsupp.single j (v + p.2)) G :=
  rfl

/-- The partial sum with no room to move: a single coefficient. -/
theorem diffQuotSum_zero (G : MvPowerSeries σ A) (ρ : σ →₀ ℕ) (v : ℕ) :
    diffQuotSum i j G ρ 0 v
      = MvPowerSeries.coeff (ρ + Finsupp.single i 0 + Finsupp.single j v) G := by
  rw [diffQuotSum_apply, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, add_zero]

/-- **The recursion the partial sums satisfy**: peeling off the term that keeps every power of
`x_i`. -/
theorem diffQuotSum_succ (G : MvPowerSeries σ A) (ρ : σ →₀ ℕ) (u v : ℕ) :
    diffQuotSum i j G ρ (u + 1) v
      = MvPowerSeries.coeff (ρ + Finsupp.single i (u + 1) + Finsupp.single j v) G
        + diffQuotSum i j G ρ u (v + 1) := by
  rw [diffQuotSum_apply, Finset.Nat.sum_antidiagonal_succ', add_zero, diffQuotSum_apply]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  rw [show v + (p.2 + 1) = v + 1 + p.2 from by omega]

theorem coeff_diffQuot_add_single_add_single (hij : i ≠ j) (G : MvPowerSeries σ A) {ρ : σ →₀ ℕ}
    (hρi : ρ i = 0) (hρj : ρ j = 0) (u v : ℕ) :
    MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v) (diffQuot i j G)
      = diffQuotSum i j G ρ u (v + 1) := by
  change diffQuotSum i j G (eraseTwo i j _) _ (_ + 1) = _
  rw [eraseTwo_add_single_add_single_eq hij hρi hρj, add_single_add_single_apply_left hij hρi,
    add_single_add_single_apply_right hij hρj]

/-! ### The quotient does what it should -/

/-- A series all of whose coefficients off total degree `d` vanish is homogeneous of degree `d`. -/
theorem isHomogeneous_of_coeff_eq_zero {φ : MvPowerSeries σ A} {d : ℕ}
    (h : ∀ α : σ →₀ ℕ, Finsupp.degree α ≠ d → MvPowerSeries.coeff α φ = 0) :
    φ.IsHomogeneous d := by
  have hw : (Finsupp.weight (1 : σ → ℕ) : (σ →₀ ℕ) →+ ℕ) = Finsupp.degree :=
    Finsupp.degree_eq_weight_one.symm
  intro α hα
  rw [show Finsupp.weight (1 : σ → ℕ) α = Finsupp.degree α from by rw [hw]]
  by_contra hne
  exact hα (h α hne)

/-- **The quotient is homogeneous one degree lower**: each of its coefficients is a sum of
coefficients of `G` at monomials of one higher total degree. -/
theorem isHomogeneous_diffQuot (hij : i ≠ j) {d : ℕ} {G : MvPowerSeries σ A}
    (hG : G.IsHomogeneous (d + 1)) : (diffQuot i j G).IsHomogeneous d := by
  refine isHomogeneous_of_coeff_eq_zero fun α hα => ?_
  have hd : Finsupp.degree α
      = Finsupp.degree (eraseTwo i j α) + α i + α j := by
    conv_lhs => rw [← eraseTwo_add_single_add_single hij α]
    rw [degree_add_single_add_single]
  change diffQuotSum i j G (eraseTwo i j α) (α i) (α j + 1) = 0
  rw [diffQuotSum_apply]
  refine Finset.sum_eq_zero fun p hp => hG.coeff_eq_zero ?_
  have hp' := Finset.mem_antidiagonal.1 hp
  rw [degree_add_single_add_single]
  omega

/-- A split monomial with one more `x_j`. -/
theorem add_single_add_single_succ_right (ρ : σ →₀ ℕ) (u v : ℕ) :
    ρ + Finsupp.single i u + Finsupp.single j (v + 1)
      = Finsupp.single j 1 + (ρ + Finsupp.single i u + Finsupp.single j v) := by
  rw [show v + 1 = 1 + v from by omega, Finsupp.single_add]
  abel

/-- A split monomial with one more `x_i`. -/
theorem add_single_succ_add_single_left (ρ : σ →₀ ℕ) (u v : ℕ) :
    ρ + Finsupp.single i (u + 1) + Finsupp.single j v
      = Finsupp.single i 1 + (ρ + Finsupp.single i u + Finsupp.single j v) := by
  rw [show u + 1 = 1 + u from by omega, Finsupp.single_add]
  abel

/-- **Vanishing on the diagonal is divisibility by the difference**, the identity read at a split
monomial. The hypothesis is spent exactly once, in the case `v = 0`: there the coefficient of
`x_j H` is `0` and the *whole* partial sum has to vanish, which is what the substitution says. -/
theorem coeff_X_sub_X_mul_diffQuot_split (hij : i ≠ j) {G : MvPowerSeries σ A}
    (h0 : MvPowerSeries.rename (collapseVar i j) G = 0) {ρ : σ →₀ ℕ} (hρi : ρ i = 0)
    (hρj : ρ j = 0) (u v : ℕ) :
    MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v)
        ((MvPowerSeries.X j - MvPowerSeries.X i) * diffQuot i j G)
      = MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v) G := by
  have hbnd : ∀ u : ℕ, diffQuotSum i j G ρ u 0 = 0 := fun u => by
    have hcr := coeff_rename_collapseVar hij G hρi hρj u
    rw [h0, MvPowerSeries.coeff_zero] at hcr
    rw [diffQuotSum_apply]
    simpa using hcr.symm
  have hXj : MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v)
      (MvPowerSeries.X j * diffQuot i j G) = diffQuotSum i j G ρ u v := by
    cases v with
    | zero => rw [coeff_X_mul_eq_zero j _ (add_single_add_single_apply_right hij hρj u 0), hbnd]
    | succ v =>
      rw [add_single_add_single_succ_right, coeff_X_mul_add,
        coeff_diffQuot_add_single_add_single hij G hρi hρj]
  have hXi : MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v)
      (MvPowerSeries.X i * diffQuot i j G)
      = diffQuotSum i j G ρ u v
        - MvPowerSeries.coeff (ρ + Finsupp.single i u + Finsupp.single j v) G := by
    cases u with
    | zero =>
      rw [coeff_X_mul_eq_zero i _ (add_single_add_single_apply_left hij hρi 0 v),
        diffQuotSum_zero, sub_self]
    | succ u =>
      rw [add_single_succ_add_single_left, coeff_X_mul_add,
        coeff_diffQuot_add_single_add_single hij G hρi hρj, diffQuotSum_succ,
        ← add_single_succ_add_single_left]
      ring
  rw [sub_mul, map_sub, hXj, hXi]
  ring

/-- **Vanishing on the diagonal is divisibility by the difference**, the identity: the series
`HJO.Sym.diffQuot` multiplied by `x_j - x_i` is `G` again. -/
theorem coeff_X_sub_X_mul_diffQuot (hij : i ≠ j) {G : MvPowerSeries σ A}
    (h0 : MvPowerSeries.rename (collapseVar i j) G = 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α ((MvPowerSeries.X j - MvPowerSeries.X i) * diffQuot i j G)
      = MvPowerSeries.coeff α G := by
  have h := coeff_X_sub_X_mul_diffQuot_split hij h0 (eraseTwo_apply_left hij α)
    (eraseTwo_apply_right i j α) (α i) (α j)
  rwa [eraseTwo_add_single_add_single hij α] at h

/-- **Vanishing on the diagonal is divisibility by the difference**, existence, over any commutative
ring: `HJO.Sym.diffQuot` is homogeneous one degree lower and is a quotient. -/
theorem isHomogeneous_and_eq_X_sub_X_mul_diffQuot (hij : i ≠ j) {d : ℕ} {G : MvPowerSeries σ A}
    (hG : G.IsHomogeneous (d + 1)) (h0 : MvPowerSeries.rename (collapseVar i j) G = 0) :
    (diffQuot i j G).IsHomogeneous d ∧
      G = (MvPowerSeries.X j - MvPowerSeries.X i) * diffQuot i j G :=
  ⟨isHomogeneous_diffQuot hij hG,
    (MvPowerSeries.ext fun α => coeff_X_sub_X_mul_diffQuot hij h0 α).symm⟩

/-- The difference of two distinct letters is not `0`. This, and not invertibility, is what the
uniqueness of the quotient needs. -/
theorem X_sub_X_ne_zero [Nontrivial A] (hij : i ≠ j) :
    (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries σ A) ≠ 0 := by
  classical
  intro h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h
  rw [map_sub, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, MvPowerSeries.coeff_zero,
    ite_eq_left rfl, ite_eq_right (fun hs => ?_), sub_zero] at hc
  · exact one_ne_zero hc
  · have h2 := congrArg (fun f : σ →₀ ℕ => f j) hs
    simp [hij] at h2

/-- **The hypothesis is satisfiable**: `x_j - x_i` itself vanishes on the diagonal. So the lemma is
not vacuous, and at `d = 0` it returns the quotient `1`. -/
theorem rename_collapseVar_X_sub_X (i j : σ) :
    MvPowerSeries.rename (collapseVar i j)
        (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries σ A) = 0 := by
  rw [map_sub, MvPowerSeries.rename_X, MvPowerSeries.rename_X, collapseVar_self, collapseVar_right,
    sub_self]

/-! ### The lemma in the series ring of the Carlsson--Mellit analysis -/

/-- **Vanishing on the diagonal is divisibility by the difference.** Let `G` be a series in the
graded part `P^gr_{k,d+1}` of `P°_k` and let `i ≠ j` be letters such that substituting `x_j` for
`x_i` in `G` gives `0`. Then `G = (x_j - x_i)H` for a unique `H ∈ P^gr_{k,d}`.

The divisor is not invertible; what licenses the division is the vanishing on the diagonal, and what
makes the quotient unique is that `P°_k` is a domain and `x_j - x_i ≠ 0`. The `d ≥ 1`
with the quotient in `P^gr_{k,d-1}` is written with the successor, no `ℕ`-subtraction appearing. -/
@[hjo "lem_cm_diff_divides"]
theorem existsUnique_mem_pGraded_eq_X_sub_X_mul {K : Type*} [CommRing K] [IsDomain K] {k d : ℕ}
    {G : AuxAlphabetSeriesFrac K k} (hG : G ∈ pGraded K k (d + 1)) {i j : ℕ} (hij : i ≠ j)
    (h0 : MvPowerSeries.rename (collapseVar i j) G = 0) :
    ∃! H : AuxAlphabetSeriesFrac K k,
      H ∈ pGraded K k d ∧ G = (MvPowerSeries.X j - MvPowerSeries.X i) * H := by
  obtain ⟨hhom, heq⟩ := isHomogeneous_and_eq_X_sub_X_mul_diffQuot hij hG h0
  refine ⟨diffQuot i j G, ⟨hhom, heq⟩, ?_⟩
  rintro H' ⟨-, heq'⟩
  exact mul_left_cancel₀ (X_sub_X_ne_zero hij) (heq'.symm.trans heq)

end HJO.Sym
