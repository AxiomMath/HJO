/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitInductionBraid

/-! # Base change for `HJO.Mellit.mellitInduction_sweepWitness`

Every operator of the sweep witness `HJO.Mellit.sweepWitness q u a b` is defined uniformly in the
coefficient field: the swaps and divided differences, the Demazure–Lusztig operators `T_i` and
their inverses, the trains, the alphabet shifts, `d_-`, `d_+`, `Δ`, the cyclic shift, `d^*_+`,
`z_1`, the sweep operators and the colouring invariant `D_{η,c}`. A ring map `φ : L → K` of fields
therefore induces a coefficient map `Λ_L[y_1, y_2, …] → Λ_K[y_1, y_2, …]`, injective because `φ`
is, which intertwines each operator over `L` at the parameters `(q, u)` with the same operator over
`K` at `(φ q, φ u)`. So the identity `D_{η,c_α} = (-1)^{(a-1)N}(qu)^{ℓ-N} G_{ℓ,α_ℓ} ⋯ G_{1,α_1}(1)`
of `HJO.Mellit.mellitInduction_sweepWitness` over `K` maps back to the same identity over `L`: the
clause descends along field extensions.

The application is to the square root of `q`. The braid representation that computes the right-hand
side needs `r` with `r² = q`, which the field `ℚ(q, u)` does not contain. Passing to the algebraic
closure supplies it, and the descent brings the clause back.

## Main definitions

* `HJO.Sweep.totalMap φ`: the coefficient map `Total L →+* Total K`.
* `HJO.Mellit.gradedMap φ`: the same map on the graded total space, degree by degree.

## Main results

* `HJO.Mellit.mellitInduction_of_ringHom`, `HJO.Mellit.mellitInduction_of_algebraMap`: the clause
  `HJO.Mellit.MellitInduction` at the sweep witness descends along a field map.
* `HJO.Mellit.mellitInduction_sweepWitness_of_sweepRecursionBEFloor'`:
  `HJO.Mellit.mellitInduction_sweepWitness` at every algebraically independent pair `(q, u)`, with
  no hypothesis that `q` is a square, from the type-`BE` clause of the braid recursion over every
  field.

## Implementation notes

The descent assumes `a` and `b` coprime and `0 < a`. Both sides of the clause quantify over every
replication family, and an arbitrary family over `L` is compared with one over `K` through the
canonical family `HJO.Mellit.replFamily`, which is defined uniformly in the field; that the stage
word does not depend on the family (`HJO.Mellit.stageWord_congr`) needs exactly these hypotheses.
At a non-coprime slope `Ω(1; a, b)` is not constrained by the recursion at all.

The `BE` clause is assumed over every field in the universe of `L`, because it is used over the
algebraic closure of `L` rather than over `L` itself.

## References

* [A. Mellit, *Toric braids and (m,n)-parking functions*][mellit2016], Section 5, for
  `HJO.Mellit.mellitInduction_sweepWitness`.
-/

@[expose] public section

namespace HJO.Sweep

open MvPolynomial

variable {L K : Type*} [Field L] [Field K] (φ : L →+* K)

/-- The coefficient map `Total L → Total K` induced by a ring map `L → K`. -/
noncomputable def totalMap : Total L →+* Total K := MvPolynomial.map (MvPolynomial.map φ)

/-- `totalMap φ` is injective. -/
theorem totalMap_injective : Function.Injective (totalMap φ) :=
  MvPolynomial.map_injective _ (MvPolynomial.map_injective _ φ.injective)

/-- `totalMap φ` maps a constant `C c` to `C (map φ c)`. -/
@[simp] theorem totalMap_C (c : Sym.Lambda L) :
    totalMap φ (C c) = C (MvPolynomial.map φ c) := map_C _ _

/-- `totalMap φ` fixes the alphabet variables `X j`. -/
@[simp] theorem totalMap_X (j : ℕ) : totalMap φ (X j : Total L) = X j := map_X _ _

/-- `totalMap φ` fixes the auxiliary variables `y_i`. -/
@[simp] theorem totalMap_auxVar (i : ℕ) : totalMap φ (auxVar i : Total L) = auxVar i :=
  map_X _ _

/-- `totalMap φ` maps the scalar `x` to the scalar `φ x`. -/
@[simp] theorem totalMap_scal (x : L) : totalMap φ (scal x) = scal (φ x) := by
  simp [scal]

/-- `totalMap φ` is `φ`-semilinear: `totalMap φ (x • F) = φ x • totalMap φ F`. -/
theorem totalMap_smul (x : L) (F : Total L) : totalMap φ (x • F) = φ x • totalMap φ F := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← scal_eq_algebraMap, ← scal_eq_algebraMap,
    totalMap_scal]

/-- `totalMap φ` intertwines the swaps of the auxiliary variables. -/
theorem totalMap_swapAux (i : ℕ) (F : Total L) :
    totalMap φ (swapAux L i F) = swapAux K i (totalMap φ F) := by
  simp [swapAux, totalMap, MvPolynomial.map_rename]

/-- `totalMap φ` intertwines the divided differences. -/
theorem totalMap_dividedDiff (i : ℕ) (F : Total L) :
    totalMap φ (dividedDiff i F) = dividedDiff i (totalMap φ F) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [dividedDiff_zero_index]
  refine dividedDiff_unique hi ?_
  have h := congrArg (totalMap φ) (dividedDiff_spec i F)
  simpa [map_mul, map_sub, totalMap_swapAux] using h

/-- `totalMap φ` intertwines `T_i` at `q` with `T_i` at `φ q`. -/
theorem totalMap_braid (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (braid q i F) = braid (φ q) i (totalMap φ F) := by
  simp [braid_apply, totalMap_swapAux, totalMap_dividedDiff]

/-- `totalMap φ` intertwines `T_i⁻¹` at `q` with `T_i⁻¹` at `φ q`. -/
theorem totalMap_braidInv (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (braidInv q i F) = braidInv (φ q) i (totalMap φ F) := by
  simp [braidInv_apply, totalMap_braid]

/-- A product of operators each intertwined with its counterpart by `totalMap φ` is intertwined
with the product of the counterparts. -/
theorem totalMap_list_prod {ι : Type*} (f : ι → Module.End L (Total L))
    (g : ι → Module.End K (Total K)) (l : List ι)
    (h : ∀ i ∈ l, ∀ F, totalMap φ (f i F) = g i (totalMap φ F)) (F : Total L) :
    totalMap φ ((l.map f).prod F) = (l.map g).prod (totalMap φ F) := by
  induction l generalizing F with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

/-- `totalMap φ` intertwines the endomorphism `T_i` at `q` with `T_i` at `φ q`. -/
theorem totalMap_braidEnd (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (braidEnd q i F) = braidEnd (φ q) i (totalMap φ F) :=
  totalMap_braid φ q i F

/-- `totalMap φ` intertwines the endomorphism `T_i⁻¹` at `q` with `T_i⁻¹` at `φ q`. -/
theorem totalMap_braidInvEnd (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (braidInvEnd q i F) = braidInvEnd (φ q) i (totalMap φ F) :=
  totalMap_braidInv φ q i F

/-- `totalMap φ` intertwines the upward train at `q` with the upward train at `φ q`. -/
theorem totalMap_trainUpEnd (q : L) (a b : ℕ) (F : Total L) :
    totalMap φ (trainUpEnd q a b F) = trainUpEnd (φ q) a b (totalMap φ F) := by
  rw [trainUpEnd, trainUpEnd, Braid.trainUp, Braid.trainUp]
  split_ifs
  · exact totalMap_list_prod φ _ _ _ (fun i _ F => totalMap_braidEnd φ q i F) F
  · exact totalMap_list_prod φ _ _ _ (fun i _ F => totalMap_braidInvEnd φ q i F) F

/-- `totalMap φ` intertwines the downward train at `q` with the downward train at `φ q`. -/
theorem totalMap_trainDownEnd (q : L) (a b : ℕ) (F : Total L) :
    totalMap φ (trainDownEnd q a b F) = trainDownEnd (φ q) a b (totalMap φ F) := by
  rw [trainDownEnd, trainDownEnd, Braid.trainDown, Braid.trainDown]
  split_ifs
  · exact totalMap_list_prod φ _ _ _ (fun i _ F => totalMap_braidEnd φ q i F) F
  · exact totalMap_list_prod φ _ _ _ (fun i _ F => totalMap_braidInvEnd φ q i F) F

/-- Two ring maps out of `Total L` agree once they agree on the doubly constant elements and on the
two families of variables. -/
theorem total_ringHom_ext {R : Type*} [CommRing R] {f g : Total L →+* R}
    (hC : ∀ x : L, f (C (C x)) = g (C (C x))) (hp : ∀ j, f (C (X j)) = g (C (X j)))
    (hX : ∀ j, f (X j) = g (X j)) : f = g := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) hX
  have : f.comp C = g.comp C := MvPolynomial.ringHom_ext hC hp
  exact congrArg (fun h : Sym.Lambda L →+* R => h c) this

/-- `totalMap φ` intertwines the alphabet shift at `q` with the alphabet shift at `φ q`. -/
theorem totalMap_qshift (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (qshift q i F) = qshift (φ q) i (totalMap φ F) := by
  have h : (totalMap φ).comp (qshift q i).toRingHom
      = (qshift (φ q) i).toRingHom.comp (totalMap φ) := by
    refine total_ringHom_ext (fun x => ?_) (fun j => ?_) (fun j => ?_)
    · simp [qshift, MvPolynomial.aevalTower_C, totalMap]
    · simp [qshift, MvPolynomial.aevalTower_C, totalMap, scal, auxVar]
    · simp [qshift, totalMap]
  exact congrArg (fun f : Total L →+* Total K => f F) h

/-- `totalMap φ` intertwines the negative alphabet shift at `q` with that at `φ q`. -/
theorem totalMap_qshiftNeg (q : L) (i : ℕ) (F : Total L) :
    totalMap φ (qshiftNeg q i F) = qshiftNeg (φ q) i (totalMap φ F) := by
  have h : (totalMap φ).comp (qshiftNeg q i).toRingHom
      = (qshiftNeg (φ q) i).toRingHom.comp (totalMap φ) := by
    refine total_ringHom_ext (fun x => ?_) (fun j => ?_) (fun j => ?_)
    · simp [qshiftNeg, MvPolynomial.aevalTower_C, totalMap]
    · simp [qshiftNeg, MvPolynomial.aevalTower_C, totalMap, scal, auxVar]
    · simp [qshiftNeg, totalMap]
  exact congrArg (fun f : Total L →+* Total K => f F) h

/-- `totalMap φ` intertwines the cyclic shift at `u` with the cyclic shift at `φ u`. -/
theorem totalMap_cycleShift (u : L) (k : ℕ) (F : Total L) :
    totalMap φ (cycleShift u k F) = cycleShift (φ u) k (totalMap φ F) := by
  have h : (totalMap φ).comp (cycleShift u k).toRingHom
      = (cycleShift (φ u) k).toRingHom.comp (totalMap φ) := by
    refine total_ringHom_ext (fun x => ?_) (fun j => ?_) (fun j => ?_)
    · simp [cycleShift, totalMap]
    · simp [cycleShift, totalMap]
    · simp only [cycleShift, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X, totalMap_X]
      split_ifs <;> simp [scal]
  exact congrArg (fun f : Total L →+* Total K => f F) h

section Newton

variable [Algebra ℚ L] [Algebra ℚ K]

/-- The coefficient map `φ` sends the elementary symmetric function `e_n` over `L` to `e_n` over
`K`. -/
theorem map_elemSymm (n : ℕ) :
    MvPolynomial.map φ (Sym.elemSymm L n) = Sym.elemSymm K n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [Sym.elemSymm, Sym.elemSymm, map_one]
    · rw [Sym.elemSymm, Sym.elemSymm, map_mul, map_C, RingHom.map_rat_algebraMap, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
      rw [map_mul, map_mul, map_pow, map_neg, map_one, ih _ (by
        have := Finset.mem_range.1 hk; omega)]
      simp [Sym.powerSum]

/-- `lowerCoeff M j` on the monomial `monomial d c`. -/
theorem lowerCoeff_monomial_eq {M : Type*} [Field M] [Algebra ℚ M] (j : ℕ) (d : ℕ →₀ ℕ)
    (c : Sym.Lambda M) :
    lowerCoeff M j (monomial d c)
      = C c * ((-1 : Total M) ^ d j * C (Sym.elemSymm M (d j)) *
        monomial (Finsupp.erase j d) 1) := by
  have : (monomial d c : Total M) = c • monomial d 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq, lowerCoeff_monomial]

/-- `totalMap φ` intertwines `lowerCoeff j`. -/
theorem totalMap_lowerCoeff (j : ℕ) (F : Total L) :
    totalMap φ (lowerCoeff L j F) = lowerCoeff K j (totalMap φ F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [lowerCoeff_monomial_eq]
    simp only [totalMap, map_monomial]
    rw [lowerCoeff_monomial_eq]
    simp [map_elemSymm]
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add, map_add]

/-- `totalMap φ` intertwines `d_-` at `q` with `d_-` at `φ q`. -/
theorem totalMap_dminus (q : L) (k : ℕ) (F : Total L) :
    totalMap φ (dminus q k F) = dminus (φ q) k (totalMap φ F) := by
  rw [dminus_apply, dminus_apply, totalMap_lowerCoeff, totalMap_qshiftNeg]

omit [Algebra ℚ L] [Algebra ℚ K] in
/-- `totalMap φ` intertwines `d_+` at `q` with `d_+` at `φ q`. -/
theorem totalMap_dplus (q : L) (k : ℕ) (F : Total L) :
    totalMap φ (dplus q k F) = dplus (φ q) k (totalMap φ F) := by
  rw [dplus_apply, dplus_apply, map_neg, totalMap_trainUpEnd, map_mul, totalMap_auxVar,
    totalMap_qshift]

omit [Algebra ℚ L] [Algebra ℚ K] in
/-- `totalMap φ` intertwines `d^*_+` at `(q, u)` with `d^*_+` at `(φ q, φ u)`. -/
theorem totalMap_dplusStar (q u : L) (k : ℕ) (F : Total L) :
    totalMap φ (dplusStar q u k F) = dplusStar (φ q) (φ u) k (totalMap φ F) := by
  rw [dplusStar_apply, dplusStar_apply, totalMap_cycleShift, totalMap_qshift]

/-- `totalMap φ` intertwines the corner operator at `q` with that at `φ q`. -/
theorem totalMap_corner (q : L) (k : ℕ) (F : Total L) :
    totalMap φ (corner q k F) = corner (φ q) k (totalMap φ F) := by
  rw [corner, corner, LinearMap.smul_apply, LinearMap.smul_apply, totalMap_smul, map_inv₀,
    map_sub, map_one]
  split_ifs
  · simp only [Module.End.mul_apply, totalMap_dminus, totalMap_dplus]
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, totalMap_dminus,
      totalMap_dplus]

/-- `totalMap φ` intertwines `z_1` at `(q, u)` with `z_1` at `(φ q, φ u)`. -/
theorem totalMap_zopOneStar (q u : L) (k : ℕ) (F : Total L) :
    totalMap φ (zopOneStar q u k F) = zopOneStar (φ q) (φ u) k (totalMap φ F) := by
  simp only [zopOneStar, LinearMap.smul_apply, totalMap_smul, Module.End.mul_apply,
    LinearMap.sub_apply, map_sub, totalMap_dminus, totalMap_dplusStar, totalMap_trainUpEnd,
    map_div₀, map_pow, map_one]

end Newton

end HJO.Sweep

universe v

namespace HJO.Mellit

open Sweep Paths

variable {L K : Type*} [Field L] [Field K] (φ : L →+* K)

/-! ### The sweep operators and the colouring invariant -/

/-- `totalMap φ` intertwines each sweep operator at `(q, u)` with the same sweep operator at
`(φ q, φ u)`. -/
theorem totalMap_sweepOperator [Algebra ℚ L] [Algebra ℚ K] (q u : L) {a b N : ℕ}
    (y : Heights a b N) (P : ℕ × ℕ) (F : Total L) :
    totalMap φ (sweepOperator q u y P F) = sweepOperator (φ q) (φ u) y P (totalMap φ F) := by
  unfold sweepOperator
  generalize eventType y P = e
  cases e
  · exact totalMap_dplus φ q _ F
  · exact totalMap_dminus φ q _ F
  · simp only [LinearMap.smul_apply, totalMap_smul, totalMap_corner, map_zpow₀]
  · simp only [LinearMap.smul_apply, totalMap_smul, Module.End.one_apply, map_pow]
  · simp only [LinearMap.smul_apply, totalMap_smul, Module.End.one_apply]

/-- `totalMap φ` intertwines the partial sweep word at `(q, u)` with that at `(φ q, φ u)`. -/
theorem totalMap_partialSweepWord [Algebra ℚ L] [Algebra ℚ K] (q u : L) {a b N : ℕ}
    (y : Heights a b N) (η : ℚ) (F : Total L) :
    totalMap φ (partialSweepWord q u y η F)
      = partialSweepWord (φ q) (φ u) y η (totalMap φ F) :=
  totalMap_list_prod φ _ _ _ (fun P _ F => totalMap_sweepOperator φ q u y P F) F

/-- `totalMap φ` maps `D_{η,c}` at `(q, u)` to `D_{η,c}` at `(φ q, φ u)`. -/
theorem totalMap_dsc [Algebra ℚ L] [Algebra ℚ K] (q u : L) (a b N : ℕ) (η : ℚ)
    (c : Finset (ℕ × ℕ)) : totalMap φ (dsc q u a b N η c) = dsc (φ q) (φ u) a b N η c := by
  simp only [dsc, map_sum, totalMap_partialSweepWord, map_one]

/-! ### The graded total space -/

/-- The coefficient map `Graded L → Graded K`, degreewise `totalMap φ`. -/
noncomputable def gradedMap : Graded L →+ Graded K :=
  DFinsupp.mapRange.addMonoidHom fun _ => (totalMap φ).toAddMonoidHom

/-- The degree-`k` component of `gradedMap φ x` is `totalMap φ (x k)`. -/
theorem gradedMap_apply (x : Graded L) (k : ℕ) : gradedMap φ x k = totalMap φ (x k) :=
  rfl

/-- `gradedMap φ` is injective. -/
theorem gradedMap_injective : Function.Injective (gradedMap φ) := by
  intro x y h
  refine DFinsupp.ext fun k => totalMap_injective φ ?_
  rw [← gradedMap_apply, ← gradedMap_apply, h]

/-- `gradedMap φ` maps `F` placed in degree `k` to `totalMap φ F` placed in degree `k`. -/
theorem gradedMap_gradedIn (k : ℕ) (F : Total L) :
    gradedMap φ (gradedIn L k F) = gradedIn K k (totalMap φ F) := by
  change DFinsupp.mapRange (fun _ => totalMap φ) (fun _ => map_zero _) (DFinsupp.single k F)
    = DFinsupp.single k (totalMap φ F)
  exact DFinsupp.mapRange_single

/-- `gradedMap φ` is `φ`-semilinear. -/
theorem gradedMap_smul (c : L) (x : Graded L) : gradedMap φ (c • x) = φ c • gradedMap φ x := by
  refine DFinsupp.ext fun j => ?_
  rw [gradedMap_apply]
  change totalMap φ (c • x j) = φ c • gradedMap φ x j
  rw [gradedMap_apply, totalMap_smul]

/-- `gradedMap φ` intertwines two degreewise operators whose components are intertwined by
`totalMap φ`. -/
theorem gradedMap_gradedOp {f : ℕ → Module.End L (Total L)} {g : ℕ → Module.End K (Total K)}
    (s : ℕ → ℕ) (h : ∀ k F, totalMap φ (f k F) = g k (totalMap φ F)) (x : Graded L) :
    gradedMap φ (gradedOp f s x) = gradedOp g s (gradedMap φ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of k F =>
    rw [← DirectSum.lof_eq_of L, ← gradedIn, gradedOp_apply, gradedMap_gradedIn,
      gradedMap_gradedIn, gradedOp_apply, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-! ### The sweep witness -/

section Witness

variable [Algebra ℚ L] [Algebra ℚ K] (q u : L) (a b : ℕ)

/-- `replFamily S` is a replication family for the sweep system `S`. -/
theorem isReplicationFamily_replFamily {M : Type*} [Field M] [Algebra ℚ M] {q' u' : M}
    (S : SweepSystem M q' u') : IsReplicationFamily S (replFamily S) := by
  refine ⟨fun m n k => (omegaAux_shape S (m + n)).1 m n k,
    fun m n k => (omegaAux_shape S (m + n)).2.1 m n k,
    fun m n k => (omegaAux_shape S (m + n)).2.2 m n k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change omegaStep S (omegaAux S 0) 1 1 0 = S.dplusStar
    rw [omegaStep_one]
    norm_num
  · change omegaStep S (omegaAux S 0) 2 1 0 = S.z1
    rw [omegaStep_two]
    norm_num
  · change omegaStep S (omegaAux S 0) 3 0 1 = S.y1
    rw [omegaStep_three]
    norm_num
  all_goals
    intro m n m₁ n₁ hmn hm hn hp
    obtain ⟨hlt1, hlt2⟩ := isSBParent_sum_lt hm hn hp
    have hpar : sbParent m n = (m₁, n₁) := sbParent_eq hmn hm hn hp
    have hp1 : (sbParent m n).1 = m₁ := by rw [hpar]
    have hp2 : (sbParent m n).2 = n₁ := by rw [hpar]
    obtain ⟨f, hf⟩ : ∃ f, m + n = f + 1 := ⟨m + n - 1, by omega⟩
    have e3 : omegaAux S f 3 m₁ n₁ = replFamily S 3 m₁ n₁ := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    have e1 : omegaAux S f 1 (m - m₁) (n - n₁) = replFamily S 1 (m - m₁) (n - n₁) := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    have e2 : omegaAux S f 2 (m - m₁) (n - n₁) = replFamily S 2 (m - m₁) (n - n₁) := by
      rw [replFamily_eq]; exact (omegaAux_eq_of_le S le_rfl (by omega)).symm
    rw [replFamily_eq, hf, omegaAux_succ_eq]
  · rw [omegaStep_one, ite_eq_right (show ¬(m = 1 ∧ n = 0) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e1]
  · rw [omegaStep_two, ite_eq_right (show ¬(m = 1 ∧ n = 0) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e2]
  · rw [omegaStep_three, ite_eq_right (show ¬(m = 0 ∧ n = 1) by omega),
      ite_eq_left (⟨hm, hn, hmn⟩ : 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n), hp1, hp2, e3, e2]

/-- `HJO.Mellit.gradedMap`, read between the total spaces of the two sweep witnesses. -/
noncomputable def witnessMap :
    (sweepWitness q u a b).W →+ (sweepWitness (φ q) (φ u) a b).W :=
  gradedMap φ

/-- `witnessMap φ q u a b` is injective. -/
theorem witnessMap_injective : Function.Injective (witnessMap φ q u a b) :=
  gradedMap_injective φ

/-- `witnessMap φ q u a b` is `φ`-semilinear. -/
theorem witnessMap_smul (c : L) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b (c • x) = φ c • witnessMap φ q u a b x :=
  gradedMap_smul φ c x

/-- `witnessMap φ q u a b` intertwines the `d^*_+` of the two sweep witnesses. -/
theorem witnessMap_dplusStar (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b ((sweepWitness q u a b).dplusStar x)
      = (sweepWitness (φ q) (φ u) a b).dplusStar (witnessMap φ q u a b x) :=
  gradedMap_gradedOp φ _ (fun k F => totalMap_dplusStar φ q u k F) x

/-- `witnessMap φ q u a b` intertwines the `z_1` of the two sweep witnesses. -/
theorem witnessMap_z1 (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b ((sweepWitness q u a b).z1 x)
      = (sweepWitness (φ q) (φ u) a b).z1 (witnessMap φ q u a b x) := by
  refine gradedMap_gradedOp φ _ (fun k F => ?_) x
  rcases k with _ | k
  · simp [z1Fam]
  · exact totalMap_zopOneStar φ q u _ F

/-- `witnessMap φ q u a b` intertwines the `y_1` of the two sweep witnesses. -/
theorem witnessMap_y1 (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b ((sweepWitness q u a b).y1 x)
      = (sweepWitness (φ q) (φ u) a b).y1 (witnessMap φ q u a b x) := by
  refine gradedMap_gradedOp φ _ (fun k F => ?_) x
  rcases k with _ | k
  · simp [y1Fam]
  · simp [y1Fam]

/-- `witnessMap φ q u a b` intertwines the downward trains of the two sweep witnesses. -/
theorem witnessMap_trainDown (j : ℕ) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b ((sweepWitness q u a b).trainDown j x)
      = (sweepWitness (φ q) (φ u) a b).trainDown j (witnessMap φ q u a b x) := by
  refine gradedMap_gradedOp φ _ (fun k F => ?_) x
  rw [trainDownFam, trainDownFam]
  split_ifs
  · exact totalMap_trainDownEnd φ q j 1 F
  · simp

/-- `witnessMap φ q u a b` intertwines the upward trains of the two sweep witnesses. -/
theorem witnessMap_trainUp (j : ℕ) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b ((sweepWitness q u a b).trainUp j x)
      = (sweepWitness (φ q) (φ u) a b).trainUp j (witnessMap φ q u a b x) := by
  refine gradedMap_gradedOp φ _ (fun k F => ?_) x
  rw [trainUpFam, trainUpFam]
  split_ifs
  · exact totalMap_trainUpEnd φ q 1 j F
  · simp

/-- `witnessMap φ q u a b` maps the vacuum to the vacuum. -/
theorem witnessMap_vac :
    witnessMap φ q u a b (sweepWitness q u a b).vac = (sweepWitness (φ q) (φ u) a b).vac :=
  (gradedMap_gradedIn φ 0 1).trans (by rw [map_one]; rfl)

/-- `witnessMap φ q u a b` maps `D_{η,c}` of one sweep witness to `D_{η,c}` of the other. -/
theorem witnessMap_D (η : ℚ) (c : Finset (ℕ × ℕ)) :
    witnessMap φ q u a b ((sweepWitness q u a b).D η c)
      = (sweepWitness (φ q) (φ u) a b).D η c :=
  (gradedMap_gradedIn φ _ _).trans (by rw [totalMap_dsc]; rfl)

/-- `witnessMap φ q u a b` intertwines `omegaAux f j m n` of the two sweep witnesses. -/
theorem witnessMap_omegaAux (f j m n : ℕ) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b (omegaAux (sweepWitness q u a b) f j m n x)
      = omegaAux (sweepWitness (φ q) (φ u) a b) f j m n (witnessMap φ q u a b x) := by
  induction f generalizing j m n x with
  | zero => exact map_zero (witnessMap φ q u a b)
  | succ f ih =>
    rw [omegaAux_succ_eq, omegaAux_succ_eq, omegaStep, omegaStep]
    split_ifs
    · exact witnessMap_dplusStar φ q u a b x
    · exact witnessMap_z1 φ q u a b x
    · exact witnessMap_y1 φ q u a b x
    · rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      exact (map_neg (witnessMap φ q u a b) _).trans (by rw [ih, ih])
    · rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      exact (map_neg (witnessMap φ q u a b) _).trans (by rw [ih, ih])
    · rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.comp_apply]
      refine (map_neg (witnessMap φ q u a b) _).trans ?_
      rw [witnessMap_smul, ih, ih, map_inv₀, map_mul]
    · exact map_zero (witnessMap φ q u a b)
    · exact map_zero (witnessMap φ q u a b)

/-- `witnessMap φ q u a b` intertwines the canonical replication families of the two sweep
witnesses. -/
theorem witnessMap_replFamily (j m n : ℕ) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b (replFamily (sweepWitness q u a b) j m n x)
      = replFamily (sweepWitness (φ q) (φ u) a b) j m n (witnessMap φ q u a b x) :=
  witnessMap_omegaAux φ q u a b _ j m n x

/-- `witnessMap φ q u a b` intertwines the stage operators of the two sweep witnesses, each built
from its canonical replication family. -/
theorem witnessMap_stage (k A : ℕ) (x : (sweepWitness q u a b).W) :
    witnessMap φ q u a b
        (stage (sweepWitness q u a b) (replFamily (sweepWitness q u a b)) a b k A x)
      = stage (sweepWitness (φ q) (φ u) a b) (replFamily (sweepWitness (φ q) (φ u) a b)) a b k A
          (witnessMap φ q u a b x) := by
  have hZ : ∀ y : (sweepWitness q u a b).W, witnessMap φ q u a b
      (replicatedLetter (sweepWitness q u a b) (replFamily (sweepWitness q u a b)) a b k y)
      = replicatedLetter (sweepWitness (φ q) (φ u) a b)
          (replFamily (sweepWitness (φ q) (φ u) a b)) a b k (witnessMap φ q u a b y) := by
    intro y
    rw [replicatedLetter, replicatedLetter, LinearMap.smul_apply, LinearMap.smul_apply,
      witnessMap_smul, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, witnessMap_trainDown, witnessMap_replFamily,
      witnessMap_trainUp, map_zpow₀]
  have hpow : ∀ (n : ℕ) (y : (sweepWitness q u a b).W), witnessMap φ q u a b
      (((replicatedLetter (sweepWitness q u a b) (replFamily (sweepWitness q u a b)) a b k)
        ^ n) y)
      = ((replicatedLetter (sweepWitness (φ q) (φ u) a b)
          (replFamily (sweepWitness (φ q) (φ u) a b)) a b k) ^ n) (witnessMap φ q u a b y) := by
    intro n
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hZ]
  simp only [stage, LinearMap.comp_apply, hpow, witnessMap_trainDown,
    witnessMap_replFamily]

/-- `witnessMap φ q u a b` maps the stage word of one sweep witness to that of the other, each
built from its canonical replication family. -/
theorem witnessMap_stageWord (α : List ℕ) :
    witnessMap φ q u a b
        (stageWord (sweepWitness q u a b) (replFamily (sweepWitness q u a b)) a b α)
      = stageWord (sweepWitness (φ q) (φ u) a b) (replFamily (sweepWitness (φ q) (φ u) a b))
          a b α := by
  have h : ∀ (α : List ℕ) (k : ℕ) (x : (sweepWitness q u a b).W),
      witnessMap φ q u a b
          (stageFrom (sweepWitness q u a b) (replFamily (sweepWitness q u a b)) a b k x α)
        = stageFrom (sweepWitness (φ q) (φ u) a b) (replFamily (sweepWitness (φ q) (φ u) a b))
            a b k (witnessMap φ q u a b x) α := by
    intro α
    induction α with
    | nil => exact fun _ _ => rfl
    | cons A β ih =>
      intro k x
      simp only [stageFrom]
      rw [ih, witnessMap_stage]
  rw [stageWord, stageWord, h, witnessMap_vac]

end Witness

/-! ### Descent of `HJO.Mellit.mellitInduction_sweepWitness` -/

section Descent

variable [Algebra ℚ L] [Algebra ℚ K]

/-- **`HJO.Mellit.mellitInduction_sweepWitness` descends along a field map.** If the clause holds at
the sweep witness over `K` with parameters `φ q`, `φ u`, it holds at the sweep witness over `L` with
parameters `q`, `u`. -/
theorem mellitInduction_of_ringHom {q u : L} {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (h : MellitInduction (sweepWitness (φ q) (φ u) a b) a b) :
    MellitInduction (sweepWitness q u a b) a b := by
  intro Ω hΩ N η hη hs α hpos hsum
  rw [stageWord_congr hΩ (isReplicationFamily_replFamily _) hab ha α]
  apply witnessMap_injective φ q u a b
  rw [witnessMap_smul, witnessMap_stageWord, witnessMap_D,
    h _ (isReplicationFamily_replFamily _) N η hη hs α hpos hsum]
  simp only [map_mul, map_pow, map_neg, map_one, map_zpow₀]

/-- **`HJO.Mellit.mellitInduction_sweepWitness` descends along an algebra map**: the case
`φ = algebraMap L K` of `HJO.Mellit.mellitInduction_of_ringHom`. -/
theorem mellitInduction_of_algebraMap [Algebra L K] {q u : L} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : 0 < a)
    (h : MellitInduction (sweepWitness (algebraMap L K q) (algebraMap L K u) a b) a b) :
    MellitInduction (sweepWitness q u a b) a b :=
  mellitInduction_of_ringHom (algebraMap L K) hab ha h

end Descent

/-- **`HJO.Mellit.mellitInduction_sweepWitness` at every `q`.** If the type-`BE` clause of the braid
recursion holds over every field, then `HJO.Mellit.MellitInduction` holds at the sweep witness over
`L` for every algebraically independent pair `(q, u)` and all coprime `1 < a < b`. -/
theorem mellitInduction_sweepWitness_of_sweepRecursionBEFloor' {L : Type v} [Field L]
    [Algebra ℚ L]
    (hBE : ∀ (M : Type v) [Field M] [Algebra ℚ M] (q u : M), AlgebraicIndependent ℤ ![q, u] →
      ∀ (r : M) (hr : r * r = q) (hq : q ≠ 0) (hq1 : q ≠ 1) (hqp : q + 1 ≠ 0) (a b N : ℕ),
        Nat.Coprime a b → 1 < a → a < b → 0 < N →
          SweepRecursionBEFloor q u a b N (braidValueColouring q u hq hq1 hqp hr a b N)) :
    ∀ q u : L, AlgebraicIndependent ℤ ![q, u] → ∀ a b : ℕ, Nat.Coprime a b →
      1 < a → a < b → MellitInduction (sweepWitness q u a b) a b := by
  intro q u hqu a b hab ha hlt
  let _ : Algebra ℚ (AlgebraicClosure L) :=
    ((algebraMap L (AlgebraicClosure L)).comp (algebraMap ℚ L)).toAlgebra
  refine mellitInduction_of_algebraMap (K := AlgebraicClosure L) hab (by omega) ?_
  have hqu' : AlgebraicIndependent ℤ
      ![algebraMap L (AlgebraicClosure L) q, algebraMap L (AlgebraicClosure L) u] := by
    have h := hqu.map' (f := (algebraMap L (AlgebraicClosure L)).toIntAlgHom)
      (algebraMap L (AlgebraicClosure L)).injective
    convert h using 1
    · funext i
      fin_cases i <;> rfl
    · exact Subsingleton.elim _ _
  have hsq : IsSquare (algebraMap L (AlgebraicClosure L) q) :=
    IsAlgClosed.exists_eq_mul_self _
  exact mellitInduction_sweepWitness_of_sweepRecursionBEFloor (hBE (AlgebraicClosure L)) _ _
    hqu' hsq a b hab ha hlt

end HJO.Mellit

end
