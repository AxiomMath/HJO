/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.Colouring
public import HJO.Shuffle.SweepStandardisation
public meta import HJO.Attr

/-! # A Carlsson–Mellit sweep system, exhibited

`HJO.Mellit.SweepSystem` enters as a hypothesis binder: every statement of the Mellit layer is of
the form "let `S` be a sweep system", and `HJO.Mellit.MellitInput` asks for one, so without a term
of that type the whole layer would be conditional on a class not known to be inhabited. This
file exhibits one, `HJO.Mellit.sweepWitness`, assembled from the operators of
`HJO.Shuffle.SweepModule`, and discharges the one interface clause that follows from the
construction, `HJO.Mellit.rhsSumsAgree_sweepWitness`.

## The graded pieces must be independent, not nested

`HJO.Sweep.piece L k` is *nested* in `k` (`HJO.Sweep.piece_mono`) inside one ambient space
`HJO.Sweep.Total L`, while the `V_*` is the *direct sum* `⨁_k V_k` — which is what
`HJO.Sweep.Vstar` records, in as many words: the graded pieces are
nested, so their union is all of `Total`, and a statement about `V_*` must name `Vstar`.

`shape_z1` is what forces the point here. The `z_1` of `HJO.Sweep.zop` is
`q^k/(1-q) (d^*_+d_- - d_-d^*_+) T^*_{k↘1}` *on `V_k`*, so the family
`HJO.Sweep.zopOneStar q u k` is genuinely `k`-dependent — its scalar alone changes by a factor of
`q` from one index to the next — whereas a single endomorphism of a *nested* family restricts to
one and the same map on the smaller pieces. So no single operator can be `z_1` on every nested
`V_k`, and `shape_z1` would be unsatisfiable by the operators. On a direct sum it is
satisfiable, by acting degreewise.

So `W` is `⨁_{k ≥ 0} Total L`, one summand per grading, and `V k` is the piece
`V_k = HJO.Sweep.piece L k` sitting inside the `k`-th summand. Every operator is
`HJO.Mellit.gradedOp` of the `k`-indexed family defined on `V_k`. Taking the
summands to be all of `Total L` rather than the pieces themselves — `⨁_k Total L` rather than
`HJO.Sweep.Vstar L` — costs nothing the structure asks for, since `V` is a field of the structure
and is nowhere required to exhaust `W`; what it buys is that the colouring invariant
`HJO.Mellit.dsc` can be carried in the grading it belongs to without first proving which piece it
lands in.

## What the three shape fields need

`shape_dplusStar`, `shape_z1` and `shape_y1` are the only *proofs* the structure asks for, and on
the degreewise reading each is one membership statement about the piece family:
`HJO.Sweep.dplusStar_mem_piece`, `HJO.Sweep.zopOneStar_mem_piece` and
`HJO.Sweep.auxVar_mem_piece`. The first two are proved here from the ground up — the substitutions
`τ_{k,i}`, `τ^-_{k,i}` and `cy_{k+1}`, the coefficient extraction of `d_-`, the braid operators and
the trains built from them, each preserving or moving the pieces exactly as the domains
and codomains say — and that is the content of the first half of the file.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### Membership in a graded piece

Two workhorses reduce a claim `f F ∈ V_m` for `F ∈ V_k` to a claim about generators: for a linear
map, to the `y`-monomials supported below `k`; for an algebra map, to the constants and the
variables `y_1, …, y_k`. -/

section CommRingBase

variable {L : Type*} [CommRing L]

/-- `y_{j+1} = X_j` lies in `V_m` as soon as `j < m`, the index convention of
`HJO.Sweep.auxVar` read on the bare variable. -/
theorem X_mem_piece {j m : ℕ} (h : j < m) : (MvPolynomial.X j : Total L) ∈ piece L m := by
  have h1 : (auxVar (j + 1) : Total L) = MvPolynomial.X j := by rw [auxVar, Nat.add_sub_cancel]
  rw [← h1]
  exact auxVar_mem_piece (by omega) (by omega)

/-- **A linear map lands in `V_m` on `V_k` as soon as it does on the monomials.** `V_k` is spanned
over `Λ` by the `y`-monomials whose exponents are supported below `k`, so that is all a linear map
has to be checked on. -/
theorem mem_piece_of_monomial {m k : ℕ} {f : Total L →ₗ[L] Total L}
    (h : ∀ d : ℕ →₀ ℕ, (∀ j ∈ d.support, j < k) → ∀ c : Sym.Lambda L,
        f (MvPolynomial.monomial d c) ∈ piece L m)
    {F : Total L} (hF : F ∈ piece L k) : f F ∈ piece L m := by
  rw [piece, MvPolynomial.mem_supported] at hF
  rw [MvPolynomial.as_sum F, map_sum]
  refine sum_mem fun d hd => h d (fun j hj => ?_) _
  exact hF (MvPolynomial.mem_vars_iff_mem_support j |>.2 ⟨d, hd, hj⟩)

/-- **An `𝕜`-algebra map lands in `V_m` on `V_k` as soon as it does on the constants and on
`y_1, …, y_k`.** -/
theorem mem_piece_of_algHom {m k : ℕ} {φ : Total L →ₐ[L] Total L}
    (hC : ∀ c : Sym.Lambda L, φ (MvPolynomial.C c) ∈ piece L m)
    (hX : ∀ j < k, φ (MvPolynomial.X j) ∈ piece L m)
    {F : Total L} (hF : F ∈ piece L k) : φ F ∈ piece L m := by
  refine mem_piece_of_monomial (f := φ.toLinearMap) ?_ hF
  intro d hd c
  change φ (MvPolynomial.monomial d c) ∈ piece L m
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
  exact mul_mem (hC c) (prod_mem fun j hj => pow_mem (hX j (hd j hj)) _)

/-- **A `Λ`-algebra map lands in `V_m` on `V_k` as soon as it does on `y_1, …, y_k`**, the
constants being fixed. -/
theorem mem_piece_of_lambdaAlgHom {m k : ℕ} {φ : Total L →ₐ[Sym.Lambda L] Total L}
    (hX : ∀ j < k, φ (MvPolynomial.X j) ∈ piece L m)
    {F : Total L} (hF : F ∈ piece L k) : φ F ∈ piece L m := by
  refine mem_piece_of_monomial (f := (φ.toLinearMap.restrictScalars L)) ?_ hF
  intro d hd c
  change φ (MvPolynomial.monomial d c) ∈ piece L m
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
  refine mul_mem ?_ (prod_mem fun j hj => pow_mem (hX j (hd j hj)) _)
  rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
  exact (piece L m).algebraMap_mem c

/-- Evaluating a symmetric function at values that lie in `V_m` gives an element of `V_m`. This is
what the alphabet substitutions of `HJO.Sweep.qshift` and `HJO.Sweep.qshiftNeg` do to a
coefficient. -/
theorem aeval_mem_piece {m : ℕ} {g : ℕ → Total L} (hg : ∀ j, g j ∈ piece L m)
    (c : Sym.Lambda L) : MvPolynomial.aeval g c ∈ piece L m := by
  induction c using MvPolynomial.induction_on with
  | C x => rw [MvPolynomial.aeval_C]; exact (piece L m).algebraMap_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hg j)

end CommRingBase

/-! ### The substitutions and the braid operators on the pieces -/

section Field

variable {L : Type*} [Field L]

/-- A scalar of the base field lies in every piece. -/
theorem scal_mem_piece (x : L) (m : ℕ) : (scal x : Total L) ∈ piece L m :=
  (piece L m).algebraMap_mem (MvPolynomial.C x)

/-- Each piece is closed under the scalar action of the base field. -/
theorem smul_mem_piece {x : L} {F : Total L} {m : ℕ} (hF : F ∈ piece L m) :
    x • F ∈ piece L m := by
  have h : x • F = scal x * F := by rw [scal_eq_algebraMap, Algebra.smul_def]
  rw [h]
  exact mul_mem (scal_mem_piece x m) hF

/-- **`τ_{k,i}` lands in `V_m` as soon as `y_i` does.** It adds the letter `(q-1)y_i` to the
alphabet and fixes every auxiliary variable, so the only new variable in the image is `y_i`, whose
index condition is `i - 1 < m`. -/
theorem qshift_mem_piece (q : L) {i k m : ℕ} (hi : i - 1 < m) (hk : k ≤ m) {F : Total L}
    (hF : F ∈ piece L k) : qshift q i F ∈ piece L m := by
  refine mem_piece_of_algHom (φ := qshift q i) (fun c => ?_) (fun j hj => ?_) hF
  · rw [qshift, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) c
    refine add_mem ((piece L m).algebraMap_mem _) (mul_mem (scal_mem_piece _ m) (pow_mem ?_ _))
    rw [auxVar]
    exact X_mem_piece hi
  · rw [qshift_auxVar]
    exact X_mem_piece (by omega)

/-- **`τ^-_{k,i}` lands in `V_m` as soon as `y_i` does**, for the same reason as `τ_{k,i}`. -/
theorem qshiftNeg_mem_piece (q : L) {i k m : ℕ} (hi : i - 1 < m) (hk : k ≤ m) {F : Total L}
    (hF : F ∈ piece L k) : qshiftNeg q i F ∈ piece L m := by
  refine mem_piece_of_algHom (φ := qshiftNeg q i) (fun c => ?_) (fun j hj => ?_) hF
  · rw [qshiftNeg, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) c
    refine sub_mem ((piece L m).algebraMap_mem _) (mul_mem (scal_mem_piece _ m) (pow_mem ?_ _))
    rw [auxVar]
    exact X_mem_piece hi
  · rw [qshiftNeg_auxVar]
    exact X_mem_piece (by omega)

/-- **`cy_{k+1}` is an endomorphism of `V_m` whenever `k < m`.** It shifts `y_1, …, y_k` up by one,
which stays inside `V_m` because the largest index it produces is `k + 1 ≤ m`, and it wraps
`y_{k+1}` round to `u y_1`. At `m = k + 1` this is the statement that `cy_{k+1}` is
an automorphism of `V_{k+1}`. -/
theorem cycleShift_mem_piece (u : L) {k m : ℕ} (hk : k < m) {F : Total L}
    (hF : F ∈ piece L m) : cycleShift u k F ∈ piece L m := by
  refine mem_piece_of_lambdaAlgHom (φ := cycleShift u k) (fun j hj => ?_) hF
  rw [cycleShift, MvPolynomial.aeval_X]
  split_ifs with h1 h2
  · exact X_mem_piece (by omega)
  · exact mul_mem (scal_mem_piece u m) (X_mem_piece (by omega))
  · exact X_mem_piece hj

/-- **`T_i` is an endomorphism of `V_m` for every `i < m`**, `HJO.Sweep.braid_mem_piece` with the
unread index `0` folded in. -/
theorem braid_mem_piece_of_lt (q : L) {i m : ℕ} (him : i < m) {F : Total L}
    (hF : F ∈ piece L m) : braid q i F ∈ piece L m := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [braid_zero_index]
    exact hF
  · exact braid_mem_piece q hi him hF

/-- **`T_i^{-1}` is an endomorphism of `V_m` for every `i < m`.** The inverse is
`(T_i + (q-1))/q`, so it lands wherever `T_i` does. -/
theorem braidInv_mem_piece (q : L) {i m : ℕ} (him : i < m) {F : Total L}
    (hF : F ∈ piece L m) : braidInv q i F ∈ piece L m := by
  rw [braidInv_apply]
  exact mul_mem (scal_mem_piece _ m)
    (add_mem (braid_mem_piece_of_lt q him hF) (mul_mem (scal_mem_piece _ m) hF))

/-- A word in operators each of which preserves `V_m` preserves `V_m`. -/
theorem listProd_mem_piece {m : ℕ} {l : List (Module.End L (Total L))}
    (h : ∀ f ∈ l, ∀ G ∈ piece L m, f G ∈ piece L m) {F : Total L} (hF : F ∈ piece L m) :
    l.prod F ∈ piece L m := by
  induction l with
  | nil => simpa using hF
  | cons f t ih =>
      rw [List.prod_cons, Module.End.mul_apply]
      exact h f (List.mem_cons_self ..) _ (ih fun g hg => h g (List.mem_cons_of_mem f hg))

/-- The ascending word `T_a ⋯ T_{b-1}` preserves `V_m` when every letter it reads does. -/
theorem ascendingWord_mem_piece {m : ℕ} {T : ℕ → Module.End L (Total L)} {a b : ℕ}
    (hT : ∀ i, i < b → ∀ G ∈ piece L m, T i G ∈ piece L m) {F : Total L}
    (hF : F ∈ piece L m) : Braid.ascendingWord T a b F ∈ piece L m := by
  rw [Braid.ascendingWord]
  refine listProd_mem_piece (fun f hf G hG => ?_) hF
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
  rw [List.mem_range'_1] at hi
  exact hT i (by omega) G hG

/-- The descending word `T_{a-1} ⋯ T_b` preserves `V_m` when every letter it reads does. -/
theorem descendingWord_mem_piece {m : ℕ} {T : ℕ → Module.End L (Total L)} {a b : ℕ}
    (hT : ∀ i, i < a → ∀ G ∈ piece L m, T i G ∈ piece L m) {F : Total L}
    (hF : F ∈ piece L m) : Braid.descendingWord T a b F ∈ piece L m := by
  rw [Braid.descendingWord]
  refine listProd_mem_piece (fun f hf G hG => ?_) hF
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hf
  rw [List.mem_reverse, List.mem_range'_1] at hi
  exact hT i (by omega) G hG

/-- **The descending train `T_{a↘b}` is an endomorphism of `V_m`** as soon as both endpoints are at
most `m`: either branch of `HJO.Braid.trainDown` reads only letters of index below `max a b`. -/
theorem trainDownEnd_mem_piece (q : L) {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m) {F : Total L}
    (hF : F ∈ piece L m) : trainDownEnd q a b F ∈ piece L m := by
  rw [trainDownEnd, Braid.trainDown]
  split_ifs
  · exact descendingWord_mem_piece (fun i hi G hG => braid_mem_piece_of_lt q (by omega) hG) hF
  · exact ascendingWord_mem_piece (fun i hi G hG => braidInv_mem_piece q (by omega) hG) hF

/-- **The ascending train `T_{a↗b}` is an endomorphism of `V_m`** as soon as both endpoints are at
most `m`. -/
theorem trainUpEnd_mem_piece (q : L) {a b m : ℕ} (ha : a ≤ m) (hb : b ≤ m) {F : Total L}
    (hF : F ∈ piece L m) : trainUpEnd q a b F ∈ piece L m := by
  rw [trainUpEnd, Braid.trainUp]
  split_ifs
  · exact ascendingWord_mem_piece (fun i hi G hG => braid_mem_piece_of_lt q (by omega) hG) hF
  · exact descendingWord_mem_piece (fun i hi G hG => braidInv_mem_piece q (by omega) hG) hF

end Field

/-! ### The graded operators of the sweep on the pieces

These are the domains and codomains of the definitions: `d_- : V_k → V_{k-1}` of `HJO.Sweep.dminus`,
`d^*_+ : V_k → V_{k+1}` of `HJO.Sweep.dplusStar`, and `z_1 : V_k → V_k` of `HJO.Sweep.zop`. -/

section Newton

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **`d^*_+` carries `V_k` into `V_{k+1}`**, the codomain `HJO.Sweep.dplusStar` gives it:
`τ_{k+1,k+1}` introduces `y_{k+1}` and `cy_{k+1}` then shifts the variables up inside
`V_{k+1}`. -/
theorem dplusStar_mem_piece (q u : L) {k : ℕ} {F : Total L} (hF : F ∈ piece L k) :
    dplusStar q u k F ∈ piece L (k + 1) := by
  rw [dplusStar_apply]
  exact cycleShift_mem_piece u (by omega) (qshift_mem_piece q (by omega) (by omega) hF)

/-- **The coefficient extraction of `d_-` carries `V_{j+1}` into `V_j`**: it deletes the exponent of
`y_{j+1}` from every monomial and multiplies by a symmetric function. -/
theorem lowerCoeff_mem_piece (j : ℕ) {F : Total L} (hF : F ∈ piece L (j + 1)) :
    lowerCoeff L j F ∈ piece L j := by
  refine mem_piece_of_monomial (f := (lowerCoeff L j).restrictScalars L) ?_ hF
  intro d hd c
  have hc : (MvPolynomial.monomial d c : Total L)
      = c • MvPolynomial.monomial d (1 : Sym.Lambda L) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hmono : (MvPolynomial.monomial (Finsupp.erase j d) (1 : Sym.Lambda L) : Total L)
      ∈ piece L j := by
    rw [piece, MvPolynomial.mem_supported, MvPolynomial.vars_monomial one_ne_zero]
    intro i hi
    rw [Finset.mem_coe, Finsupp.support_erase, Finset.mem_erase] at hi
    have := hd i hi.2
    exact Set.mem_Iio.2 (by omega)
  change lowerCoeff L j (MvPolynomial.monomial d c) ∈ piece L j
  rw [hc, map_smul, lowerCoeff_monomial, Algebra.smul_def]
  refine mul_mem ((piece L j).algebraMap_mem c) (mul_mem (mul_mem ?_ ?_) hmono)
  · exact pow_mem (neg_mem (one_mem (piece L j))) _
  · exact (piece L j).algebraMap_mem _

/-- **`d_-` carries `V_k` into `V_{k-1}`**, the codomain `HJO.Sweep.dminus` gives it: `τ^-_{k,k}`
stays inside `V_k` and the coefficient extraction then deletes `y_k`. At the unread index `k = 0`
the substitution introduces `y_1` and the extraction removes it again, so the statement holds
there too with `k - 1 = 0`. -/
theorem dminus_mem_piece (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    dminus q k F ∈ piece L (k - 1) := by
  rw [dminus_apply]
  rcases k with _ | k
  · exact lowerCoeff_mem_piece 0 (qshiftNeg_mem_piece q (by omega) (by omega) hF)
  · exact lowerCoeff_mem_piece k (qshiftNeg_mem_piece q (by omega) (by omega) hF)

/-- **`z_1` is an endomorphism of `V_k` for `k ≥ 1`**, the domain and codomain `HJO.Sweep.zop` gives
it. Each of the four factors moves between the pieces as its own definition says: `T^*_{k↘1}`
preserves `V_k` — it is a word in `T_1, …, T_{k-1}` whichever order the letters are taken in —
`d_-` drops the index by one and `d^*_+` raises it by one, so both composites `d^*_+d_-` and
`d_-d^*_+` return to `V_k`. -/
theorem zopOneStar_mem_piece (q u : L) {k : ℕ} (hk : 1 ≤ k) {F : Total L} (hF : F ∈ piece L k) :
    zopOneStar q u k F ∈ piece L k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hT : trainUpEnd q (j + 1) 1 F ∈ piece L (j + 1) :=
    trainUpEnd_mem_piece q le_rfl (by omega) hF
  rw [zopOneStar, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply]
  refine smul_mem_piece (sub_mem ?_ ?_)
  · have h1 : dminus q (j + 1) (trainUpEnd q (j + 1) 1 F) ∈ piece L j := by
      simpa using dminus_mem_piece q (j + 1) hT
    simpa using dplusStar_mem_piece q u h1
  · have h2 : dplusStar q u (j + 1) (trainUpEnd q (j + 1) 1 F) ∈ piece L (j + 2) :=
      dplusStar_mem_piece q u hT
    simpa using dminus_mem_piece q (j + 2) h2

end Newton

end HJO.Sweep

namespace HJO.Mellit

open HJO.Sweep

/-! ### The graded total space, and degreewise operators

`W` is one copy of `HJO.Sweep.Total L` per grading, `V k` the `V_k` inside the `k`-th
copy, and every operator of the sweep system acts on the `k`-th copy by the member of index `k` of
the family. -/

section Graded

variable {L : Type*} [CommRing L]

/-- **The graded total space.** One copy of `HJO.Sweep.Total L` for each grading `k`, in which the
space `V_*` sits as `⨁_k V_k`. The summands are independent, which is what
`HJO.Mellit.SweepSystem.shape_z1` needs and the nested family `HJO.Sweep.piece` cannot give: see
the module docstring. -/
abbrev Graded (L : Type*) [CommRing L] : Type _ := DirectSum ℕ fun _ : ℕ => Total L

/-- The `k`-th copy of the total space inside `HJO.Mellit.Graded L`. -/
noncomputable def gradedIn (L : Type*) [CommRing L] (k : ℕ) : Total L →ₗ[L] Graded L :=
  DirectSum.lof L ℕ (fun _ : ℕ => Total L) k

/-- The `V_k`, sitting in the `k`-th copy of the total space. -/
noncomputable def gradedPiece (L : Type*) [CommRing L] (k : ℕ) : Submodule L (Graded L) :=
  (pieceSub L k).map (gradedIn L k)

/-- **A degreewise operator.** From a family `f` of endomorphisms of the total space — the
operator read on each `V_k` — and a degree map `s`, the endomorphism of
`HJO.Mellit.Graded L` acting on the `k`-th copy by `f k` and landing in the `s k`-th. This is the
only way the `k`-indexed families of `HJO.Shuffle.SweepModule` can become the single maps the
structure's fields are, and it is faithful because the summands are independent: nothing about
`f k` is read outside grading `k`. -/
noncomputable def gradedOp {L : Type*} [CommRing L] (f : ℕ → Module.End L (Total L))
    (s : ℕ → ℕ) : Graded L →ₗ[L] Graded L :=
  DirectSum.toModule L ℕ _ fun k => (gradedIn L (s k)).comp (f k)

@[simp]
theorem gradedOp_apply {L : Type*} [CommRing L] (f : ℕ → Module.End L (Total L)) (s : ℕ → ℕ)
    (k : ℕ) (F : Total L) : gradedOp f s (gradedIn L k F) = gradedIn L (s k) (f k F) := by
  rw [gradedOp, gradedIn, DirectSum.toModule_lof]
  rfl

/-- **The shape of a degreewise operator.** `V_k` is carried into `V_{s k}` exactly when the family
member of index `k` carries the `V_k` into the `V_{s k}`. So each of the
three `shape_*` fields is one membership statement about `HJO.Sweep.piece`. -/
theorem map_gradedOp_le {f : ℕ → Module.End L (Total L)} {s : ℕ → ℕ} {k : ℕ}
    (h : ∀ F ∈ piece L k, f k F ∈ piece L (s k)) :
    (gradedPiece L k).map (gradedOp f s) ≤ gradedPiece L (s k) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨F, hF, rfl⟩ := hy
  rw [gradedOp_apply]
  exact ⟨f k F, h F hF, rfl⟩

end Graded

/-! ### The data the `D` field's arity drops

The `D_{η,c}` of `HJO.Mellit.dsc` is an invariant of a colouring of an
`aN × bN` rectangle, so it depends on `a`, `b` and `N`; `HJO.Mellit.dsc` carries all three. The
structure's `D` field takes only `η` and `c`. Inside `HJO.Mellit.MellitInput` the pair `(a, b)` is
fixed before the sweep system is chosen, so it can be a parameter of the witness — but `N` is
quantified *after* it, inside `MellitInduction` and `Rem41`, and the grading `D_{η,c_α}` must
live in is `ℓ = α.length`, which is quantified there too. Both therefore have to be read back off
the colouring, and these two functions do exactly that, against
`HJO.Mellit.compColouring`'s own formula
`c_α = {(aA_{i-1}, bA_{i-1})} ∪ {(aA_i - 1, bA_i)}`:

* the largest second coordinate of `c_α` is `bA_ℓ = bN`, so `N` is that divided by `b`;
* the two families are disjoint and each has `ℓ` elements, so `ℓ` is half the number of cells.

Both are identities, proved in `HJO.Shuffle.SweepWitnessColour`:
`HJO.Mellit.colourMult_compColouring` for `0 < b`, and `HJO.Mellit.colourParts_compColouring` for
`0 < a`, `0 < b` and every part of `α` positive. Each hypothesis is needed — the three corners where
the truncating division lies are the `decide`-checked refutations there — and each holds wherever
the interface reads `D`, except that the `hD` hypothesis of `HJO.Mellit.rem41_of_sweepComputes`
quantifies over every `α` of sum `N` and so needs the positivity of the parts added;
`HJO.Mellit.sweepWitness_proj_dminus_pow_D` is `hD` proved of this witness with it.

That the arity forces a convention at all is a defect of the structure, not of the mathematics — see
the module docstring of the interface. -/

/-- The multiplier `N` read back off a colouring. -/
def colourMult (b : ℕ) (c : Finset (ℕ × ℕ)) : ℕ := (c.sup fun p => p.2) / b

/-- The number of parts `ℓ` read back off a colouring. -/
def colourParts (c : Finset (ℕ × ℕ)) : ℕ := c.card / 2

/-! ### The witness -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- Multiplication by `y_1` on each grading. At the unread grading `0`, where `y_1` is not one of
the ring's generators and `HJO.Mellit.IsReplicationFamily` asks nothing, it is zero. -/
noncomputable def y1Fam (L : Type*) [Field L] : ℕ → Module.End L (Total L)
  | 0 => 0
  | _ + 1 => LinearMap.mulLeft L (auxVar 1)

/-- The `z_1` of `HJO.Sweep.zop` on each grading. At the unread grading `0`, where
`HJO.Sweep.zop` defines no `z_1`, it is zero. -/
noncomputable def z1Fam (q u : L) : ℕ → Module.End L (Total L)
  | 0 => 0
  | j + 1 => zopOneStar q u (j + 1)

/-- The train `T_{j↘1}` of `HJO.Braid.trainDown`, read on the grading it belongs to: it is a word in
`T_1, …, T_{j-1}`, hence an endomorphism of `V_m` for `j ≤ m` and not in general otherwise. -/
noncomputable def trainDownFam (q : L) (j m : ℕ) : Module.End L (Total L) :=
  if 1 ≤ j ∧ j ≤ m then trainDownEnd q j 1 else 0

/-- The train `T_{1↗j}` of `HJO.Braid.trainUp`, read on the grading it belongs to. -/
noncomputable def trainUpFam (q : L) (j m : ℕ) : Module.End L (Total L) :=
  if 1 ≤ j ∧ j ≤ m then trainUpEnd q 1 j else 0

omit [Algebra ℚ L] in
/-- Multiplication by `y_1` is an endomorphism of `V_{k+1}`: the `shape_y1`, which
`HJO.Sweep.piece` gives because `y_1` is then one of the ring's own generators. -/
theorem y1Fam_mem_piece (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    y1Fam L (k + 1) F ∈ piece L (k + 1) := by
  rw [y1Fam, LinearMap.mulLeft_apply]
  exact mul_mem (auxVar_mem_piece le_rfl (by omega)) hF

/-- `z_1` is an endomorphism of `V_{k+1}`: the `shape_z1`. -/
theorem z1Fam_mem_piece (q u : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L (k + 1)) :
    z1Fam q u (k + 1) F ∈ piece L (k + 1) := by
  rw [z1Fam]
  exact zopOneStar_mem_piece q u (by omega) hF

/-- **A Carlsson–Mellit sweep system.** A term of `HJO.Mellit.SweepSystem`: `W` is the graded
total space `⨁_k V_*`, `V k` the piece
`V_k = Λ ⊗_𝕜 𝕜[y_1, …, y_k]` of `HJO.Sweep.piece` in the `k`-th grading, and each operator field is
the corresponding operator acting degreewise —

* `dminus` is `HJO.Sweep.dminus q k` of `HJO.Sweep.dminus`, dropping the grading by one, so that
  `S.dminus ^ ℓ` on `V_ℓ` is the composite `d_- ∘ ⋯ ∘ d_-` with its indices
  `ℓ, ℓ-1, …, 1` and lands in `V_0`;
* `dplusStar` is `HJO.Sweep.dplusStar q u k` of `HJO.Sweep.dplusStar`, raising it by one;
* `z1` is `HJO.Sweep.zopOneStar q u k` of `HJO.Sweep.zop` and `y1` is multiplication by
  `y_1 = HJO.Sweep.auxVar 1`, both endomorphisms of `V_k` for `k ≥ 1`; at the unread grading `0`,
  where `HJO.Sweep.zop` defines neither, both are zero;
* `trainDown j` and `trainUp j` are the trains `T_{j↘1}` and `T_{1↗j}` of `HJO.Braid.trainDown` and
  `HJO.Braid.trainUp` in the braid operators `HJO.Sweep.braid` of `HJO.Sweep.braid`. A train is read
  on the grading it belongs to: `T_{j↘1}` is a word in `T_1, …, T_{j-1}`, which is an endomorphism
  of `V_m` only for `j ≤ m`, and outside that range the grading is sent to zero. Nothing reads it
  there — `HJO.Mellit.stage` applies `trainDown (k+1)` to the image of `Ω(1;a,b)` on `V_k`, which
  is `V_{k+1}`, so the index and the grading always agree;
* `chi` is `HJO.Paths.sweepChar q` of `HJO.Paths.sweepChar`, which is what makes
  `HJO.Mellit.rhsSumsAgree_sweepWitness` available;
* `proj` reads `V_0 = Λ` back in `Λ`, by taking the constant term of the `0`-th grading, and `vac`
  is the unit of `V_0`.

The three `shape_*` fields are `HJO.Sweep.dplusStar_mem_piece`, `HJO.Sweep.zopOneStar_mem_piece` and
`HJO.Sweep.auxVar_mem_piece`. No *relation* is claimed, and none is asked for: the structure is the
vocabulary the interface predicates are written in. What the term does is make every statement of
the Mellit layer non-vacuous, and make `HJO.Mellit.MellitInput` a question about four identities
rather than about whether the class is inhabited at all.

`a` and `b` are parameters because the `D` field needs them and cannot carry them; see
`HJO.Mellit.colourMult`. -/
noncomputable def sweepWitness (q u : L) (a b : ℕ) : SweepSystem L q u where
  W := Graded L
  V := gradedPiece L
  vac := gradedIn L 0 1
  proj := (MvPolynomial.lcoeff (Sym.Lambda L) (0 : ℕ →₀ ℕ)).restrictScalars L ∘ₗ
    DirectSum.component L ℕ (fun _ : ℕ => Total L) 0
  dminus := gradedOp (fun k => dminus q k) (fun k => k - 1)
  dplusStar := gradedOp (fun k => dplusStar q u k) (fun k => k + 1)
  y1 := gradedOp (y1Fam L) id
  z1 := gradedOp (z1Fam q u) id
  trainDown j := gradedOp (trainDownFam q j) id
  trainUp j := gradedOp (trainUpFam q j) id
  chi _ _ _ y := Paths.sweepChar q y
  D η c := gradedIn L (colourParts c) (dsc q u a b (colourMult b c) η c)
  shape_dplusStar k := map_gradedOp_le (k := k) fun _ hF => dplusStar_mem_piece q u hF
  shape_z1 k := map_gradedOp_le (k := k + 1) fun _ hF => z1Fam_mem_piece q u k hF
  shape_y1 k := map_gradedOp_le (k := k + 1) fun _ hF => y1Fam_mem_piece k hF

/-! ### Value checks on the witness

The degreewise assembly is where an index slip would hide, and a slipped index is invisible to the
three `shape_*` fields: the zero operator satisfies all three. So the four values below are read off
explicitly — the vacuum, the grading `d_-` and `d^*_+` move it to, and the one place the
definitions leave unread. -/

/-- `proj` reads the vacuum of `V_0 = Λ` back as `1`. -/
theorem sweepWitness_proj_vac (q u : L) (a b : ℕ) :
    (sweepWitness q u a b).proj (sweepWitness q u a b).vac = 1 := by
  change MvPolynomial.lcoeff (Sym.Lambda L) 0
      (DirectSum.component L ℕ (fun _ : ℕ => Total L) 0 (gradedIn L 0 (1 : Total L))) = 1
  rw [gradedIn, DirectSum.component.lof_self]
  simp

/-- **`d_-` lowers the grading and computes.** On `y_1 ∈ V_1` it gives `-e_1 ∈ V_0`, which is
`HJO.Sweep.dminus_auxVar_pow` at `m = 1`. This is the check that `dminus` is not the zero map and
that its degree map is `k ↦ k - 1`: were the grading left alone, `S.dminus ^ ℓ` would not reach
`V_0` and `HJO.Mellit.LhsRewrite` could not be about `d_-^ℓ`. -/
theorem sweepWitness_dminus_auxVar (q u : L) (a b : ℕ) :
    (sweepWitness q u a b).dminus (gradedIn L 1 (auxVar 1))
      = gradedIn L 0 (-(MvPolynomial.C (Sym.elemSymm L 1))) := by
  have h := dminus_auxVar_pow (L := L) q 0 1
  rw [pow_one] at h
  change gradedOp (fun k => dminus q k) (fun k => k - 1) (gradedIn L 1 (auxVar 1)) = _
  rw [gradedOp_apply, h]
  norm_num

/-- **`d^*_+` raises the grading.** On the vacuum it gives the unit of `V_1`. -/
theorem sweepWitness_dplusStar_vac (q u : L) (a b : ℕ) :
    (sweepWitness q u a b).dplusStar (gradedIn L 0 1) = gradedIn L 1 1 := by
  change gradedOp (fun k => dplusStar q u k) (fun k => k + 1) (gradedIn L 0 1) = _
  rw [gradedOp_apply, dplusStar_apply, map_one, map_one]

/-- **`y_1` is multiplication by `y_1` on `V_1`.** -/
theorem sweepWitness_y1_one (q u : L) (a b : ℕ) :
    (sweepWitness q u a b).y1 (gradedIn L 1 1) = gradedIn L 1 (auxVar 1) := by
  change gradedOp (y1Fam L) id (gradedIn L 1 1) = _
  rw [gradedOp_apply, y1Fam]
  simp

/-- **`y_1` is zero on the unread grading `V_0`**, where `HJO.Mellit.IsReplicationFamily` asks
nothing of it and `y_1` is not one of the ring's generators. -/
theorem sweepWitness_y1_grade_zero (q u : L) (a b : ℕ) :
    (sweepWitness q u a b).y1 (gradedIn L 0 1) = 0 := by
  change gradedOp (y1Fam L) id (gradedIn L 0 1) = _
  rw [gradedOp_apply, y1Fam]
  exact map_zero _

/-- The witness's characteristic function is the `χ` of `HJO.Paths.sweepChar`. -/
theorem sweepWitness_chi (q u : L) (a b : ℕ) {a' b' N' : ℕ} (y : Paths.Heights a' b' N') :
    (sweepWitness q u a b).chi a' b' N' y = Paths.sweepChar q y := rfl

/-- **`HJO.Mellit.RhsSumsAgree` holds of the witness.** It comes free from the construction: the
clause is `HJO.Mellit.rhsSumsAgree_of_chi_eq_sweepChar` for any system whose `χ` is
`HJO.Paths.sweepChar`, and the witness's is, by definition. This is the check that the term is the
right one rather than merely a term: a system with `χ = 0` inhabits the structure and refutes this
clause. -/
theorem rhsSumsAgree_sweepWitness {q u : L} {a b : ℕ} (ha : 0 < a) (hq : q ≠ 0) :
    RhsSumsAgree (sweepWitness q u a b) a b :=
  rhsSumsAgree_of_chi_eq_sweepChar _ ha hq fun _ _ _ _ => rfl

end HJO.Mellit
