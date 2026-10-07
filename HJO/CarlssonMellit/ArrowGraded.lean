/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ArrowGrading
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public meta import HJO.Attr

/-! # `Ã` and `Ã𝟏_0/I𝟏_0` are graded by the arrow degree

`HJO.CarlssonMellit.ArrowGrading` names the degree components of `Ã` and proves that every
relation and every generator of the left ideal `I` is homogeneous. This file draws the conclusion
needed from that: the components are independent and they span, so `Ã` is their internal
direct sum, and the same holds for `Ã𝟏_0` and for the quotient of it by `I𝟏_0`.

## Main definitions

* `HJO.Dyck.Tilde.reesHom`, `HJO.Dyck.Tilde.Atilde.reesQuot`: the Rees homomorphism into
  `Polynomial Ã`, which records the arrow degree in the degree of a monomial.
* `HJO.Dyck.Tilde.Atilde.proj`: the projection of `Ã` onto its degree-`d` component.
* `HJO.Dyck.Tilde.Atilde.atildeE0`, `HJO.Dyck.Tilde.Atilde.gradeE0`: the submodule `Ã𝟏_0` and its
  degree components.
* `HJO.Dyck.Tilde.Atilde.kernelIdealE0`, `HJO.Dyck.Tilde.Atilde.kernelGradeE0`: the submodule
  `I𝟏_0` and its degree components.

## Main results

* `HJO.Dyck.Tilde.Atilde.isInternal_grade`: `Ã` is the internal direct sum of its degree
  components.
* `HJO.Dyck.Tilde.Atilde.isInternal_gradeE0`: so is `Ã𝟏_0`.
* `HJO.Dyck.Tilde.Atilde.iSup_grade_inf_kernelIdeal`: the left ideal `I` is homogeneous, that is,
  it is the sum of its own degree components.
* `HJO.Dyck.Tilde.Atilde.isInternal_gradeE0_map_mkQ`: `Ã𝟏_0/I𝟏_0` is the internal direct sum of the
  images of the degree components of `Ã𝟏_0`.

## Implementation notes

The obstruction is that `Ã` is a `RingQuot`, and Mathlib has no grading of a quotient of a
noncommutative graded algebra by a homogeneous ideal. The way round it is the Rees trick, which
needs no graded-ring machinery at all. Send a generator `g` of the free algebra to
`monomial (arrowDeg g) (mk g)` in `Polynomial Ã`: because `X` is central this is an algebra
homomorphism, it sends a word to its own image times `X` to the word's degree, and therefore it
takes both sides of a homogeneous relation to the same polynomial. So it descends to
`HJO.Dyck.Tilde.Atilde.reesQuot : Ã →ₐ[K] Polynomial Ã`, which is a section of the grading in the
only sense needed: on the degree-`d` component it is `a ↦ monomial d a`. Reading off the
coefficient at `d` is then a `K`-linear projection `HJO.Dyck.Tilde.Atilde.proj d` of `Ã` onto its
degree-`d` component, and every statement below is an easy consequence of the two equations
`proj d = id` on `grade d` and `proj e = 0` on `grade d` for `e ≠ d`.

Independence is stated as `iSupIndep` and proved once for an arbitrary family of submodules bounded
by the components (`HJO.Dyck.Tilde.Atilde.iSupIndep_of_le_grade`), because the three families
needed — the components of `Ã`, those of `Ã𝟏_0` and those of `I𝟏_0` — are all of that shape;
and once again for their images in a quotient by a homogeneous submodule
(`HJO.Dyck.Tilde.Atilde.iSupIndep_map_mkQ`), which is what the quotient `Ã𝟏_0/I𝟏_0` needs.

The quotient `Ã𝟏_0/I𝟏_0` is read inside the ambient quotient `Ã ⧸ I𝟏_0`, as the submodule
`(Ã𝟏_0).map (I𝟏_0).mkQ`, rather than as a quotient of one submodule of `Ã` by another: `I𝟏_0` is a
submodule of `Ã𝟏_0`, so the two are canonically the same module, and the ambient reading avoids
carrying a module structure over a subobject — the same choice `HJO.Dyck.Tilde.Atilde.mellitKernel`
makes. `HJO.Dyck.Tilde.isInternal_comap_subtype` is the general fact that an independent family
decomposes its own supremum; Mathlib has it only for a family indexed by a subset of the index
type.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math.
Soc. **31** (2018) 661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Tilde

variable {K : Type*} [CommRing K] {q u : K} [Invertible q] [Invertible (q - 1)]

/-! ### Internal direct sums inside a supremum -/

/-- **An independent family of submodules decomposes its own supremum.** Mathlib has this for a
family indexed by a subset of the index type (`DirectSum.isInternal_biSup_submodule_of_iSupIndep`);
this is the same statement for a family indexed by the whole type, which is the shape every grading
below has. -/
theorem isInternal_comap_subtype {M : Type*} [AddCommGroup M] [Module K M]
    {A : ℕ → Submodule K M} (hA : iSupIndep A) :
    DirectSum.IsInternal fun d => (A d).comap (⨆ d, A d).subtype := by
  have hle : ∀ d, A d ≤ ⨆ d, A d := fun d => le_iSup A d
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · suffices h : ((⨆ d, A d).mapIic ∘ fun d => (A d).comap (⨆ d, A d).subtype)
        = fun d => (⟨A d, hle d⟩ : Set.Iic (⨆ d, A d)) by
      rw [← iSupIndep_map_orderIso_iff (⨆ d, A d).mapIic, h]
      exact iSupIndep.of_coe_Iic_comp hA
    ext d m
    change m ∈ ((A d).comap (⨆ d, A d).subtype).map (⨆ d, A d).subtype ↔ _
    rw [Submodule.map_comap_subtype, inf_of_le_right (hle d)]
  · have h := Submodule.biSup_comap_subtype_eq_top (Set.univ : Set ℕ) A
    rw [iSup_univ] at h
    simpa using h

/-! ### The free algebra is spanned by its components -/

/-- The unit is the empty word, of arrow degree `0`. -/
theorem one_mem_freeGrade : (1 : FreeAlgebra K Gen) ∈ freeGrade K 0 :=
  freeWord_mem_freeGrade []

/-- **The components of the free algebra span it.** Every element is a `K`-combination of words,
and a word lies in the component of its own arrow degree. -/
theorem iSup_freeGrade_eq_top : (⨆ d : ℕ, freeGrade K d) = ⊤ := by
  have hmul : (⨆ d : ℕ, freeGrade K d) * (⨆ d : ℕ, freeGrade K d) ≤ ⨆ d : ℕ, freeGrade K d := by
    rw [Submodule.iSup_mul]
    refine iSup_le fun a => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun b => Submodule.mul_le.2 fun x hx y hy =>
      Submodule.mem_iSup_of_mem (a + b) (mul_mem_freeGrade hx hy)
  refine top_unique fun x hx => ?_
  clear hx
  induction x with
  | grade0 r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.mem_iSup_of_mem 0 (Submodule.smul_mem _ _ one_mem_freeGrade)
  | grade1 g => exact Submodule.mem_iSup_of_mem _ (ι_mem_freeGrade g)
  | mul a b ha hb => exact hmul (Submodule.mul_mem_mul ha hb)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

/-! ### The Rees homomorphism -/

/-- **The Rees homomorphism**: the algebra map of the free algebra into `Polynomial Ã` sending a
generator `g` to its own image in `Ã` placed in polynomial degree `arrowDeg g`. It is the device
that replaces the graded-quotient machinery Mathlib does not have: `X` is central, so this is an
algebra map, and it remembers the arrow degree of a word in the degree of a monomial. -/
noncomputable def reesHom (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    FreeAlgebra K Gen →ₐ[K] Polynomial (Atilde K q u) :=
  FreeAlgebra.lift K fun g =>
    Polynomial.monomial (arrowDeg g) (Atilde.mk K q u (FreeAlgebra.ι K g))

/-- The Rees homomorphism on a generator, by construction. -/
theorem reesHom_ι (g : Gen) : reesHom K q u (FreeAlgebra.ι K g)
    = Polynomial.monomial (arrowDeg g) (Atilde.mk K q u (FreeAlgebra.ι K g)) :=
  FreeAlgebra.lift_ι_apply _ _

/-- The Rees homomorphism sends a word to its image in `Ã`, in polynomial degree the word's arrow
degree. -/
theorem reesHom_freeWord (w : List Gen) : reesHom K q u (freeWord K w)
    = Polynomial.monomial (arrowDegWord w) (Atilde.mk K q u (freeWord K w)) := by
  induction w with
  | nil => rw [freeWord_nil, arrowDegWord_nil, map_one, map_one, Polynomial.monomial_zero_one]
  | cons g w ih =>
    rw [freeWord_cons, map_mul (reesHom K q u), ih, reesHom_ι,
      Polynomial.monomial_mul_monomial, arrowDegWord_cons, map_mul (Atilde.mk K q u)]

/-- On the degree-`d` component of the free algebra the Rees homomorphism is
`x ↦ monomial d (mk x)`. -/
theorem reesHom_of_mem_freeGrade {d : ℕ} {x : FreeAlgebra K Gen} (hx : x ∈ freeGrade K d) :
    reesHom K q u x = Polynomial.monomial d (Atilde.mk K q u x) := by
  refine Submodule.span_induction (p := fun x _ =>
    reesHom K q u x = Polynomial.monomial d (Atilde.mk K q u x)) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨w, hw, rfl⟩
    rw [← hw]
    exact reesHom_freeWord w
  · rw [map_zero, map_zero, Polynomial.monomial_zero_right]
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, map_add, map_add]
  · intro c y _ hy
    rw [map_smul (reesHom K q u), hy, map_smul (Atilde.mk K q u), Polynomial.smul_monomial]

/-- **The Rees homomorphism kills the relations of `Ã`**: both sides of a relation lie in one
component, on which the homomorphism is `x ↦ monomial d (mk x)`, and `mk` identifies them. -/
theorem reesHom_rel {x y : FreeAlgebra K Gen} (h : Rel K q u x y) :
    reesHom K q u x = reesHom K q u y := by
  obtain ⟨d, hx, hy⟩ := rel_homogeneous h
  rw [reesHom_of_mem_freeGrade hx, reesHom_of_mem_freeGrade hy, Atilde.mk_rel h]

namespace Atilde

/-- **The Rees homomorphism of `Ã`**, the descent of `HJO.Dyck.Tilde.reesHom` to the quotient. -/
noncomputable def reesQuot (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    Atilde K q u →ₐ[K] Polynomial (Atilde K q u) :=
  RingQuot.liftAlgHom K ⟨reesHom K q u, fun _ _ h => reesHom_rel h⟩

/-- The descent agrees with `HJO.Dyck.Tilde.reesHom` on the image of the free algebra. -/
@[simp] theorem reesQuot_mk (x : FreeAlgebra K Gen) :
    reesQuot K q u (mk K q u x) = reesHom K q u x :=
  RingQuot.liftAlgHom_mkAlgHom_apply K (reesHom K q u) (s := Rel K q u)
    (fun _ _ h => reesHom_rel h) x

/-- On the degree-`d` component of `Ã` the Rees homomorphism is `a ↦ monomial d a`. -/
theorem reesQuot_of_mem_grade {d : ℕ} {a : Atilde K q u} (ha : a ∈ grade K q u d) :
    reesQuot K q u a = Polynomial.monomial d a := by
  obtain ⟨x, hx, rfl⟩ := ha
  change reesQuot K q u (mk K q u x) = Polynomial.monomial d (mk K q u x)
  rw [reesQuot_mk, reesHom_of_mem_freeGrade hx]

/-! ### The projections onto the components -/

/-- **The projection of `Ã` onto its degree-`d` component**: the coefficient at `d` of the Rees
homomorphism. It is the identity on `grade d` and zero on every other component, which is all the
grading statements below need. -/
noncomputable def proj (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (d : ℕ) : Atilde K q u →ₗ[K] Atilde K q u where
  toFun a := (reesQuot K q u a).coeff d
  map_add' a b := by rw [map_add, Polynomial.coeff_add]
  map_smul' c a := by rw [map_smul, Polynomial.coeff_smul]; rfl

/-- The projection, unfolded. -/
theorem proj_apply (d : ℕ) (a : Atilde K q u) : proj K q u d a = (reesQuot K q u a).coeff d := rfl

/-- The projections read a homogeneous element: the one at its own degree returns it, the others
return zero. -/
theorem proj_of_mem_grade {d e : ℕ} {a : Atilde K q u} (ha : a ∈ grade K q u d) :
    proj K q u e a = if d = e then a else 0 := by
  rw [proj_apply, reesQuot_of_mem_grade ha, Polynomial.coeff_monomial]

/-- The projection at a homogeneous element's own degree returns it. -/
theorem proj_self_of_mem_grade {d : ℕ} {a : Atilde K q u} (ha : a ∈ grade K q u d) :
    proj K q u d a = a := by simpa using proj_of_mem_grade (e := d) ha

/-- The projections at the other degrees kill a homogeneous element. -/
theorem proj_eq_zero_of_mem_grade {d e : ℕ} {a : Atilde K q u} (ha : a ∈ grade K q u d)
    (hde : d ≠ e) : proj K q u e a = 0 := by simp [proj_of_mem_grade ha, hde]

/-! ### Independence of any family of homogeneous submodules -/

variable {N : ℕ → Submodule K (Atilde K q u)}

/-- The projection at `d` of a sum of homogeneous pieces is its degree-`d` piece. -/
theorem proj_mem_of_mem_iSup (hN : ∀ d, N d ≤ grade K q u d) {a : Atilde K q u}
    (ha : a ∈ ⨆ d, N d) (e : ℕ) : proj K q u e a ∈ N e := by
  refine Submodule.iSup_induction N (motive := fun z => proj K q u e z ∈ N e) ha ?_ ?_ ?_
  · intro d x hx
    rcases eq_or_ne d e with rfl | hde
    · rw [proj_self_of_mem_grade (hN d hx)]
      exact hx
    · rw [proj_eq_zero_of_mem_grade (hN d hx) hde]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

/-- Nothing built from the components other than the `d`-th survives the projection at `d`. -/
theorem proj_eq_zero_of_mem_biSup (hN : ∀ d, N d ≤ grade K q u d) {d : ℕ} {a : Atilde K q u}
    (ha : a ∈ ⨆ (j) (_ : j ≠ d), N j) : proj K q u d a = 0 := by
  have hN' : ∀ j, (⨆ _ : j ≠ d, N j) ≤ grade K q u j := fun j => iSup_le fun _ => hN j
  have := proj_mem_of_mem_iSup hN' ha d
  rwa [iSup_neg (not_not_intro rfl), Submodule.mem_bot] at this

/-- **Any family of homogeneous submodules is independent.** This is the one fact the three gradings
below rest on: the components of `Ã`, those of `Ã𝟏_0` and those of `I𝟏_0` are all bounded by the
degree components, and that alone forces independence. -/
theorem iSupIndep_of_le_grade (hN : ∀ d, N d ≤ grade K q u d) : iSupIndep N := by
  rw [iSupIndep_def]
  intro d
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [← proj_self_of_mem_grade (hN d hx), proj_eq_zero_of_mem_biSup hN hx']

/-- **Homogeneous submodules stay independent in the quotient by a sum of homogeneous submodules.**
Given `x` in the `d`-th piece and `y` in the sum of the others with the same class, the projection
at `d` fixes `x`, kills `y` and carries `x - y` into the submodule quotiented by; so `x` lies in it
and the class is zero. -/
theorem iSupIndep_map_mkQ (hN : ∀ d, N d ≤ grade K q u d) {P : ℕ → Submodule K (Atilde K q u)}
    (hP : ∀ d, P d ≤ grade K q u d) : iSupIndep fun d => (N d).map (⨆ e, P e).mkQ := by
  rw [iSupIndep_def]
  intro d
  rw [Submodule.disjoint_def]
  rintro z ⟨x, hx, rfl⟩ hz
  rw [show (⨆ (j) (_ : j ≠ d), (N j).map (⨆ e, P e).mkQ)
      = (⨆ (j) (_ : j ≠ d), N j).map (⨆ e, P e).mkQ from by
    simp only [Submodule.map_iSup]] at hz
  obtain ⟨y, hy, hxy⟩ := hz
  have hsub : x - y ∈ ⨆ e, P e := by
    have h0 : (⨆ e, P e).mkQ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hxP := proj_mem_of_mem_iSup hP hsub d
  rw [map_sub, proj_self_of_mem_grade (hN d hx), proj_eq_zero_of_mem_biSup hN hy, sub_zero] at hxP
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_iSup_of_mem d hxP

/-! ### `Ã` is graded by the arrow degree -/

/-- The degree-`d` component of `Ã` is by definition the image of the one upstairs. -/
theorem grade_eq_map (d : ℕ) : grade K q u d = (freeGrade K d).map (mk K q u).toLinearMap := rfl

/-- **The components of `Ã` span it**: they are the images of the components of the free algebra,
which span, under the surjection onto `Ã`. -/
theorem iSup_grade_eq_top : (⨆ d : ℕ, grade K q u d) = ⊤ := by
  simp only [grade_eq_map, ← Submodule.map_iSup, iSup_freeGrade_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.2 (RingQuot.mkAlgHom_surjective K (Rel K q u))

/-- The components of `Ã` are independent. -/
theorem iSupIndep_grade : iSupIndep (grade K q u) := iSupIndep_of_le_grade fun _ => le_rfl

/-- **`Ã` is graded by the arrow degree**: it is the internal direct sum of its degree components.
This is the second clause of the arrow-degree grading statement (that `Ã` and `Ãe_0/Ie_0` are
graded), for `Ã` itself. -/
@[hjo "lem_cm_arrow_degree_graded"]
theorem isInternal_grade : DirectSum.IsInternal (grade K q u) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_grade, iSup_grade_eq_top⟩

/-! ### `Ã𝟏_0` is graded by the arrow degree -/

/-- An idempotent has arrow degree `0`. -/
theorem e_mem_grade (k : ℕ) : e K q u k ∈ grade K q u 0 := mem_grade_of_free (freeE_mem k)

/-- The components of `Ã` multiply as a grading should. -/
theorem mul_mem_grade {a b : ℕ} {x y : Atilde K q u} (hx : x ∈ grade K q u a)
    (hy : y ∈ grade K q u b) : x * y ∈ grade K q u (a + b) := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨x' * y', mul_mem_freeGrade hx' hy', by simp⟩

/-- **Right multiplication by the idempotent `𝟏_0`**, the `K`-linear map whose image is `Ã𝟏_0` and
which carries the components of `Ã` onto those of `Ã𝟏_0`. -/
noncomputable def rightE0 (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    Atilde K q u →ₗ[K] Atilde K q u :=
  LinearMap.mulRight K (e K q u 0)

/-- Right multiplication by `𝟏_0`, unfolded. -/
@[simp] theorem rightE0_apply (x : Atilde K q u) : rightE0 K q u x = x * e K q u 0 := rfl

/-- Right multiplication by `𝟏_0` preserves each component, the idempotent having arrow degree
`0`. -/
theorem rightE0_mem_grade {d : ℕ} {x : Atilde K q u} (hx : x ∈ grade K q u d) :
    rightE0 K q u x ∈ grade K q u d := by
  simpa using mul_mem_grade hx (e_mem_grade 0)

/-- **The submodule `Ã𝟏_0`** of `Ã`: the paths that begin at the vertex `0`. -/
noncomputable def atildeE0 (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] : Submodule K (Atilde K q u) := LinearMap.range (rightE0 K q u)

/-- **The degree-`d` component of `Ã𝟏_0`**: the image of the degree-`d` component of `Ã`. -/
noncomputable def gradeE0 (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (d : ℕ) : Submodule K (Atilde K q u) := (grade K q u d).map (rightE0 K q u)

/-- The components of `Ã𝟏_0` sit inside those of `Ã`. -/
theorem gradeE0_le_grade (d : ℕ) : gradeE0 K q u d ≤ grade K q u d := by
  rintro x ⟨y, hy, rfl⟩
  exact rightE0_mem_grade hy

/-- The components of `Ã𝟏_0` sum to `Ã𝟏_0`. -/
theorem iSup_gradeE0 : (⨆ d : ℕ, gradeE0 K q u d) = atildeE0 K q u := by
  simp only [gradeE0, ← Submodule.map_iSup, iSup_grade_eq_top, Submodule.map_top, atildeE0]

/-- The components of `Ã𝟏_0` are independent. -/
theorem iSupIndep_gradeE0 : iSupIndep (gradeE0 K q u) := iSupIndep_of_le_grade gradeE0_le_grade

/-- **`Ã𝟏_0` is graded by the arrow degree**: it is the internal direct sum of its degree
components. -/
theorem isInternal_gradeE0 : DirectSum.IsInternal fun d : ℕ =>
    (gradeE0 K q u d).comap (atildeE0 K q u).subtype := by
  have h := isInternal_comap_subtype (iSupIndep_gradeE0 (q := q) (u := u))
  rwa [iSup_gradeE0] at h

/-! ### The left ideal `I` is homogeneous -/

/-- Each generator of the left ideal `I` is homogeneous of arrow degree `m + 1`: it is the
difference of two elements of that degree. -/
theorem kernelIdeal_generator_mem_grade (v m : ℕ) :
    dPlusStar K q u (v + m) * dPlusPow K q u v m - dPlusPow K q u v (m + 1)
      ∈ grade K q u (m + 1) :=
  Submodule.sub_mem _ (kernelIdeal_gen_homogeneous v m).1 (kernelIdeal_gen_homogeneous v m).2

/-- **The left ideal `I` is homogeneous**: it is the sum of its own degree components. The
generators are homogeneous and `Ã` is spanned by its components, so every left multiple of a
generator is a sum of homogeneous elements of `I`. -/
theorem iSup_grade_inf_kernelIdeal :
    (⨆ d : ℕ, grade K q u d ⊓ (kernelIdeal K q u).restrictScalars K)
      = (kernelIdeal K q u).restrictScalars K := by
  refine le_antisymm (iSup_le fun _ => inf_le_right) ?_
  set J : Submodule K (Atilde K q u) :=
    ⨆ d : ℕ, grade K q u d ⊓ (kernelIdeal K q u).restrictScalars K
  have hgrade : ∀ (e : ℕ) (a : Atilde K q u), a ∈ grade K q u e → ∀ x ∈ J, a * x ∈ J := by
    intro e a ha x hx
    refine Submodule.iSup_induction _ (motive := fun z => a * z ∈ J) hx ?_ ?_ ?_
    · intro d y hy
      exact Submodule.mem_iSup_of_mem (e + d)
        ⟨mul_mem_grade ha hy.1, Ideal.mul_mem_left _ _ hy.2⟩
    · rw [mul_zero]
      exact zero_mem _
    · intro y z hy hz
      rw [mul_add]
      exact add_mem hy hz
  have hmul : ∀ (a : Atilde K q u), ∀ x ∈ J, a * x ∈ J := by
    intro a x hx
    have ha : a ∈ ⨆ e : ℕ, grade K q u e := by rw [iSup_grade_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun b => b * x ∈ J) ha ?_ ?_ ?_
    · intro e b hb
      exact hgrade e b hb x hx
    · rw [zero_mul]
      exact zero_mem _
    · intro b c hb hc
      rw [add_mul]
      exact add_mem hb hc
  intro z hz
  refine Submodule.span_induction (p := fun z _ => z ∈ J) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨v, m, rfl⟩
    exact Submodule.mem_iSup_of_mem (m + 1)
      ⟨kernelIdeal_generator_mem_grade v m, Submodule.subset_span ⟨v, m, rfl⟩⟩
  · exact zero_mem _
  · intro x y _ _ hx hy
    exact add_mem hx hy
  · intro a x _ hx
    rw [smul_eq_mul]
    exact hmul a x hx

/-! ### `Ã𝟏_0/I𝟏_0` is graded by the arrow degree -/

/-- **The submodule `I𝟏_0`** of `Ã𝟏_0`, the image of the left ideal `I` under right multiplication
by `𝟏_0`. -/
noncomputable def kernelIdealE0 (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] : Submodule K (Atilde K q u) :=
  ((kernelIdeal K q u).restrictScalars K).map (rightE0 K q u)

/-- **The degree-`d` component of `I𝟏_0`.** -/
noncomputable def kernelGradeE0 (K : Type*) [CommRing K] (q u : K) [Invertible q]
    [Invertible (q - 1)] (d : ℕ) : Submodule K (Atilde K q u) :=
  (grade K q u d ⊓ (kernelIdeal K q u).restrictScalars K).map (rightE0 K q u)

/-- The components of `I𝟏_0` sit inside those of `Ã`. -/
theorem kernelGradeE0_le_grade (d : ℕ) : kernelGradeE0 K q u d ≤ grade K q u d := by
  rintro x ⟨y, hy, rfl⟩
  exact rightE0_mem_grade hy.1

/-- **`I𝟏_0` is homogeneous**: it is the sum of its own degree components. -/
theorem iSup_kernelGradeE0 : (⨆ d : ℕ, kernelGradeE0 K q u d) = kernelIdealE0 K q u := by
  simp only [kernelGradeE0, ← Submodule.map_iSup, iSup_grade_inf_kernelIdeal, kernelIdealE0]

/-- The components of `I𝟏_0` are independent. -/
theorem iSupIndep_kernelGradeE0 : iSupIndep (kernelGradeE0 K q u) :=
  iSupIndep_of_le_grade kernelGradeE0_le_grade

/-- The components of `Ã𝟏_0` stay independent modulo `I𝟏_0`, which is homogeneous. -/
theorem iSupIndep_gradeE0_map_mkQ :
    iSupIndep fun d : ℕ => (gradeE0 K q u d).map (kernelIdealE0 K q u).mkQ := by
  rw [← iSup_kernelGradeE0]
  exact iSupIndep_map_mkQ gradeE0_le_grade kernelGradeE0_le_grade

/-- Modulo `I𝟏_0` the components of `Ã𝟏_0` still sum to the whole of it. -/
theorem iSup_gradeE0_map_mkQ :
    (⨆ d : ℕ, (gradeE0 K q u d).map (kernelIdealE0 K q u).mkQ)
      = (atildeE0 K q u).map (kernelIdealE0 K q u).mkQ := by
  rw [← Submodule.map_iSup, iSup_gradeE0]

/-- **`Ã𝟏_0/I𝟏_0` is graded by the arrow degree**: inside `Ã ⧸ I𝟏_0` the image of `Ã𝟏_0` is the
internal direct sum of the images of the degree components of `Ã𝟏_0`. This is the second clause of
the arrow-degree grading statement, for the quotient. -/
@[hjo "lem_cm_arrow_degree_graded"]
theorem isInternal_gradeE0_map_mkQ : DirectSum.IsInternal fun d : ℕ =>
    ((gradeE0 K q u d).map (kernelIdealE0 K q u).mkQ).comap
      ((atildeE0 K q u).map (kernelIdealE0 K q u).mkQ).subtype := by
  have h := isInternal_comap_subtype (iSupIndep_gradeE0_map_mkQ (q := q) (u := u))
  rwa [iSup_gradeE0_map_mkQ] at h

end Atilde

end HJO.Dyck.Tilde
