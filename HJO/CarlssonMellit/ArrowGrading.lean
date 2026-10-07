/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DPATildeIdeals
public meta import HJO.Attr

/-! # The arrow-degree components, and the homogeneity of the relations

`HJO.Dyck.Tilde.arrowDeg` counts arrows and ignores loops and idempotents. This file turns that
count into a family of submodules — the degree components — and proves what is needed of
them: every relation of `Ã` is homogeneous, every generator of the left ideal `I` is homogeneous,
and the corner elements `y_i` and `z_i` are homogeneous of degree `2`.

## Main definitions

* `HJO.Dyck.Tilde.freeWord`: the product of a list of generators in the free algebra.
* `HJO.Dyck.Tilde.freeGrade`: the degree-`d` component of the free algebra, the span of the words
  of arrow degree `d`.
* `HJO.Dyck.Tilde.Atilde.grade`: the degree-`d` component of `Ã`, the image of `freeGrade d`.

## Main results

* `HJO.Dyck.Tilde.Atilde.yElt_mem_grade`, `HJO.Dyck.Tilde.Atilde.zElt_mem_grade`: `y_i` and `z_i`
  are homogeneous of arrow degree `2`.
* `HJO.Dyck.Tilde.rel_homogeneous`: both sides of every relation of `Ã` lie in one and the same
  degree component.
* `HJO.Dyck.Tilde.Atilde.kernelIdeal_gen_homogeneous`: each generator of `I` is homogeneous.

## Implementation notes

The degree-`d` component of a quotient of a graded algebra by a homogeneous ideal is the image of
the degree-`d` component upstairs, and that is how `HJO.Dyck.Tilde.Atilde.grade` is defined: no
grading of `Ã` has to be constructed to say what "homogeneous of degree `2`" means for `y_i`.

**Where the two clauses of the arrow-degree grading statement live.** The statement has two
clauses: that the relations are homogeneous, and that `Ã` and `Ãe_0/Ie_0` are therefore *graded* —
that is, that the components span and sum directly. The first clause is `rel_homogeneous` below
together with `Atilde.kernelIdeal_gen_homogeneous`. The second is a direct-sum decomposition of
a `RingQuot` by a homogeneous left ideal, which Mathlib does not supply; it is built in
`HJO.CarlssonMellit.ArrowGraded` — `Atilde.isInternal_grade` and
`Atilde.isInternal_gradeE0_map_mkQ` — by the formal-variable trick.

The homogeneity of the defining relations of `𝔸_q` is proved once, in an arbitrary generator family
(`sourceRel_homogeneous`), and read twice — at the unstarred family and at the starred one — for
the same reason the relations themselves are written once. What the starred reading needs is that
`T̂_i` has degree `0`, which is `freeTinv_mem`: the polynomial inverse is a combination of a loop
and an idempotent, and the arrow degree ignores both.

`HJO.Dyck.Tilde.mul_mem_freeGrade'` takes the degree equation `a + b = c` as its *last* argument on
purpose. With it first, `exact` meets `rfl : ?a + ?b = ?c` with all three unknown and the
unification blows past the heartbeat limit; with the two memberships elaborated first, `a` and `b`
are fixed and the equation is decided immediately.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31** (2018)
661--697, Section 3.
-/

@[expose] public section

namespace HJO.Dyck.Tilde

/-! ### The degree components of the free algebra -/

/-- The product of a list of generators, read left to right. -/
def freeWord (K : Type*) [CommRing K] : List Gen → FreeAlgebra K Gen
  | [] => 1
  | g :: w => FreeAlgebra.ι K g * freeWord K w

@[simp] theorem freeWord_nil (K : Type*) [CommRing K] : freeWord K [] = 1 := rfl

theorem freeWord_cons (K : Type*) [CommRing K] (g : Gen) (w : List Gen) :
    freeWord K (g :: w) = FreeAlgebra.ι K g * freeWord K w := rfl

theorem freeWord_single (K : Type*) [CommRing K] (g : Gen) :
    freeWord K [g] = FreeAlgebra.ι K g := by rw [freeWord_cons, freeWord_nil, mul_one]

theorem freeWord_append (K : Type*) [CommRing K] (v w : List Gen) :
    freeWord K (v ++ w) = freeWord K v * freeWord K w := by
  induction v with
  | nil => rw [List.nil_append, freeWord_nil, one_mul]
  | cons g v ih => rw [List.cons_append, freeWord_cons, freeWord_cons, ih, mul_assoc]

/-- **The degree-`d` component of the free algebra**: the span of the words of arrow degree `d`. -/
def freeGrade (K : Type*) [CommRing K] (d : ℕ) : Submodule K (FreeAlgebra K Gen) :=
  Submodule.span K {x | ∃ w : List Gen, arrowDegWord w = d ∧ x = freeWord K w}

variable {K : Type*} [CommRing K]

theorem freeWord_mem_freeGrade (w : List Gen) : freeWord K w ∈ freeGrade K (arrowDegWord w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

/-- A single generator lies in the component of its own arrow degree. -/
theorem ι_mem_freeGrade (g : Gen) : FreeAlgebra.ι K g ∈ freeGrade K (arrowDeg g) := by
  have h := freeWord_mem_freeGrade (K := K) [g]
  rw [freeWord_single, show arrowDegWord [g] = arrowDeg g from by simp [arrowDegWord]] at h
  exact h

/-- The components multiply as a grading should. -/
theorem mul_mem_freeGrade {a b : ℕ} {x y : FreeAlgebra K Gen} (hx : x ∈ freeGrade K a)
    (hy : y ∈ freeGrade K b) : x * y ∈ freeGrade K (a + b) := by
  have hle : freeGrade K a * freeGrade K b ≤ freeGrade K (a + b) := by
    rw [freeGrade, freeGrade, Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨p, ⟨v, hv, rfl⟩, c, ⟨w, hw, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨v ++ w, by rw [arrowDegWord_append, hv, hw],
      (freeWord_append K v w).symm⟩
  exact hle (Submodule.mul_mem_mul hx hy)

/-- The multiplication rule with the target degree supplied last: with the two memberships
elaborated first the degrees `a` and `b` are already fixed, and the equation is decided at once. -/
theorem mul_mem_freeGrade' {a b c : ℕ} {x y : FreeAlgebra K Gen} (hx : x ∈ freeGrade K a)
    (hy : y ∈ freeGrade K b) (habc : a + b = c) : x * y ∈ freeGrade K c :=
  habc ▸ mul_mem_freeGrade hx hy

theorem freeE_mem (k : ℕ) : freeE K k ∈ freeGrade K 0 := ι_mem_freeGrade (Gen.vertex k)

theorem freeUp_mem (k : ℕ) : freeUp K k ∈ freeGrade K 1 := ι_mem_freeGrade (Gen.up k)

theorem freeUpStar_mem (k : ℕ) : freeUpStar K k ∈ freeGrade K 1 := ι_mem_freeGrade (Gen.upStar k)

theorem freeDown_mem (k : ℕ) : freeDown K k ∈ freeGrade K 1 := ι_mem_freeGrade (Gen.down k)

theorem freeT_mem (k i : ℕ) : freeT K k i ∈ freeGrade K 0 := ι_mem_freeGrade (Gen.braid k i)

/-! ### The generic data is homogeneous -/

theorem commOf_mem {U D : ℕ → FreeAlgebra K Gen} (hU : ∀ n, U n ∈ freeGrade K 1)
    (hD : ∀ n, D n ∈ freeGrade K 1) (n : ℕ) : commOf U D n ∈ freeGrade K 2 := by
  rw [commOf]
  exact Submodule.sub_mem _ (mul_mem_freeGrade' (hU n) (hD n) rfl)
    (mul_mem_freeGrade' (hD (n + 1)) (hU (n + 1)) rfl)

theorem tinvOf_mem {T ε : FreeAlgebra K Gen} (q' qi : K) (hT : T ∈ freeGrade K 0)
    (hε : ε ∈ freeGrade K 0) : tinvOf q' qi T ε ∈ freeGrade K 0 := by
  rw [tinvOf]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hT (Submodule.smul_mem _ _ hε))

theorem tinvWordOf_mem {E : ℕ → FreeAlgebra K Gen} {T : ℕ → ℕ → FreeAlgebra K Gen} (q' qi : K)
    (hE : ∀ n, E n ∈ freeGrade K 0) (hT : ∀ n m, T n m ∈ freeGrade K 0) (k n : ℕ) :
    tinvWordOf q' qi E T k n ∈ freeGrade K 0 := by
  induction n with
  | zero => exact hE k
  | succ n ih =>
    rw [tinvWordOf]
    exact mul_mem_freeGrade' (tinvOf_mem q' qi (hT k n) (hE k)) ih rfl

theorem cornerAux_mem {E U D : ℕ → FreeAlgebra K Gen} {T : ℕ → ℕ → FreeAlgebra K Gen}
    (q' qi di : K) (hE : ∀ n, E n ∈ freeGrade K 0) (hU : ∀ n, U n ∈ freeGrade K 1)
    (hD : ∀ n, D n ∈ freeGrade K 1) (hT : ∀ n m, T n m ∈ freeGrade K 0) (k j : ℕ) :
    cornerAux q' qi di E U D T k j ∈ freeGrade K 2 := by
  induction j with
  | zero =>
    rw [cornerAux]
    exact Submodule.smul_mem _ _ (mul_mem_freeGrade'
      (mul_mem_freeGrade' (tinvWordOf_mem q' qi hE hT k (k - 1)) (commOf_mem hU hD (k - 1)) rfl)
      (hE k) rfl)
  | succ j ih =>
    rw [cornerAux]
    exact Submodule.smul_mem _ _ (mul_mem_freeGrade'
      (mul_mem_freeGrade' (hT k (k - j - 2)) ih rfl) (hT k (k - j - 2)) rfl)

theorem cornerOf_mem {E U D : ℕ → FreeAlgebra K Gen} {T : ℕ → ℕ → FreeAlgebra K Gen}
    (q' qi di : K) (hE : ∀ n, E n ∈ freeGrade K 0) (hU : ∀ n, U n ∈ freeGrade K 1)
    (hD : ∀ n, D n ∈ freeGrade K 1) (hT : ∀ n m, T n m ∈ freeGrade K 0) (k i : ℕ) :
    cornerOf q' qi di E U D T k i ∈ freeGrade K 2 :=
  cornerAux_mem q' qi di hE hU hD hT k (k - i)

/-! ### The corner elements of `Ã` -/

variable {q u : K} [Invertible q]

theorem freeTinv_mem (k i : ℕ) : freeTinv K q k i ∈ freeGrade K 0 := by
  rw [freeTinv]
  exact tinvOf_mem q ⅟q (freeT_mem k i) (freeE_mem k)

variable [Invertible (q - 1)]

theorem freeY_mem (k i : ℕ) : freeY K q k i ∈ freeGrade K 2 := by
  rw [freeY]
  exact cornerOf_mem q ⅟q ⅟(q - 1) freeE_mem freeUp_mem freeDown_mem freeT_mem k i

theorem freeZ_mem (k i : ℕ) : freeZ K q k i ∈ freeGrade K 2 := by
  rw [freeZ]
  exact cornerOf_mem (⅟q) q (-(q * ⅟(q - 1))) freeE_mem freeUpStar_mem freeDown_mem
    freeTinv_mem k i

namespace Atilde

/-- **The degree-`d` component of `Ã`**: the image of the degree-`d` component of the free algebra.
This is what the degree-`d` component of a quotient by a homogeneous ideal is, so no grading of `Ã`
has to be constructed for the notion to be available. -/
noncomputable def grade (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (d : ℕ) : Submodule K (Atilde K q u) :=
  (freeGrade K d).map (mk K q u).toLinearMap

theorem mem_grade_of_free {d : ℕ} {x : FreeAlgebra K Gen} (h : x ∈ freeGrade K d) :
    mk K q u x ∈ grade K q u d :=
  Submodule.mem_map_of_mem h

/-- **The corner element `y_i` is homogeneous of arrow degree `2`**: it is a word of loops and
idempotents, all of degree `0`, times the commutator, whose every term has one `d₊` and one `d₋`. -/
@[hjo "lem_cm_arrow_degree_corner"]
theorem yElt_mem_grade (k i : ℕ) : yElt K q u k i ∈ grade K q u 2 := by
  rw [← mk_freeY]
  exact mem_grade_of_free (freeY_mem k i)

/-- **The corner element `z_i` is homogeneous of arrow degree `2`**: it is the image of `y_i` under
the starred substitution, which exchanges `d₊` for `d₊^*` and so preserves the degree. -/
@[hjo "lem_cm_arrow_degree_corner"]
theorem zElt_mem_grade (k i : ℕ) : zElt K q u k i ∈ grade K q u 2 := by
  rw [← mk_freeZ]
  exact mem_grade_of_free (freeZ_mem k i)

end Atilde

/-! ### The relations are homogeneous -/

/-- **The defining relations of `𝔸_q` are homogeneous**, in an arbitrary family of generators: both
sides of each lie in one and the same degree component. Read at the unstarred family and at the
starred one, this is the first two groups of `HJO.Dyck.Tilde.Atilde`. -/
theorem sourceRel_homogeneous {q' : K} {E U D : ℕ → FreeAlgebra K Gen}
    {T : ℕ → ℕ → FreeAlgebra K Gen} (hE : ∀ n, E n ∈ freeGrade K 0)
    (hU : ∀ n, U n ∈ freeGrade K 1) (hD : ∀ n, D n ∈ freeGrade K 1)
    (hT : ∀ n m, T n m ∈ freeGrade K 0) {x y : FreeAlgebra K Gen}
    (h : SourceRel q' E U D T x y) : ∃ d : ℕ, x ∈ freeGrade K d ∧ y ∈ freeGrade K d := by
  induction h with
  | vertex_mul_up k => exact ⟨1, mul_mem_freeGrade' (hE (k + 1)) (hU k) rfl, hU k⟩
  | up_mul_vertex k => exact ⟨1, mul_mem_freeGrade' (hU k) (hE k) rfl, hU k⟩
  | quadratic h =>
    exact ⟨0, mul_mem_freeGrade' (Submodule.sub_mem _ (hT _ _) (hE _))
      (Submodule.add_mem _ (hT _ _) (Submodule.smul_mem _ _ (hE _))) rfl, Submodule.zero_mem _⟩
  | braid_braid h =>
    exact ⟨0, mul_mem_freeGrade' (mul_mem_freeGrade' (hT _ _) (hT _ _) rfl) (hT _ _) rfl,
      mul_mem_freeGrade' (mul_mem_freeGrade' (hT _ _) (hT _ _) rfl) (hT _ _) rfl⟩
  | braid_comm hi hj hij =>
    exact ⟨0, mul_mem_freeGrade' (hT _ _) (hT _ _) rfl, mul_mem_freeGrade' (hT _ _) (hT _ _) rfl⟩
  | braid_down h =>
    exact ⟨1, mul_mem_freeGrade' (hT _ _) (hD _) rfl, mul_mem_freeGrade' (hD _) (hT _ _) rfl⟩
  | up_braid h =>
    exact ⟨1, mul_mem_freeGrade' (hU _) (hT _ _) rfl, mul_mem_freeGrade' (hT _ _) (hU _) rfl⟩
  | braid_up_up k =>
    exact ⟨2, mul_mem_freeGrade' (hT _ _) (mul_mem_freeGrade' (hU _) (hU _) rfl) rfl,
      mul_mem_freeGrade' (hU _) (hU _) rfl⟩
  | down_down_braid m =>
    exact ⟨2, mul_mem_freeGrade' (mul_mem_freeGrade' (hD _) (hD _) rfl) (hT _ _) rfl,
      mul_mem_freeGrade' (hD _) (hD _) rfl⟩
  | down_delta j =>
    exact ⟨3, mul_mem_freeGrade'
      (mul_mem_freeGrade' (hD _) (commOf_mem hU hD _) rfl) (hT _ _) rfl,
      Submodule.smul_mem _ _ (mul_mem_freeGrade' (commOf_mem hU hD _) (hD _) rfl)⟩
  | braid_delta m =>
    exact ⟨3, mul_mem_freeGrade'
      (mul_mem_freeGrade' (hT _ _) (commOf_mem hU hD _) rfl) (hU _) rfl,
      Submodule.smul_mem _ _ (mul_mem_freeGrade' (hU _) (commOf_mem hU hD _) rfl)⟩

/-- **Every relation of `Ã` is homogeneous for the arrow degree**: both sides of each lie in one and
the same degree component. This is the first clause of the arrow-degree grading statement; the
second — that `Ã` and `Ãe_0/Ie_0` are therefore graded — is
`HJO.Dyck.Tilde.Atilde.isInternal_grade` of `HJO.CarlssonMellit.ArrowGraded`. -/
@[hjo "lem_cm_arrow_degree_graded"]
theorem rel_homogeneous {x y : FreeAlgebra K Gen} (h : Rel K q u x y) :
    ∃ d : ℕ, x ∈ freeGrade K d ∧ y ∈ freeGrade K d := by
  induction h with
  | vertex_mul_self k => exact ⟨0, mul_mem_freeGrade' (freeE_mem k) (freeE_mem k) rfl, freeE_mem k⟩
  | vertex_mul_vertex h =>
    exact ⟨0, mul_mem_freeGrade' (freeE_mem _) (freeE_mem _) rfl, Submodule.zero_mem _⟩
  | vertex_mul_down k =>
    exact ⟨1, mul_mem_freeGrade' (freeE_mem k) (freeDown_mem k) rfl, freeDown_mem k⟩
  | down_mul_vertex k =>
    exact ⟨1, mul_mem_freeGrade' (freeDown_mem k) (freeE_mem (k + 1)) rfl, freeDown_mem k⟩
  | vertex_mul_braid k i =>
    exact ⟨0, mul_mem_freeGrade' (freeE_mem k) (freeT_mem k i) rfl, freeT_mem k i⟩
  | braid_mul_vertex k i =>
    exact ⟨0, mul_mem_freeGrade' (freeT_mem k i) (freeE_mem k) rfl, freeT_mem k i⟩
  | braid_eq_zero h => exact ⟨0, freeT_mem _ _, Submodule.zero_mem _⟩
  | source h => exact sourceRel_homogeneous freeE_mem freeUp_mem freeDown_mem freeT_mem h
  | sourceStar h =>
    exact sourceRel_homogeneous freeE_mem freeUpStar_mem freeDown_mem freeTinv_mem h
  | mixed_z h1 h2 =>
    exact ⟨3, mul_mem_freeGrade' (freeZ_mem _ _) (freeUp_mem _) rfl,
      mul_mem_freeGrade' (freeUp_mem _) (freeZ_mem _ _) rfl⟩
  | mixed_y h1 h2 =>
    exact ⟨3, mul_mem_freeGrade' (freeY_mem _ _) (freeUpStar_mem _) rfl,
      mul_mem_freeGrade' (freeUpStar_mem _) (freeY_mem _ _) rfl⟩
  | mixed_top k =>
    exact ⟨3, mul_mem_freeGrade' (freeZ_mem _ _) (freeUp_mem _) rfl,
      Submodule.smul_mem _ _ (mul_mem_freeGrade' (freeY_mem _ _) (freeUpStar_mem _) rfl)⟩

/-! ### The kernel ideal is generated in one degree at a time -/

namespace Atilde

theorem exists_free_dPlusPow (v : ℕ) :
    ∀ m : ℕ, ∃ x ∈ freeGrade K m, mk K q u x = dPlusPow K q u v m := by
  intro m
  induction m with
  | zero => exact ⟨freeE K v, freeE_mem v, rfl⟩
  | succ m ih =>
    obtain ⟨x, hx, hxe⟩ := ih
    refine ⟨freeUp K (v + m) * x, mul_mem_freeGrade' (freeUp_mem _) hx (Nat.add_comm 1 m), ?_⟩
    rw [map_mul, hxe]
    rfl

theorem dPlusPow_mem_grade (v m : ℕ) : dPlusPow K q u v m ∈ grade K q u m := by
  obtain ⟨x, hx, hxe⟩ := exists_free_dPlusPow (K := K) (q := q) (u := u) v m
  exact hxe ▸ mem_grade_of_free hx

/-- **Each generator of the left ideal `I` is homogeneous**: `d₊^*d₊^m` and `d₊^{m+1}` both have
arrow degree `m + 1`. This is the first clause of the arrow-degree grading statement at the ideal
`I`;
that `I` is therefore a homogeneous submodule is
`HJO.Dyck.Tilde.Atilde.iSup_grade_inf_kernelIdeal` of `HJO.CarlssonMellit.ArrowGraded`. -/
@[hjo "lem_cm_arrow_degree_graded"]
theorem kernelIdeal_gen_homogeneous (v m : ℕ) :
    dPlusStar K q u (v + m) * dPlusPow K q u v m ∈ grade K q u (m + 1) ∧
      dPlusPow K q u v (m + 1) ∈ grade K q u (m + 1) := by
  refine ⟨?_, dPlusPow_mem_grade v (m + 1)⟩
  obtain ⟨x, hx, hxe⟩ := exists_free_dPlusPow (K := K) (q := q) (u := u) v m
  have hmul : mk K q u (freeUpStar K (v + m) * x)
      = dPlusStar K q u (v + m) * dPlusPow K q u v m := by rw [map_mul, hxe]; rfl
  exact hmul ▸ mem_grade_of_free
    (mul_mem_freeGrade' (freeUpStar_mem _) hx (Nat.add_comm 1 m))

end Atilde

end HJO.Dyck.Tilde
