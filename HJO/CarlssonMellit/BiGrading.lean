/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ArrowGrading
public meta import HJO.Attr

/-! # The bigraded components of `Ã`, and how the two homomorphisms move them

`HJO.Dyck.Tilde.arrowDeg` counts all three arrows at once. Mellit's bigrading counts the two
*raising* arrows separately and ignores `d₋`: the bidegree of a path is the pair `(m, n)` where `m`
is the number of letters `d₊^*` and `n` the number of letters `d₊`. This file builds those
components and proves the four facts needed of them: the bidegree adds along a product,
the corner elements `y_i` and `z_i` are homogeneous of bidegrees `(0,1)` and `(1,0)`, and an algebra
endomorphism fixing all generators but one raising arrow moves the components by a linear map of
the bidegrees, `(m,n) ↦ (m+n,n)` or `(m,n) ↦ (m,m+n)`.

## Main definitions

* `HJO.Dyck.Tilde.biDeg`, `HJO.Dyck.Tilde.biDegWord`: the bidegree of a generator and of a word.
* `HJO.Dyck.Tilde.freeBiGrade`: the bidegree-`d` component of the free algebra.
* `HJO.Dyck.Tilde.Atilde.biGrade`: the bidegree-`d` component `Ã_{m,n}` of `Ã`.

## Main results

* `HJO.Dyck.Tilde.Atilde.biGrade_mul_biGrade_le`: `Ã_{m,n}Ã_{m',n'} ⊆ Ã_{m+m',n+n'}`.
* `HJO.Dyck.Tilde.Atilde.e_mem_biGrade_zero`, `dMinus_mem_biGrade_zero`, `Tg_mem_biGrade_zero`,
  `Tinv_mem_biGrade_zero`: the non-raising generators and the polynomial inverses of the loops have
  bidegree `(0,0)`.
* `HJO.Dyck.Tilde.Atilde.yElt_mem_biGrade`, `HJO.Dyck.Tilde.Atilde.zElt_mem_biGrade`: `y_i` lies in
  `Ã_{0,1}` and `z_i` in `Ã_{1,0}`.
* `HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj`: an endomorphism fixing `e_k`, `T_i`, `d₋` and `d₊^*`
  and sending `d₊` to a scalar multiple of `z_1d₊` carries `Ã_{m,n}` into `Ã_{m+n,n}`.
* `HJO.Dyck.Tilde.Atilde.map_biGrade_le_shift`: an endomorphism fixing `e_k`, `T_i`, `d₋` and `d₊`
  and sending `d₊^*` to `-y_1d₊^*` carries `Ã_{m,n}` into `Ã_{m,m+n}`.

## Implementation notes

**The shape of the bidegree.** The index is `ℕ × ℕ`, and the components are `Submodule K (Ã K q u)`
indexed by it, defined — exactly as `HJO.Dyck.Tilde.Atilde.grade` is — as the image under the
quotient map of the span of the words of that bidegree. No grading of `Ã` has to be constructed for
"`y_i` is homogeneous of bidegree `(0,1)`" to be a statement, and no direct-sum decomposition is
needed by any of the uses here.

`ℕ × ℕ` rather than `ℤ × ℤ` is safe here because *nothing here subtracts bidegrees*: the
product adds, the first homomorphism sends `(m,n)` to `(m+n,n)` and the second to `(m,m+n)`. Both of
those are additive maps `ℕ × ℕ → ℕ × ℕ`, and that additivity — `hf0` and `hfadd` below — is all the
transport lemma uses, so it is taken as a hypothesis rather than through `AddMonoidHom`, which would
have to be built twice for two one-line uses.

**The scalar in the two homomorphism lemmas.** The value of the first
homomorphism at `d₊` is `-(qu)^{-1}z_1d₊`. The bidegree conclusion does not depend on that scalar at
all — a scalar multiple stays inside the same span — and `u` carries no invertibility assumption
anywhere here, `Ã` itself being built over a `CommRing` with only `q` and `q - 1`
invertible. So `map_biGrade_le_conj` takes the scalar as an arbitrary `c : K`; the literal
statement is the instance `c = -(qu)^{-1}`, recorded as `map_biGrade_le_conj'` for the case where
`q * u` happens to be invertible. The second homomorphism's scalar is `-1`, which needs nothing, so
`map_biGrade_le_shift` states it literally.

The generic membership lemmas for `HJO.Dyck.commOf` and `HJO.Dyck.cornerOf` are stated with the
raising family's degree left as a parameter `a`, since they are read twice: at `d₊`, where `a` is
`(0,1)` and the answer is `y_i`, and at `d₊^*`, where `a` is `(1,0)` and the answer is `z_i`. This
is the same economy `HJO.Dyck.Tilde.sourceRel_homogeneous` makes for the relations.

`HJO.Dyck.Tilde.mul_mem_freeBiGrade'` takes the degree equation as its last argument for the reason
recorded at `HJO.Dyck.Tilde.mul_mem_freeGrade'`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
(2018) 661--697, Section 5.
-/

@[expose] public section

namespace HJO.Dyck.Tilde

/-! ### The bidegree of a word -/

/-- **The bidegree of a generator**: `(1,0)` on the raising arrow `d₊^*`, `(0,1)` on the raising
arrow `d₊`, and `(0,0)` on the lowering arrow `d₋`, on each loop `T_i` and on each idempotent. -/
@[hjo "def_mellit_ns_bidegree"]
def biDeg : Gen → ℕ × ℕ
  | .vertex _ => 0
  | .up _ => (0, 1)
  | .upStar _ => (1, 0)
  | .down _ => 0
  | .braid _ _ => 0

/-- **The bidegree of a word**: the pair counting how often it traverses `d₊^*` and how often it
traverses `d₊`. -/
@[hjo "def_mellit_ns_bidegree"]
def biDegWord (w : List Gen) : ℕ × ℕ := (w.map biDeg).sum

@[simp] theorem biDegWord_nil : biDegWord [] = 0 := rfl

@[simp] theorem biDegWord_cons (g : Gen) (w : List Gen) :
    biDegWord (g :: w) = biDeg g + biDegWord w := rfl

@[simp] theorem biDegWord_append (v w : List Gen) :
    biDegWord (v ++ w) = biDegWord v + biDegWord w := by
  simp [biDegWord, List.sum_append]

/-! ### The bidegree components of the free algebra -/

/-- **The bidegree-`d` component of the free algebra**: the span of the words of bidegree `d`. -/
def freeBiGrade (K : Type*) [CommRing K] (d : ℕ × ℕ) : Submodule K (FreeAlgebra K Gen) :=
  Submodule.span K {x | ∃ w : List Gen, biDegWord w = d ∧ x = freeWord K w}

variable {K : Type*} [CommRing K]

theorem freeWord_mem_freeBiGrade (w : List Gen) :
    freeWord K w ∈ freeBiGrade K (biDegWord w) :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

/-- A single generator lies in the component of its own bidegree. -/
theorem ι_mem_freeBiGrade (g : Gen) : FreeAlgebra.ι K g ∈ freeBiGrade K (biDeg g) := by
  have h := freeWord_mem_freeBiGrade (K := K) [g]
  rwa [freeWord_single, show biDegWord [g] = biDeg g from by simp] at h

theorem one_mem_freeBiGrade : (1 : FreeAlgebra K Gen) ∈ freeBiGrade K 0 :=
  freeWord_mem_freeBiGrade (K := K) []

/-- The components multiply as a bigrading should. -/
theorem mul_mem_freeBiGrade {a b : ℕ × ℕ} {x y : FreeAlgebra K Gen} (hx : x ∈ freeBiGrade K a)
    (hy : y ∈ freeBiGrade K b) : x * y ∈ freeBiGrade K (a + b) := by
  have hle : freeBiGrade K a * freeBiGrade K b ≤ freeBiGrade K (a + b) := by
    rw [freeBiGrade, freeBiGrade, Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨p, ⟨v, hv, rfl⟩, c, ⟨w, hw, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨v ++ w, by rw [biDegWord_append, hv, hw],
      (freeWord_append K v w).symm⟩
  exact hle (Submodule.mul_mem_mul hx hy)

/-- The multiplication rule with the target bidegree supplied last; see
`HJO.Dyck.Tilde.mul_mem_freeGrade'`. -/
theorem mul_mem_freeBiGrade' {a b c : ℕ × ℕ} {x y : FreeAlgebra K Gen} (hx : x ∈ freeBiGrade K a)
    (hy : y ∈ freeBiGrade K b) (habc : a + b = c) : x * y ∈ freeBiGrade K c :=
  habc ▸ mul_mem_freeBiGrade hx hy

theorem freeE_mem_biGrade (k : ℕ) : freeE K k ∈ freeBiGrade K 0 :=
  ι_mem_freeBiGrade (Gen.vertex k)

theorem freeUp_mem_biGrade (k : ℕ) : freeUp K k ∈ freeBiGrade K (0, 1) :=
  ι_mem_freeBiGrade (Gen.up k)

theorem freeUpStar_mem_biGrade (k : ℕ) : freeUpStar K k ∈ freeBiGrade K (1, 0) :=
  ι_mem_freeBiGrade (Gen.upStar k)

theorem freeDown_mem_biGrade (k : ℕ) : freeDown K k ∈ freeBiGrade K 0 :=
  ι_mem_freeBiGrade (Gen.down k)

theorem freeT_mem_biGrade (k i : ℕ) : freeT K k i ∈ freeBiGrade K 0 :=
  ι_mem_freeBiGrade (Gen.braid k i)

/-! ### The generic data is bihomogeneous

The raising family's bidegree is left as the parameter `a`: the unstarred reading takes `a = (0,1)`
and produces `y_i`, the starred one takes `a = (1,0)` and produces `z_i`. -/

theorem commOf_mem_biGrade {a : ℕ × ℕ} {U D : ℕ → FreeAlgebra K Gen}
    (hU : ∀ n, U n ∈ freeBiGrade K a) (hD : ∀ n, D n ∈ freeBiGrade K 0) (n : ℕ) :
    commOf U D n ∈ freeBiGrade K a := by
  rw [commOf]
  exact Submodule.sub_mem _ (mul_mem_freeBiGrade' (hU n) (hD n) (add_zero a))
    (mul_mem_freeBiGrade' (hD (n + 1)) (hU (n + 1)) (zero_add a))

theorem tinvOf_mem_biGrade {T ε : FreeAlgebra K Gen} (q' qi : K) (hT : T ∈ freeBiGrade K 0)
    (hε : ε ∈ freeBiGrade K 0) : tinvOf q' qi T ε ∈ freeBiGrade K 0 := by
  rw [tinvOf]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hT (Submodule.smul_mem _ _ hε))

theorem tinvWordOf_mem_biGrade {E : ℕ → FreeAlgebra K Gen} {T : ℕ → ℕ → FreeAlgebra K Gen}
    (q' qi : K) (hE : ∀ n, E n ∈ freeBiGrade K 0) (hT : ∀ n m, T n m ∈ freeBiGrade K 0) (k n : ℕ) :
    tinvWordOf q' qi E T k n ∈ freeBiGrade K 0 := by
  induction n with
  | zero => exact hE k
  | succ n ih =>
    rw [tinvWordOf]
    exact mul_mem_freeBiGrade' (tinvOf_mem_biGrade q' qi (hT k n) (hE k)) ih (add_zero 0)

theorem cornerAux_mem_biGrade {a : ℕ × ℕ} {E U D : ℕ → FreeAlgebra K Gen}
    {T : ℕ → ℕ → FreeAlgebra K Gen} (q' qi di : K) (hE : ∀ n, E n ∈ freeBiGrade K 0)
    (hU : ∀ n, U n ∈ freeBiGrade K a) (hD : ∀ n, D n ∈ freeBiGrade K 0)
    (hT : ∀ n m, T n m ∈ freeBiGrade K 0) (k j : ℕ) :
    cornerAux q' qi di E U D T k j ∈ freeBiGrade K a := by
  induction j with
  | zero =>
    rw [cornerAux]
    exact Submodule.smul_mem _ _ (mul_mem_freeBiGrade'
      (mul_mem_freeBiGrade' (tinvWordOf_mem_biGrade q' qi hE hT k (k - 1))
        (commOf_mem_biGrade hU hD (k - 1)) (zero_add a)) (hE k) (add_zero a))
  | succ j ih =>
    rw [cornerAux]
    exact Submodule.smul_mem _ _ (mul_mem_freeBiGrade'
      (mul_mem_freeBiGrade' (hT k (k - j - 2)) ih (zero_add a)) (hT k (k - j - 2)) (add_zero a))

theorem cornerOf_mem_biGrade {a : ℕ × ℕ} {E U D : ℕ → FreeAlgebra K Gen}
    {T : ℕ → ℕ → FreeAlgebra K Gen} (q' qi di : K) (hE : ∀ n, E n ∈ freeBiGrade K 0)
    (hU : ∀ n, U n ∈ freeBiGrade K a) (hD : ∀ n, D n ∈ freeBiGrade K 0)
    (hT : ∀ n m, T n m ∈ freeBiGrade K 0) (k i : ℕ) :
    cornerOf q' qi di E U D T k i ∈ freeBiGrade K a :=
  cornerAux_mem_biGrade q' qi di hE hU hD hT k (k - i)

/-! ### The corner elements of the free algebra -/

variable {q u : K} [Invertible q]

theorem freeTinv_mem_biGrade (k i : ℕ) : freeTinv K q k i ∈ freeBiGrade K 0 := by
  rw [freeTinv]
  exact tinvOf_mem_biGrade q ⅟q (freeT_mem_biGrade k i) (freeE_mem_biGrade k)

variable [Invertible (q - 1)]

/-- `y_i` has bidegree `(0,1)`: one `d₊` from the commutator and nothing else. -/
theorem freeY_mem_biGrade (k i : ℕ) : freeY K q k i ∈ freeBiGrade K (0, 1) := by
  rw [freeY]
  exact cornerOf_mem_biGrade q ⅟q ⅟(q - 1) freeE_mem_biGrade freeUp_mem_biGrade
    freeDown_mem_biGrade freeT_mem_biGrade k i

/-- `z_i` has bidegree `(1,0)`: the starred substitution puts `d₊^*` where the commutator had `d₊`,
and the loops it puts in place of the `T_j` are still of bidegree `(0,0)`. -/
theorem freeZ_mem_biGrade (k i : ℕ) : freeZ K q k i ∈ freeBiGrade K (1, 0) := by
  rw [freeZ]
  exact cornerOf_mem_biGrade (⅟q) q (-(q * ⅟(q - 1))) freeE_mem_biGrade freeUpStar_mem_biGrade
    freeDown_mem_biGrade freeTinv_mem_biGrade k i

namespace Atilde

/-! ### The bigraded components of `Ã` -/

/-- **The bigraded component `Ã_{m,n}`**: the `K`-span of the images in `Ã` of the paths of the
enlarged quiver traversing `d₊^*` exactly `m` times and `d₊` exactly `n` times, written as the image
under the quotient map of the bidegree-`(m,n)` component of the free algebra. -/
@[hjo "def_mellit_ns_bidegree"]
noncomputable def biGrade (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)]
    (d : ℕ × ℕ) : Submodule K (Atilde K q u) :=
  (freeBiGrade K d).map (mk K q u).toLinearMap

theorem mem_biGrade_of_free {d : ℕ × ℕ} {x : FreeAlgebra K Gen} (h : x ∈ freeBiGrade K d) :
    mk K q u x ∈ biGrade K q u d :=
  Submodule.mem_map_of_mem h

theorem one_mem_biGrade : (1 : Atilde K q u) ∈ biGrade K q u 0 := by
  have h := mem_biGrade_of_free (K := K) (q := q) (u := u) one_mem_freeBiGrade
  rwa [map_one] at h

/-! ### The bidegree adds along a product -/

/-- **The bidegree adds along a product**: `Ã_{m,n}Ã_{m',n'} ⊆ Ã_{m+m',n+n'}`. -/
@[hjo "lem_mellit_ns_bidegree_product"]
theorem biGrade_mul_biGrade_le (m n m' n' : ℕ) :
    biGrade K q u (m, n) * biGrade K q u (m', n') ≤ biGrade K q u (m + m', n + n') := by
  rw [Submodule.mul_le]
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
  have h := mem_biGrade_of_free (q := q) (u := u) (mul_mem_freeBiGrade hx' hy')
  rw [map_mul] at h
  exact h

/-- The element form of `HJO.Dyck.Tilde.Atilde.biGrade_mul_biGrade_le`, with the target bidegree
supplied last. -/
theorem mul_mem_biGrade' {a b c : ℕ × ℕ} {x y : Atilde K q u} (hx : x ∈ biGrade K q u a)
    (hy : y ∈ biGrade K q u b) (habc : a + b = c) : x * y ∈ biGrade K q u c := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have h := mem_biGrade_of_free (q := q) (u := u) (mul_mem_freeBiGrade' hx' hy' habc)
  rw [map_mul] at h
  exact h

/-! ### The non-raising generators have bidegree zero -/

/-- **The idempotent `e_k` has bidegree `(0,0)`**. -/
@[hjo "lem_mellit_ns_bidegree_loops"]
theorem e_mem_biGrade_zero (k : ℕ) : e K q u k ∈ biGrade K q u 0 :=
  mem_biGrade_of_free (freeE_mem_biGrade k)

/-- **The lowering arrow `d₋` has bidegree `(0,0)`**: the bidegree counts only the two raising
arrows. -/
@[hjo "lem_mellit_ns_bidegree_loops"]
theorem dMinus_mem_biGrade_zero (k : ℕ) : dMinus K q u k ∈ biGrade K q u 0 :=
  mem_biGrade_of_free (freeDown_mem_biGrade k)

/-- **The loop `T_i` has bidegree `(0,0)`**. -/
@[hjo "lem_mellit_ns_bidegree_loops"]
theorem Tg_mem_biGrade_zero (k i : ℕ) : Tg K q u k i ∈ biGrade K q u 0 :=
  mem_biGrade_of_free (freeT_mem_biGrade k i)

/-- **The polynomial inverse `T̂_i` has bidegree `(0,0)`**: it is a `K`-combination of the loop and
the idempotent, and `Ã_{0,0}` is a `K`-span. -/
@[hjo "lem_mellit_ns_bidegree_braid_inverse"]
theorem Tinv_mem_biGrade_zero (k i : ℕ) : Tinv K q u k i ∈ biGrade K q u 0 := by
  rw [← mk_freeTinv]
  exact mem_biGrade_of_free (freeTinv_mem_biGrade k i)

/-- **The raising arrow `d₊` has bidegree `(0,1)`**. -/
@[hjo "def_mellit_ns_bidegree"]
theorem dPlus_mem_biGrade (k : ℕ) : dPlus K q u k ∈ biGrade K q u (0, 1) :=
  mem_biGrade_of_free (freeUp_mem_biGrade k)

/-- **The raising arrow `d₊^*` has bidegree `(1,0)`**. -/
@[hjo "def_mellit_ns_bidegree"]
theorem dPlusStar_mem_biGrade (k : ℕ) : dPlusStar K q u k ∈ biGrade K q u (1, 0) :=
  mem_biGrade_of_free (freeUpStar_mem_biGrade k)

/-! ### The corner elements are bihomogeneous -/

/-- **The corner element `y_i` lies in `Ã_{0,1}`**: a word of idempotents, loops and polynomial
inverses, all of bidegree `(0,0)`, times the commutator `d₊d₋ - d₋d₊`, each of whose two words
traverses `d₊` once and `d₊^*` not at all. -/
@[hjo "lem_mellit_ns_bidegree_corner"]
theorem yElt_mem_biGrade (k i : ℕ) : yElt K q u k i ∈ biGrade K q u (0, 1) := by
  rw [← mk_freeY]
  exact mem_biGrade_of_free (freeY_mem_biGrade k i)

/-- **The starred corner element `z_i` lies in `Ã_{1,0}`**: the same reading of the same two
formulas, with `d₊^*` in place of `d₊` in the commutator and `T̂_j` in place of `T_j`, the latter
still of bidegree `(0,0)`. -/
@[hjo "lem_mellit_ns_bidegree_corner_star"]
theorem zElt_mem_biGrade (k i : ℕ) : zElt K q u k i ∈ biGrade K q u (1, 0) := by
  rw [← mk_freeZ]
  exact mem_biGrade_of_free (freeZ_mem_biGrade k i)

/-! ### Transporting the bigrading along an endomorphism

An endomorphism whose value at each generator is bihomogeneous of the bidegree an additive map `f`
assigns to that generator carries `Ã_d` into `Ã_{f d}`, because a word's image is the product of the
images of its letters and the bidegree adds along a product. -/

section Transport

variable (Φ : Atilde K q u →ₐ[K] Atilde K q u) {f : ℕ × ℕ → ℕ × ℕ}

/-- A word's image lies in the component `f` assigns to the word's bidegree. -/
theorem map_freeWord_mem_biGrade (hf0 : f 0 = 0) (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hgen : ∀ g : Gen, Φ (mk K q u (FreeAlgebra.ι K g)) ∈ biGrade K q u (f (biDeg g)))
    (w : List Gen) : Φ (mk K q u (freeWord K w)) ∈ biGrade K q u (f (biDegWord w)) := by
  induction w with
  | nil => rw [freeWord_nil, map_one, map_one, biDegWord_nil, hf0]; exact one_mem_biGrade
  | cons g w ih =>
    rw [freeWord_cons, map_mul, map_mul, biDegWord_cons]
    exact mul_mem_biGrade' (hgen g) ih (hfadd _ _).symm

/-- The image of the whole free component lies in the component `f` assigns to it. -/
theorem map_mem_biGrade_of_free (hf0 : f 0 = 0) (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hgen : ∀ g : Gen, Φ (mk K q u (FreeAlgebra.ι K g)) ∈ biGrade K q u (f (biDeg g)))
    {d : ℕ × ℕ} {x : FreeAlgebra K Gen} (hx : x ∈ freeBiGrade K d) :
    Φ (mk K q u x) ∈ biGrade K q u (f d) := by
  have h : freeBiGrade K d ≤
      Submodule.comap (Φ.toLinearMap ∘ₗ (mk K q u).toLinearMap) (biGrade K q u (f d)) := by
    rw [freeBiGrade, Submodule.span_le]
    rintro y ⟨w, rfl, rfl⟩
    exact map_freeWord_mem_biGrade Φ hf0 hfadd hgen w
  exact h hx

/-- **The transport rule**: an endomorphism bihomogeneous on the generators for an additive `f`
carries `Ã_d` into `Ã_{f d}`. -/
theorem map_biGrade_le (hf0 : f 0 = 0) (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hgen : ∀ g : Gen, Φ (mk K q u (FreeAlgebra.ι K g)) ∈ biGrade K q u (f (biDeg g)))
    (d : ℕ × ℕ) : (biGrade K q u d).map Φ.toLinearMap ≤ biGrade K q u (f d) := by
  rintro y ⟨x, ⟨x', hx', rfl⟩, rfl⟩
  exact map_mem_biGrade_of_free Φ hf0 hfadd hgen hx'

end Transport

section Homomorphisms

variable (Φ : Atilde K q u →ₐ[K] Atilde K q u)
  (hE : ∀ k, Φ (e K q u k) = e K q u k)
  (hT : ∀ k i, Φ (Tg K q u k i) = Tg K q u k i)
  (hD : ∀ k, Φ (dMinus K q u k) = dMinus K q u k)

include hE hT hD

/-- **The reading-off on generators for the first homomorphism**: an endomorphism of `Ã` fixing
every idempotent `e_k`, every `T_i`, every `d₋` and every `d₊^*`, and sending `d₊` at the vertex `k`
to a scalar multiple of `z_1d₊`, carries `Ã_{m,n}` into `Ã_{m+n,n}`.

The scalar is `-(qu)^{-1}`; it is left arbitrary because the conclusion is a membership
in a `K`-span and so does not depend on it, and because `u` carries no invertibility assumption
here. See `map_biGrade_le_conj'` for the literal instance. -/
@[hjo "lem_mellit_ns_bidegree_conj"]
theorem map_biGrade_le_conj (c : K) (hS : ∀ k, Φ (dPlusStar K q u k) = dPlusStar K q u k)
    (hU : ∀ k, Φ (dPlus K q u k) = c • (zElt K q u (k + 1) 1 * dPlus K q u k)) (m n : ℕ) :
    (biGrade K q u (m, n)).map Φ.toLinearMap ≤ biGrade K q u (m + n, n) :=
  map_biGrade_le Φ (f := fun d => (d.1 + d.2, d.2)) rfl
    (by rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩; simp [Prod.ext_iff]; omega)
    (by
      intro g
      cases g with
      | vertex k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.vertex k)) = e K q u k from rfl, hE]
        exact e_mem_biGrade_zero k
      | up k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.up k)) = dPlus K q u k from rfl, hU]
        exact Submodule.smul_mem _ _
          (mul_mem_biGrade' (zElt_mem_biGrade (k + 1) 1) (dPlus_mem_biGrade k) rfl)
      | upStar k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.upStar k)) = dPlusStar K q u k from rfl, hS]
        exact dPlusStar_mem_biGrade k
      | down k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.down k)) = dMinus K q u k from rfl, hD]
        exact dMinus_mem_biGrade_zero k
      | braid k i =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.braid k i)) = Tg K q u k i from rfl, hT]
        exact Tg_mem_biGrade_zero k i)
    (m, n)

/-- `map_biGrade_le_conj` at the stated scalar `-(qu)^{-1}`, where `q * u` is invertible.
The invertibility of `u` is nowhere assumed here, which is why the general form above
is the one used. -/
theorem map_biGrade_le_conj' [Invertible (q * u)]
    (hS : ∀ k, Φ (dPlusStar K q u k) = dPlusStar K q u k)
    (hU : ∀ k, Φ (dPlus K q u k) = -⅟(q * u) • (zElt K q u (k + 1) 1 * dPlus K q u k)) (m n : ℕ) :
    (biGrade K q u (m, n)).map Φ.toLinearMap ≤ biGrade K q u (m + n, n) :=
  map_biGrade_le_conj Φ hE hT hD (-⅟(q * u)) hS hU m n

/-- **The reading-off on generators for the second homomorphism**: an endomorphism of `Ã` fixing
every idempotent `e_k`, every `T_i`, every `d₋` and every `d₊`, and sending `d₊^*` at the vertex `k`
to `-y_1d₊^*`, carries `Ã_{m,n}` into `Ã_{m,m+n}`. -/
@[hjo "lem_mellit_ns_bidegree_shift"]
theorem map_biGrade_le_shift (hU : ∀ k, Φ (dPlus K q u k) = dPlus K q u k)
    (hS : ∀ k, Φ (dPlusStar K q u k) = -(yElt K q u (k + 1) 1 * dPlusStar K q u k)) (m n : ℕ) :
    (biGrade K q u (m, n)).map Φ.toLinearMap ≤ biGrade K q u (m, m + n) :=
  map_biGrade_le Φ (f := fun d => (d.1, d.1 + d.2)) rfl
    (by rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩; simp [Prod.ext_iff]; omega)
    (by
      intro g
      cases g with
      | vertex k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.vertex k)) = e K q u k from rfl, hE]
        exact e_mem_biGrade_zero k
      | up k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.up k)) = dPlus K q u k from rfl, hU]
        exact dPlus_mem_biGrade k
      | upStar k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.upStar k)) = dPlusStar K q u k from rfl, hS]
        exact Submodule.neg_mem _
          (mul_mem_biGrade' (yElt_mem_biGrade (k + 1) 1) (dPlusStar_mem_biGrade k) rfl)
      | down k =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.down k)) = dMinus K q u k from rfl, hD]
        exact dMinus_mem_biGrade_zero k
      | braid k i =>
        rw [show mk K q u (FreeAlgebra.ι K (Gen.braid k i)) = Tg K q u k i from rfl, hT]
        exact Tg_mem_biGrade_zero k i)
    (m, n)

end Homomorphisms

end Atilde

end HJO.Dyck.Tilde
