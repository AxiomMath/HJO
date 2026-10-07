/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.BiGrading
public meta import HJO.Attr

/-! # The bigrading of `Ã` is well defined, and the sign it fixes

`HJO.CarlssonMellit.BiGrading` builds the components `Ã_{m,n}` and reads the two
homomorphisms off the generators. Two things the bigrading lemma asserts are not there:
that the bidegree is *well defined* on `Ã` — every relation of `HJO.Dyck.Tilde.Atilde` is
homogeneous in the two counts separately — and the sign clause, that the two homomorphisms differ
from the normalisations of `HJO.Sym.IsMacdonaldConjugator` and `HJO.Sym.IsIndexShift` by `(-1)^n`
and `(-1)^m` on `Ã_{m,n}`, so that multiplication
by `(-1)^{m+n}` intertwines the two pairs. This file supplies both and assembles the lemma.

## Main definitions

* `HJO.Dyck.Tilde.biSign`: the sign `(-1)^{m+n}` of the bidegree `(m,n)`.
* `HJO.Dyck.Tilde.Atilde.signTwist`: **multiplication by `(-1)^{m+n}`**, presented not through the
  grading but as the algebra endomorphism of `Ã` negating both raising arrows and fixing every
  idempotent, every loop and `d₋`. It exists *because* the relations are bihomogeneous, and
  `signTwist_of_mem_biGrade` is the statement that it is multiplication by `(-1)^{m+n}` on each
  component.

## Main results

* `HJO.Dyck.Tilde.rel_biHomogeneous`: **the bidegree is well defined** — both sides of every
  relation of `Ã` lie in one and the same bidegree component of the free algebra. The generic half
  is `sourceRel_biHomogeneous`, read twice: at the unstarred family, where the raising arrow has
  bidegree `(0,1)`, and at the starred one, where it has `(1,0)`.
* `HJO.Dyck.Tilde.Atilde.signTwist_of_mem_biGrade`: `signTwist` acts on `Ã_{m,n}` as `(-1)^{m+n}`.
* `HJO.Dyck.Tilde.Atilde.signTwist_signTwist`: it is an involution, so conjugating by it is
  conjugating by an automorphism.
* `HJO.Dyck.Tilde.Atilde.biGrading`: **the lemma**. For the two homomorphisms `Φ_c` and `Φ_s`, the
  two degree shifts `(m,n) ↦ (m+n,n)` and `(m,n) ↦ (m,m+n)`, together with the two sign clauses
  `signTwist ∘ Φ_c ∘ signTwist = (-1)^n Φ_c` and `signTwist ∘ Φ_s ∘ signTwist = (-1)^m Φ_s` on
  `Ã_{m,n}`.

## Implementation notes

**Which grading this is.** The bidegree counts the two *raising arrows* of the enlarged quiver,
`d₊^*` and `d₊`, and assigns `(0,0)` to `d₋`, to every loop and to every idempotent. It is neither
the arrow grading of `HJO.CarlssonMellit.ArrowGrading` (which counts all three arrows, so
`d₋` contributes and `y_i` has degree `2`) nor the grading of `V_*` by the number of auxiliary
variables (`HJO.Sweep.piece`, `HJO.Sweep.Vstar`), under which `d₊d₋` moves nothing. Nothing here is
a statement about `V_*` at all.

**Why the sign clause is stated as a conjugation and not against the two normalisations.** The
normalisations are those of `HJO.Sym.IsMacdonaldConjugator` (a predicate on
`Module.End L (Lambda L)`) and `HJO.Sym.IsIndexShift` (a predicate on
`DopAlgebra q u →ₐ[L] DopAlgebra q u`, over a `Field L` with `Algebra ℚ L`). Neither is an
endomorphism of `Ã`, so "`Φ_c` differs from the normalisation of `HJO.Sym.IsMacdonaldConjugator` by
`(-1)^n`" cannot be written as an equation between two endomorphisms of `Ã`: there is no second
endomorphism of `Ã` to compare with. What the clause does say, and what its consumers use, is that
the two normalisations differ by the scalar `(-1)^n` on the component — equivalently that
conjugating `Φ_c` by multiplication by `(-1)^{m+n}` rescales it by `(-1)^n` there. That is the form
proved here, and it is the form `HJO.Sym.nsShiftComp_comp_smul_map` quotes when it says the repair
of `HJO.Sym.IsIndexShift` is forced to be "the `(-1)^m`-twist" of this lemma.

**Why the two homomorphisms are hypotheses.** As in `HJO.Dyck.Tilde.Atilde.map_biGrade_le_conj`, the
endomorphisms `Φ_c` and `Φ_s` are taken as data pinned by their generator values rather than
constructed. Nothing here constructs them: `HJO.Sweep.exists_isDpaAction_replication` and
`HJO.Sweep.exists_isDpaAction_replication_star` produce an *action* — an algebra map
`𝔸_q → Module.End L (Vstar L)` — and not an endomorphism of `Ã`. So the conditional form is not a
weakening of what is available; it is what is available. Both hypotheses are discharged at any
consumer that has the maps.

**The scalar at `d₊`.** Left arbitrary, for the reason recorded at `map_biGrade_le_conj`: `u` is
nowhere assumed invertible, so the `-(qu)^{-1}` is not expressible at the ambient
hypotheses, and no conclusion here depends on the value.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, J. Amer. Math. Soc. **31**
(2018) 661--697, Section 3.7. -/

@[expose] public section

namespace HJO.Dyck.Tilde

variable {K : Type*} [CommRing K]

/-! ### The relations are bihomogeneous

This is the first step of the proof: the relations of `HJO.Dyck.Aq` involve no
`d₊^*`, their starred copies no `d₊`, and each of the three mixed relations has one `d₊` and one
`d₊^*` on each side. -/

/-- **The defining relations of `𝔸_q` are bihomogeneous**, in an arbitrary family of generators:
both sides of each lie in one and the same bidegree component. The raising family's bidegree is the
parameter `a`, since this is read twice — at `a = (0,1)` for `d₊` and at `a = (1,0)` for `d₊^*` —
while `d₋`, the loops and the idempotents sit at `(0,0)` in both readings. -/
theorem sourceRel_biHomogeneous {q' : K} {a : ℕ × ℕ} {E U D : ℕ → FreeAlgebra K Gen}
    {T : ℕ → ℕ → FreeAlgebra K Gen} (hE : ∀ n, E n ∈ freeBiGrade K 0)
    (hU : ∀ n, U n ∈ freeBiGrade K a) (hD : ∀ n, D n ∈ freeBiGrade K 0)
    (hT : ∀ n m, T n m ∈ freeBiGrade K 0) {x y : FreeAlgebra K Gen}
    (h : SourceRel q' E U D T x y) :
    ∃ d : ℕ × ℕ, x ∈ freeBiGrade K d ∧ y ∈ freeBiGrade K d := by
  induction h with
  | vertex_mul_up k => exact ⟨a, mul_mem_freeBiGrade' (hE (k + 1)) (hU k) (zero_add a), hU k⟩
  | up_mul_vertex k => exact ⟨a, mul_mem_freeBiGrade' (hU k) (hE k) (add_zero a), hU k⟩
  | quadratic h =>
    exact ⟨0, mul_mem_freeBiGrade' (Submodule.sub_mem _ (hT _ _) (hE _))
      (Submodule.add_mem _ (hT _ _) (Submodule.smul_mem _ _ (hE _))) (add_zero 0),
      Submodule.zero_mem _⟩
  | braid_braid h =>
    exact ⟨0, mul_mem_freeBiGrade'
        (mul_mem_freeBiGrade' (hT _ _) (hT _ _) (add_zero 0)) (hT _ _) (add_zero 0),
      mul_mem_freeBiGrade'
        (mul_mem_freeBiGrade' (hT _ _) (hT _ _) (add_zero 0)) (hT _ _) (add_zero 0)⟩
  | braid_comm hi hj hij =>
    exact ⟨0, mul_mem_freeBiGrade' (hT _ _) (hT _ _) (add_zero 0),
      mul_mem_freeBiGrade' (hT _ _) (hT _ _) (add_zero 0)⟩
  | braid_down h =>
    exact ⟨0, mul_mem_freeBiGrade' (hT _ _) (hD _) (add_zero 0),
      mul_mem_freeBiGrade' (hD _) (hT _ _) (add_zero 0)⟩
  | up_braid h =>
    exact ⟨a, mul_mem_freeBiGrade' (hU _) (hT _ _) (add_zero a),
      mul_mem_freeBiGrade' (hT _ _) (hU _) (zero_add a)⟩
  | braid_up_up k =>
    exact ⟨a + a, mul_mem_freeBiGrade' (hT _ _)
        (mul_mem_freeBiGrade' (hU _) (hU _) rfl) (zero_add _),
      mul_mem_freeBiGrade' (hU _) (hU _) rfl⟩
  | down_down_braid m =>
    exact ⟨0, mul_mem_freeBiGrade'
        (mul_mem_freeBiGrade' (hD _) (hD _) (add_zero 0)) (hT _ _) (add_zero 0),
      mul_mem_freeBiGrade' (hD _) (hD _) (add_zero 0)⟩
  | down_delta j =>
    exact ⟨a, mul_mem_freeBiGrade'
        (mul_mem_freeBiGrade' (hD _) (commOf_mem_biGrade hU hD _) (zero_add a)) (hT _ _)
        (add_zero a),
      Submodule.smul_mem _ _
        (mul_mem_freeBiGrade' (commOf_mem_biGrade hU hD _) (hD _) (add_zero a))⟩
  | braid_delta m =>
    exact ⟨a + a, mul_mem_freeBiGrade'
        (mul_mem_freeBiGrade' (hT _ _) (commOf_mem_biGrade hU hD _) (zero_add a)) (hU _) rfl,
      Submodule.smul_mem _ _
        (mul_mem_freeBiGrade' (hU _) (commOf_mem_biGrade hU hD _) rfl)⟩

variable {q u : K} [Invertible q] [Invertible (q - 1)]

/-- **The bidegree is well defined on `Ã`**: both sides of every relation lie in one and the same
bidegree component of the free algebra. This is the clause "Grade `Ã` by assigning the bidegree
`(0,1)` to `d₊` and `(1,0)` to `d₊^*`" of the bigrading lemma, and it is what makes
`HJO.Dyck.Tilde.Atilde.signTwist` exist. The three mixed relations all sit at `(1,1)`: `z_1d₊` and
`y_1d₊^*` both traverse each raising arrow once, which is exactly what makes
`z_1d₊ + uq^{k+1}y_1d₊^*` bihomogeneous. -/
@[hjo "lem_mellit_ns_bigrading"]
theorem rel_biHomogeneous {x y : FreeAlgebra K Gen} (h : Rel K q u x y) :
    ∃ d : ℕ × ℕ, x ∈ freeBiGrade K d ∧ y ∈ freeBiGrade K d := by
  induction h with
  | vertex_mul_self k =>
    exact ⟨0, mul_mem_freeBiGrade' (freeE_mem_biGrade k) (freeE_mem_biGrade k) (add_zero 0),
      freeE_mem_biGrade k⟩
  | vertex_mul_vertex h =>
    exact ⟨0, mul_mem_freeBiGrade' (freeE_mem_biGrade _) (freeE_mem_biGrade _) (add_zero 0),
      Submodule.zero_mem _⟩
  | vertex_mul_down k =>
    exact ⟨0, mul_mem_freeBiGrade' (freeE_mem_biGrade k) (freeDown_mem_biGrade k) (add_zero 0),
      freeDown_mem_biGrade k⟩
  | down_mul_vertex k =>
    exact ⟨0, mul_mem_freeBiGrade' (freeDown_mem_biGrade k) (freeE_mem_biGrade (k + 1))
      (add_zero 0), freeDown_mem_biGrade k⟩
  | vertex_mul_braid k i =>
    exact ⟨0, mul_mem_freeBiGrade' (freeE_mem_biGrade k) (freeT_mem_biGrade k i) (add_zero 0),
      freeT_mem_biGrade k i⟩
  | braid_mul_vertex k i =>
    exact ⟨0, mul_mem_freeBiGrade' (freeT_mem_biGrade k i) (freeE_mem_biGrade k) (add_zero 0),
      freeT_mem_biGrade k i⟩
  | braid_eq_zero h => exact ⟨0, freeT_mem_biGrade _ _, Submodule.zero_mem _⟩
  | source h =>
    exact sourceRel_biHomogeneous freeE_mem_biGrade freeUp_mem_biGrade freeDown_mem_biGrade
      freeT_mem_biGrade h
  | sourceStar h =>
    exact sourceRel_biHomogeneous freeE_mem_biGrade freeUpStar_mem_biGrade freeDown_mem_biGrade
      (freeTinv_mem_biGrade (q := q)) h
  | mixed_z h1 h2 =>
    exact ⟨(1, 1), mul_mem_freeBiGrade' (freeZ_mem_biGrade _ _) (freeUp_mem_biGrade _) rfl,
      mul_mem_freeBiGrade' (freeUp_mem_biGrade _) (freeZ_mem_biGrade _ _) rfl⟩
  | mixed_y h1 h2 =>
    exact ⟨(1, 1), mul_mem_freeBiGrade' (freeY_mem_biGrade _ _) (freeUpStar_mem_biGrade _) rfl,
      mul_mem_freeBiGrade' (freeUpStar_mem_biGrade _) (freeY_mem_biGrade _ _) rfl⟩
  | mixed_top k =>
    exact ⟨(1, 1), mul_mem_freeBiGrade' (freeZ_mem_biGrade _ _) (freeUp_mem_biGrade _) rfl,
      Submodule.smul_mem _ _
        (mul_mem_freeBiGrade' (freeY_mem_biGrade _ _) (freeUpStar_mem_biGrade _) rfl)⟩

/-! ### The sign of a bidegree -/

/-- **The sign of a bidegree**: `(-1)^{m+n}` at `(m,n)`. -/
def biSign (K : Type*) [CommRing K] (d : ℕ × ℕ) : K := (-1) ^ (d.1 + d.2)

@[simp] theorem biSign_zero : biSign K 0 = 1 := by simp [biSign]

theorem biSign_add (a b : ℕ × ℕ) : biSign K (a + b) = biSign K a * biSign K b := by
  have h : (a + b).1 + (a + b).2 = a.1 + a.2 + (b.1 + b.2) := by
    simp only [Prod.fst_add, Prod.snd_add]; omega
  simp only [biSign, h, pow_add]

/-- The sign of the `Φ_c`-image of `(m,n)` times the sign of `(m,n)` is `(-1)^n`: the first
discrepancy between the two normalisations. -/
theorem biSign_mul_biSign_conj (m n : ℕ) :
    biSign K (m, n) * biSign K (m + n, n) = (-1 : K) ^ n := by
  have h : m + n + (m + n + n) = 2 * (m + n) + n := by omega
  simp only [biSign]
  rw [← pow_add]
  change (-1 : K) ^ (m + n + (m + n + n)) = _
  rw [h, pow_add, pow_mul]
  simp

/-- The sign of the `Φ_s`-image of `(m,n)` times the sign of `(m,n)` is `(-1)^m`: the second
discrepancy between the two normalisations. -/
theorem biSign_mul_biSign_shift (m n : ℕ) :
    biSign K (m, n) * biSign K (m, m + n) = (-1 : K) ^ m := by
  have h : m + n + (m + (m + n)) = 2 * (m + n) + m := by omega
  simp only [biSign]
  rw [← pow_add]
  change (-1 : K) ^ (m + n + (m + (m + n))) = _
  rw [h, pow_add, pow_mul]
  simp

/-! ### Multiplication by `(-1)^{m+n}`

The operator "multiplication by `(-1)^{m+n}`" is built here from the
generators rather than from a direct-sum decomposition: negate both raising arrows, fix everything
else. That it descends to `Ã` is exactly `rel_biHomogeneous`, and that it *is* multiplication by
`(-1)^{m+n}` on each component is `Atilde.signTwist_of_mem_biGrade`. -/

/-- The free-algebra lift of multiplication by `(-1)^{m+n}`: a generator goes to its own image in
`Ã`, negated when it is a raising arrow. -/
noncomputable def signHom (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    FreeAlgebra K Gen →ₐ[K] Atilde K q u :=
  FreeAlgebra.lift K fun g => biSign K (biDeg g) • Atilde.mk K q u (FreeAlgebra.ι K g)

theorem signHom_ι (g : Gen) : signHom K q u (FreeAlgebra.ι K g)
    = biSign K (biDeg g) • Atilde.mk K q u (FreeAlgebra.ι K g) :=
  FreeAlgebra.lift_ι_apply _ _

theorem signHom_freeWord (w : List Gen) : signHom K q u (freeWord K w)
    = biSign K (biDegWord w) • Atilde.mk K q u (freeWord K w) := by
  induction w with
  | nil => rw [freeWord_nil, map_one, map_one, biDegWord_nil, biSign_zero, one_smul]
  | cons g w ih =>
    rw [freeWord_cons, map_mul (signHom K q u), ih, signHom_ι, biDegWord_cons, biSign_add,
      map_mul (Atilde.mk K q u), smul_mul_smul_comm]

/-- On the bidegree-`d` component of the free algebra the lift is `x ↦ (-1)^{m+n} • mk x`. -/
theorem signHom_of_mem_freeBiGrade {d : ℕ × ℕ} {x : FreeAlgebra K Gen}
    (hx : x ∈ freeBiGrade K d) : signHom K q u x = biSign K d • Atilde.mk K q u x := by
  refine Submodule.span_induction (p := fun x _ =>
    signHom K q u x = biSign K d • Atilde.mk K q u x) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨w, hw, rfl⟩
    rw [← hw]
    exact signHom_freeWord w
  · rw [map_zero, map_zero, smul_zero]
  · intro y z _ _ hy hz
    rw [map_add, hy, hz, map_add, smul_add]
  · intro c y _ hy
    rw [map_smul (signHom K q u), hy, map_smul (Atilde.mk K q u), smul_comm]

/-- **The lift kills the relations of `Ã`**: both sides of a relation lie in one bidegree component,
on which the lift is `x ↦ (-1)^{m+n} • mk x`, and `mk` identifies them. -/
theorem signHom_rel {x y : FreeAlgebra K Gen} (h : Rel K q u x y) :
    signHom K q u x = signHom K q u y := by
  obtain ⟨d, hx, hy⟩ := rel_biHomogeneous h
  rw [signHom_of_mem_freeBiGrade hx, signHom_of_mem_freeBiGrade hy, Atilde.mk_rel h]

namespace Atilde

/-- **Multiplication by `(-1)^{m+n}`**, the algebra endomorphism of `Ã` negating both raising arrows
and fixing every idempotent, every loop and `d₋`. It exists because the relations are
bihomogeneous, and `signTwist_of_mem_biGrade` identifies it with multiplication by `(-1)^{m+n}`.
-/
@[hjo "lem_mellit_ns_bigrading"]
noncomputable def signTwist (K : Type*) [CommRing K] (q u : K) [Invertible q] [Invertible (q - 1)] :
    Atilde K q u →ₐ[K] Atilde K q u :=
  RingQuot.liftAlgHom K ⟨signHom K q u, fun _ _ h => signHom_rel h⟩

@[simp] theorem signTwist_mk (x : FreeAlgebra K Gen) :
    signTwist K q u (mk K q u x) = signHom K q u x :=
  RingQuot.liftAlgHom_mkAlgHom_apply K (signHom K q u) (s := Rel K q u)
    (fun _ _ h => signHom_rel h) x

theorem signTwist_ι (g : Gen) : signTwist K q u (mk K q u (FreeAlgebra.ι K g))
    = biSign K (biDeg g) • mk K q u (FreeAlgebra.ι K g) := by
  rw [signTwist_mk, signHom_ι]

/-- **`signTwist` is multiplication by `(-1)^{m+n}` on `Ã_{m,n}`**: the sense in which
"multiplication by `(-1)^{m+n}`" is a well-defined operator on `Ã`. -/
@[hjo "lem_mellit_ns_bigrading"]
theorem signTwist_of_mem_biGrade {d : ℕ × ℕ} {a : Atilde K q u} (ha : a ∈ biGrade K q u d) :
    signTwist K q u a = biSign K d • a := by
  obtain ⟨x, hx, rfl⟩ := ha
  change signTwist K q u (mk K q u x) = biSign K d • mk K q u x
  rw [signTwist_mk, signHom_of_mem_freeBiGrade hx]

/-- **`signTwist` is an involution**, so conjugation by it is conjugation by an automorphism of `Ã`.
Checked on the generators, where the sign appears squared, and transported by the surjectivity of
the quotient map. -/
theorem signTwist_signTwist (a : Atilde K q u) : signTwist K q u (signTwist K q u a) = a := by
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective K (Rel K q u) a
  have key : (signTwist K q u).comp ((signTwist K q u).comp (RingQuot.mkAlgHom K (Rel K q u)))
      = RingQuot.mkAlgHom K (Rel K q u) := by
    refine FreeAlgebra.hom_ext (funext fun g => ?_)
    have h : signTwist K q u (mk K q u (FreeAlgebra.ι K g))
        = biSign K (biDeg g) • mk K q u (FreeAlgebra.ι K g) := signTwist_ι g
    simp only [AlgHom.comp_apply, Function.comp_apply]
    change signTwist K q u (signTwist K q u (mk K q u (FreeAlgebra.ι K g)))
      = mk K q u (FreeAlgebra.ι K g)
    rw [h, map_smul, h, smul_smul, ← biSign_add, biSign]
    have h2 : (biDeg g + biDeg g).1 + (biDeg g + biDeg g).2
        = 2 * ((biDeg g).1 + (biDeg g).2) := by
      simp only [Prod.fst_add, Prod.snd_add]; omega
    rw [h2, pow_mul]
    simp
  exact congrFun (congrArg (fun f : FreeAlgebra K Gen →ₐ[K] Atilde K q u => f.toFun) key) x

/-! ### The bigrading lemma -/

section Homomorphisms

variable (Φc Φs : Atilde K q u →ₐ[K] Atilde K q u)

/-- **Mellit, the bigrading fixes the two sign discrepancies.** Grade `Ã` by the bidegree of
`HJO.Dyck.Tilde.biDeg`, well defined by `HJO.Dyck.Tilde.rel_biHomogeneous`. Let `Φ_c` be an
algebra endomorphism of `Ã` sending `d₊` to a scalar multiple of `z_1d₊` and fixing `d₋`, each
`T_i`, each `e_k` and `d₊^*`, and let `Φ_s` be one sending `d₊^*` to `-y_1d₊^*` and fixing `d₋`,
each `T_i`, each `e_k` and `d₊`. Then `Φ_c` carries the `(m,n)` component to the `(m+n,n)`
component and `Φ_s` carries it to the `(m,m+n)` component; and conjugating by multiplication by
`(-1)^{m+n}` rescales the first by `(-1)^n` and the second by `(-1)^m` there, which is the
discrepancy between the normalisations of `HJO.Sym.IsMacdonaldConjugator` and
`HJO.Sym.IsIndexShift` and the ones written here.

The two sign clauses are the statement "the first differs from the normalisation of
`HJO.Sym.IsMacdonaldConjugator` by `(-1)^n` and the second from that of `HJO.Sym.IsIndexShift` by
`(-1)^m`, so multiplication by `(-1)^{m+n}` intertwines the two pairs". They are stated as
conjugation identities because neither cited normalisation is an endomorphism of `Ã` to compare
against; see the module docstring. -/
@[hjo "lem_mellit_ns_bigrading"]
theorem biGrading (c : K)
    (hEc : ∀ k, Φc (e K q u k) = e K q u k)
    (hTc : ∀ k i, Φc (Tg K q u k i) = Tg K q u k i)
    (hDc : ∀ k, Φc (dMinus K q u k) = dMinus K q u k)
    (hSc : ∀ k, Φc (dPlusStar K q u k) = dPlusStar K q u k)
    (hUc : ∀ k, Φc (dPlus K q u k) = c • (zElt K q u (k + 1) 1 * dPlus K q u k))
    (hEs : ∀ k, Φs (e K q u k) = e K q u k)
    (hTs : ∀ k i, Φs (Tg K q u k i) = Tg K q u k i)
    (hDs : ∀ k, Φs (dMinus K q u k) = dMinus K q u k)
    (hUs : ∀ k, Φs (dPlus K q u k) = dPlus K q u k)
    (hSs : ∀ k, Φs (dPlusStar K q u k) = -(yElt K q u (k + 1) 1 * dPlusStar K q u k))
    (m n : ℕ) :
    (biGrade K q u (m, n)).map Φc.toLinearMap ≤ biGrade K q u (m + n, n) ∧
      (biGrade K q u (m, n)).map Φs.toLinearMap ≤ biGrade K q u (m, m + n) ∧
      (∀ x ∈ biGrade K q u (m, n),
        signTwist K q u (Φc (signTwist K q u x)) = (-1 : K) ^ n • Φc x) ∧
      (∀ x ∈ biGrade K q u (m, n),
        signTwist K q u (Φs (signTwist K q u x)) = (-1 : K) ^ m • Φs x) := by
  have hc := map_biGrade_le_conj Φc hEc hTc hDc c hSc hUc m n
  have hs := map_biGrade_le_shift Φs hEs hTs hDs hUs hSs m n
  refine ⟨hc, hs, fun x hx => ?_, fun x hx => ?_⟩
  · have hΦ : Φc x ∈ biGrade K q u (m + n, n) := hc ⟨x, hx, rfl⟩
    rw [signTwist_of_mem_biGrade hx, map_smul, map_smul, signTwist_of_mem_biGrade hΦ, smul_smul,
      biSign_mul_biSign_conj]
  · have hΦ : Φs x ∈ biGrade K q u (m, m + n) := hs ⟨x, hx, rfl⟩
    rw [signTwist_of_mem_biGrade hx, map_smul, map_smul, signTwist_of_mem_biGrade hΦ, smul_smul,
      biSign_mul_biSign_shift]

end Homomorphisms

end Atilde

end HJO.Dyck.Tilde
