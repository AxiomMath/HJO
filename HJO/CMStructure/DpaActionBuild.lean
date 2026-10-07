/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.DyckPathAlgebra
public import HJO.Shuffle.BraidRelations
public import HJO.Shuffle.DpaAction
public import HJO.Shuffle.SweepAppendWidth
public meta import HJO.Attr

/-! # Building an action of the Dyck path algebra out of nine relations

`HJO.Dyck.Aq` presents `𝔸_q` as a `RingQuot` of the free algebra on the arrows of Carlsson and
Mellit's quiver, and `HJO.Sweep.IsDpaAction` asks for a `𝕜`-algebra homomorphism `𝔸_q → End_𝕜(V_*)`
sending `𝟏_k` to the projection onto `V_k`. So producing an action means: send each generator to an
operator, lift through `FreeAlgebra.lift`, and check the eighteen relations of `HJO.Dyck.Aq` — nine
of the path-algebra structure and Carlsson and Mellit's nine.

Two statements ask for exactly that, differing only in which family of operators is used:
`HJO.Sweep.exists_isDpaAction_cm` for Carlsson and Mellit's own `d_-`, `d_+` of `HJO.Sweep.dminusCM`
and `HJO.Sweep.cmDPlus`, and `HJO.Sweep.exists_isDpaAction_mod` for Mellit's modified `d^♭_-`,
`d^♭_+` of `HJO.Sweep.dminus` and `HJO.Sweep.dplus_eq_ascWord`. The braid operators are the same in
both. This file does the construction once, with the three operator families abstract and Carlsson
and Mellit's nine relations as hypotheses (`HJO.Sweep.IsDpaOperators`), so that each of the two
statements is an instance and nothing is duplicated.

## Main definitions

* `HJO.Sweep.loopVstar`, `HJO.Sweep.lowerVstar`, `HJO.Sweep.raiseVstar` — a family of maps between
  the graded pieces, read as endomorphisms of `V_*`: on the summand the arrow starts at, the given
  map; zero on every other summand.
* `HJO.Sweep.deltaVstar` — the image of `HJO.Dyck.Aq.Delta`, the commutator `d_+d_- - d_-d_+`.
* `HJO.Sweep.IsDpaOperators` — Carlsson and Mellit's nine relations for an abstract triple of
  families, together with the vanishing of the loops the quiver does not have.
* `HJO.Sweep.actionOf` — the action such a triple generates.
* `HJO.Sweep.braidModPiece` — the Demazure--Lusztig operator `T_{i+1}` on `V_k`, and `0` when the
  quiver has no such loop. This is the loop family of both instances.

## Main results

* `HJO.Sweep.IsDpaOperators.exists_isDpaAction` — the construction: nine relations give an action.
* `HJO.Sweep.braidModPiece_quadratic`, `HJO.Sweep.braidModPiece_braid`,
  `HJO.Sweep.braidModPiece_comm` — the first relation family, which both instances share:
  `HJO.Sweep.braid_braid_apply`, `HJO.Sweep.braid_braid` and `HJO.Sweep.braid_comm` read on the
  summand.

## Implementation notes

**Composability is enforced by sandwiching, not asserted.** Each generator goes to
`ι_k ∘ (map) ∘ π_j`, with `π_j` the projection onto the summand its arrow starts at and `ι_k` the
inclusion of the one it ends at. The nine path-algebra relations of `HJO.Dyck.Aq` then reduce to the
two computations `π_kι_k = 1` and `π_kι_l = 0` of `HJO.Sweep.toPiece_ofPiece` and
`HJO.Sweep.toPiece_ofPiece_of_ne`, and `HJO.Sweep.IsDpaAction`'s clause `ρ(𝟏_k) = ` the projection
onto `V_k` holds by construction. This is why one can say "a path algebra is free on its arrows
subject only to composability, and composability is respected" and pass on.

**The action lives on `V_*` and could not live on the total space.** Two of Carlsson and Mellit's
nine relations — `T_1d_+^2 = d_+^2` and `d_-^2T_{k-1} = d_-^2` — are false on `HJO.Sweep.Total` and
hold only on the graded pieces. Here the hypotheses of `IsDpaOperators` are stated for maps between
the pieces `HJO.Sweep.pieceSub`, so the membership those two relations read is the defining property
of the element the relation is applied to, and nothing has to be carried.

**The loop index is shifted by one**, as `HJO.Dyck.Aq` declares: its generator `Tg k i` is the
Carlsson and Mellit's `T_{i+1}` at the vertex `k`, so `HJO.Sweep.braidModPiece q k i` is
`HJO.Sweep.braid` at the index `i + 1`, and the quiver's range `i + 2 ≤ k` is what
`HJO.Sweep.braid_mem_piece` reads. Outside it the generator is `0` by `HJO.Dyck.Rel.braid_eq_zero`,
which is `HJO.Sweep.braidModPiece_of_le`.

## References

The two results this construction serves are `HJO.Sweep.exists_isDpaAction_cm` and
`HJO.Sweep.exists_isDpaAction_mod`. Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, §3, and A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

section Build

variable {L : Type*} [CommRing L]

/-! ### A family of maps between the pieces, read on `V_*` -/

/-- **A family of endomorphisms of the pieces, read on `V_*`**: on the summand `V_k` the given map,
zero on every other summand. This is the image of the loop `Tg k i` of `HJO.Dyck.Aq`. -/
noncomputable def loopVstar (T : ∀ k : ℕ, ℕ → (pieceSub L k →ₗ[L] pieceSub L k)) (k i : ℕ) :
    Module.End L (Vstar L) :=
  (ofPiece L k).comp ((T k i).comp (toPiece L k))

/-- **A family of maps `V_{k+1} → V_k`, read on `V_*`**: the image of the lowering arrow `d₋` of
`HJO.Dyck.Aq` at the vertex `k + 1`. -/
noncomputable def lowerVstar (D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k) (k : ℕ) :
    Module.End L (Vstar L) :=
  (ofPiece L k).comp ((D k).comp (toPiece L (k + 1)))

/-- **A family of maps `V_k → V_{k+1}`, read on `V_*`**: the image of the raising arrow `d₊` of
`HJO.Dyck.Aq` at the vertex `k`. -/
noncomputable def raiseVstar (U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)) (k : ℕ) :
    Module.End L (Vstar L) :=
  (ofPiece L (k + 1)).comp ((U k).comp (toPiece L k))

/-- **The image of `HJO.Dyck.Aq.Delta`**, the commutator `d₊d₋ - d₋d₊` at the vertex `k + 1`. -/
noncomputable def deltaVstar (D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k)
    (U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)) (k : ℕ) : Module.End L (Vstar L) :=
  raiseVstar U k * lowerVstar D k - lowerVstar D (k + 1) * raiseVstar U (k + 1)

variable {T : ∀ k : ℕ, ℕ → (pieceSub L k →ₗ[L] pieceSub L k)}
  {D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k}
  {U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)}

@[simp]
theorem loopVstar_ofPiece (k i : ℕ) (F : pieceSub L k) :
    loopVstar T k i (ofPiece L k F) = ofPiece L k (T k i F) := by
  rw [loopVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece]

@[simp]
theorem loopVstar_ofPiece_of_ne {k l : ℕ} (i : ℕ) (h : l ≠ k) (F : pieceSub L l) :
    loopVstar T k i (ofPiece L l F) = 0 := by
  rw [loopVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece_of_ne h, map_zero,
    map_zero]

@[simp]
theorem lowerVstar_ofPiece (k : ℕ) (F : pieceSub L (k + 1)) :
    lowerVstar D k (ofPiece L (k + 1) F) = ofPiece L k (D k F) := by
  rw [lowerVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece]

@[simp]
theorem lowerVstar_ofPiece_of_ne {k l : ℕ} (h : l ≠ k + 1) (F : pieceSub L l) :
    lowerVstar D k (ofPiece L l F) = 0 := by
  rw [lowerVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece_of_ne h, map_zero,
    map_zero]

@[simp]
theorem raiseVstar_ofPiece (k : ℕ) (F : pieceSub L k) :
    raiseVstar U k (ofPiece L k F) = ofPiece L (k + 1) (U k F) := by
  rw [raiseVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece]

@[simp]
theorem raiseVstar_ofPiece_of_ne {k l : ℕ} (h : l ≠ k) (F : pieceSub L l) :
    raiseVstar U k (ofPiece L l F) = 0 := by
  rw [raiseVstar, LinearMap.comp_apply, LinearMap.comp_apply, toPiece_ofPiece_of_ne h, map_zero,
    map_zero]

/-- `HJO.Dyck.Aq.Delta` at the vertex `k + 1`, read on that summand. -/
theorem deltaVstar_ofPiece (k : ℕ) (F : pieceSub L (k + 1)) :
    deltaVstar D U k (ofPiece L (k + 1) F)
      = ofPiece L (k + 1) (U k (D k F) - D (k + 1) (U (k + 1) F)) := by
  rw [deltaVstar, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    lowerVstar_ofPiece, raiseVstar_ofPiece, raiseVstar_ofPiece, lowerVstar_ofPiece, map_sub]

/-- `HJO.Dyck.Aq.Delta` at the vertex `k + 1` kills every other summand. -/
@[simp]
theorem deltaVstar_ofPiece_of_ne {k l : ℕ} (h : l ≠ k + 1) (F : pieceSub L l) :
    deltaVstar D U k (ofPiece L l F) = 0 := by
  rw [deltaVstar, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    lowerVstar_ofPiece_of_ne h, raiseVstar_ofPiece_of_ne h, map_zero, map_zero, sub_zero]

/-- **Endomorphisms of `V_*` agree as soon as they agree on every summand.** -/
theorem vstar_ext {f g : Module.End L (Vstar L)}
    (h : ∀ (l : ℕ) (F : pieceSub L l), f (ofPiece L l F) = g (ofPiece L l F)) : f = g :=
  DirectSum.linearMap_ext L fun l => LinearMap.ext fun F => h l F

/-- Two elements of one summand agree as soon as their underlying elements of the total space do. -/
theorem ofPiece_congr {k : ℕ} {X Y : pieceSub L k} (h : (X : Total L) = Y) :
    ofPiece L k X = ofPiece L k Y :=
  congrArg (ofPiece L k) (Subtype.ext h)

/-! ### The nine relations of the path-algebra structure -/

/-- `𝟏_{k+1}d₊ = d₊`: the raising arrow lands at the vertex `k + 1`. -/
theorem pieceProj_mul_raiseVstar (k : ℕ) :
    pieceProj L (k + 1) * raiseVstar U k = raiseVstar U k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | h
  · rw [raiseVstar_ofPiece, pieceProj_ofPiece]
  · rw [raiseVstar_ofPiece_of_ne (Ne.symm h), map_zero]

/-- `d₊𝟏_k = d₊`: the raising arrow starts at the vertex `k`. -/
theorem raiseVstar_mul_pieceProj (k : ℕ) :
    raiseVstar U k * pieceProj L k = raiseVstar U k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | h
  · rw [pieceProj_ofPiece]
  · rw [pieceProj_ofPiece_of_ne (Ne.symm h), map_zero, raiseVstar_ofPiece_of_ne (Ne.symm h)]

/-- `𝟏_kd₋ = d₋`: the lowering arrow lands at the vertex `k`. -/
theorem pieceProj_mul_lowerVstar (k : ℕ) :
    pieceProj L k * lowerVstar D k = lowerVstar D k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne l (k + 1) with rfl | h
  · rw [lowerVstar_ofPiece, pieceProj_ofPiece]
  · rw [lowerVstar_ofPiece_of_ne h, map_zero]

/-- `d₋𝟏_{k+1} = d₋`: the lowering arrow starts at the vertex `k + 1`. -/
theorem lowerVstar_mul_pieceProj (k : ℕ) :
    lowerVstar D k * pieceProj L (k + 1) = lowerVstar D k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne l (k + 1) with rfl | h
  · rw [pieceProj_ofPiece]
  · rw [pieceProj_ofPiece_of_ne h, map_zero, lowerVstar_ofPiece_of_ne h]

/-- `𝟏_kT = T`: a loop at the vertex `k` lands there. -/
theorem pieceProj_mul_loopVstar (k i : ℕ) :
    pieceProj L k * loopVstar T k i = loopVstar T k i := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | h
  · rw [loopVstar_ofPiece, pieceProj_ofPiece]
  · rw [loopVstar_ofPiece_of_ne i (Ne.symm h), map_zero]

/-- `T𝟏_k = T`: a loop at the vertex `k` starts there. -/
theorem loopVstar_mul_pieceProj (k i : ℕ) :
    loopVstar T k i * pieceProj L k = loopVstar T k i := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | h
  · rw [pieceProj_ofPiece]
  · rw [pieceProj_ofPiece_of_ne (Ne.symm h), map_zero, loopVstar_ofPiece_of_ne i (Ne.symm h)]

/-! ### Carlsson and Mellit's nine relations, abstractly -/

/-- **Carlsson and Mellit's nine relations for a triple of operator families**, together with the
vanishing of the loops the quiver does not have. This is what `HJO.Dyck.Aq` asks of the operators,
stated for maps between the graded pieces `HJO.Sweep.pieceSub` so that the two relations reading a
membership get it from the element they are applied to.

The commutator `d₊d₋ - d₋d₊` at the vertex `k + 1` is written out in the last two fields, as
`HJO.Dyck.Aq` writes it. -/
structure IsDpaOperators (q : L) (T : ∀ k : ℕ, ℕ → (pieceSub L k →ₗ[L] pieceSub L k))
    (D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k)
    (U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)) : Prop where
  /-- The quiver has the loops `T_1, …, T_{k-1}` at the vertex `k` and no others. -/
  loop_eq_zero : ∀ {k i : ℕ}, k ≤ i + 1 → T k i = 0
  /-- The Hecke relation `(T_{i+1} - 1)(T_{i+1} + q) = 0`, expanded. -/
  quadratic : ∀ {k i : ℕ}, i + 2 ≤ k → ∀ F : pieceSub L k,
    T k i (T k i F) = (1 - q) • T k i F + q • F
  /-- The braid relation `T_{i+1}T_{i+2}T_{i+1} = T_{i+2}T_{i+1}T_{i+2}`. -/
  braid : ∀ {k i : ℕ}, i + 3 ≤ k → ∀ F : pieceSub L k,
    T k i (T k (i + 1) (T k i F)) = T k (i + 1) (T k i (T k (i + 1) F))
  /-- Two distant loops commute. -/
  comm : ∀ {k i j : ℕ}, i + 2 ≤ k → j + 2 ≤ k → i + 1 < j → ∀ F : pieceSub L k,
    T k i (T k j F) = T k j (T k i F)
  /-- `T_{i+1}d₋ = d₋T_{i+1}`. -/
  loop_lower : ∀ {m i : ℕ}, i + 2 ≤ m → ∀ F : pieceSub L (m + 1),
    T m i (D m F) = D m (T (m + 1) i F)
  /-- `d₋²T_{m+1} = d₋²`. -/
  lower_sq : ∀ (m : ℕ) (F : pieceSub L (m + 2)),
    D m (D (m + 1) (T (m + 2) m F)) = D m (D (m + 1) F)
  /-- `d₊T_{i+1} = T_{i+2}d₊`. -/
  raise_loop : ∀ {k i : ℕ}, i + 2 ≤ k → ∀ F : pieceSub L k,
    U k (T k i F) = T (k + 1) (i + 1) (U k F)
  /-- `T_1d₊² = d₊²`. -/
  raise_sq : ∀ (k : ℕ) (F : pieceSub L k),
    T (k + 2) 0 (U (k + 1) (U k F)) = U (k + 1) (U k F)
  /-- `d₋(d₊d₋ - d₋d₊)T_{j+1} = q(d₊d₋ - d₋d₊)d₋`. -/
  extra_lower : ∀ (j : ℕ) (F : pieceSub L (j + 2)),
    D (j + 1) (U (j + 1) (D (j + 1) (T (j + 2) j F))
        - D (j + 2) (U (j + 2) (T (j + 2) j F)))
      = q • (U j (D j (D (j + 1) F)) - D (j + 1) (U (j + 1) (D (j + 1) F)))
  /-- `T_1(d₊d₋ - d₋d₊)d₊ = qd₊(d₊d₋ - d₋d₊)`. -/
  extra_raise : ∀ (m : ℕ) (F : pieceSub L (m + 1)),
    T (m + 2) 0 (U (m + 1) (D (m + 1) (U (m + 1) F))
        - D (m + 2) (U (m + 2) (U (m + 1) F)))
      = q • U (m + 1) (U m (D m F) - D (m + 1) (U (m + 1) F))

variable {q : L}

/-! ### Carlsson and Mellit's nine relations, on `V_*` -/

theorem IsDpaOperators.loopVstar_eq_zero (h : IsDpaOperators q T D U) {k i : ℕ}
    (hki : k ≤ i + 1) : loopVstar T k i = 0 := by
  rw [loopVstar, h.loop_eq_zero hki, LinearMap.zero_comp, LinearMap.comp_zero]

theorem IsDpaOperators.loopVstar_quadratic (h : IsDpaOperators q T D U) {k i : ℕ}
    (hik : i + 2 ≤ k) :
    (loopVstar T k i - pieceProj L k) * (loopVstar T k i + q • pieceProj L k) = 0 := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply]
  rcases eq_or_ne k l with rfl | hl
  · have hinner : (loopVstar T k i + q • pieceProj L k) (ofPiece L k F)
        = ofPiece L k (T k i F + q • F) := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, loopVstar_ofPiece, pieceProj_ofPiece,
        map_add, map_smul]
    have key : T k i (T k i F + q • F) - (T k i F + q • F) = 0 := by
      rw [map_add, map_smul, h.quadratic hik, sub_smul, one_smul]
      abel
    rw [hinner, LinearMap.sub_apply, loopVstar_ofPiece, pieceProj_ofPiece, ← map_sub, key,
      map_zero]
  · rw [LinearMap.add_apply, LinearMap.smul_apply, loopVstar_ofPiece_of_ne i (Ne.symm hl),
      pieceProj_ofPiece_of_ne (Ne.symm hl), smul_zero, add_zero, map_zero]

theorem IsDpaOperators.loopVstar_braid (h : IsDpaOperators q T D U) {k i : ℕ} (hik : i + 3 ≤ k) :
    loopVstar T k i * loopVstar T k (i + 1) * loopVstar T k i
      = loopVstar T k (i + 1) * loopVstar T k i * loopVstar T k (i + 1) := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · simp only [loopVstar_ofPiece]
    exact congrArg (ofPiece L k) (h.braid hik F)
  · simp only [loopVstar_ofPiece_of_ne _ (Ne.symm hl), map_zero]

theorem IsDpaOperators.loopVstar_comm (h : IsDpaOperators q T D U) {k i j : ℕ} (hi : i + 2 ≤ k)
    (hj : j + 2 ≤ k) (hij : i + 1 < j) :
    loopVstar T k i * loopVstar T k j = loopVstar T k j * loopVstar T k i := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · simp only [loopVstar_ofPiece]
    exact congrArg (ofPiece L k) (h.comm hi hj hij F)
  · simp only [loopVstar_ofPiece_of_ne _ (Ne.symm hl), map_zero]

theorem IsDpaOperators.loopVstar_mul_lowerVstar (h : IsDpaOperators q T D U) {m i : ℕ}
    (him : i + 2 ≤ m) :
    loopVstar T m i * lowerVstar D m = lowerVstar D m * loopVstar T (m + 1) i := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne l (m + 1) with rfl | hl
  · rw [lowerVstar_ofPiece, loopVstar_ofPiece, loopVstar_ofPiece, lowerVstar_ofPiece]
    exact congrArg (ofPiece L m) (h.loop_lower him F)
  · rw [lowerVstar_ofPiece_of_ne hl, loopVstar_ofPiece_of_ne i hl, map_zero, map_zero]

theorem IsDpaOperators.lowerVstar_lowerVstar_mul_loopVstar (h : IsDpaOperators q T D U) (m : ℕ) :
    lowerVstar D m * lowerVstar D (m + 1) * loopVstar T (m + 2) m
      = lowerVstar D m * lowerVstar D (m + 1) := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne l (m + 2) with rfl | hl
  · have hd : ∀ G : pieceSub L (m + 2), lowerVstar D (m + 1) (ofPiece L (m + 2) G)
        = ofPiece L (m + 1) (D (m + 1) G) := fun G => lowerVstar_ofPiece (m + 1) G
    rw [loopVstar_ofPiece, hd, hd, lowerVstar_ofPiece, lowerVstar_ofPiece]
    exact congrArg (ofPiece L m) (h.lower_sq m F)
  · simp [hl]

theorem IsDpaOperators.raiseVstar_mul_loopVstar (h : IsDpaOperators q T D U) {k i : ℕ}
    (hik : i + 2 ≤ k) :
    raiseVstar U k * loopVstar T k i = loopVstar T (k + 1) (i + 1) * raiseVstar U k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · rw [loopVstar_ofPiece, raiseVstar_ofPiece, raiseVstar_ofPiece, loopVstar_ofPiece]
    exact congrArg (ofPiece L (k + 1)) (h.raise_loop hik F)
  · rw [loopVstar_ofPiece_of_ne i (Ne.symm hl), raiseVstar_ofPiece_of_ne (Ne.symm hl), map_zero,
      map_zero]

theorem IsDpaOperators.loopVstar_mul_raiseVstar_raiseVstar (h : IsDpaOperators q T D U) (k : ℕ) :
    loopVstar T (k + 2) 0 * (raiseVstar U (k + 1) * raiseVstar U k)
      = raiseVstar U (k + 1) * raiseVstar U k := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply]
  rcases eq_or_ne k l with rfl | hl
  · have hu : ∀ G : pieceSub L (k + 1), raiseVstar U (k + 1) (ofPiece L (k + 1) G)
        = ofPiece L (k + 2) (U (k + 1) G) := fun G => raiseVstar_ofPiece (k + 1) G
    rw [raiseVstar_ofPiece, hu, loopVstar_ofPiece]
    exact congrArg (ofPiece L (k + 2)) (h.raise_sq k F)
  · simp [Ne.symm hl]

theorem IsDpaOperators.lowerVstar_mul_deltaVstar_mul_loopVstar (h : IsDpaOperators q T D U)
    (j : ℕ) :
    lowerVstar D (j + 1) * deltaVstar D U (j + 1) * loopVstar T (j + 2) j
      = q • (deltaVstar D U j * lowerVstar D (j + 1)) := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rcases eq_or_ne l (j + 2) with rfl | hl
  · have hdel2 : ∀ G : pieceSub L (j + 2), deltaVstar D U (j + 1) (ofPiece L (j + 2) G)
        = ofPiece L (j + 2) (U (j + 1) (D (j + 1) G) - D (j + 2) (U (j + 2) G)) :=
      fun G => deltaVstar_ofPiece (j + 1) G
    have hd : ∀ G : pieceSub L (j + 2), lowerVstar D (j + 1) (ofPiece L (j + 2) G)
        = ofPiece L (j + 1) (D (j + 1) G) := fun G => lowerVstar_ofPiece (j + 1) G
    have hdel1 : ∀ G : pieceSub L (j + 1), deltaVstar D U j (ofPiece L (j + 1) G)
        = ofPiece L (j + 1) (U j (D j G) - D (j + 1) (U (j + 1) G)) :=
      fun G => deltaVstar_ofPiece j G
    rw [loopVstar_ofPiece, hdel2, hd, hd, hdel1, ← map_smul]
    exact congrArg (ofPiece L (j + 1)) (h.extra_lower j F)
  · simp [hl]

theorem IsDpaOperators.loopVstar_mul_deltaVstar_mul_raiseVstar (h : IsDpaOperators q T D U)
    (m : ℕ) :
    loopVstar T (m + 2) 0 * deltaVstar D U (m + 1) * raiseVstar U (m + 1)
      = q • (raiseVstar U (m + 1) * deltaVstar D U m) := by
  refine vstar_ext fun l F => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rcases eq_or_ne l (m + 1) with rfl | hl
  · have hu : ∀ G : pieceSub L (m + 1), raiseVstar U (m + 1) (ofPiece L (m + 1) G)
        = ofPiece L (m + 2) (U (m + 1) G) := fun G => raiseVstar_ofPiece (m + 1) G
    have hdel2 : ∀ G : pieceSub L (m + 2), deltaVstar D U (m + 1) (ofPiece L (m + 2) G)
        = ofPiece L (m + 2) (U (m + 1) (D (m + 1) G) - D (m + 2) (U (m + 2) G)) :=
      fun G => deltaVstar_ofPiece (m + 1) G
    have hdel1 : ∀ G : pieceSub L (m + 1), deltaVstar D U m (ofPiece L (m + 1) G)
        = ofPiece L (m + 1) (U m (D m G) - D (m + 1) (U (m + 1) G)) :=
      fun G => deltaVstar_ofPiece m G
    rw [hu, hdel2, loopVstar_ofPiece, hdel1, hu, ← map_smul]
    exact congrArg (ofPiece L (m + 2)) (h.extra_raise m F)
  · simp [hl]

/-! ### The action -/

/-- The assignment of the generators of `HJO.Dyck.Aq` to the operators on `V_*`: the idempotent at
the vertex `k` to the projection onto `V_k`, the two arrows and the loops to the given families. -/
noncomputable def genOp (T : ∀ k : ℕ, ℕ → (pieceSub L k →ₗ[L] pieceSub L k))
    (D : ∀ k : ℕ, pieceSub L (k + 1) →ₗ[L] pieceSub L k)
    (U : ∀ k : ℕ, pieceSub L k →ₗ[L] pieceSub L (k + 1)) :
    Dyck.Gen → Module.End L (Vstar L)
  | Dyck.Gen.vertex k => pieceProj L k
  | Dyck.Gen.up k => raiseVstar U k
  | Dyck.Gen.down k => lowerVstar D k
  | Dyck.Gen.braid k i => loopVstar T k i

/-- **The eighteen relations of `HJO.Dyck.Aq` hold for the assignment**: the nine of the
path-algebra structure and Carlsson and Mellit's nine. -/
theorem IsDpaOperators.lift_genOp_rel (h : IsDpaOperators q T D U)
    {x y : FreeAlgebra L Dyck.Gen} (hxy : Dyck.Rel L q x y) :
    FreeAlgebra.lift L (genOp T D U) x = FreeAlgebra.lift L (genOp T D U) y := by
  have hE : ∀ k : ℕ, FreeAlgebra.lift L (genOp T D U) (Dyck.freeE L k) = pieceProj L k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hU : ∀ k : ℕ, FreeAlgebra.lift L (genOp T D U) (Dyck.freeUp L k) = raiseVstar U k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hD : ∀ k : ℕ, FreeAlgebra.lift L (genOp T D U) (Dyck.freeDown L k) = lowerVstar D k :=
    fun _ => FreeAlgebra.lift_ι_apply _ _
  have hT : ∀ k i : ℕ, FreeAlgebra.lift L (genOp T D U) (Dyck.freeT L k i) = loopVstar T k i :=
    fun _ _ => FreeAlgebra.lift_ι_apply _ _
  have hDel : ∀ k : ℕ,
      FreeAlgebra.lift L (genOp T D U) (Dyck.freeDelta L k) = deltaVstar D U k := by
    intro k
    rw [Dyck.freeDelta, map_sub, map_mul, map_mul, hU, hD, hD, hU, deltaVstar]
  cases hxy with
  | vertex_mul_self k =>
      simp only [map_mul, hE]
      exact pieceProj_mul_pieceProj k
  | vertex_mul_vertex hkl =>
      simp only [map_mul, map_zero, hE]
      exact pieceProj_mul_pieceProj_of_ne (Ne.symm hkl)
  | vertex_mul_up k =>
      simp only [map_mul, hE, hU]
      exact pieceProj_mul_raiseVstar k
  | up_mul_vertex k =>
      simp only [map_mul, hE, hU]
      exact raiseVstar_mul_pieceProj k
  | vertex_mul_down k =>
      simp only [map_mul, hE, hD]
      exact pieceProj_mul_lowerVstar k
  | down_mul_vertex k =>
      simp only [map_mul, hE, hD]
      exact lowerVstar_mul_pieceProj k
  | vertex_mul_braid k i =>
      simp only [map_mul, hE, hT]
      exact pieceProj_mul_loopVstar k i
  | braid_mul_vertex k i =>
      simp only [map_mul, hE, hT]
      exact loopVstar_mul_pieceProj k i
  | braid_eq_zero hki =>
      simp only [map_zero, hT]
      exact h.loopVstar_eq_zero hki
  | quadratic hik =>
      simp only [map_mul, map_sub, map_add, map_smul, map_zero, hE, hT]
      exact h.loopVstar_quadratic hik
  | braid_braid hik =>
      simp only [map_mul, hT]
      exact h.loopVstar_braid hik
  | braid_comm hi hj hij =>
      simp only [map_mul, hT]
      exact h.loopVstar_comm hi hj hij
  | braid_down him =>
      simp only [map_mul, hD, hT]
      exact h.loopVstar_mul_lowerVstar him
  | up_braid hik =>
      simp only [map_mul, hU, hT]
      exact h.raiseVstar_mul_loopVstar hik
  | braid_up_up k =>
      simp only [map_mul, hU, hT]
      exact h.loopVstar_mul_raiseVstar_raiseVstar k
  | down_down_braid m =>
      simp only [map_mul, hD, hT]
      exact h.lowerVstar_lowerVstar_mul_loopVstar m
  | down_delta =>
      simp only [map_mul, map_smul, hD, hT, hDel]
      exact h.lowerVstar_mul_deltaVstar_mul_loopVstar _
  | braid_delta =>
      simp only [map_mul, map_smul, hU, hT, hDel]
      exact h.loopVstar_mul_deltaVstar_mul_raiseVstar _

/-- **The action a triple of operator families generates**: the descent to `𝔸_q` of the assignment
of the generators. -/
noncomputable def IsDpaOperators.actionOf (h : IsDpaOperators q T D U) :
    Dyck.Aq L q →ₐ[L] Module.End L (Vstar L) :=
  RingQuot.liftAlgHom L ⟨FreeAlgebra.lift L (genOp T D U), fun _ _ hr => h.lift_genOp_rel hr⟩

@[simp]
theorem IsDpaOperators.actionOf_mk (h : IsDpaOperators q T D U) (x : FreeAlgebra L Dyck.Gen) :
    h.actionOf (Dyck.Aq.mk L q x) = FreeAlgebra.lift L (genOp T D U) x :=
  RingQuot.liftAlgHom_mkAlgHom_apply L (FreeAlgebra.lift L (genOp T D U))
    (s := Dyck.Rel L q) (fun _ _ hr => h.lift_genOp_rel hr) x

/-- `ρ(𝟏_k)` is the projection of `V_*` onto `V_k`. -/
theorem IsDpaOperators.actionOf_e (h : IsDpaOperators q T D U) (k : ℕ) :
    h.actionOf (Dyck.Aq.e L q k) = pieceProj L k := by
  rw [Dyck.Aq.e, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

/-- The loop `Tg k i` acts by the given family. -/
theorem IsDpaOperators.actionOf_Tg (h : IsDpaOperators q T D U) (k i : ℕ) :
    h.actionOf (Dyck.Aq.Tg L q k i) = loopVstar T k i := by
  rw [Dyck.Aq.Tg, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

/-- The lowering arrow acts by the given family. -/
theorem IsDpaOperators.actionOf_dMinus (h : IsDpaOperators q T D U) (k : ℕ) :
    h.actionOf (Dyck.Aq.dMinus L q k) = lowerVstar D k := by
  rw [Dyck.Aq.dMinus, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

/-- The raising arrow acts by the given family. -/
theorem IsDpaOperators.actionOf_dPlus (h : IsDpaOperators q T D U) (k : ℕ) :
    h.actionOf (Dyck.Aq.dPlus L q k) = raiseVstar U k := by
  rw [Dyck.Aq.dPlus, h.actionOf_mk]
  exact FreeAlgebra.lift_ι_apply _ _

/-- The descent is an action in the sense of `HJO.Sweep.IsDpaAction`. -/
theorem IsDpaOperators.isDpaAction (h : IsDpaOperators q T D U) :
    IsDpaAction q h.actionOf :=
  ⟨h.actionOf_e⟩

/-- **Nine relations give an action**: the construction both `HJO.Sweep.exists_isDpaAction_cm` and
`HJO.Sweep.exists_isDpaAction_mod` are instances of. -/
theorem IsDpaOperators.exists_isDpaAction (h : IsDpaOperators q T D U) :
    ∃ ρ : Dyck.Aq L q →ₐ[L] Module.End L (Vstar L), IsDpaAction q ρ
      ∧ (∀ k i : ℕ, ρ (Dyck.Aq.Tg L q k i) = loopVstar T k i)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dMinus L q k) = lowerVstar D k)
      ∧ (∀ k : ℕ, ρ (Dyck.Aq.dPlus L q k) = raiseVstar U k) :=
  ⟨h.actionOf, h.isDpaAction, h.actionOf_Tg, h.actionOf_dMinus, h.actionOf_dPlus⟩

end Build

/-! ### The loop family, shared by both instances -/

section Braid

variable {L : Type*} [Field L]

/-- **`T_{i+1}` as an endomorphism of the graded piece `V_k`**, and `0` when the quiver has no such
loop, that is when `k ≤ i + 1`. The index shift is `HJO.Dyck.Aq`'s: its generator `Tg k i` is the
Carlsson and Mellit's `T_{i+1}`. -/
noncomputable def braidModPiece (q : L) (k i : ℕ) : pieceSub L k →ₗ[L] pieceSub L k :=
  if h : i + 2 ≤ k then
    ((braid q (i + 1)).restrictScalars L).restrict
      fun _ hx => braid_mem_piece q (by omega) (by omega) hx
  else 0

theorem coe_braidModPiece (q : L) {k i : ℕ} (h : i + 2 ≤ k) (F : pieceSub L k) :
    (braidModPiece q k i F : Total L) = braid q (i + 1) F := by
  rw [braidModPiece]
  simp only [h, ↓reduceDIte]
  rfl

theorem braidModPiece_of_le (q : L) {k i : ℕ} (h : k ≤ i + 1) : braidModPiece q k i = 0 := by
  rw [braidModPiece]
  simp only [show ¬(i + 2 ≤ k) from by omega, ↓reduceDIte]

/-- **The Hecke relation on the summand**, `HJO.Sweep.braid_braid_apply` read there:
`T_{i+1}² = (1-q)T_{i+1} + q`. -/
theorem braidModPiece_quadratic (q : L) {k i : ℕ} (h : i + 2 ≤ k) (F : pieceSub L k) :
    braidModPiece q k i (braidModPiece q k i F)
      = (1 - q) • braidModPiece q k i F + q • F := by
  refine Subtype.ext ?_
  simp only [AddMemClass.coe_add, SetLike.val_smul, coe_braidModPiece q h, smul_eq_scal_mul]
  exact braid_braid_apply q (i + 1) _

/-- **The braid relation on the summand**, `HJO.Sweep.braid_braid` read there. -/
theorem braidModPiece_braid (q : L) {k i : ℕ} (h : i + 3 ≤ k) (F : pieceSub L k) :
    braidModPiece q k i (braidModPiece q k (i + 1) (braidModPiece q k i F))
      = braidModPiece q k (i + 1) (braidModPiece q k i (braidModPiece q k (i + 1) F)) := by
  refine Subtype.ext ?_
  simp only [coe_braidModPiece q (show i + 2 ≤ k from by omega),
    coe_braidModPiece q (show i + 1 + 2 ≤ k from by omega)]
  exact braid_braid q (by omega) _

/-- **Two distant loops commute on the summand**, `HJO.Sweep.braid_comm` read there. -/
theorem braidModPiece_comm (q : L) {k i j : ℕ} (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
    (hij : i + 1 < j) (F : pieceSub L k) :
    braidModPiece q k i (braidModPiece q k j F) = braidModPiece q k j (braidModPiece q k i F) := by
  refine Subtype.ext ?_
  simp only [coe_braidModPiece q hi, coe_braidModPiece q hj]
  exact braid_comm q (by omega) (by omega) _

end Braid

end HJO.Sweep

end
