/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.FlipCorners
public import HJO.CarlssonMellit.MarkedCharSeries
public import HJO.CarlssonMellit.TwoLetterChar
public meta import HJO.Attr

/-! # Corner inclusion--exclusion for the characteristic series

The marked characteristic series `χ(π, T)` of `HJO.Dyck.pathMarkedCharSeries` is an alternating sum
of *unmarked* series over the flips of the marking:

`(1 - q) ^ #T · χ(π, T) = ∑_{S ⊆ T} (-1) ^ #S · χ(π_S)`.

This is the paper's equation (3.7), and it is the identity that turns the marking — a constraint on
the labellings, which no word in the operators `d_±` can express — into a signed combination of
unconstrained series, each of which `HJO.Dyck.realisation_constantCoeff_markedWordOp'` computes. It
is what makes `HJO.Mellit.map_constantCoeff_markedWordOp'` possible.

The whole content is local to a single labelling. By `HJO.Dyck.attackSet_flipCorners` the attack set
of the flip `π_S` is `At(π) ⊔ S`, so a labelling `w` inverts `#(S ∩ D(w))` more cells of `At(π_S)`
than of `At(π)`, where `D(w)` is the set of cells `w` inverts. The sum over `S ⊆ T` then factors
over the corners of `T`, one factor per corner, and the factor at a corner `w` does *not* invert
is `1 - 1 = 0`. So only the labellings marked by `T` survive, each with the scalar `(1 - q) ^ #T`.

## Main results

* `HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion`: the identity.

## Implementation notes

*`χ(π_S)` appears as `HJO.Dyck.pathMarkedCharSeries q (flipCorners x S) ∅` and not under a name of
its own*: `HJO.Dyck.pathCharSeries`, the unmarked series, is defined in
`HJO/CarlssonMellit/CharSeries.lean`, which this file does not import, as the marked series at the
empty marking rather than written out again. So the right-hand side is the unmarked series
`χ(π_S)`.

*Cells are counted in `ℕ × ℕ` and inversions in `Fin n × Fin n`, and the bridge is explicit.* The
attack set and the corner set are `Finset (ℕ × ℕ)`, while `HJO.Dyck.markedCharSeries` forms its
inversion set at pairs of `Fin n`, the labelling being a tuple. The product over the corners of `T`
has to run over cells, so the inversion count is transported to cells by
`HJO.Dyck.card_invSet_finPairs`, whose hypothesis is that the cells lie inside the square — true of
every corner, by `HJO.Dyck.IsSquareDyck.lt_of_mem_corner`.

*The scalar is `(1 - q) ^ #T` and not `(1 - q⁻¹) ^ #T`.* The second is what the other corner
convention produces. With `HJO.Dyck.corner` naming the cell *above* the turning point, flipping
*adjoins* that cell to the attack set, each corner contributes `1 - q`, and the identity is the
paper's.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, equation (3.7) of §3.1, the last
display of that section, formalised as `HJO.Dyck.pathMarkedCharSeries_inclusion_exclusion`, using
`HJO.Dyck.IsSquareDyck`, `HJO.Dyck.corner`, `HJO.Dyck.flipCorners`, `HJO.Dyck.pathCharSeries` and
`HJO.Dyck.pathMarkedCharSeries`, and consuming `HJO.Dyck.IsSquareDyck.flipCorners` and
`HJO.Dyck.attackSet_flipCorners`. Consumed by `HJO.Mellit.map_constantCoeff_markedWordOp'`, and
through it by `HJO.Mellit.constantCoeff_psiWord_one_mem_lambdaComp_and_map_eq_sweepChar`.
-/

@[expose] public section

open Finset HJO.Sym

namespace HJO.Dyck

variable {n : ℕ} {x : Fin n → ℕ}

/-! ### Reading a labelling at a cell of the square -/

/-- A labelling `w` of the `n` positions, read as a function on all of `ℕ`, with the junk value `0`
outside the square. This is what makes a *cell* `(i, j)` — an element of `Finset (ℕ × ℕ)`, as the
attack set and the corner set are — an inversion or not without carrying two bounds:
`HJO.Dyck.invSet (S : Finset (ℕ × ℕ)) (extendLabelling w)` is the set of cells of `S` that `w`
inverts, and no statement below reads the junk, every cell in sight coming from `c(π)`. -/
def extendLabelling {n : ℕ} (w : Fin n → ℕ) : ℕ → ℕ :=
  fun i => if h : i < n then w ⟨i, h⟩ else 0

theorem extendLabelling_apply {w : Fin n → ℕ} {i : ℕ} (h : i < n) :
    extendLabelling w i = w ⟨i, h⟩ := by
  simp only [extendLabelling, h, ↓reduceDIte]

/-- `HJO.Dyck.finPairs` is the filter that `HJO.Dyck.markedCharSeries` forms its inversion set at:
the two are the same term, and this is the rewrite that names it. -/
theorem finPairs_eq_filter (m : ℕ) (R : Finset (ℕ × ℕ)) :
    finPairs m R = ({p : Fin m × Fin m | ((p.1 : ℕ), (p.2 : ℕ)) ∈ R} : Finset (Fin m × Fin m)) :=
  rfl

/-- Reading a union of sets of cells on the positions of `Fin n` is the union of the readings. -/
theorem finPairs_union (m : ℕ) (R R' : Finset (ℕ × ℕ)) :
    finPairs m (R ∪ R') = finPairs m R ∪ finPairs m R' := by
  ext p; simp [Finset.mem_union]

/-- Disjoint sets of cells are read as disjoint sets of pairs of positions. -/
theorem disjoint_finPairs {m : ℕ} {R R' : Finset (ℕ × ℕ)} (h : Disjoint R R') :
    Disjoint (finPairs m R) (finPairs m R') :=
  Finset.disjoint_left.2 fun _ hp hp' =>
    Finset.disjoint_left.1 h (mem_finPairs.1 hp) (mem_finPairs.1 hp')

/-- The inversions of `w` among a set `S` of cells of the square may be counted either as pairs of
positions of `Fin n` or as cells of `ℕ × ℕ`: the coercion `Fin.val` is a bijection between the two
descriptions, `S` lying inside the square. -/
theorem card_invSet_finPairs {S : Finset (ℕ × ℕ)} (hS : ∀ c ∈ S, c.1 < n ∧ c.2 < n)
    (w : Fin n → ℕ) : #(invSet (finPairs n S) w) = #(invSet S (extendLabelling w)) := by
  refine Finset.card_nbij (fun p => ((p.1 : ℕ), (p.2 : ℕ))) (fun p hp => ?_)
    (fun p _ p' _ hpp' => ?_) fun c hc => ?_
  · rw [Finset.mem_coe, mem_invSet, mem_finPairs] at hp
    rw [Finset.mem_coe, mem_invSet]
    exact ⟨hp.1, by rw [extendLabelling_apply p.2.isLt, extendLabelling_apply p.1.isLt]; exact hp.2⟩
  · obtain ⟨e1, e2⟩ := Prod.mk.injEq .. ▸ hpp'
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · rw [Finset.mem_coe, mem_invSet] at hc
    obtain ⟨h1, h2⟩ := hS c hc.1
    refine ⟨(⟨c.1, h1⟩, ⟨c.2, h2⟩), ?_, rfl⟩
    rw [Finset.mem_coe, mem_invSet, mem_finPairs]
    refine ⟨hc.1, ?_⟩
    rw [← extendLabelling_apply (w := w) h1, ← extendLabelling_apply (w := w) h2]
    exact hc.2

/-- Both coordinates of a corner of a square Dyck path of length `n` are positions of the path:
`x_k - 1 < x_k ≤ k < n` for the first and `k < n` for the second. -/
theorem IsSquareDyck.lt_of_mem_corner (h : IsSquareDyck n x) {c : ℕ × ℕ} (hc : c ∈ corner x) :
    c.1 < n ∧ c.2 < n := by
  obtain ⟨k, -, rfl⟩ := mem_corner.1 hc
  have := h.le_index k
  have := k.isLt
  exact ⟨by omega, k.isLt⟩

/-- A labelling is marked by a set `T` of corners exactly when it inverts every cell of `T`, read
through `HJO.Dyck.extendLabelling`: the form in which the marking condition enters the
inclusion--exclusion, where the product runs over the cells of `T` and not over pairs of
positions. -/
theorem isMarkedLabelling_iff_forall (h : IsSquareDyck n x) {T : Finset (ℕ × ℕ)}
    (hT : T ⊆ corner x) (w : Fin n → ℕ) :
    IsMarkedLabelling T w ↔
      ∀ c ∈ T, extendLabelling w c.2 < extendLabelling w c.1 := by
  constructor
  · intro hw c hc
    obtain ⟨h1, h2⟩ := h.lt_of_mem_corner (hT hc)
    rw [extendLabelling_apply h1, extendLabelling_apply h2]
    exact hw (⟨c.1, h1⟩, ⟨c.2, h2⟩) hc
  · intro hw p hp
    have := hw _ hp
    rwa [extendLabelling_apply p.1.isLt, extendLabelling_apply p.2.isLt, Fin.eta, Fin.eta] at this

/-! ### The identity -/

variable {K : Type*} [CommRing K]

/-- **Corner inclusion--exclusion.** For a square Dyck path `π` of length `n` and a set `T ⊆ c(π)`
of its corners,

`(1 - q) ^ #T · χ(π, T) = ∑_{S ⊆ T} (-1) ^ #S · χ(π_S)`,

where `χ(π_S)` is the *unmarked* characteristic series of the flipped path — the marked series of
`HJO.Dyck.pathMarkedCharSeries` at the empty marking, which is what `HJO.Dyck.pathCharSeries` names.

Read one monomial at a time. By `HJO.Dyck.attackSet_flipCorners` and
`HJO.Dyck.disjoint_attackSet_of_subset_corner`, `At(π_S)` is `At(π)` with the cells of `S` adjoined
disjointly, so for a fixed labelling `w` the exponent `inv(At(π_S), w)` is
`inv(At(π), w) + #(S ∩ D(w))`, where `D(w)` is the set of cells `w` inverts. The contribution of `w`
to the right-hand side is therefore `q ^ inv(At(π), w)` times

`∑_{S ⊆ T} ∏_{c ∈ S} (-q ^ [c ∈ D(w)]) = ∏_{c ∈ T} (1 - q ^ [c ∈ D(w)])`,

by `Finset.prod_add`: the product has a factor `1 - q` at each corner `w` inverts and a factor
`1 - 1 = 0` at each corner it does not. So the sum vanishes unless `w` is marked by `T`, and for a
marked `w` it is `(1 - q) ^ #T`, which is the left-hand side coefficient by coefficient. -/
@[hjo "lem_cm_chi_zero_inclusion"]
theorem pathMarkedCharSeries_inclusion_exclusion (q : K) (h : IsSquareDyck n x)
    {T : Finset (ℕ × ℕ)} (hT : T ⊆ corner x) :
    (1 - q) ^ #T • pathMarkedCharSeries q x T =
      ∑ S ∈ T.powerset, (-1 : K) ^ #S • pathMarkedCharSeries q (flipCorners x S) ∅ := by
  classical
  have hkey : ∀ w : Fin n → ℕ,
      (∑ S ∈ T.powerset, (-1 : K) ^ #S *
          q ^ #(invSet (finPairs n (attackSet (flipCorners x S))) w)) =
        if IsMarkedLabelling T w then
          (1 - q) ^ #T * q ^ #(invSet (finPairs n (attackSet x)) w) else 0 := by
    intro w
    have hsplit : ∀ S ∈ T.powerset,
        #(invSet (finPairs n (attackSet (flipCorners x S))) w) =
          #(invSet (finPairs n (attackSet x)) w) + #(invSet S (extendLabelling w)) := by
      intro S hS
      have hSc : S ⊆ corner x := (Finset.mem_powerset.1 hS).trans hT
      rw [attackSet_flipCorners h hSc, finPairs_union, invSet_union,
        Finset.card_union_of_disjoint
          ((disjoint_finPairs (disjoint_attackSet_of_subset_corner hSc)).mono
            (invSet_subset _ _) (invSet_subset _ _)),
        card_invSet_finPairs (fun c hc => h.lt_of_mem_corner (hSc hc)) w]
    have step1 : (∑ S ∈ T.powerset, (-1 : K) ^ #S *
          q ^ #(invSet (finPairs n (attackSet (flipCorners x S))) w)) =
        q ^ #(invSet (finPairs n (attackSet x)) w) * ∑ S ∈ T.powerset,
          ∏ c ∈ S, (-(if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hprod : (∏ c ∈ S, (-(if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)))
          = (-1 : K) ^ #S * q ^ #(invSet S (extendLabelling w)) := by
        rw [show (fun c : ℕ × ℕ =>
              (-(if extendLabelling w c.2 < extendLabelling w c.1 then q else (1 : K))))
            = fun c => (-1 : K) * (if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)
            from funext fun c => by ring,
          Finset.prod_mul_distrib, Finset.prod_const,
          Finset.prod_ite (fun _ => q) (fun _ => (1 : K)), Finset.prod_const,
          Finset.prod_const_one, mul_one, invSet]
      rw [hsplit S hS, pow_add, hprod]
      ring
    have step2 : (∑ S ∈ T.powerset,
          ∏ c ∈ S, (-(if extendLabelling w c.2 < extendLabelling w c.1 then q else (1 : K)))) =
        ∏ c ∈ T, ((1 : K) - (if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)) := by
      rw [show (fun c : ℕ × ℕ =>
            ((1 : K) - (if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)))
          = fun c => (-(if extendLabelling w c.2 < extendLabelling w c.1 then q else (1 : K))) + 1
          from funext fun c => by ring, Finset.prod_add]
      simp
    rw [step1, step2]
    split_ifs with hm
    · have hall := (isMarkedLabelling_iff_forall h hT w).1 hm
      rw [Finset.prod_congr rfl fun c hc => show
          ((1 : K) - (if extendLabelling w c.2 < extendLabelling w c.1 then q else 1)) = 1 - q by
        simp only [hall c hc, ↓reduceIte], Finset.prod_const]
      ring
    · rw [isMarkedLabelling_iff_forall h hT w] at hm
      obtain ⟨c, hc, hcn⟩ : ∃ c ∈ T, ¬(extendLabelling w c.2 < extendLabelling w c.1) := by
        simpa using hm
      rw [Finset.prod_eq_zero hc (by simp only [hcn, ↓reduceIte, sub_self]), mul_zero]
  refine MvPowerSeries.ext fun d => ?_
  rw [map_smul, map_sum]
  simp only [map_smul, smul_eq_mul, coeff_markedCharSeries,
    isMarkedLabelling_empty, and_true, ← finPairs_eq_filter]
  rw [show (∑ S ∈ T.powerset, (-1 : K) ^ #S * ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n =>
        d.support | wordExponent w = d},
          q ^ #(invSet (finPairs n (attackSet (flipCorners x S))) w))
      = ∑ w ∈ {w ∈ Fintype.piFinset fun _ : Fin n => d.support | wordExponent w = d},
        ∑ S ∈ T.powerset, (-1 : K) ^ #S *
          q ^ #(invSet (finPairs n (attackSet (flipCorners x S))) w) from by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.mul_sum _ _ _]
  rw [Finset.sum_congr rfl fun w _ => hkey w, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr (Finset.ext fun w => ?_) fun w _ => rfl
  simp only [Finset.mem_filter]
  tauto

end HJO.Dyck
