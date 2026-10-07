/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.CornerCommute
public import HJO.CarlssonMellit.CornerPowers
public import HJO.CarlssonMellit.CornerTCommute
public meta import HJO.Attr

/-! # The straightening rule in the corner of the Dyck path algebra

A loop `T_i` standing to the left of a monomial in the corner elements can be pushed to the right
at the cost of lower terms: `T_iy_1^{a_1}⋯y_k^{a_k}` is a `K`-linear combination of the elements
`y_1^{b_1}⋯y_k^{b_k}T_i` and `y_1^{b_1}⋯y_k^{b_k}` with `b` of the same total degree as `a`. This
is what makes the corner monomials with a trailing `T` a spanning set, and it is the last purely
algebraic input the structure theorem of the corner needs.

## Main results

* `HJO.Dyck.Aq.Tg_mul_yMon_mem_span`: the straightening rule.

## Implementation notes

**The monomial is an ordered list product, not a `Finset.prod`.** `𝔸_q` is noncommutative, so
`Finset.prod` is not even available on it; `yProd` multiplies the powers along an explicit list of
vertex indices and `yMon` takes that list to be `List.range' 1 k = [1, …, k]`, which is the usual
order `y_1^{b_1}⋯y_k^{b_k}`. Two structural facts about that product are proved once each and
used throughout: a corner element commutes with the whole product (`commute_yElt_yProd`, from
`HJO.Dyck.Aq.yElt_comm`), and raising one exponent by one peels a factor off the front
(`yProd_of_succ`, which is where the `Nodup` of the index list is used).

**The exponents are functions `ℕ → ℕ` and the degree is summed over `Finset.Icc 1 k`.** Values of
`b` outside `[1, k]` are read by neither `yMon` nor `yMonDeg`, so allowing them narrows nothing:
the spanning set is the usual one. Carrying a `Fin k → ℕ` instead would put a cast in every
statement of the induction, whose two steps change the exponent at the indices `i` and `i + 1`.

**The side conditions are `1 ≤ i` and `i < k`, with no subtraction.** The statement is usually
written with `k ≥ 2` and `1 ≤ i ≤ k-1`; `1 ≤ i < k` is equivalent and implies `2 ≤ k`, and it keeps
truncated subtraction out of the statement. The one subtraction that remains is the library-wide
index shift in `HJO.Dyck.Aq.Tg`, where the usual `T_i` at the vertex `k` is `Tg K q k (i - 1)`.

**The induction is single, on `a_i + a_{i+1}`.** The usual proof extracts the factors away
from `i` and `i+1` into an element `z` commuting with `T_i` and then runs a double induction on the
two remaining exponents. Extracting `z` is exactly the work that a noncommutative ordered product
makes expensive, and it is unnecessary: both of the induction steps lower
`a_i + a_{i+1}` by one, and its base case is `a_i = a_{i+1} = 0`, where the whole monomial commutes
with `T_i` because the two factors that would not are `y^0 = 1`. So one induction on the sum does
the work of the extraction and of both inductions.

## References

This file proves `HJO.Dyck.Aq.Tg_mul_yMon_mem_span`, a straightening rule in the Dyck path algebra.
-/

@[expose] public section

namespace HJO.Dyck.Aq

variable {K : Type*} [CommRing K] {q : K} [Invertible q] [Invertible (q - 1)]

/-! ### Ordered monomials in the corner elements -/

/-- The ordered product `∏_{s ∈ l} y_s^{b_s}` of powers of corner elements along a list of vertex
indices. The list records the order, which matters in `𝔸_q` before the commutation lemmas are
applied. -/
noncomputable def yProd (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) (b : ℕ → ℕ) (l : List ℕ) : Aq K q :=
  (l.map fun s => yElt K q k s ^ b s).prod

@[simp]
theorem yProd_nil (k : ℕ) (b : ℕ → ℕ) : yProd K q k b [] = 1 := rfl

@[simp]
theorem yProd_cons (k : ℕ) (b : ℕ → ℕ) (s : ℕ) (l : List ℕ) :
    yProd K q k b (s :: l) = yElt K q k s ^ b s * yProd K q k b l := rfl

/-- **The corner monomial** `y_1^{b_1} ⋯ y_k^{b_k}`, in the usual order. -/
noncomputable def yMon (K : Type*) [CommRing K] (q : K) [Invertible q] [Invertible (q - 1)]
    (k : ℕ) (b : ℕ → ℕ) : Aq K q :=
  yProd K q k b (List.range' 1 k)

/-- The total degree `b_1 + ⋯ + b_k` of a corner monomial. -/
def yMonDeg (k : ℕ) (b : ℕ → ℕ) : ℕ := ∑ s ∈ Finset.Icc 1 k, b s

/-- Every index the monomial reads lies in `[1, k]`. -/
theorem mem_range'_one_bounds {k s : ℕ} (hs : s ∈ List.range' 1 k) : 1 ≤ s ∧ s ≤ k := by
  rw [List.mem_range'_1] at hs
  omega

/-- A corner element commutes with every ordered product of powers of corner elements. -/
theorem commute_yElt_yProd {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) (b : ℕ → ℕ) (l : List ℕ)
    (hl : ∀ s ∈ l, 1 ≤ s ∧ s ≤ k) : Commute (yElt K q k r) (yProd K q k b l) := by
  refine Commute.list_prod_right _ _ ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨hs1, hsk⟩ := hl s hs
  exact Commute.pow_right (yElt_comm hr1 hrk hs1 hsk) (b s)

/-- **The loop `T_i` commutes with a monomial in which `y_i` and `y_{i+1}` do not occur.** Those are
the only two corner elements `T_i` fails to commute with, and at exponent `0` they contribute the
factor `1`. -/
theorem commute_Tg_yProd {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) {b : ℕ → ℕ}
    (hbi : b i = 0) (hbi1 : b (i + 1) = 0) (l : List ℕ) (hl : ∀ s ∈ l, 1 ≤ s ∧ s ≤ k) :
    Commute (Tg K q k (i - 1)) (yProd K q k b l) := by
  refine Commute.list_prod_right _ _ ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨hs1, hsk⟩ := hl s hs
  by_cases hsi : s = i
  · rw [hsi, hbi, pow_zero]
    exact Commute.one_right _
  · by_cases hsi1 : s = i + 1
    · rw [hsi1, hbi1, pow_zero]
      exact Commute.one_right _
    · have hc : Commute (yElt K q k s) (Tg K q k (i - 1)) :=
        yElt_mul_Tg_comm hs1 hsk (by omega) (by omega)
      exact Commute.pow_right hc.symm (b s)

/-- **Peeling a factor off the front.** If `b'` agrees with `b` away from `r` and has one more `r`,
then `y_r` comes off the front of the `b'`-monomial. The list must have no repeated index, which is
what carries the fact that the factor being peeled is the only occurrence of `y_r`. -/
theorem yProd_of_succ {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) (b b' : ℕ → ℕ)
    (hb : b' r = b r + 1) (hbs : ∀ s, s ≠ r → b' s = b s) :
    ∀ l : List ℕ, l.Nodup → (∀ s ∈ l, 1 ≤ s ∧ s ≤ k) → r ∈ l →
      yProd K q k b' l = yElt K q k r * yProd K q k b l := by
  intro l
  induction l with
  | nil => intro _ _ hrl; simp at hrl
  | cons s t ih =>
    intro hnd hl hrl
    rw [List.nodup_cons] at hnd
    by_cases hsr : s = r
    · subst hsr
      have hrest : yProd K q k b' t = yProd K q k b t := by
        rw [yProd, yProd]
        refine congrArg List.prod (List.map_congr_left ?_)
        intro x hx
        rw [hbs x fun h => hnd.1 (h ▸ hx)]
      rw [yProd_cons, yProd_cons, hrest, hb, pow_succ',
        mul_assoc (yElt K q k s) (yElt K q k s ^ b s) (yProd K q k b t)]
    · have hrt : r ∈ t := by
        rcases List.mem_cons.1 hrl with h | h
        · exact absurd h.symm hsr
        · exact h
      obtain ⟨hs1, hsk⟩ := hl s List.mem_cons_self
      have hcomm : Commute (yElt K q k r) (yElt K q k s ^ b s) :=
        Commute.pow_right (yElt_comm hr1 hrk hs1 hsk) (b s)
      rw [yProd_cons, yProd_cons,
        ih hnd.2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hrt, hbs s hsr,
        ← mul_assoc (yElt K q k s ^ b s) (yElt K q k r) (yProd K q k b t), ← hcomm.eq,
        mul_assoc (yElt K q k r) (yElt K q k s ^ b s) (yProd K q k b t)]

/-- Peeling a factor off the front of a corner monomial. -/
theorem yMon_of_succ {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) {b b' : ℕ → ℕ}
    (hb : b' r = b r + 1) (hbs : ∀ s, s ≠ r → b' s = b s) :
    yMon K q k b' = yElt K q k r * yMon K q k b :=
  yProd_of_succ hr1 hrk b b' hb hbs _ List.nodup_range'
    (fun _ hs => mem_range'_one_bounds hs) (List.mem_range'_1.2 ⟨hr1, by omega⟩)

/-- Raising one exponent by one raises the total degree by one. -/
theorem yMonDeg_of_succ {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) {b b' : ℕ → ℕ}
    (hb : b' r = b r + 1) (hbs : ∀ s, s ≠ r → b' s = b s) :
    yMonDeg k b' = yMonDeg k b + 1 := by
  have hr : r ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨hr1, hrk⟩
  have hrest : ∑ s ∈ (Finset.Icc 1 k).erase r, b' s = ∑ s ∈ (Finset.Icc 1 k).erase r, b s :=
    Finset.sum_congr rfl fun s hs => hbs s (Finset.ne_of_mem_erase hs)
  rw [yMonDeg, yMonDeg, ← Finset.add_sum_erase _ b' hr, ← Finset.add_sum_erase _ b hr, hrest, hb]
  omega

/-! ### The spanning set and the straightening rule -/

/-- **The straightened elements of total degree `n`**: the corner monomials `y_1^{b_1}⋯y_k^{b_k}` of
total degree `n`, and those same monomials with the loop `T_i` on the right. -/
noncomputable def straightenSet (K : Type*) [CommRing K] (q : K) [Invertible q]
    [Invertible (q - 1)] (k i n : ℕ) : Set (Aq K q) :=
  {x | ∃ b : ℕ → ℕ, yMonDeg k b = n ∧
    (x = yMon K q k b * Tg K q k (i - 1) ∨ x = yMon K q k b)}

/-- Multiplying on the left by a corner element raises the degree of the spanning set by one. -/
theorem mul_left_mem_span_straightenSet {k i r n : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) {x : Aq K q}
    (hx : x ∈ Submodule.span K (straightenSet K q k i n)) :
    yElt K q k r * x ∈ Submodule.span K (straightenSet K q k i (n + 1)) := by
  have hmap : Submodule.map (LinearMap.mulLeft K (yElt K q k r))
      (Submodule.span K (straightenSet K q k i n))
      ≤ Submodule.span K (straightenSet K q k i (n + 1)) := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro y ⟨z, ⟨b, hbdeg, hz⟩, rfl⟩
    have hupd : Function.update b r (b r + 1) r = b r + 1 := Function.update_self r (b r + 1) b
    have hupds : ∀ s, s ≠ r → Function.update b r (b r + 1) s = b s :=
      fun s hs => Function.update_of_ne hs (b r + 1) b
    have hy : yMon K q k (Function.update b r (b r + 1)) = yElt K q k r * yMon K q k b :=
      yMon_of_succ hr1 hrk hupd hupds
    refine Submodule.subset_span ⟨Function.update b r (b r + 1), ?_, ?_⟩
    · rw [yMonDeg_of_succ hr1 hrk hupd hupds, hbdeg]
    · rcases hz with rfl | rfl
      · exact Or.inl (by
          rw [LinearMap.mulLeft_apply, hy,
            mul_assoc (yElt K q k r) (yMon K q k b) (Tg K q k (i - 1))])
      · exact Or.inr (by rw [LinearMap.mulLeft_apply, hy])
  simpa using hmap (Submodule.mem_map_of_mem hx)

/-- The induction behind the straightening rule, on `a_i + a_{i+1}`. -/
theorem Tg_mul_yMon_mem_span_aux {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) :
    ∀ m : ℕ, ∀ b : ℕ → ℕ, b i + b (i + 1) = m →
      Tg K q k (i - 1) * yMon K q k b
        ∈ Submodule.span K (straightenSet K q k i (yMonDeg k b)) := by
  intro m
  induction m with
  | zero =>
    intro b hm
    have hcomm : Commute (Tg K q k (i - 1)) (yMon K q k b) :=
      commute_Tg_yProd h1 hik (by omega) (by omega) _ fun _ hs => mem_range'_one_bounds hs
    rw [hcomm.eq]
    exact Submodule.subset_span ⟨b, rfl, Or.inl rfl⟩
  | succ m ih =>
    intro b hm
    by_cases hbi : b i = 0
    · -- `y_i` is absent: peel a `y_{i+1}` and use `T_iy_{i+1} = y_iT_i + (q-1)y_i`.
      have hcu : Function.update b (i + 1) m (i + 1) = m := Function.update_self (i + 1) m b
      have hcs : ∀ s, s ≠ i + 1 → Function.update b (i + 1) m s = b s :=
        fun s hs => Function.update_of_ne hs m b
      set c := Function.update b (i + 1) m with hcdef
      have hci : c i = 0 := by rw [hcs i (by omega), hbi]
      have hb1 : b (i + 1) = c (i + 1) + 1 := by omega
      have hbs : ∀ s, s ≠ i + 1 → b s = c s := fun s hs => (hcs s hs).symm
      have hsplit : yMon K q k b = yElt K q k (i + 1) * yMon K q k c :=
        yMon_of_succ (by omega) (by omega) hb1 hbs
      have hdeg : yMonDeg k b = yMonDeg k c + 1 :=
        yMonDeg_of_succ (r := i + 1) (by omega) (by omega) hb1 hbs
      have hih : Tg K q k (i - 1) * yMon K q k c
          ∈ Submodule.span K (straightenSet K q k i (yMonDeg k c)) := ih c (by omega)
      have key : Tg K q k (i - 1) * yMon K q k b
          = yElt K q k i * (Tg K q k (i - 1) * yMon K q k c)
            + (q - 1) • (yElt K q k i * yMon K q k c) := by
        rw [hsplit, ← mul_assoc (Tg K q k (i - 1)) (yElt K q k (i + 1)) (yMon K q k c),
          Tg_mul_yElt_succ h1 hik, add_mul, smul_mul_assoc]
        simp only [mul_assoc]
      rw [hdeg, key]
      refine Submodule.add_mem _ (mul_left_mem_span_straightenSet h1 (by omega) hih)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Function.update c i (c i + 1), ?_, ?_⟩))
      · exact yMonDeg_of_succ (r := i) h1 (by omega) (Function.update_self i (c i + 1) c)
          fun s hs => Function.update_of_ne hs (c i + 1) c
      · exact Or.inr (yMon_of_succ (r := i) h1 (by omega) (Function.update_self i (c i + 1) c)
          fun s hs => Function.update_of_ne hs (c i + 1) c).symm
    · -- `y_i` is present: peel a `y_i` and use `T_iy_i = y_{i+1}T_i + (1-q)y_i`.
      have hcu : Function.update b i (b i - 1) i = b i - 1 :=
        Function.update_self i (b i - 1) b
      have hcs : ∀ s, s ≠ i → Function.update b i (b i - 1) s = b s :=
        fun s hs => Function.update_of_ne hs (b i - 1) b
      set c := Function.update b i (b i - 1) with hcdef
      have hc1 : c (i + 1) = b (i + 1) := hcs _ (by omega)
      have hbc : b i = c i + 1 := by omega
      have hbs : ∀ s, s ≠ i → b s = c s := fun s hs => (hcs s hs).symm
      have hsplit : yMon K q k b = yElt K q k i * yMon K q k c :=
        yMon_of_succ h1 (by omega) hbc hbs
      have hdeg : yMonDeg k b = yMonDeg k c + 1 :=
        yMonDeg_of_succ (r := i) h1 (by omega) hbc hbs
      have hih : Tg K q k (i - 1) * yMon K q k c
          ∈ Submodule.span K (straightenSet K q k i (yMonDeg k c)) := ih c (by omega)
      have key : Tg K q k (i - 1) * yMon K q k b
          = yElt K q k (i + 1) * (Tg K q k (i - 1) * yMon K q k c)
            + (1 - q) • (yElt K q k i * yMon K q k c) := by
        rw [hsplit, ← mul_assoc (Tg K q k (i - 1)) (yElt K q k i) (yMon K q k c),
          Tg_mul_yElt h1 hik, add_mul, smul_mul_assoc]
        simp only [mul_assoc]
      rw [hdeg, key]
      refine Submodule.add_mem _
        (mul_left_mem_span_straightenSet (by omega) (by omega) hih)
        (Submodule.smul_mem _ _ ?_)
      rw [← hsplit]
      exact Submodule.subset_span ⟨b, hdeg, Or.inr rfl⟩

/-- **The straightening rule.** For `1 ≤ i < k` — that is, `k ≥ 2` and `1 ≤ i ≤ k-1` — and any
exponent vector `a`, the element `T_iy_1^{a_1}⋯y_k^{a_k}` of `e_k𝔸_qe_k` is a `K`-linear
combination of the elements `y_1^{b_1}⋯y_k^{b_k}T_i` and `y_1^{b_1}⋯y_k^{b_k}` with
`b_1 + ⋯ + b_k = a_1 + ⋯ + a_k`. -/
@[hjo "lem_cm_hecke_straighten"]
theorem Tg_mul_yMon_mem_span {k i : ℕ} (h1 : 1 ≤ i) (hik : i < k) (a : ℕ → ℕ) :
    Tg K q k (i - 1) * yMon K q k a
      ∈ Submodule.span K (straightenSet K q k i (yMonDeg k a)) :=
  Tg_mul_yMon_mem_span_aux h1 hik (a i + a (i + 1)) a rfl

end HJO.Dyck.Aq
