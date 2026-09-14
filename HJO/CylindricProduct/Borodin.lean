/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Defs
public import HJO.CylindricProduct.Assembled
public import HJO.CylindricProduct.PrefTrace
public import HJO.CylindricProduct.WindingLimit
public meta import HJO.Attr

/-! # Borodin's product form of the cylindric series

The assembly step is `borodin_form`,

`C_c(q) (q^{d}; q^{d})_∞ = ∏_{m ≥ 1}(1 - q^m)^{-w_{a,b}(m)}`,

and its proof uses three identities: the winding identity
`selfQPochhammerInf_mul_prod_qPochhammerInf_mul_windTrace`, the assembled-exponent identity
`assembled_exponents_rotSlot`, and the prefactor identity `prod_slotPairs_mul_unboundedGF`. It
does not need the invertibility of `(q^{d}; q^{d})_∞` given by `isUnit_selfQPochhammerInf`: the
arrangement below is inverse-free, the cancellation being carried by the exponent product instead.

The implication is isolated as `borodin_form_of_pref_trace`, which takes the prefactor identity in
the inverse-free shape

`(∏_{s' < s} (1 - q^{s-s'})) C_c(q) = Tr S`,

as a hypothesis; `borodin_form` discharges it with `prod_slotPairs_mul_unboundedGF`.

The three moves are:

* the trace of `transferKernel` is a `windTrace`, at the exponent lists `m_s = s + 1` over the
  lowering slots and `p_{s'} = d - 1 - s'` over the raising slots (`ktrace_transferKernel_eq`);
  the raising exponents are positive because slot `d - 1` of the rotated word is lowering, which is
  the whole point of the rotation in `transferKernel`;
* the winding product `∏_{s,s'}(q^{p_{s'} + m_s}; q^{d})_∞` of
  `selfQPochhammerInf_mul_prod_qPochhammerInf_mul_windTrace`, a product over two lists, is the
  product over `slotPairs` that `assembled_exponents_rotSlot` consumes, since
  `p_{s'} + m_s = d + s - s'` (`prod_qPochhammerInf_slots_eq`);
* the crossing prefactor is the second factor of `assembled_exponents_rotSlot`, so the two
  multiply into `∏_{m ≥ 1}(1 - q^m)^{w_{a,b}(m)}`, whose inverse is the right-hand side.
-/

@[expose] public section

open Finset PowerSeries
open scoped QTheory Topology PowerSeries.DiscreteTopology

namespace HJO.CylindricProduct

/-! ### The transfer kernel as a winding trace -/

/-- The exponents of the lowering arguments of `transferKernel`: `y_s = q^{s+1}` at the
lowering slots of the rotated word, in increasing order. -/
noncomputable def lowExps (a b : ℕ) : List ℕ := (loweringSlots a b).map (· + 1)

/-- The exponents of the raising arguments of `transferKernel`: `x_{s'} = q^{d-1-s'}` at the
raising slots of the rotated word, in increasing order. -/
noncomputable def hiExps (a b : ℕ) : List ℕ := (raisingSlots a b).map fun s => a + b - 1 - s

theorem one_le_of_mem_lowExps {a b m : ℕ} (hm : m ∈ lowExps a b) : 1 ≤ m := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hm
  omega

/-- Every raising argument is a positive power of `q`: a raising slot `s'` of the rotated word is
not `d - 1`, by `not_isRaising_rotSlot_last`, so `d - 1 - s' ≥ 1`. -/
theorem one_le_of_mem_hiExps {a b p : ℕ} (hb : 0 < b) (hp : p ∈ hiExps a b) : 1 ≤ p := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  rw [hiExps, raisingSlots] at hp
  have hs' : s ∈ (range (a + b)).filter fun t => IsRaising a b (rotSlot a b t) :=
    (Finset.mem_sort (α := ℕ) (· ≤ ·)).mp hs
  rw [Finset.mem_filter, Finset.mem_range] at hs'
  have hne : s ≠ a + b - 1 := fun h => not_isRaising_rotSlot_last hb (h ▸ hs'.2)
  omega

/-- **The trace of `transferKernel` is the winding trace** at the exponent lists
`lowExps` and `hiExps`: the two products are the same list of kernels. -/
theorem ktrace_transferKernel_eq (a b : ℕ) :
    windTrace (a + b) (lowExps a b) (hiExps a b) = ktrace (transferKernel a b) := by
  rw [windTrace, transferKernel, lowList, raiseList, lowExps, hiExps, List.map_map, List.map_map]
  rfl

/-! ### The winding product over the slots -/

/-- **The winding product is the product over `slotPairs`.** At a lowering slot `s` and a raising
slot `s'` the winding exponent is `p_{s'} + m_s = (d - 1 - s') + (s + 1)`, which is `d + s - s'`,
the exponent `assembled_exponents` runs over. -/
theorem prod_qPochhammerInf_slots_eq (a b : ℕ) :
    ((lowExps a b).map fun m =>
        ((hiExps a b).map fun p => ((X ^ (p + m); X ^ (a + b))_∞ : ℤ⟦X⟧)).prod).prod
      = ∏ p ∈ ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
          ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)),
            ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧) := by
  rw [Finset.prod_product, lowExps, loweringSlots, List.map_map, prod_map_sort]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Function.comp_apply, hiExps, raisingSlots, List.map_map, prod_map_sort]
  refine Finset.prod_congr rfl fun s' hs' => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hs'
  rw [Function.comp_apply, show a + b - 1 - s' + (s + 1) = a + b + s - s' from by omega]

/-! ### The assembly -/

/-- **Borodin's product form of the cylindric series, given the prefactor identity.** This is
`borodin_form` with its one remaining input, the prefactor identity
`prod_slotPairs_mul_unboundedGF`, taken as the hypothesis `hpref`. That hypothesis is

`C_c(q) = (∏_{s lowering, s' raising, s' < s} (1 - q^{s-s'})^{-1}) Tr S`

multiplied through by the prefactor, with the index set in the shape
`crossFrom_zero_eq_prod_slotPairs` produces it and `assembled_exponents` consumes it: the pairs
`(s, s')` of a lowering and a raising slot of the rotated word of `transferKernel`, with `s' < s`.
On the right, `∏_{m ≥ 1}(1 - q^m)^{-w_{a,b}(m)}` is spelled
`∏' m, zpowOneSub m (-w_{a,b}(m+1))`. -/
theorem borodin_form_of_pref_trace {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a) (hab : a < b)
    (hpref : (∏ p ∈ (slotPairs a b ((a + b) - rotOffset a b % (a + b))).filter fun p => p.2 < p.1,
          (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)) * HJO.Cylindric.unboundedGF a b
        = ktrace (transferKernel a b)) :
    HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      = ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) := by
  classical
  have hd : 0 < a + b := by omega
  have hb : 0 < b := by omega
  -- The two index sets agree: `slotPairs` at the rotation shift is the pairs of `rotSlot` slots.
  have hset : slotPairs a b ((a + b) - rotOffset a b % (a + b))
      = ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
        ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)) := by
    simp only [slotPairs, rotSlot_eq_add_mod hd]
  -- The winding identity, at the arguments of `transferKernel`.
  have hwind : ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      * (∏ p ∈ ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
          ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)),
            ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧))
      * ktrace (transferKernel a b) = 1 := by
    rw [← prod_qPochhammerInf_slots_eq a b, ← ktrace_transferKernel_eq a b]
    exact selfQPochhammerInf_mul_prod_qPochhammerInf_mul_windTrace hd
      (fun _ hm => one_le_of_mem_lowExps hm) fun _ hp => one_le_of_mem_hiExps hb hp
  -- The assembled exponents, at the same index set.
  have hass := assembled_exponents_rotSlot hco ha hab
  -- The exponent product and its inverse.
  have hinv : (∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ))
      * ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) = 1 := by
    rw [Limits.tprod_zpowOneSub_mul]
    simp
  -- The prefactor identity, at the same index set.
  have hpref' : (∏ p ∈ (((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
        ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t))).filter fun p => p.2 < p.1,
          (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)) * HJO.Cylindric.unboundedGF a b
      = ktrace (transferKernel a b) := by rw [← hset]; exact hpref
  -- Combining: the winding product times the prefactor is the exponent product, so
  -- `C_c(q) (q^d; q^d)_∞` is its inverse.
  have hkey : HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      * ∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ) = 1 := by
    calc HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
        * ∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ)
        = ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
            * (∏ p ∈ ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
                ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)),
                  ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧))
            * ((∏ p ∈ (((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
                  ((range (a + b)).filter fun t =>
                    IsRaising a b (rotSlot a b t))).filter fun p => p.2 < p.1,
                    (1 - X ^ (p.1 - p.2) : ℤ⟦X⟧)) * HJO.Cylindric.unboundedGF a b) := by
          rw [← hass]; ring
      _ = ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
            * (∏ p ∈ ((range (a + b)).filter fun t => ¬ IsRaising a b (rotSlot a b t)) ×ˢ
                ((range (a + b)).filter fun t => IsRaising a b (rotSlot a b t)),
                  ((X ^ (a + b + p.1 - p.2); X ^ (a + b))_∞ : ℤ⟦X⟧))
            * ktrace (transferKernel a b) := by rw [hpref']
      _ = 1 := hwind
  calc HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      = HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
          * ((∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ))
            * ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ))) := by
        rw [hinv, mul_one]
    _ = (HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
          * ∏' m, Limits.zpowOneSub m (HJO.Defs.cylWeight a b (m + 1) : ℤ))
        * ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) := by ring
    _ = ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) := by
        rw [hkey, one_mul]

/-- **Borodin's product form of the cylindric series.** With `d = a + b`,

`C_c(q) (q^{d}; q^{d})_∞ = ∏_{m ≥ 1}(1 - q^m)^{-w_{a,b}(m)}`,

the right-hand side being `∏' m, zpowOneSub m (-w_{a,b}(m+1))`. This is
`borodin_form_of_pref_trace` with its hypothesis discharged by the prefactor identity
`prod_slotPairs_mul_unboundedGF`. -/
@[hjo "prop_borodin_form"]
theorem borodin_form {a b : ℕ} (hco : Nat.Coprime a b) (ha : 0 < a) (hab : a < b) :
    HJO.Cylindric.unboundedGF a b * ((X ^ (a + b); X ^ (a + b))_∞ : ℤ⟦X⟧)
      = ∏' m, Limits.zpowOneSub m (-(HJO.Defs.cylWeight a b (m + 1) : ℤ)) :=
  borodin_form_of_pref_trace hco ha hab (prod_slotPairs_mul_unboundedGF hco ha (by omega))

end HJO.CylindricProduct
