/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.TotalCompletion
public meta import HJO.Attr

/-! # The corner substitution against the multiplier, and `d^*_+` on the completion

The third of Mellit's three relations between a substitution and the corner multiplier
`E_k = Exp[-X/M - (y_1+⋯+y_k)/(u-1)]`, and the consequence Mellit records:
`HJO.Sweep.hatMap_cycleShift_cornerMultiplier`, `cy_{k+1}(E_{k+1}) = (1-y_1)E_{k+1}`, and
`HJO.Sweep.hatFracDplusStar_nsShiftStarFrac`, `d^*_+τ^*_k = (1-y_1)τ^*_{k+1}d^*_+`.

## The functional equation, without a functional equation

In one variable `HJO.Sweep.hatMap_cycleShift_cornerMultiplier` is the identity `G(uy) = (1-y)G(y)`
for `G(y) = exp(-∑_r y^r/(r(u^r-1)))`, and one proves it by applying `cy_{k+1}` to the
exponent and recognising `-∑_r y_1^r/r` as `log(1-y_1)`. Under the reading `Exp[A] = ∑_n h_n[A]`
neither the logarithm nor the exponential appears. What is left is:

* `cy_{k+1}` carries the alphabet `A_{k+1}` to `A_{k+1} - y_1`, the factor `u^r - 1` cancelling
  exactly (`HJO.Sweep.cycleShift_cornerAlphabet_powerSum`) — this is where `u^r ≠ 1` is spent;
* the elementary symmetric functions of a sum of alphabets convolve
  (`HJO.Bglx.map_elemSymm_add`), and those of a single letter are `1, y_1, 0, 0, …`
  (`HJO.Bglx.map_elemSymm_geom`);
* and `h_r[A] = (-1)^r e_r[-A]` (`HJO.Sym.map_completeHomog_eq_neg`) turns the `h`-side statement
  into the `e`-side one that those two lemmas are about.

The last item is the one piece of new plethystic vocabulary. `HJO.Sym.negAlph`, the substitution
`p_r ↦ -p_r`, is an involution, and `HJO.Sym.map_completeHomog_eq_elemSymm` at `u = 1` says it
carries `h_r` to `(-1)^r e_r`. So the existing `e`-convolution `HJO.Bglx.map_elemSymm_add` serves
the `h`-side, and no `h`-convolution has to be proved.

## The convolution is a commutative ring here

`HJO/Shuffle/TotalCompletion.lean` gives the completion only `Mul` and `One`, as the `Λ̂`
construction does, proving no ring axiom that no statement needs. Here one is needed:
`HJO.Sweep.hatFracDplusStar_nsShiftStarFrac` moves the factor `(1-y_1)` across a product of three
elements of the completion, which is associativity and commutativity. Both are proved below — the
first by the reindexing `(e, a) ↦ (a, e-a)` of the double sum — and with them the rest of the
`CommRing` structure, which is cheap once that reindexing is in hand.

## Main results

* `HJO.Sweep.hatMap_cycleShift_cornerMultiplier` — `cy_{k+1}(E_{k+1}) = (1-y_1)E_{k+1}`.
* `HJO.Sweep.hatDplusStar_nsShiftStarExt` — the completion-level form of
  `HJO.Sweep.hatFracDplusStar_nsShiftStarFrac`, `d^*_+(τ^*_kF) = (1-y_1)τ^*_{k+1}(d^*_+F)`.

## Why the operators here act on the completion only

The extended operators `d^*_+` and `τ^*_k` are naturally stated on `V̂°_k`, the **localization at
`y_1⋯y_k`** of the completion, which is not constructed here; the operators below act on the
completion itself, which is a subring of it. Defining an operator on a smaller domain is a
weakening, so `HJO.Sweep.hatDplusStar` and `HJO.Sweep.nsShiftStarExt` are not those operators:
they are the completion-level readings that the two lemmas above actually need.
`HJO/Shuffle/MellitCompletionFrac.lean` extends them to the fraction field of the completion, as
`HJO.Sweep.hatFracDplusStar` and `HJO.Sweep.nsShiftStarFrac`.

## References

A. Mellit, *Toric braids and
`(m,n)`-parking functions*, §3.7.
-/

@[expose] public section

open Finset MvPolynomial

/-! ### Negating an alphabet, and `h` in terms of `e` -/

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **The negation of an alphabet**: the substitution `p_r ↦ -p_r`, that is `f ↦ f[-X]`. -/
noncomputable def negAlph (K : Type*) [Field K] : Lambda K →ₐ[K] Lambda K :=
  diagScale fun _ => (-1 : K)

omit [Algebra ℚ K] in
theorem negAlph_C (a : K) : negAlph K (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [negAlph]; exact diagScale_C _ _

omit [Algebra ℚ K] in
theorem negAlph_powerSum (j : ℕ) :
    negAlph K (powerSum K j) = MvPolynomial.C (-1 : K) * powerSum K j :=
  diagScale_powerSum _ j

/-- **`h_r[-X] = (-1)^r e_r`**, which is `HJO.Sym.map_completeHomog_eq_elemSymm` at `u = 1`. -/
theorem negAlph_completeHomog (r : ℕ) :
    negAlph K (completeHomog K r) = MvPolynomial.C ((-1 : K) ^ r) * elemSymm K r := by
  have h := map_completeHomog_eq_elemSymm (K := K) (u := 1)
    (τ := (negAlph K : Lambda K →ₐ[K] Lambda K).toRingHom)
    (fun r => negAlph_C (algebraMap ℚ K r))
    (fun k => by simpa using negAlph_powerSum (K := K) (k + 1)) r
  simpa using h

omit [Algebra ℚ K] in
/-- **Negating twice is the identity.** -/
theorem negAlph_negAlph (f : Lambda K) : negAlph K (negAlph K f) = f := by
  have key : (negAlph K).comp (negAlph K) = AlgHom.id K (Lambda K) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    have hx : (MvPolynomial.X i : Lambda K) = powerSum K (i + 1) := by
      rw [powerSum, Nat.add_sub_cancel]
    rw [AlgHom.comp_apply, hx, negAlph_powerSum, map_mul, negAlph_powerSum, negAlph_C]
    rw [AlgHom.id_apply, ← mul_assoc, ← MvPolynomial.C_mul]
    norm_num
  exact congrArg (fun g : Lambda K →ₐ[K] Lambda K => g f) key

/-- **`h_r` of an alphabet is `(-1)^r e_r` of its negative.** This is what lets a statement about
the complete homogeneous functions of a sum of alphabets be read off `HJO.Bglx.map_elemSymm_add`,
which is about the elementary ones. -/
theorem map_completeHomog_eq_neg {R : Type*} [CommRing R] [Algebra K R]
    (φ : Lambda K →ₐ[K] R) (r : ℕ) :
    φ (completeHomog K r)
      = algebraMap K R ((-1 : K) ^ r) * (φ.comp (negAlph K)) (elemSymm K r) := by
  have h : completeHomog K r
      = MvPolynomial.C ((-1 : K) ^ r) * negAlph K (elemSymm K r) := by
    have h2 := congrArg (negAlph K) (negAlph_completeHomog (K := K) r)
    rw [negAlph_negAlph, map_mul, negAlph_C] at h2
    exact h2
  rw [h, map_mul, AlgHom.comp_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]

end HJO.Sym

/-! ### The convolution is a commutative ring -/

namespace HJO.Sweep

namespace TotalHat

variable {L : Type*} [CommRing L]

/-- **The convolution is commutative**, by the reflection `e ↦ d - e` of the index. -/
theorem mul_comm' (F G : TotalHat L) : F * G = G * F :=
  TotalHat.ext fun d => by
    rw [coe_mul, coe_mul]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_range] at he
    rw [show d + 1 - 1 - e = d - e from by omega, show d - (d - e) = e from by omega,
      _root_.mul_comm]

/-- **The convolution is associative.** Both sides are the sum over the triangle
`{(a,b) : a + b ≤ d}` of `F_aG_bH_{d-a-b}`; the bijection `(e,a) ↦ (a, e-a)` from the index set of
one iterated sum to the other is what identifies them. -/
theorem mul_assoc' (F G H : TotalHat L) : F * G * H = F * (G * H) :=
  TotalHat.ext fun d => by
    rw [coe_mul, coe_mul]
    have hL : ∑ e ∈ range (d + 1), ((F * G) e : Total L) * (H (d - e) : Total L)
        = ∑ e ∈ range (d + 1), ∑ a ∈ range (e + 1),
          (F a : Total L) * (G (e - a) : Total L) * (H (d - e) : Total L) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [coe_mul, Finset.sum_mul]
    have hR : ∑ a ∈ range (d + 1), (F a : Total L) * ((G * H) (d - a) : Total L)
        = ∑ a ∈ range (d + 1), ∑ b ∈ range (d - a + 1),
          (F a : Total L) * ((G b : Total L) * (H (d - a - b) : Total L)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [coe_mul, Finset.mul_sum]
    rw [hL, hR, Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (i := fun x => ⟨x.2, x.1 - x.2⟩) (j := fun y => ⟨y.1 + y.2, y.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨e, a⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      omega
    · rintro ⟨a, b⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
      omega
    · rintro ⟨e, a⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      omega
    · rintro ⟨a, b⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_range] at hy
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      omega
    · rintro ⟨e, a⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      rw [show d - a - (e - a) = d - e from by omega, mul_assoc]

theorem one_mul' (F : TotalHat L) : 1 * F = F :=
  TotalHat.ext fun d => by
    rw [coe_mul, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (by omega))
      (fun e _ hne => by rw [coe_one]; simp [hne])]
    rw [coe_one]
    simp

theorem mul_one' (F : TotalHat L) : F * 1 = F := by rw [mul_comm', one_mul']

theorem zero_mul' (F : TotalHat L) : 0 * F = 0 :=
  TotalHat.ext fun d => by
    rw [coe_mul, coe_zero]
    exact Finset.sum_eq_zero fun e _ => by rw [coe_zero, zero_mul]

theorem mul_zero' (F : TotalHat L) : F * 0 = 0 := by rw [mul_comm', zero_mul']

theorem left_distrib' (F G H : TotalHat L) : F * (G + H) = F * G + F * H :=
  TotalHat.ext fun d => by
    rw [coe_add, coe_mul, coe_mul, coe_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [coe_add, mul_add]

theorem right_distrib' (F G H : TotalHat L) : (F + G) * H = F * H + G * H := by
  rw [mul_comm', left_distrib', mul_comm' H F, mul_comm' H G]

/-- **The completion is a commutative ring.** The additive structure is the one a product of
submodules already has; only the convolution's laws are new. -/
noncomputable instance : CommRing (TotalHat L) where
  __ := (inferInstance : AddCommGroup (TotalHat L))
  mul := (· * ·)
  one := 1
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  mul_comm := mul_comm'

/-- **A homogeneous element of the total space, read in the completion**: the family concentrated
in its own degree. -/
noncomputable def ofComp {e : ℕ} (a : Total L) (ha : a ∈ TotalComp L e) : TotalHat L :=
  fun d => if h : d = e then ⟨a, h ▸ ha⟩ else 0

theorem coe_ofComp {e : ℕ} (a : Total L) (ha : a ∈ TotalComp L e) (d : ℕ) :
    (ofComp a ha d : Total L) = if d = e then a else 0 := by
  rw [ofComp]
  split_ifs with h
  · rfl
  · rfl

/-- Multiplying by a homogeneous element shifts the degree by its own. -/
theorem coe_ofComp_mul {e : ℕ} (a : Total L) (ha : a ∈ TotalComp L e) (F : TotalHat L) (d : ℕ) :
    ((ofComp a ha * F) d : Total L) = if e ≤ d then a * (F (d - e) : Total L) else 0 := by
  rw [coe_mul]
  split_ifs with hd
  · rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.2 (by omega))
      (fun j _ hne => by rw [coe_ofComp]; simp [hne]), coe_ofComp]
    simp
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [coe_ofComp]
    simp [show ¬(j = e) from by omega]

end TotalHat

/-- **The letter `y_1`, read in the completion.** -/
noncomputable def auxVarOne (L : Type*) [Field L] : TotalHat L :=
  TotalHat.ofComp (auxVar 1) (auxVar_mem_totalComp L 1)

/-! ### The corner substitution against the corner multiplier -/

section Gamma

variable {L : Type*} [Field L] [Algebra ℚ L]

open HJO.Sym

omit [Algebra ℚ L] in
/-- **The corner substitution lowers the alphabet by the single letter `y_1`.**
`cy_{k+1}` fixes every `p_r` and permutes `y_1, …, y_{k+1}` cyclically up to the scalar `u`, so it
changes the exponent by `(u^r-1)y_1^r/(u^r-1) = y_1^r` — the factor `u^r-1` cancelling exactly,
which is where `u^r ≠ 1` is spent. -/
theorem cycleShift_cornerAlphabet_powerSum (q u : L) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (k i : ℕ) :
    cycleShift u k (cornerAlphabet q u (k + 1) (Sym.powerSum L (i + 1)))
      = cornerAlphabet q u (k + 1) (Sym.powerSum L (i + 1))
        - (auxVar 1 : Total L) ^ (i + 1) := by
  set r := i + 1 with hr
  set S : Total L := ∑ m ∈ range k, (auxVar (m + 2) : Total L) ^ r with hS
  have horig : (∑ m ∈ range (k + 1), (auxVar (m + 1) : Total L) ^ r)
      = S + (auxVar 1 : Total L) ^ r := by
    rw [hS, Finset.sum_range_succ']
  have hcy : cycleShift u k (∑ m ∈ range (k + 1), (auxVar (m + 1) : Total L) ^ r)
      = S + scal (u ^ r) * (auxVar 1 : Total L) ^ r := by
    rw [map_sum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      rw [map_pow, cycleShift_auxVar u (by omega) (by omega)]
    · rw [map_pow, cycleShift_auxVar_last, mul_pow, scal_eq_algebraMap, scal_eq_algebraMap,
        ← map_pow]
  rw [cornerAlphabet_powerSum, map_neg, map_add, map_mul, map_mul, hcy, horig]
  have hCfix : ∀ a : Sym.Lambda L, cycleShift u k (MvPolynomial.C a : Total L)
      = MvPolynomial.C a := fun a => AlgHom.commutes (cycleShift u k) a
  have hpfix := hCfix (Sym.powerSum L r)
  have hsc : ∀ x : L, cycleShift u k (scal x : Total L) = scal x := fun x =>
    hCfix (MvPolynomial.C x)
  rw [hpfix, hsc, hsc]
  have hkey : (scal ((u ^ r - 1)⁻¹) : Total L) * (scal (u ^ r) * (auxVar 1 : Total L) ^ r)
      = scal ((u ^ r - 1)⁻¹) * ((auxVar 1 : Total L) ^ r) + (auxVar 1 : Total L) ^ r := by
    have hne : (u ^ r - 1) ≠ 0 := sub_ne_zero.2 (hu r (by omega))
    have hsplit : (scal ((u ^ r - 1)⁻¹ * u ^ r) : Total L)
        = scal ((u ^ r - 1)⁻¹) + scal 1 := by
      rw [← scal_add]
      congr 1
      field_simp
      ring
    rw [← mul_assoc, ← scal_mul, hsplit]
    simp [add_mul]
  rw [mul_add, hkey]
  ring

/-- The single letter `y_1` as an alphabet: the substitution `p_r ↦ y_1^r`. -/
noncomputable def oneLetterAux (L : Type*) [Field L] : Sym.Lambda L →ₐ[L] Total L :=
  MvPolynomial.aeval fun i : ℕ => (auxVar 1 : Total L) ^ (i + 1)

omit [Algebra ℚ L] in
theorem oneLetterAux_powerSum {j : ℕ} (hj : 1 ≤ j) :
    oneLetterAux L (Sym.powerSum L j) = (auxVar 1 : Total L) ^ j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [Sym.powerSum, Nat.add_sub_cancel, oneLetterAux, MvPolynomial.aeval_X]

/-- The elementary symmetric functions of a single letter are `1, y_1, 0, 0, …`. -/
theorem oneLetterAux_elemSymm (s : ℕ) :
    oneLetterAux L (Sym.elemSymm L s)
      = if s = 0 then 1 else if s = 1 then (auxVar 1 : Total L) else 0 :=
  Bglx.map_elemSymm_geom _ (oneLetterAux L) (fun _ hj => oneLetterAux_powerSum hj) s

/-- **The corner substitution against the corner multiplier, memberwise**:
`cy_{k+1}(E_{k+1})_{n+1} = (E_{k+1})_{n+1} - y_1(E_{k+1})_n`.

The alphabet of `cy_{k+1}∘Θ_{k+1}` is that of `Θ_{k+1}` less the single letter `y_1`, so after
negating both — `HJO.Sym.map_completeHomog_eq_neg` — the `e`-convolution of
`HJO.Bglx.map_elemSymm_add` applies, and the single-letter factor contributes only its terms in
degrees `0` and `1`. -/
theorem cycleShift_cornerAlphabet_completeHomog (q u : L) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1)
    (k n : ℕ) :
    cycleShift u k (cornerAlphabet q u (k + 1) (Sym.completeHomog L (n + 1)))
      = cornerAlphabet q u (k + 1) (Sym.completeHomog L (n + 1))
        - (auxVar 1 : Total L) * cornerAlphabet q u (k + 1) (Sym.completeHomog L n) := by
  set Θ : Sym.Lambda L →ₐ[L] Total L := cornerAlphabet q u (k + 1) with hΘ
  set Θ' : Sym.Lambda L →ₐ[L] Total L :=
    ((cycleShift u k).restrictScalars L).comp Θ with hΘ'
  have hsplit : ∀ j : ℕ, 1 ≤ j → (Θ'.comp (negAlph L)) (Sym.powerSum L j)
      = (Θ.comp (negAlph L)) (Sym.powerSum L j) + oneLetterAux L (Sym.powerSum L j) := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hneg : (negAlph L) (Sym.powerSum L (i + 1))
        = MvPolynomial.C (-1 : L) * Sym.powerSum L (i + 1) := negAlph_powerSum _
    have hcy := cycleShift_cornerAlphabet_powerSum q u hu k i
    rw [← hΘ] at hcy
    have hCneg : Θ (MvPolynomial.C (-1 : L)) = -1 := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      simp
    have hΘ'p : ∀ f : Sym.Lambda L, Θ' f = cycleShift u k (Θ f) := fun _ => rfl
    have hRHS : (Θ.comp (negAlph L)) (Sym.powerSum L (i + 1))
        = -Θ (Sym.powerSum L (i + 1)) := by
      rw [AlgHom.comp_apply, hneg, map_mul, hCneg]
      ring
    have hLHS : (Θ'.comp (negAlph L)) (Sym.powerSum L (i + 1))
        = -(cycleShift u k (Θ (Sym.powerSum L (i + 1)))) := by
      rw [AlgHom.comp_apply, hneg, map_mul, hΘ'p, hΘ'p, hCneg, map_neg, map_one]
      ring
    rw [hLHS, hRHS, hcy, oneLetterAux_powerSum hj]
    ring
  have hconv := Bglx.map_elemSymm_add (Θ.comp (negAlph L)) (oneLetterAux L)
    (Θ'.comp (negAlph L)) hsplit (n + 1)
  rw [Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp) (by omega) ?_] at hconv
  · rw [oneLetterAux_elemSymm, oneLetterAux_elemSymm] at hconv
    norm_num at hconv
    have hh : ∀ (φ : Sym.Lambda L →ₐ[L] Total L) (r : ℕ), φ (Sym.completeHomog L r)
        = scal ((-1 : L) ^ r) * (φ.comp (negAlph L)) (Sym.elemSymm L r) := fun φ r => by
      rw [map_completeHomog_eq_neg φ r, scal_eq_algebraMap]
    change Θ' (Sym.completeHomog L (n + 1)) = _
    rw [hh Θ' (n + 1), hh Θ (n + 1), hh Θ n]
    simp only [AlgHom.comp_apply]
    rw [hconv]
    rw [show ((-1 : L) ^ (n + 1)) = (-1) * (-1) ^ n from by ring, scal_mul, scal_neg, scal_one]
    ring
  · intro s hs hs01
    rw [oneLetterAux_elemSymm]
    simp [hs01.1, hs01.2]

/-- **The corner substitution retracts the corner multiplier.**
`HJO.Sweep.hatMap_cycleShift_cornerMultiplier`: `cy_{k+1}(E_{k+1}) = (1-y_1)E_{k+1}`.

In degree `0` both sides are `h_0 = 1`; in degree `n+1` this is
`HJO.Sweep.cycleShift_cornerAlphabet_completeHomog`, the factor `1 - y_1` contributing exactly its
two members. -/
@[hjo "lem_mellit_ns_multiplier_gamma"]
theorem hatMap_cycleShift_cornerMultiplier (q u : L) (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (k : ℕ) :
    hatMap (preservesTotalComp_cycleShift u k) (cornerMultiplier q u (k + 1))
      = (1 - auxVarOne L) * cornerMultiplier q u (k + 1) := by
  refine TotalHat.ext fun d => ?_
  rw [sub_mul, one_mul, coe_hatMap, TotalHat.coe_sub, auxVarOne, TotalHat.coe_ofComp_mul,
    coe_cornerMultiplier]
  match d with
  | 0 =>
    change cycleShift u k (cornerAlphabet q u (k + 1) (Sym.completeHomog L 0)) = _
    rw [UkRegular.completeHomog_zero L, map_one, map_one]
    simp
  | n + 1 =>
    change cycleShift u k (cornerAlphabet q u (k + 1) (Sym.completeHomog L (n + 1))) = _
    rw [cycleShift_cornerAlphabet_completeHomog q u hu k n]
    simp [coe_cornerMultiplier]

end Gamma

/-! ### `d^*_+` on the completion, and the conjugate shift -/

section Dstar

variable {L : Type*} [Field L]

/-- **`d^*_+` as an algebra endomorphism of the total space**, `cy_{k+1}∘τ_{k+1,k+1}`. The
`HJO.Sweep.dplusStar` is the same map read `𝕜`-linearly
(`HJO.Sweep.dplusStarAlg_eq_dplusStar`); what the completion needs is that it is multiplicative,
which the linear reading does not record. -/
noncomputable def dplusStarAlg (q u : L) (k : ℕ) : Total L →ₐ[L] Total L :=
  ((cycleShift u k).restrictScalars L).comp (qshift q (k + 1))

theorem dplusStarAlg_apply (q u : L) (k : ℕ) (F : Total L) :
    dplusStarAlg q u k F = cycleShift u k (qshift q (k + 1) F) := rfl

theorem dplusStarAlg_eq_dplusStar [Algebra ℚ L] (q u : L) (k : ℕ) (F : Total L) :
    dplusStarAlg q u k F = dplusStar q u k F := rfl

/-- **`d^*_+` is homogeneous of degree zero**, being a composite of two substitutions that are.
This is what `HJO.Sweep.hatFracDplusStar` asks in order to read it on the completion. -/
theorem preservesTotalComp_dplusStarAlg (q u : L) (k : ℕ) :
    PreservesTotalComp (dplusStarAlg q u k) := fun _ _ hF =>
  cycleShift_mem_totalComp u k (qshift_mem_totalComp q (k + 1) hF)

/-- **`d^*_+` on the completion.** The completion-level reading of `HJO.Sweep.hatFracDplusStar`; the
extended operator itself is stated on the localization and is not this declaration. -/
noncomputable def hatDplusStar (q u : L) (k : ℕ) : TotalHat L → TotalHat L :=
  hatMap (preservesTotalComp_dplusStarAlg q u k)

theorem hatDplusStar_eq (q u : L) (k : ℕ) (F : TotalHat L) :
    hatDplusStar q u k F
      = hatMap (preservesTotalComp_cycleShift u k)
          (hatMap (preservesTotalComp_qshift q (k + 1)) F) :=
  TotalHat.ext fun _ => rfl

theorem hatDplusStar_mul (q u : L) (k : ℕ) (F G : TotalHat L) :
    hatDplusStar q u k (F * G) = hatDplusStar q u k F * hatDplusStar q u k G :=
  hatMap_mul _ F G

end Dstar

section ShiftStar

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The extended conjugate shift `τ^*_k`**, multiplication by the corner multiplier. The
completion-level reading of `HJO.Sweep.nsShiftStarFrac`; the extended operator itself is stated on
the localization and is not this declaration. -/
noncomputable def nsShiftStarExt (q u : L) (k : ℕ) (F : TotalHat L) : TotalHat L :=
  F * cornerMultiplier q u k

/-- **`d^*_+` of the corner multiplier is `(1-y_1)E_{k+1}`**: the two halves of the
proof, `HJO.Sweep.hatMap_qshift_cornerMultiplier` then
`HJO.Sweep.hatMap_cycleShift_cornerMultiplier`. -/
theorem hatDplusStar_cornerMultiplier (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1)
    (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (k : ℕ) :
    hatDplusStar q u k (cornerMultiplier q u k)
      = (1 - auxVarOne L) * cornerMultiplier q u (k + 1) := by
  rw [hatDplusStar_eq, hatMap_qshift_cornerMultiplier q u hq k,
    hatMap_cycleShift_cornerMultiplier q u hu k]

/-- **The starred raising operator against the conjugate shift.**
`HJO.Sweep.hatFracDplusStar_nsShiftStarFrac`: `d^*_+(τ^*_kF) = (1-y_1)τ^*_{k+1}(d^*_+F)`.

`d^*_+` is a composite of two algebra homomorphisms, hence multiplicative on the convolution
(`HJO.Sweep.hatDplusStar_mul`), so the only content is its value on the multiplier; the rest is
commutativity and associativity of the convolution. -/
theorem hatDplusStar_nsShiftStarExt (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1)
    (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (k : ℕ) (F : TotalHat L) :
    hatDplusStar q u k (nsShiftStarExt q u k F)
      = (1 - auxVarOne L) * nsShiftStarExt q u (k + 1) (hatDplusStar q u k F) := by
  rw [nsShiftStarExt, hatDplusStar_mul, hatDplusStar_cornerMultiplier q u hq hu k,
    nsShiftStarExt]
  ring

end ShiftStar

end HJO.Sweep

end
