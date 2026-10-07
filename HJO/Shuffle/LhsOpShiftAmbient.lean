/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitShiftGenerators

/-! # The common ambient for `τ^*_kτ_k` at every level

Mellit's `S`-step (§3.7 of *Toric braids and `(m,n)`-parking functions*) uses, on each piece `V_k`,
the composite `Φ_k = τ^*_kτ_k`, `Φ_kF = F[X+1]∏_{i ≤ k}(1-y_i^{-1})·E_k`, with `E_k` the corner
multiplier `HJO.Sweep.cornerMultiplier`. The factor `∏(1-y_i^{-1})` is what forces the direct
approach into a localisation. This file avoids it by **renormalising**: multiplying by `y_1⋯y_k`,

  `Ψ_kF = (∏_{i ≤ k}(y_i - 1))·ϑ(F)·E_k  ∈  Λ̂[[y]]` (`HJO.Mellit.LhsShift.psiAmb`),

which lives in the completion `HJO.Sweep.TotalHat` itself. The price is that the generators are
conjugated by `π_k = y_1⋯y_k`: the partner of `d_-` becomes `d_- ∘ y_k^{-1}`, which is the honest
polynomial operator `HJO.Mellit.LhsShift.dminusDown` (`d_-(y_kH) = dminusDown(…)`'s defining
property), and the partner of `d^*_+` becomes `-d^*_+`.

## Main definitions

* `tproj d F`: the degree-`d` part of `F` for the total grading, and `toHat F` the family of those
  parts.
* `IsHom c X`: `X` shifts that grading by `c`.
* `extT X c G n`: the `n`-th member of `X` applied memberwise to `G ∈ TotalHat`, shifted by `c`.
* `ExtRel X c A B`: `A = X̂B` memberwise.
* `lowerCoeffDown`, `dminusDown`: the coefficient extraction `y^d ↦ (-1)^{d_j-1}e_{d_j-1}y^{d∖j}`
  and the operator `d_- ∘ y_k^{-1}`.
* `psiAmb q u k F`: the renormalised `τ^*_kτ_k`.

## Main results

The four generator checks, each for every `F` in the total space:

* `extRel_psiAmb_auxVar_one`: `Ψ_k(y_1F) = ŷ_1 Ψ_kF`;
* `extRel_psiAmb_braid`, `extRel_psiAmb_braidInv`: `Ψ_k(T_i^{±1}F) = T̂_i^{±1}Ψ_kF`, `i + 1 ≤ k`;
* `extRel_psiAmb_dplusStar`: `Ψ_{k+1}(d^*_+F) = -d̂^*_+Ψ_kF`;
* `extRel_psiAmb_dminus`: `Ψ_k(d_-F) = \widehat{dminusDown}\,Ψ_{k+1}F` (degree `-1`).
-/

@[expose] public section

open Finset MvPolynomial

namespace HJO.Mellit.LhsShift

open HJO.Sweep

section Proj

variable {L : Type*} [Field L]

/-! ### The graded projection of the total space -/

/-- The integer-indexed component of a symmetric function, `0` below degree zero. -/
noncomputable def lcInt (c : ℤ) : Sym.Lambda L →ₗ[L] Sym.Lambda L :=
  if 0 ≤ c then Sym.lambdaComponent L c.toNat else 0

/-- `lcInt c a` lies in the degree-`c` component of `Λ`. -/
theorem lcInt_mem (c : ℤ) (a : Sym.Lambda L) : lcInt c a ∈ Sym.LambdaCompInt L c := by
  unfold lcInt Sym.LambdaCompInt
  split_ifs with h
  · exact Sym.lambdaComponent_mem L _ a
  · simp

/-- On an element homogeneous of degree `c`, `lcInt c'` is the identity if `c' = c` and `0`
otherwise. -/
theorem lcInt_of_mem {c c' : ℤ} {a : Sym.Lambda L} (ha : a ∈ Sym.LambdaCompInt L c) :
    lcInt c' a = if c' = c then a else 0 := by
  rcases lt_or_ge c 0 with hc | hc
  · rw [Sym.eq_zero_of_mem_lambdaCompInt hc ha]; simp
  lift c to ℕ using hc with d
  rw [Sym.lambdaCompInt_natCast] at ha
  unfold lcInt
  by_cases h1 : 0 ≤ c'
  · rw [ite_eq_left h1, Sym.lambdaComponent_of_mem ha]
    by_cases h2 : c' = d
    · subst h2; simp
    · rw [ite_eq_right h2, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, ite_eq_right (by omega)]; rfl

/-- **The degree-`d` part of an element of the total space**: on each `y`-monomial `m` the
component of the coefficient in degree `d - |m|`. -/
noncomputable def tproj (d : ℕ) (F : Total L) : Total L :=
  ∑ m ∈ F.support, MvPolynomial.monomial m (lcInt ((d : ℤ) - (m.degree : ℤ)) (F.coeff m))

/-- The coefficient of `y^m` in `tproj d F` is the degree-`(d - |m|)` component of the coefficient
of `y^m` in `F`. -/
theorem coeff_tproj (d : ℕ) (F : Total L) (m : ℕ →₀ ℕ) :
    (tproj d F).coeff m = lcInt ((d : ℤ) - (m.degree : ℤ)) (F.coeff m) := by
  classical
  rw [tproj, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hm
    simp [MvPolynomial.notMem_support_iff.1 hm]

theorem tproj_add (d : ℕ) (F G : Total L) : tproj d (F + G) = tproj d F + tproj d G := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, coeff_add, coeff_add, coeff_tproj, coeff_tproj, map_add]

theorem tproj_smul (d : ℕ) (r : L) (F : Total L) : tproj d (r • F) = r • tproj d F := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, coeff_smul, coeff_smul, coeff_tproj, map_smul]

theorem tproj_zero (d : ℕ) : tproj d (0 : Total L) = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, coeff_zero, map_zero]

theorem tproj_neg (d : ℕ) (F : Total L) : tproj d (-F) = -tproj d F := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, coeff_neg, coeff_neg, coeff_tproj, map_neg]

theorem tproj_sub (d : ℕ) (F G : Total L) : tproj d (F - G) = tproj d F - tproj d G := by
  rw [sub_eq_add_neg, tproj_add, tproj_neg, ← sub_eq_add_neg]

theorem tproj_mem (d : ℕ) (F : Total L) : tproj d F ∈ TotalComp L d := by
  intro m
  rw [coeff_tproj]
  exact lcInt_mem _ _

/-- **A homogeneous element is its own part in its own degree, and has none in any other.** -/
theorem tproj_of_mem {e : ℕ} {F : Total L} (hF : F ∈ TotalComp L e) (d : ℕ) :
    tproj d F = if d = e then F else 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_tproj, lcInt_of_mem (hF m)]
  by_cases h : d = e
  · subst h; simp
  · rw [ite_eq_right (by omega), ite_eq_right h, coeff_zero]

/-- **Induction over homogeneous elements**: every element of the total space is a finite sum of
homogeneous ones. -/
theorem induction_homog {P : Total L → Prop} (h0 : P 0)
    (hadd : ∀ F G, P F → P G → P (F + G)) (hhom : ∀ d, ∀ F ∈ TotalComp L d, P F) (F : Total L) :
    P F := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [← Sym.sum_lambdaComponent a, map_sum]
    exact Finset.sum_induction _ P hadd h0 fun d _ =>
      hhom _ _ (monomial_mem_totalComp (Sym.lambdaComponent_mem L d a) m)
  | add p q hp hq => exact hadd _ _ hp hq

/-- **Every element of the total space is the finite sum of its parts.** -/
theorem exists_sum_tproj (F : Total L) :
    ∃ N : ℕ, (∀ d, N ≤ d → tproj d F = 0) ∧ ∑ d ∈ range N, tproj d F = F := by
  refine induction_homog (P := fun F => ∃ N : ℕ, (∀ d, N ≤ d → tproj d F = 0) ∧
    ∑ d ∈ range N, tproj d F = F) ⟨0, fun d _ => tproj_zero d, by simp⟩ ?_ ?_ F
  · rintro F G ⟨N₁, h₁, s₁⟩ ⟨N₂, h₂, s₂⟩
    refine ⟨max N₁ N₂, fun d hd => by
      rw [tproj_add, h₁ d (by omega), h₂ d (by omega), add_zero], ?_⟩
    rw [Finset.sum_congr rfl (fun d _ => tproj_add d F G), Finset.sum_add_distrib]
    have e₁ : ∑ d ∈ range (max N₁ N₂), tproj d F = ∑ d ∈ range N₁, tproj d F :=
      (Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun d _ hd =>
        h₁ d (by simpa using hd)).symm
    have e₂ : ∑ d ∈ range (max N₁ N₂), tproj d G = ∑ d ∈ range N₂, tproj d G :=
      (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun d _ hd =>
        h₂ d (by simpa using hd)).symm
    rw [e₁, e₂, s₁, s₂]
  · intro e F hF
    refine ⟨e + 1, fun d hd => by rw [tproj_of_mem hF, ite_eq_right (by omega)], ?_⟩
    rw [Finset.sum_eq_single e (fun d _ hd => by rw [tproj_of_mem hF, ite_eq_right hd])
      (fun h => absurd (Finset.mem_range.2 (by omega)) h), tproj_of_mem hF, ite_eq_left rfl]

/-- An element all of whose parts vanish is zero. -/
theorem eq_zero_of_tproj {F : Total L} (h : ∀ d, tproj d F = 0) : F = 0 := by
  obtain ⟨N, -, hs⟩ := exists_sum_tproj F
  rw [← hs]
  exact Finset.sum_eq_zero fun d _ => h d

/-- An element whose parts vanish outside degree `e` is homogeneous of degree `e`. -/
theorem mem_of_tproj {F : Total L} {e : ℕ} (h : ∀ d, d ≠ e → tproj d F = 0) :
    F ∈ TotalComp L e := by
  have : F = tproj e F := by
    refine sub_eq_zero.1 (eq_zero_of_tproj fun d => ?_)
    rw [tproj_sub]
    by_cases hd : d = e
    · subst hd
      rw [tproj_of_mem (tproj_mem d F), ite_eq_left rfl, sub_self]
    · rw [h d hd, tproj_of_mem (tproj_mem e F), ite_eq_right hd, sub_zero]
  rw [this]
  exact tproj_mem e F

/-- Multiplying by a homogeneous element of degree `a` moves the parts up by `a`. -/
theorem tproj_mul_of_mem {a : ℕ} {A : Total L} (hA : A ∈ TotalComp L a) (G : Total L) (n : ℕ) :
    tproj n (A * G) = if a ≤ n then A * tproj (n - a) G else 0 := by
  refine induction_homog (P := fun G => tproj n (A * G)
    = if a ≤ n then A * tproj (n - a) G else 0) ?_ ?_ ?_ G
  · rw [mul_zero, tproj_zero, tproj_zero, mul_zero, ite_self]
  · intro F G hF hG
    rw [mul_add, tproj_add, hF, hG, tproj_add]
    split_ifs <;> ring
  · intro e F hF
    rw [tproj_of_mem (mul_mem_totalComp hA hF), tproj_of_mem hF]
    by_cases h1 : n = a + e
    · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      split_ifs with h2 h3
      · omega
      · rw [mul_zero]
      · rfl

/-! ### The family of parts -/

/-- **`F` read in the completion**, as the family of its parts. -/
noncomputable def toHat (F : Total L) : TotalHat L := fun d => ⟨tproj d F, tproj_mem d F⟩

/-- The `d`-th member of `toHat F` is `tproj d F`. -/
theorem coe_toHat (F : Total L) (d : ℕ) : (toHat F d : Total L) = tproj d F := rfl

/-- `toHat` is additive. -/
theorem toHat_add (F G : Total L) : toHat (F + G) = toHat F + toHat G :=
  TotalHat.ext fun d => by rw [TotalHat.coe_add, coe_toHat, coe_toHat, coe_toHat, tproj_add]

theorem toHat_neg (F : Total L) : toHat (-F) = -toHat F :=
  TotalHat.ext fun d => by
    change tproj d (-F) = -tproj d F
    rw [tproj_neg]

theorem toHat_sub (F G : Total L) : toHat (F - G) = toHat F - toHat G :=
  TotalHat.ext fun d => by rw [TotalHat.coe_sub, coe_toHat, coe_toHat, coe_toHat, tproj_sub]

theorem toHat_of_mem {e : ℕ} {F : Total L} (hF : F ∈ TotalComp L e) :
    toHat F = TotalHat.ofComp F hF :=
  TotalHat.ext fun d => by rw [coe_toHat, tproj_of_mem hF, TotalHat.coe_ofComp]

theorem toHat_zero : toHat (0 : Total L) = 0 :=
  TotalHat.ext fun d => by rw [coe_toHat, tproj_zero, TotalHat.coe_zero]

theorem toHat_smul (r : L) (F : Total L) : toHat (r • F) = r • toHat F :=
  TotalHat.ext fun d => by rw [TotalHat.coe_smul, coe_toHat, coe_toHat, tproj_smul]

/-- The `L`-action passes through a convolution product. -/
theorem smul_mul_hat (r : L) (A B : TotalHat L) : (r • A) * B = r • (A * B) :=
  TotalHat.ext fun d => by
    rw [TotalHat.coe_smul, TotalHat.coe_mul, TotalHat.coe_mul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [TotalHat.coe_smul, smul_mul_assoc]

/-! ### Degree-shifting endomorphisms and their memberwise extension -/

/-- `X` shifts the grading of the total space by `c`. -/
def IsHom (c : ℤ) (X : Module.End L (Total L)) : Prop :=
  ∀ d : ℕ, ∀ F ∈ TotalComp L d, X F ∈ TotalCompInt L ((d : ℤ) + c)

/-- The composite of operators shifting degree by `c₁` and `c₂` shifts degree by `c₁ + c₂`. -/
theorem IsHom.mul {c₁ c₂ : ℤ} {X₁ X₂ : Module.End L (Total L)} (h₁ : IsHom c₁ X₁)
    (h₂ : IsHom c₂ X₂) : IsHom (c₁ + c₂) (X₁ * X₂) := by
  intro d F hF
  have h := h₂ d F hF
  change X₁ (X₂ F) ∈ _
  rcases lt_or_ge ((d : ℤ) + c₂) 0 with hlt | hge
  · rw [eq_zero_of_mem_totalCompInt hlt h, map_zero]; exact zero_mem _
  · obtain ⟨e, he⟩ : ∃ e : ℕ, (d : ℤ) + c₂ = e := ⟨_, (Int.toNat_of_nonneg hge).symm⟩
    rw [he, totalCompInt_natCast] at h
    have := h₁ e _ h
    rwa [show (e : ℤ) + c₁ = d + (c₁ + c₂) by omega] at this

/-- The sum of two operators shifting degree by `c` shifts degree by `c`. -/
theorem IsHom.add {c : ℤ} {X₁ X₂ : Module.End L (Total L)} (h₁ : IsHom c X₁)
    (h₂ : IsHom c X₂) : IsHom c (X₁ + X₂) := fun d F hF => add_mem (h₁ d F hF) (h₂ d F hF)

/-- The difference of two operators shifting degree by `c` shifts degree by `c`. -/
theorem IsHom.sub {c : ℤ} {X₁ X₂ : Module.End L (Total L)} (h₁ : IsHom c X₁)
    (h₂ : IsHom c X₂) : IsHom c (X₁ - X₂) := fun d F hF => sub_mem (h₁ d F hF) (h₂ d F hF)

/-- A scalar multiple of an operator shifting degree by `c` shifts degree by `c`. -/
theorem IsHom.smul {c : ℤ} {X : Module.End L (Total L)} (r : L) (h : IsHom c X) :
    IsHom c (r • X) := fun d F hF => Submodule.smul_mem _ r (h d F hF)

/-- The negative of an operator shifting degree by `c` shifts degree by `c`. -/
theorem IsHom.neg {c : ℤ} {X : Module.End L (Total L)} (h : IsHom c X) : IsHom c (-X) :=
  fun d F hF => neg_mem (h d F hF)

/-- The identity preserves degree. -/
theorem isHom_one : IsHom 0 (1 : Module.End L (Total L)) := fun d F hF => by
  rw [add_zero, totalCompInt_natCast]; exact hF

/-- The `n`-th power of an operator shifting degree by `c` shifts degree by `n * c`. -/
theorem IsHom.pow {c : ℤ} {X : Module.End L (Total L)} (h : IsHom c X) (n : ℕ) :
    IsHom ((n : ℤ) * c) (X ^ n) := by
  induction n with
  | zero => simpa using (isHom_one (L := L))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul h
    rwa [show (n : ℤ) * c + c = ((n + 1 : ℕ) : ℤ) * c by push_cast; ring] at this

/-- Left multiplication by a homogeneous element of degree `a` shifts degree by `a`. -/
theorem isHom_mulLeft {a : ℕ} {A : Total L} (hA : A ∈ TotalComp L a) :
    IsHom (a : ℤ) (LinearMap.mulLeft L A) := fun d F hF => by
  rw [show ((d : ℤ) + a) = ((a + d : ℕ) : ℤ) by push_cast; ring, totalCompInt_natCast]
  exact mul_mem_totalComp hA hF

/-- **The memberwise extension of `X`, shifted by `c`**: the `n`-th member of `X̂G`. -/
noncomputable def extT (X : Module.End L (Total L)) (c : ℤ) (G : TotalHat L) (n : ℕ) :
    Total L :=
  if c ≤ (n : ℤ) then X (G ((n : ℤ) - c).toNat) else 0

/-- **`A = X̂B` memberwise.** -/
def ExtRel (X : Module.End L (Total L)) (c : ℤ) (A B : TotalHat L) : Prop :=
  ∀ n : ℕ, (A n : Total L) = extT X c B n

/-- **The extension is multiplicative**, as soon as the inner factor is homogeneous. -/
theorem ExtRel.comp {X₁ X₂ : Module.End L (Total L)} {c₁ c₂ : ℤ} {A B C : TotalHat L}
    (h₁ : ExtRel X₁ c₁ A B) (h₂ : ExtRel X₂ c₂ B C) (hX₂ : IsHom c₂ X₂) :
    ExtRel (X₁ * X₂) (c₁ + c₂) A C := by
  intro n
  rw [h₁ n]
  unfold extT
  by_cases h1 : c₁ ≤ (n : ℤ)
  · rw [ite_eq_left h1, h₂, extT]
    by_cases h2 : c₂ ≤ (((n : ℤ) - c₁).toNat : ℤ)
    · rw [ite_eq_left h2, ite_eq_left (by omega),
        show ((((n : ℤ) - c₁).toNat : ℤ) - c₂).toNat = ((n : ℤ) - (c₁ + c₂)).toNat by omega]
      rfl
    · rw [ite_eq_right h2, map_zero, ite_eq_right (by omega)]
  · rw [ite_eq_right h1]
    by_cases h3 : c₁ + c₂ ≤ (n : ℤ)
    · rw [ite_eq_left h3, Module.End.mul_apply]
      have hm := hX₂ _ _ (C ((n : ℤ) - (c₁ + c₂)).toNat).2
      rw [eq_zero_of_mem_totalCompInt (by omega) hm, map_zero]
    · rw [ite_eq_right h3]

theorem ExtRel.add {X₁ X₂ : Module.End L (Total L)} {c : ℤ} {A₁ A₂ B : TotalHat L}
    (h₁ : ExtRel X₁ c A₁ B) (h₂ : ExtRel X₂ c A₂ B) : ExtRel (X₁ + X₂) c (A₁ + A₂) B := by
  intro n
  rw [TotalHat.coe_add, h₁ n, h₂ n]
  unfold extT
  split_ifs
  · rfl
  · rw [add_zero]

theorem ExtRel.smul {X : Module.End L (Total L)} {c : ℤ} {A B : TotalHat L} (r : L)
    (h : ExtRel X c A B) : ExtRel (r • X) c (r • A) B := by
  intro n
  rw [TotalHat.coe_smul, h n]
  unfold extT
  split_ifs
  · rfl
  · rw [smul_zero]

theorem ExtRel.neg {X : Module.End L (Total L)} {c : ℤ} {A B : TotalHat L}
    (h : ExtRel X c A B) : ExtRel (-X) c (-A) B := by
  have := h.smul (-1 : L)
  rwa [neg_one_smul L X, neg_one_smul L A] at this

/-- If `A₁ = X̂₁B` and `A₂ = X̂₂B` memberwise, then `A₁ - A₂ = (X₁ - X₂)^B` memberwise. -/
theorem ExtRel.sub {X₁ X₂ : Module.End L (Total L)} {c : ℤ} {A₁ A₂ B : TotalHat L}
    (h₁ : ExtRel X₁ c A₁ B) (h₂ : ExtRel X₂ c A₂ B) : ExtRel (X₁ - X₂) c (A₁ - A₂) B := by
  have := h₁.add h₂.neg
  rwa [← sub_eq_add_neg X₁ X₂, ← sub_eq_add_neg A₁ A₂] at this

/-- `ExtRel` is compatible with equalities of the operator and of the left-hand side. -/
theorem ExtRel.congr {X X' : Module.End L (Total L)} {c : ℤ} {A A' B : TotalHat L}
    (h : ExtRel X c A B) (hA : A = A') (hX : X = X') : ExtRel X' c A' B := hA ▸ hX ▸ h

/-- **A multiplier the operator passes through.** If `X` shifts degree by `c` and
`X(H·E_b) = X(H)·E'_b` for every `H` and every member `E_b`, then `X̂(Ĝ·E) = \widehat{XG}·E'`. -/
theorem extRel_toHat_mul {X : Module.End L (Total L)} {c : ℤ} (hX : IsHom c X)
    {E E' : TotalHat L}
    (hXE : ∀ (H : Total L) (b : ℕ), X (H * (E b : Total L)) = X H * (E' b : Total L))
    (G : Total L) : ExtRel X c (toHat (X G) * E') (toHat G * E) := by
  refine induction_homog (P := fun G => ExtRel X c (toHat (X G) * E') (toHat G * E)) ?_ ?_ ?_ G
  · intro n
    rw [map_zero, toHat_zero, zero_mul, TotalHat.coe_zero, extT]
    split_ifs
    · rw [zero_mul, TotalHat.coe_zero, map_zero]
    · rfl
  · intro F G hF hG n
    rw [map_add, toHat_add, add_mul, TotalHat.coe_add, hF n, hG n, toHat_add, add_mul]
    unfold extT
    split_ifs
    · rw [TotalHat.coe_add, map_add]
    · rw [add_zero]
  · intro e F hF n
    have hXF := hX e F hF
    rw [toHat_of_mem hF, extT, TotalHat.coe_ofComp_mul]
    rcases lt_or_ge ((e : ℤ) + c) 0 with hneg | hpos
    · rw [eq_zero_of_mem_totalCompInt hneg hXF, toHat_zero, zero_mul, TotalHat.coe_zero]
      split_ifs
      · rw [hXE, eq_zero_of_mem_totalCompInt hneg hXF, zero_mul]
      · rw [map_zero]
      · rfl
    · obtain ⟨f, hf⟩ : ∃ f : ℕ, (e : ℤ) + c = f := ⟨_, (Int.toNat_of_nonneg hpos).symm⟩
      rw [hf, totalCompInt_natCast] at hXF
      rw [toHat_of_mem hXF, TotalHat.coe_ofComp_mul]
      by_cases h1 : f ≤ n
      · rw [ite_eq_left h1, ite_eq_left (by omega), ite_eq_left (by omega), hXE,
          show ((n : ℤ) - c).toNat - e = n - f by omega]
      · rw [ite_eq_right h1]
        split_ifs with h2 h3
        · omega
        · rw [map_zero]
        · rfl

/-- The unit of the completion passes through every operator. -/
theorem map_mul_one_hat (X : Module.End L (Total L)) (H : Total L) (b : ℕ) :
    X (H * ((1 : TotalHat L) b : Total L)) = X H * ((1 : TotalHat L) b : Total L) := by
  rw [TotalHat.coe_one]
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

/-- **A degree-shifting operator commutes with taking parts.** -/
theorem extRel_toHat {X : Module.End L (Total L)} {c : ℤ} (hX : IsHom c X) (G : Total L) :
    ExtRel X c (toHat (X G)) (toHat G) := by
  have h := extRel_toHat_mul hX (map_mul_one_hat X) G
  rwa [mul_one, mul_one] at h

/-- **Multiplying by a homogeneous element, read in the completion.** -/
theorem toHat_mul_of_mem {a : ℕ} {A : Total L} (hA : A ∈ TotalComp L a) (G : Total L) :
    toHat (A * G) = TotalHat.ofComp A hA * toHat G :=
  TotalHat.ext fun n => by
    have h := extRel_toHat (isHom_mulLeft hA) G n
    rw [LinearMap.mulLeft_apply] at h
    rw [h, extT, TotalHat.coe_ofComp_mul]
    by_cases h1 : a ≤ n
    · rw [ite_eq_left (by omega), ite_eq_left h1, LinearMap.mulLeft_apply,
        show ((n : ℤ) - a).toNat = n - a by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h1]

/-! ### The braid operators are homogeneous -/

theorem swapAux_mem_totalComp (i : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    swapAux L i F ∈ TotalComp L d := by
  have h := mem_of_mem_totalComp (TotalCompInt L) (one_mem_totalCompInt L)
    (fun {_ _ _ _} hx hy => mul_mem_totalCompInt hx hy)
    ((swapAux L i).toAlgHom.restrictScalars L) (fun j => by
      rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      change swapAux L i (MvPolynomial.X j) ∈ TotalComp L 1
      rw [swapAux_X]
      exact X_mem_totalComp L _) (fun n => by
      rw [show ((n : ℤ) + 1) = (((n + 1 : ℕ)) : ℤ) by push_cast; ring, totalCompInt_natCast]
      change swapAux L i (MvPolynomial.C _) ∈ TotalComp L (n + 1)
      rw [swapAux_C]
      exact powerSum_mem_totalComp L n) hF
  rwa [totalCompInt_natCast] at h

/-- The divided difference `∂_i` lowers degree by one. -/
theorem dividedDiff_mem_totalCompInt (i : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    dividedDiff i F ∈ TotalCompInt L ((d : ℤ) - 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [dividedDiff_zero_index]; exact zero_mem _
  set D : Total L := MvPolynomial.X i - MvPolynomial.X (i - 1) with hD
  have hDm : D ∈ TotalComp L 1 := sub_mem (X_mem_totalComp L _) (X_mem_totalComp L _)
  have hDne : D ≠ 0 := auxVar_sub_ne_zero hi
  have hH : F - swapAux L i F ∈ TotalComp L d := sub_mem hF (swapAux_mem_totalComp i hF)
  have key : ∀ e : ℕ, e + 1 ≠ d → tproj e (dividedDiff i F) = 0 := by
    intro e he
    have h := tproj_mul_of_mem hDm (dividedDiff i F) (e + 1)
    rw [dividedDiff_spec, tproj_of_mem hH, ite_eq_right he, ite_eq_left (by omega),
      Nat.add_sub_cancel] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hDne
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [eq_zero_of_tproj fun e => key e (by omega)]; exact zero_mem _
  · rw [show (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) by omega, totalCompInt_natCast]
    exact mem_of_tproj fun e he => key e (by omega)

/-- The braid operator `T_i` maps homogeneous elements to homogeneous elements of the same
degree. -/
theorem braid_mem_totalComp (q : L) (i : ℕ) {d : ℕ} {F : Total L} (hF : F ∈ TotalComp L d) :
    braid q i F ∈ TotalComp L d := by
  rw [braid_apply]
  refine add_mem (swapAux_mem_totalComp i hF) ?_
  have h := mul_mem_totalCompInt (mul_mem_totalCompInt
    (show (scal (q - 1) : Total L) ∈ TotalCompInt L 0 by
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      exact scal_mem_totalComp _)
    (show (auxVar i : Total L) ∈ TotalCompInt L 1 by
      rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      exact auxVar_mem_totalComp L i)) (dividedDiff_mem_totalCompInt i hF)
  rwa [show (0 : ℤ) + 1 + ((d : ℤ) - 1) = (d : ℤ) by ring, totalCompInt_natCast] at h

/-- The braid operator `T_i` preserves degree. -/
theorem isHom_braidEnd (q : L) (i : ℕ) : IsHom 0 (braidEnd q i) := fun d F hF => by
  rw [add_zero, totalCompInt_natCast]
  exact braid_mem_totalComp q i hF

/-- The inverse braid operator `T_i^{-1}` preserves degree. -/
theorem isHom_braidInvEnd (q : L) (i : ℕ) : IsHom 0 (braidInvEnd q i) := fun d F hF => by
  rw [add_zero, totalCompInt_natCast]
  change braidInv q i F ∈ _
  rw [braidInv_apply]
  have h := mul_mem_totalComp (scal_mem_totalComp q⁻¹) (add_mem (braid_mem_totalComp q i hF)
    (by simpa using mul_mem_totalComp (scal_mem_totalComp (q - 1)) hF))
  simpa using h

end Proj

/-! ### The lowering operator read through `y_k^{-1}` -/

section Down

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The coefficient extraction one index further down**: `y^d ↦ (-1)^{d_j-1}e_{d_j-1}y^{d∖j}`
when `d_j ≥ 1`, and `0` when `d_j = 0`. It is `HJO.Sweep.lowerCoeff` read through division by
`y_{j+1}` (`lowerCoeffDown_X_mul`). -/
noncomputable def lowerCoeffDown (L : Type*) [Field L] [Algebra ℚ L] (j : ℕ) :
    Total L →ₗ[Sym.Lambda L] Total L :=
  (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)).constr (Sym.Lambda L) fun d =>
    if d j = 0 then 0 else
      (-1 : Total L) ^ (d j - 1) * MvPolynomial.C (Sym.elemSymm L (d j - 1)) *
        MvPolynomial.monomial (Finsupp.erase j d) 1

/-- `lowerCoeffDown` on the monomial `y^d`. -/
theorem lowerCoeffDown_monomial (j : ℕ) (d : ℕ →₀ ℕ) :
    lowerCoeffDown L j (MvPolynomial.monomial d 1)
      = if d j = 0 then 0 else
        (-1 : Total L) ^ (d j - 1) * MvPolynomial.C (Sym.elemSymm L (d j - 1)) *
          MvPolynomial.monomial (Finsupp.erase j d) 1 := by
  have hb : (MvPolynomial.basisMonomials ℕ (Sym.Lambda L)) d
      = MvPolynomial.monomial d 1 := congrFun (MvPolynomial.coe_basisMonomials ℕ _) d
  rw [lowerCoeffDown, ← hb]
  exact Module.Basis.constr_basis _ _ _ _

/-- `lowerCoeffDown` on the monomial `a y^d`. -/
theorem lowerCoeffDown_monomial' (j : ℕ) (d : ℕ →₀ ℕ) (a : Sym.Lambda L) :
    lowerCoeffDown L j (MvPolynomial.monomial d a)
      = MvPolynomial.C a * (if d j = 0 then 0 else
        (-1 : Total L) ^ (d j - 1) * MvPolynomial.C (Sym.elemSymm L (d j - 1)) *
          MvPolynomial.monomial (Finsupp.erase j d) 1) := by
  have h : (MvPolynomial.monomial d a : Total L) = a • MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [h, map_smul, lowerCoeffDown_monomial, MvPolynomial.smul_eq_C_mul]

/-- **Dividing by `y_{j+1}` first**: `lowerCoeffDown(y_{j+1}H) = lowerCoeff(H)`. -/
theorem lowerCoeffDown_X_mul (j : ℕ) (H : Total L) :
    lowerCoeffDown L j ((MvPolynomial.X j : Total L) * H) = lowerCoeff L j H := by
  induction H using MvPolynomial.induction_on' with
  | monomial m a =>
    set m' : ℕ →₀ ℕ := Finsupp.single j 1 + m with hm'
    have hmul : (MvPolynomial.X j : Total L) * MvPolynomial.monomial m a
        = MvPolynomial.monomial m' a := by
      rw [MvPolynomial.X, hm', MvPolynomial.monomial_mul, one_mul]
    have hj : m' j = m j + 1 := by
      rw [hm']
      simp [add_comm]
    have herase : Finsupp.erase j m' = Finsupp.erase j m := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i = j
      · subst hi; rw [Finsupp.erase_same, Finsupp.erase_same]
      · rw [Finsupp.erase_ne hi, Finsupp.erase_ne hi, hm', Finsupp.add_apply]
        simp [show ¬(j = i) from fun h => hi h.symm]
    rw [hmul, lowerCoeffDown_monomial', lowerCoeff_monomial', hj, herase,
      ite_eq_right (by omega), Nat.add_sub_cancel]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq]

theorem lowerCoeffDown_monomial_mul {j : ℕ} {n : ℕ →₀ ℕ} (hn : n j = 0) (b : Sym.Lambda L)
    (H : Total L) :
    lowerCoeffDown L j (MvPolynomial.monomial n b * H)
      = MvPolynomial.monomial n b * lowerCoeffDown L j H := by
  induction H using MvPolynomial.induction_on' with
  | monomial m a =>
    have hsum : (n + m) j = m j := by rw [Finsupp.add_apply, hn, zero_add]
    have herase : Finsupp.erase j (n + m) = n + Finsupp.erase j m := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i = j
      · subst hi
        rw [Finsupp.erase_same, Finsupp.add_apply, Finsupp.erase_same, hn, add_zero]
      · rw [Finsupp.erase_ne hi, Finsupp.add_apply, Finsupp.add_apply, Finsupp.erase_ne hi]
    have h1 : (MvPolynomial.monomial (n + Finsupp.erase j m) (1 : Sym.Lambda L) : Total L)
        = MvPolynomial.monomial n 1 * MvPolynomial.monomial (Finsupp.erase j m) 1 := by
      rw [MvPolynomial.monomial_mul, one_mul]
    have h2 : (MvPolynomial.monomial n b : Total L)
        = MvPolynomial.C b * MvPolynomial.monomial n 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [MvPolynomial.monomial_mul, lowerCoeffDown_monomial', lowerCoeffDown_monomial',
      hsum, herase, MvPolynomial.C_mul, h1, h2]
    split_ifs
    · ring
    · ring
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]

theorem lowerCoeffDown_mul_of_mem_piece {j : ℕ} {A : Total L} (hA : A ∈ piece L j)
    (H : Total L) : lowerCoeffDown L j (A * H) = A * lowerCoeffDown L j H := by
  conv_lhs => rw [A.as_sum]
  conv_rhs => rw [A.as_sum]
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm =>
    lowerCoeffDown_monomial_mul (exponent_eq_zero_of_mem_piece hA hm) _ H

/-- **The unit shift against the extraction**:
`ϑ(lowerCoeff G) = lowerCoeff(ϑG) - lowerCoeffDown(ϑG)`, which on each monomial is
`e_n[X+1] = e_n + e_{n-1}`. -/
theorem unitShiftTotal_lowerCoeff (j : ℕ) (G : Total L) :
    unitShiftTotal L (lowerCoeff L j G)
      = lowerCoeff L j (unitShiftTotal L G) - lowerCoeffDown L j (unitShiftTotal L G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [lowerCoeff_monomial', unitShiftTotal_monomial, lowerCoeff_monomial',
      lowerCoeffDown_monomial', map_mul, map_mul, map_mul, unitShiftTotal_C, unitShiftTotal_C,
      map_pow, map_neg, map_one]
    have hm : unitShiftTotal L (MvPolynomial.monomial (Finsupp.erase j d) (1 : Sym.Lambda L))
        = MvPolynomial.monomial (Finsupp.erase j d) (1 : Sym.Lambda L) := by
      rw [unitShiftTotal_monomial, map_one]
    rw [hm]
    rcases h : d j with _ | r
    · have he : Sym.elemSymm L 0 = 1 := by rw [Sym.elemSymm]
      rw [ite_eq_left rfl, he, map_one]
      ring
    · rw [ite_eq_right (by omega), Nat.add_sub_cancel, Sym.unitShift_elemSymm,
        MvPolynomial.C_add]
      ring
  | add p q hp hq => simp only [map_add, hp, hq]; ring

/-- **`d_- ∘ y_k^{-1}`**, the partner of `d_-` under the renormalisation by `y_1⋯y_k`. -/
noncomputable def dminusDown (q : L) (k : ℕ) : Module.End L (Total L) :=
  (lowerCoeffDown L (k - 1)).restrictScalars L ∘ₗ (qshiftNeg q k).toLinearMap

/-- `dminusDown q (k + 1)` is `lowerCoeffDown k` after `qshiftNeg q (k + 1)`. -/
theorem dminusDown_succ_apply (q : L) (k : ℕ) (F : Total L) :
    dminusDown q (k + 1) F = lowerCoeffDown L k (qshiftNeg q (k + 1) F) := rfl

/-- `dminusDown(y_kH) = d_-H`. -/
theorem dminusDown_auxVar_mul (q : L) (k : ℕ) (H : Total L) :
    dminusDown q (k + 1) ((auxVar (k + 1) : Total L) * H) = dminus q (k + 1) H := by
  rw [dminusDown_succ_apply, map_mul, qshiftNeg_auxVar_apply, auxVar, Nat.add_sub_cancel,
    lowerCoeffDown_X_mul, dminus_succ_apply]

theorem dminusDown_mul_of_mem_piece (q : L) {k : ℕ} {A : Total L} (hA : A ∈ piece L k)
    (hfix : qshiftNeg q (k + 1) A = A) (H : Total L) :
    dminusDown q (k + 1) (A * H) = A * dminusDown q (k + 1) H := by
  rw [dminusDown_succ_apply, map_mul, hfix, lowerCoeffDown_mul_of_mem_piece hA,
    dminusDown_succ_apply]

/-- **The check at `d_-` against `τ_k`, renormalised**:
`dminusDown(∏_{i ≤ k+1}(y_i-1)·ϑF) = ∏_{i ≤ k}(y_i-1)·ϑ(d_-F)`, for every `F`. -/
theorem dminusDown_auxProd_unitShiftTotal (q : L) (k : ℕ) (F : Total L) :
    dminusDown q (k + 1) (auxProd L (k + 1) * unitShiftTotal L F)
      = auxProd L k * unitShiftTotal L (dminus q (k + 1) F) := by
  have hprod : auxProd L (k + 1) = auxProd L k * ((auxVar (k + 1) : Total L) - 1) := by
    rw [auxProd, auxProd, Finset.prod_range_succ]
  rw [hprod, mul_assoc, dminusDown_mul_of_mem_piece q (auxProd_mem_piece k)
    (qshiftNeg_auxProd q (k + 1) k), sub_mul, one_mul, map_sub, dminusDown_auxVar_mul,
    dminus_succ_apply, dminusDown_succ_apply, dminus_succ_apply, unitShiftTotal_lowerCoeff,
    unitShiftTotal_qshiftNeg]

theorem dminusDown_cornerAlphabet_mul (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ)
    (f : Sym.Lambda L) (F : Total L) :
    dminusDown q (k + 1) (cornerAlphabet q u (k + 1) f * F)
      = cornerAlphabet q u k f * dminusDown q (k + 1) F := by
  rw [dminusDown_succ_apply, dminusDown_succ_apply, map_mul, qshiftNeg_cornerAlphabet q u hq k,
    lowerCoeffDown_mul_of_mem_piece (cornerAlphabet_mem_piece q u k f)]

theorem lowerCoeffDown_mem_totalCompInt (j : ℕ) {d : ℕ} {G : Total L}
    (hG : G ∈ TotalComp L d) : lowerCoeffDown L j G ∈ TotalCompInt L ((d : ℤ) - 1) := by
  rw [G.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [lowerCoeffDown_monomial']
  split_ifs with hm
  · rw [mul_zero]; exact zero_mem _
  · have h1 : (MvPolynomial.C (G.coeff m) : Total L) ∈ TotalCompInt L ((d : ℤ) - m.degree) :=
      C_mem_totalCompInt (hG m)
    have h2 : ((-1 : Total L) ^ (m j - 1)) ∈ TotalCompInt L 0 := by
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, totalCompInt_natCast]
      have := pow_mem_totalComp (neg_mem (one_mem_totalComp L)) (m j - 1)
      simpa using this
    have h3 : (MvPolynomial.C (Sym.elemSymm L (m j - 1)) : Total L)
        ∈ TotalCompInt L ((m j - 1 : ℕ) : ℤ) := by
      rw [totalCompInt_natCast]
      exact C_mem_totalComp (Sym.elemSymm_mem_lambdaComp L _)
    have h4 : (MvPolynomial.monomial (Finsupp.erase j m) (1 : Sym.Lambda L) : Total L)
        ∈ TotalCompInt L ((Finsupp.erase j m).degree : ℤ) := by
      rw [totalCompInt_natCast]
      simpa using monomial_mem_totalComp (Sym.one_mem_lambdaComp L) (Finsupp.erase j m)
    have hdeg : (Finsupp.erase j m).degree + m j = m.degree := by
      conv_rhs => rw [← Finsupp.erase_add_single j m]
      simp [Finsupp.degree_single]
    have h := mul_mem_totalCompInt h1 (mul_mem_totalCompInt (mul_mem_totalCompInt h2 h3) h4)
    have hidx : (d : ℤ) - (m.degree : ℤ) + (0 + ((m j - 1 : ℕ) : ℤ)
        + ((Finsupp.erase j m).degree : ℤ)) = (d : ℤ) - 1 := by
      have : ((m j - 1 : ℕ) : ℤ) = (m j : ℤ) - 1 := by omega
      rw [this]
      have h' : ((Finsupp.erase j m).degree : ℤ) + (m j : ℤ) = (m.degree : ℤ) := by
        exact_mod_cast hdeg
      linarith
    rwa [hidx] at h

/-- `dminusDown q k` is `lowerCoeffDown (k - 1)` after `qshiftNeg q k`. -/
theorem dminusDown_apply (q : L) (k : ℕ) (F : Total L) :
    dminusDown q k F = lowerCoeffDown L (k - 1) (qshiftNeg q k F) := rfl

/-- `dminusDown` lowers degree by one. -/
theorem isHom_dminusDown (q : L) (k : ℕ) : IsHom (-1) (dminusDown q k) := fun d F hF => by
  rw [← sub_eq_add_neg, dminusDown_apply]
  exact lowerCoeffDown_mem_totalCompInt _ (qshiftNeg_mem_totalComp q k hF)

/-- `d^*_+` preserves degree. -/
theorem isHom_dplusStar (q u : L) (k : ℕ) : IsHom 0 (dplusStar q u k) := fun d F hF => by
  rw [add_zero, totalCompInt_natCast, ← dplusStarAlg_eq_dplusStar]
  exact preservesTotalComp_dplusStarAlg q u k d F hF

end Down

/-! ### The renormalised composite shift and the four generator checks -/

section Psi

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The renormalised `τ^*_kτ_k`**: `Ψ_kF = (∏_{i ≤ k}(y_i-1))·ϑ(F)·E_k`, which is
`y_1⋯y_k·τ^*_kτ_kF` and needs no localisation. -/
noncomputable def psiAmb (q u : L) (k : ℕ) (F : Total L) : TotalHat L :=
  toHat (auxProd L k * unitShiftTotal L F) * cornerMultiplier q u k

/-- `Ψ_k` is additive. -/
theorem psiAmb_add (q u : L) (k : ℕ) (F G : Total L) :
    psiAmb q u k (F + G) = psiAmb q u k F + psiAmb q u k G := by
  rw [psiAmb, psiAmb, psiAmb, map_add, mul_add, toHat_add, add_mul]

theorem psiAmb_smul (q u : L) (k : ℕ) (r : L) (F : Total L) :
    psiAmb q u k (r • F) = r • psiAmb q u k F := by
  rw [psiAmb, psiAmb, map_smul, mul_smul_comm, toHat_smul, smul_mul_hat]

theorem psiAmb_neg (q u : L) (k : ℕ) (F : Total L) : psiAmb q u k (-F) = -psiAmb q u k F := by
  rw [← neg_one_smul L F, psiAmb_smul, neg_one_smul]

theorem psiAmb_sub (q u : L) (k : ℕ) (F G : Total L) :
    psiAmb q u k (F - G) = psiAmb q u k F - psiAmb q u k G := by
  rw [sub_eq_add_neg, psiAmb_add, psiAmb_neg, ← sub_eq_add_neg]

/-- **The check at `y_1`.** -/
theorem extRel_psiAmb_auxVar_one (q u : L) (k : ℕ) (F : Total L) :
    ExtRel (LinearMap.mulLeft L (auxVar 1 : Total L)) 1
      (psiAmb q u k ((auxVar 1 : Total L) * F)) (psiAmb q u k F) := by
  have hX : IsHom 1 (LinearMap.mulLeft L (auxVar 1 : Total L)) := by
    simpa using isHom_mulLeft (auxVar_mem_totalComp L 1)
  have h := extRel_toHat_mul hX (E := cornerMultiplier q u k) (E' := cornerMultiplier q u k)
    (fun H b => by rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_assoc])
    (auxProd L k * unitShiftTotal L F)
  rwa [LinearMap.mulLeft_apply, ← mul_assoc, mul_comm (auxVar 1 : Total L), mul_assoc,
    ← unitShiftTotal_auxVar 1, ← map_mul, unitShiftTotal_auxVar] at h

/-- **The check at `T_i`**, for `1 ≤ i` and `i + 1 ≤ k`. -/
theorem extRel_psiAmb_braid (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k) (F : Total L) :
    ExtRel (braidEnd q i) 0 (psiAmb q u k (braidEnd q i F)) (psiAmb q u k F) := by
  have h := extRel_toHat_mul (isHom_braidEnd q i) (E := cornerMultiplier q u k)
    (E' := cornerMultiplier q u k)
    (fun H b => by
      change braid q i (H * cornerAlphabet q u k _) = braid q i H * cornerAlphabet q u k _
      rw [mul_comm, braid_cornerAlphabet_mul q u hi hik, mul_comm])
    (auxProd L k * unitShiftTotal L F)
  have he : braidEnd q i (auxProd L k * unitShiftTotal L F)
      = auxProd L k * unitShiftTotal L (braidEnd q i F) := by
    change braid q i _ = _ * unitShiftTotal L (braid q i F)
    rw [braid_auxProd_mul q hi hik, unitShiftTotal_braid]
  rwa [he] at h

omit [Algebra ℚ L] in
/-- `T_i^{-1}` commutes with multiplication by an `s_i`-symmetric element. -/
theorem braidInv_symmetric_mul (q : L) {i : ℕ} {g : Total L} (hg : swapAux L i g = g)
    (F : Total L) : braidInv q i (g * F) = g * braidInv q i F := by
  rw [braidInv_apply, braidInv_apply, braid_symmetric_mul q hg]
  ring

omit [Algebra ℚ L] in
/-- The unit shift `ϑ` commutes with `T_i^{-1}`. -/
theorem unitShiftTotal_braidInv (q : L) (i : ℕ) (F : Total L) :
    unitShiftTotal L (braidInv q i F) = braidInv q i (unitShiftTotal L F) := by
  rw [braidInv_apply, braidInv_apply, map_mul, map_add, map_mul, unitShiftTotal_scal,
    unitShiftTotal_scal, unitShiftTotal_braid]

/-- **The check at `T_i^{-1}`**, for `1 ≤ i` and `i + 1 ≤ k`. -/
theorem extRel_psiAmb_braidInv (q u : L) {i k : ℕ} (hi : 1 ≤ i) (hik : i + 1 ≤ k)
    (F : Total L) :
    ExtRel (braidInvEnd q i) 0 (psiAmb q u k (braidInvEnd q i F)) (psiAmb q u k F) := by
  have h := extRel_toHat_mul (isHom_braidInvEnd q i) (E := cornerMultiplier q u k)
    (E' := cornerMultiplier q u k)
    (fun H b => by
      change braidInv q i (H * cornerAlphabet q u k _) = braidInv q i H * cornerAlphabet q u k _
      rw [mul_comm, braidInv_symmetric_mul q (swapAux_cornerAlphabet q u hi hik _), mul_comm])
    (auxProd L k * unitShiftTotal L F)
  have he : braidInvEnd q i (auxProd L k * unitShiftTotal L F)
      = auxProd L k * unitShiftTotal L (braidInvEnd q i F) := by
    change braidInv q i _ = _ * unitShiftTotal L (braidInv q i F)
    rw [braidInv_symmetric_mul q (swapAux_auxProd hi hik), unitShiftTotal_braidInv]
  rwa [he] at h

/-- **The check at `d_-`**: `Ψ_k(d_-F) = \widehat{dminusDown}(Ψ_{k+1}F)`, of degree `-1`. -/
theorem extRel_psiAmb_dminus (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ)
    (F : Total L) :
    ExtRel (dminusDown q (k + 1)) (-1) (psiAmb q u k (dminus q (k + 1) F))
      (psiAmb q u (k + 1) F) := by
  have h := extRel_toHat_mul (isHom_dminusDown q (k + 1)) (E := cornerMultiplier q u (k + 1))
    (E' := cornerMultiplier q u k)
    (fun H b => by
      rw [coe_cornerMultiplier, coe_cornerMultiplier, mul_comm,
        dminusDown_cornerAlphabet_mul q u hq, mul_comm])
    (auxProd L (k + 1) * unitShiftTotal L F)
  rwa [dminusDown_auxProd_unitShiftTotal] at h

/-- `(y_1 - 1)·d^*_+(∏_{i ≤ k}(y_i - 1)) = ∏_{i ≤ k+1}(y_i - 1)`. -/
theorem dplusStar_auxProd (q u : L) (k : ℕ) :
    (auxVar 1 - 1 : Total L) * dplusStar q u k (auxProd L k) = auxProd L (k + 1) := by
  rw [← dplusStarAlg_eq_dplusStar, auxProd, map_prod, auxProd, Finset.prod_range_succ']
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [map_sub, map_one, dplusStarAlg_auxVar q u (by omega) (by omega)]

/-- **The check at `d^*_+`**: `Ψ_{k+1}(d^*_+F) = -\widehat{d^*_+}(Ψ_kF)`. -/
theorem extRel_psiAmb_dplusStar (q u : L) (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1)
    (hu : ∀ r : ℕ, 1 ≤ r → u ^ r ≠ 1) (k : ℕ) (F : Total L) :
    ExtRel (-dplusStar q u k) 0 (psiAmb q u (k + 1) (dplusStar q u k F))
      (psiAmb q u k F) := by
  set G : Total L := auxProd L k * unitShiftTotal L F with hG
  have hhat : hatDplusStar q u k (toHat G) = toHat (dplusStar q u k G) :=
    TotalHat.ext fun n => by
      rw [hatDplusStar, coe_hatMap, extRel_toHat (isHom_dplusStar q u k) G n, extT,
        ite_eq_left (by omega), sub_zero, Int.toNat_natCast, coe_toHat,
        dplusStarAlg_eq_dplusStar]
  have e1 : dplusStar q u k G
      = dplusStar q u k (auxProd L k) * dplusStar q u k (unitShiftTotal L F) := by
    simp only [← dplusStarAlg_eq_dplusStar, hG, map_mul]
  have e2 : unitShiftTotal L (dplusStar q u k F) = dplusStar q u k (unitShiftTotal L F) := by
    simp only [← dplusStarAlg_eq_dplusStar, unitShiftTotal_dplusStarAlg]
  have hpoly : auxProd L (k + 1) * unitShiftTotal L (dplusStar q u k F)
      = (auxVar 1 : Total L) * dplusStar q u k G - dplusStar q u k G := by
    rw [e1, e2, ← dplusStar_auxProd q u k]
    ring
  have h1 : ∀ n : ℕ, (hatDplusStar q u k (psiAmb q u k F) n : Total L)
      = dplusStar q u k ((psiAmb q u k F) n) := fun n => by
    rw [hatDplusStar, coe_hatMap, dplusStarAlg_eq_dplusStar]
  have key : psiAmb q u (k + 1) (dplusStar q u k F)
      = -(hatDplusStar q u k (psiAmb q u k F)) := by
    change toHat _ * _ = -(hatDplusStar q u k (toHat G * cornerMultiplier q u k))
    rw [hatDplusStar_mul, hhat, hatDplusStar_cornerMultiplier q u hq hu k, hpoly, toHat_sub,
      toHat_mul_of_mem (auxVar_mem_totalComp L 1),
      show (TotalHat.ofComp (auxVar 1 : Total L) (auxVar_mem_totalComp L 1)) = auxVarOne L
        from rfl]
    ring
  intro n
  rw [key, extT, ite_eq_left (by omega), sub_zero, Int.toNat_natCast, LinearMap.neg_apply,
    ← h1]
  rfl

end Psi

end HJO.Mellit.LhsShift

end
