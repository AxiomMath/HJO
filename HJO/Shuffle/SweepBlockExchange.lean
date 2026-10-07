/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepRoundBoundary
public import HJO.Shuffle.SweepAppendOneB
public meta import HJO.Attr

/-!
# The base layer is bilinear: its exponent is named, and the identity becomes an operator identity

`HJO.Mellit.exists_layerWord_shiftAux_of_sorted` transports a base layer past the shift
`Σ_δ = HJO.Sweep.shiftAux`, producing a power of `q` and a staircase. Its exponent is
**existentially quantified after `g` and `F`**, so that statement does not record that the
exponent is the same for every `g` and every `F`. It is: reading the induction rule by rule, types
`A`, `B` and `E` leave the exponent alone, type `C` lowers it by `δ` and type `D` raises it by `δ`,
so the exponent is

`δ · (#D(ℓ) − #C(ℓ))`,

an integer depending only on the layer. That is `HJO.Mellit.dcBalance` below, and
`HJO.Mellit.layerWord_shiftAux_of_sorted` is the same transport with it written out.

## Why naming the exponent is what was missing

With the exponent named, the identity is **bilinear**: both the exponent `s` and the staircase
height `m = HJO.Mellit.acCount z ℓ` depend only on `z`, `ℓ` and `δ`, and neither slot carries a
rank-one condition. So the identity survives summation in *both* arguments
(`HJO.Mellit.layerWord_shiftAux_sum`), and summation is what turns it from a statement about vectors
of the special shape `g·Σ_δF` into a statement about the **whole graded piece**: by
`HJO.Sweep.exists_mul_shiftAux_of_monomial` every `y`-monomial of `V_{k+δ}` is of that shape, so
every vector of `V_{k+δ}` is a finite sum of such, and

`BL_ℓ = q^{δ(#D−#C)} · S_{0,m} ∘ (id ⊗ W_ℓ)`

on `V_{k+δ}`, where `id ⊗ W_ℓ` acts on a decomposition `∑ᵢ gᵢ·Σ_δFᵢ` by
`∑ᵢ gᵢ·Σ_δ(W_ℓFᵢ)` — `HJO.Mellit.layerWord_shiftAux_piece`. **Had the exponent stayed under the
existential this would have been false as stated**, since a different `q`-power per monomial cannot
be pulled out of the sum.

What is *not* claimed is that `id ⊗ W_ℓ` is a well-defined operator on `V_{k+δ}` independently of
the decomposition. That is a separate fact about
`HJO.Sweep.pieceTensorAlgEquiv` and is not needed here: the identity above holds for *every*
decomposition, and `HJO.Mellit.exists_decomp_piece` produces one for every vector, which is what the
reconciliation consumes.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*,
sections 4 and 6.
-/

@[expose] public section

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {a b N : ℕ}

/-! ### The exponent of a layer -/

/-- **THE EXPONENT THE BASE LAYER EMITS, per unit of `δ`**: the number of type-`D` events of a list
of lattice points less the number of type-`C` events. Those are exactly the two rules whose operator
is a scalar power of `q` relative to the base's own — rule `D` reads at a raised width and rule `C`
carries `q^{-sweepRight}` — and the two shifts are `+δ` and `−δ`. -/
@[hjo "lem_sweep_layer_shift_append"]
def dcBalance (z : Heights a b N) (ℓ : List (ℕ × ℕ)) : ℤ :=
  (ℓ.countP fun Q => decide (eventType z Q = EventType.D)) -
    (ℓ.countP fun Q => decide (eventType z Q = EventType.C))

@[simp] theorem dcBalance_nil (z : Heights a b N) : dcBalance z [] = 0 := by simp [dcBalance]

variable {z : Heights a b N} {x : ℕ × ℕ}

theorem dcBalance_cons_of_A (ℓ : List (ℕ × ℕ)) (hx : eventType z x = EventType.A) :
    dcBalance z (x :: ℓ) = dcBalance z ℓ := by simp [dcBalance, hx]

theorem dcBalance_cons_of_B (ℓ : List (ℕ × ℕ)) (hx : eventType z x = EventType.B) :
    dcBalance z (x :: ℓ) = dcBalance z ℓ := by simp [dcBalance, hx]

theorem dcBalance_cons_of_C (ℓ : List (ℕ × ℕ)) (hx : eventType z x = EventType.C) :
    dcBalance z (x :: ℓ) = dcBalance z ℓ - 1 := by
  simp only [dcBalance, List.countP_cons, hx]
  push_cast
  simp
  ring

theorem dcBalance_cons_of_D (ℓ : List (ℕ × ℕ)) (hx : eventType z x = EventType.D) :
    dcBalance z (x :: ℓ) = dcBalance z ℓ + 1 := by
  simp only [dcBalance, List.countP_cons, hx]
  push_cast
  simp
  ring

theorem dcBalance_cons_of_E (ℓ : List (ℕ × ℕ)) (hx : eventType z x = EventType.E) :
    dcBalance z (x :: ℓ) = dcBalance z ℓ := by simp [dcBalance, hx]

/-! ### The base layer with its exponent named -/

section Layer

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {A : ℕ}
  {z : Heights a b N} {w : Heights a b A}

/-- **THE BASE LAYER PROPAGATION, WITH ITS EXPONENT NAMED.** This is
`HJO.Mellit.exists_layerWord_shiftAux_of_sorted` with the existential discharged: the exponent is
`δ · HJO.Mellit.dcBalance z ℓ`, an integer read off the layer alone.

`(∏_{P ∈ ℓ} O^{ext}_P)(g·Σ_δF) = q^{δ(#D−#C)} · S_{0,m}(g·Σ_δ((∏_{P ∈ ℓ} O^{base}_P)F))`

The difference from the existential statement is not cosmetic. There the exponent is bound *after*
`g` and `F`, so nothing rules out its depending on them, and the identity cannot be summed over a
decomposition of a vector into monomials. Here it manifestly does not, and
`HJO.Mellit.layerWord_shiftAux_sum` is the consequence. -/
@[hjo "lem_sweep_layer_shift_append"]
theorem layerWord_shiftAux_of_sorted (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L δ) (F : Total L) :
    ∀ ℓ : List (ℕ × ℕ), (∀ P ∈ ℓ, P ∈ sweptRegion z) → (∀ P ∈ ℓ, P.1 < a * N) →
      (∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ) →
      ℓ.Pairwise (fun P Q => P.1 < Q.1) →
      (∀ P ∈ ℓ, ∀ Q ∈ ℓ, diagExcess a b P = diagExcess a b Q) →
        (ℓ.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
          = q ^ (δ * dcBalance z ℓ) • stairWord q δ 0 (acCount z ℓ)
              (g * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod F)) := by
  intro ℓ
  induction ℓ with
  | nil => intro _ _ _ _ _; simp
  | cons x t ih =>
    intro hreg hlow hδ hsort hexc
    have hsortt : t.Pairwise (fun P Q => P.1 < Q.1) := (List.pairwise_cons.1 hsort).2
    have hxlt : ∀ Q ∈ t, x.1 < Q.1 := (List.pairwise_cons.1 hsort).1
    have heq := ih
      (fun P hP => hreg P (List.mem_cons_of_mem _ hP))
      (fun P hP => hlow P (List.mem_cons_of_mem _ hP))
      (fun P hP => hδ P (List.mem_cons_of_mem _ hP)) hsortt
      (fun P hP Q hQ => hexc P (List.mem_cons_of_mem _ hP) Q (List.mem_cons_of_mem _ hQ))
    have hxmem : x ∈ x :: t := List.mem_cons_self ..
    have hlowx : x.1 < a * N := hlow x hxmem
    have hδx : #(tailLiveSteps w (diagExcess a b x)) = δ := hδ x hxmem
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact absurd hlowx (by simp [h])
      · exact h
    have hndt : t.Nodup := hsortt.imp (fun {P Q} h => by intro hPQ; rw [hPQ] at h; omega)
    have hm : acCount z t ≤ sweepRight z x :=
      acCount_le_sweepRight hN ha hlowx.le hndt
        (fun Q hQ => hreg Q (List.mem_cons_of_mem _ hQ))
        (fun Q hQ => hlow Q (List.mem_cons_of_mem _ hQ)) hxlt
        (fun Q hQ => (hexc x hxmem Q (List.mem_cons_of_mem _ hQ)).symm)
    have hmw : acCount z t ≤ sweepWidth z x := hm.trans (sweepRight_le_sweepWidth z x)
    have hwext : sweepWidth (appendHeights z w) x = sweepWidth z x + δ := by
      rw [sweepWidth_appendHeights_eq hz hw hN hlowx, hδx]
    have hgpx : g ∈ piece L (#(tailLiveSteps w (diagExcess a b x))) := by rw [hδx]; exact hgp
    have htyp : eventType (appendHeights z w) x = eventType z x :=
      eventType_appendHeights (by omega)
    have hbA : acCount z t + δ ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
    set Y : Total L := (t.map (sweepOperator q u z)).prod F with hY
    have hLc : ((x :: t).map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = sweepOperator q u (appendHeights z w) x
            ((t.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)) := by
      rw [List.map_cons, List.prod_cons]; rfl
    have hRc : ((x :: t).map (sweepOperator q u z)).prod F = sweepOperator q u z x Y := by
      rw [List.map_cons, List.prod_cons, hY]; rfl
    cases hevx : eventType z x with
    | A =>
      have hac : acCount z (x :: t) = acCount z t + 1 := acCount_cons_of_ac t (Or.inl hevx)
      have hev := sweepOperator_shiftAux_appendHeights_A (q := q) (u := u) hz hw hN hlowx hevx
        hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, dcBalance_cons_of_A t hevx, hLc, heq, map_smul,
        sweepOperator_stairWord_A (htyp.trans hevx) hbA, hev,
        stairWord_succ_shift_zero_apply, hRc]
    | B =>
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hlt : acCount z t < sweepWidth z x :=
        hm.trans_lt (sweepRight_lt_sweepWidth_of_eventType_B_or_C (Or.inl hevx))
      have hbB : acCount z t + δ + 1 ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
      have hev := sweepOperator_shiftAux_appendHeights_B (q := q) (u := u) hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, dcBalance_cons_of_B t hevx, hLc, heq, map_smul,
        sweepOperator_stairWord_B (htyp.trans hevx) hbB, hev, hRc]
    | C =>
      have hac : acCount z (x :: t) = acCount z t + 1 := acCount_cons_of_ac t (Or.inr hevx)
      have hlt : acCount z t < sweepWidth z x :=
        hm.trans_lt (sweepRight_lt_sweepWidth_of_eventType_B_or_C (Or.inr hevx))
      have hbB : acCount z t + δ + 1 ≤ sweepWidth (appendHeights z w) x := by rw [hwext]; omega
      have hev := sweepOperator_shiftAux_appendHeights_C (q := q) (u := u) hq hz hw hN hlowx
        (by omega) hevx hgaux hgpx Y
      rw [hδx] at hev
      rw [hac, dcBalance_cons_of_C t hevx, hLc, heq, map_smul,
        sweepOperator_stairWord_C (htyp.trans hevx) hbB, hev, map_smul,
        stairWord_succ_shift_zero_apply, hRc, smul_smul, ← zpow_add₀ hq]
      congr 2
      ring
    | D =>
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hev := sweepOperator_shiftAux_appendHeights_D (q := q) (u := u) hz hw hN hlowx hevx g Y
      rw [hδx] at hev
      rw [hac, dcBalance_cons_of_D t hevx, hLc, heq, map_smul,
        sweepOperator_stairWord_D (htyp.trans hevx), hev, map_smul,
        hRc, smul_smul, ← zpow_natCast q δ, ← zpow_add₀ hq]
      congr 2
      ring
    | E =>
      have hac : acCount z (x :: t) = acCount z t := acCount_cons_of_not_ac t (by simp [hevx])
      have hev := sweepOperator_shiftAux_appendHeights_E (q := q) (u := u) (z := z) (w := w)
        (by omega) hevx g Y
      rw [hδx] at hev
      rw [hac, dcBalance_cons_of_E t hevx, hLc, heq, map_smul,
        sweepOperator_stairWord_E (htyp.trans hevx), hev, hRc]

/-- The earlier existential form is a corollary: nothing is lost by naming the exponent. -/
theorem exists_layerWord_shiftAux_of_sorted' (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L δ) (F : Total L) (ℓ : List (ℕ × ℕ))
    (hreg : ∀ P ∈ ℓ, P ∈ sweptRegion z) (hlow : ∀ P ∈ ℓ, P.1 < a * N)
    (hδ : ∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ)
    (hsort : ℓ.Pairwise (fun P Q => P.1 < Q.1))
    (hexc : ∀ P ∈ ℓ, ∀ Q ∈ ℓ, diagExcess a b P = diagExcess a b Q) :
    ∃ s : ℤ,
      (ℓ.map (sweepOperator q u (appendHeights z w))).prod (g * shiftAux L δ F)
        = q ^ s • stairWord q δ 0 (acCount z ℓ)
            (g * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod F)) :=
  ⟨δ * dcBalance z ℓ,
    layerWord_shiftAux_of_sorted hq hz hw hN δ hgaux hgp F ℓ hreg hlow hδ hsort hexc⟩

/-! ### Bilinearity: the identity survives summation -/

/-- **THE BASE LAYER IS BILINEAR IN THE TWO BLOCKS.** The exponent and the staircase height depend
only on `z`, `ℓ` and `δ`, so they come out of a sum: for any finite family `(gᵢ, Fᵢ)` with each `gᵢ`
a `Λ`-free vector of `V_δ`,

`BL_ℓ(∑ᵢ gᵢ·Σ_δFᵢ) = q^{δ(#D−#C)} · S_{0,m}(∑ᵢ gᵢ·Σ_δ(W_ℓFᵢ))`.

There is **no rank-one condition in either slot** — nothing is assumed about the family beyond the
two block memberships of each `gᵢ`. This is the step the existential form blocks: a per-term
exponent could not be pulled out of the sum. -/
@[hjo "lem_sweep_layer_shift_piece"]
theorem layerWord_shiftAux_sum (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (δ : ℕ) {ι : Type*} (t : Finset ι) (g F : ι → Total L)
    (hgaux : ∀ i ∈ t, g i ∈ auxSubalg L) (hgp : ∀ i ∈ t, g i ∈ piece L δ)
    (ℓ : List (ℕ × ℕ)) (hreg : ∀ P ∈ ℓ, P ∈ sweptRegion z) (hlow : ∀ P ∈ ℓ, P.1 < a * N)
    (hδ : ∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ)
    (hsort : ℓ.Pairwise (fun P Q => P.1 < Q.1))
    (hexc : ∀ P ∈ ℓ, ∀ Q ∈ ℓ, diagExcess a b P = diagExcess a b Q) :
    (ℓ.map (sweepOperator q u (appendHeights z w))).prod (∑ i ∈ t, g i * shiftAux L δ (F i))
      = q ^ (δ * dcBalance z ℓ) • stairWord q δ 0 (acCount z ℓ)
          (∑ i ∈ t, g i * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod (F i))) := by
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact layerWord_shiftAux_of_sorted hq hz hw hN δ (hgaux i hi) (hgp i hi) (F i) ℓ hreg hlow hδ
    hsort hexc

/-! ### Every vector of the graded piece is a sum of two-block vectors -/

section Decomp

variable {L : Type*} [Field L]

/-- **THE TWO-BLOCK DECOMPOSITION OF A WHOLE GRADED PIECE.** Every `x ∈ V_{k+δ}` is a finite sum
`∑ᵢ gᵢ·Σ_δFᵢ` with each `gᵢ` a `Λ`-free vector of `V_δ` and each `Fᵢ ∈ V_k`, indexed by the
exponents of `x`.

This is `HJO.Sweep.exists_mul_shiftAux_of_monomial` summed over `MvPolynomial.support`: the
monomial splitting is what makes the base layer's form cover the graded piece rather than a subspace
of it, and the sum is legitimate because the base layer's identity is bilinear. -/
@[hjo "lem_sweep_shift_split"]
theorem exists_decomp_piece (k δ : ℕ) {x : Total L} (hx : x ∈ piece L (k + δ)) :
    ∃ (t : Finset (ℕ →₀ ℕ)) (g F : (ℕ →₀ ℕ) → Total L),
      (∀ d ∈ t, g d ∈ auxSubalg L) ∧ (∀ d ∈ t, g d ∈ piece L δ) ∧
        (∀ d ∈ t, F d ∈ piece L k) ∧ x = ∑ d ∈ t, g d * shiftAux L δ (F d) := by
  classical
  -- every exponent of `x` is supported below `k + δ`
  have hsupp : ∀ d ∈ x.support, ∀ j, k + δ ≤ j → d j = 0 := by
    intro d hd j hj
    by_contra hne
    have hj' : j ∈ x.vars := by
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨d, hd, Finsupp.mem_support_iff.2 hne⟩
    have := (MvPolynomial.mem_supported.1 hx) hj'
    simp only [Set.mem_Iio] at this
    omega
  -- split each monomial of `x`
  have hchoice : ∀ d ∈ x.support, ∃ gF : Total L × Total L,
      gF.1 ∈ auxSubalg L ∧ gF.1 ∈ piece L δ ∧ gF.2 ∈ piece L k ∧
        (MvPolynomial.monomial d (MvPolynomial.coeff d x) : Total L)
          = gF.1 * shiftAux L δ gF.2 := by
    intro d hd
    obtain ⟨g, F, h1, h2, h3, h4⟩ :=
      exists_mul_shiftAux_of_monomial (L := L) δ k (hsupp d hd) (MvPolynomial.coeff d x)
    exact ⟨(g, F), h1, h2, h3, h4⟩
  choose! gF hg1 hg2 hg3 hg4 using hchoice
  refine ⟨x.support, fun d => (gF d).1, fun d => (gF d).2, hg1, hg2, hg3, ?_⟩
  rw [← Finset.sum_congr rfl hg4]
  exact (MvPolynomial.as_sum x)

end Decomp

/-! ### THE OPERATOR FORM ON THE WHOLE GRADED PIECE -/

/-- **THE BASE LAYER AS AN OPERATOR IDENTITY ON THE GRADED PIECE `V_{k+δ}`.** For every vector `x`
of `V_{k+δ}` there is a two-block decomposition `x = ∑ᵢ gᵢ·Σ_δFᵢ` with each `gᵢ` a `Λ`-free vector
of `V_δ` and each `Fᵢ ∈ V_k`, on which

`BL_ℓ(x) = q^{δ(#D−#C)} · S_{0,m}(∑ᵢ gᵢ·Σ_δ(W_ℓFᵢ))`,

with `m = HJO.Mellit.acCount z ℓ` and the exponent `δ · HJO.Mellit.dcBalance z ℓ` — **both read off
the layer alone, neither depending on `x`**. In operator notation this is

`BL_ℓ = q^{s_ℓ} · S_{0,m_ℓ} ∘ (id ⊗ W_ℓ)`

on the whole graded piece, the base's own word `W_ℓ` acting in the high block and the low block
carried along untouched.

Two things are deliberately not claimed. The decomposition is produced, not asserted unique, and
`id ⊗ W_ℓ` is not asserted to be a decomposition-independent operator — that is a statement about
`HJO.Sweep.pieceTensorAlgEquiv`, and the reconciliation does not need it, since the identity holds
for every decomposition and one exists for every vector. -/
@[hjo "lem_sweep_layer_shift_piece"]
theorem layerWord_shiftAux_piece (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) (k δ : ℕ) {x : Total L} (hx : x ∈ piece L (k + δ))
    (ℓ : List (ℕ × ℕ)) (hreg : ∀ P ∈ ℓ, P ∈ sweptRegion z) (hlow : ∀ P ∈ ℓ, P.1 < a * N)
    (hδ : ∀ P ∈ ℓ, #(tailLiveSteps w (diagExcess a b P)) = δ)
    (hsort : ℓ.Pairwise (fun P Q => P.1 < Q.1))
    (hexc : ∀ P ∈ ℓ, ∀ Q ∈ ℓ, diagExcess a b P = diagExcess a b Q) :
    ∃ (t : Finset (ℕ →₀ ℕ)) (g F : (ℕ →₀ ℕ) → Total L),
      (∀ d ∈ t, g d ∈ auxSubalg L) ∧ (∀ d ∈ t, g d ∈ piece L δ) ∧
        (∀ d ∈ t, F d ∈ piece L k) ∧ x = ∑ d ∈ t, g d * shiftAux L δ (F d) ∧
        (ℓ.map (sweepOperator q u (appendHeights z w))).prod x
          = q ^ (δ * dcBalance z ℓ) • stairWord q δ 0 (acCount z ℓ)
              (∑ d ∈ t, g d * shiftAux L δ ((ℓ.map (sweepOperator q u z)).prod (F d))) := by
  obtain ⟨t, g, F, hg1, hg2, hg3, hxeq⟩ := exists_decomp_piece k δ hx
  refine ⟨t, g, F, hg1, hg2, hg3, hxeq, ?_⟩
  rw [hxeq]
  exact layerWord_shiftAux_sum hq hz hw hN δ t g F hg1 hg2 ℓ hreg hlow hδ hsort hexc

end Layer

/-! ### THE ROUND-BOUNDARY PASS BOUND IS FALSE: the staircase cannot be carried outward

`HJO.Mellit.tailRoundWord_stairWord` carries a staircase across a tail layer under the side
condition `c + #AC(ℓ) + m + δ + 1 ≤ k^w(p) + β` at every point of the layer. The base layer's own
width condition is **automatic** — `HJO.Mellit.acCount_le_sweepRight` discharges it by injecting the
layer's type-`A`-or-`C` events into the live steps to its right. This one is not: it couples the
emitting round's `m` and `δ` to a *later* round's width and `β`, and the counts run the wrong way.

The refutation below is on `a = 2`, `b = 3`, `N = A = 1` — the smallest instance with `1 < a < b`
and a genuine tail — at `z = w = HJO.Mellit.baseTwoThreeB`, the path `(0,3,3)`. Its round `6` is a
single type-`A` base event, so the base layer emits `S_{0,1}` at `δ = 1`; round `5` is empty, so
that staircase arrives at round `4` with its offset still `0`; and round `4`'s tail layer is the
single type-`C` point `(0,2)`, whose width plus `β_4` is `2`. The bound asks `3 ≤ 2`.

**And the failure is not the harmless kind.** A staircase all of whose letters sit strictly above
the current grading is the identity: `HJO.Sweep.swapAux_of_mem_piece` fixes a vector of `V_k` under
`s_i` as soon as `k + 1 ≤ i`, and `HJO.Sweep.braid_of_swapAux_eq` then makes each letter the
identity. Here the arriving staircase is `HJO.Sweep.stairWord q 1 0 1`, which by
`HJO.Sweep.stairWord_one` and `HJO.Sweep.cmAscWord_self` is the single letter `T_1`, and the grading
at the point is `2`: the escape hatch would need `2 + 1 ≤ 1`. So the overlap is real and no lemma
proved so far covers it.

## What the witness rules out is the *one-step* reading too, which is the stronger statement

One might hope the accumulation is the only problem — that a staircase need only be carried across
the **first** tail layer below the round that emitted it, and then be absorbed rather than
transported further. The witness closes that hope as well, and this is the point of
`HJO.Mellit.round_five_baseTwoThreeB_empty`: round `5` of `HJO.Mellit.baseTwoThreeB` is empty, so
round `4` **is** the first tail layer the round-`6` staircase meets. It fails at the first boundary,
with nothing accumulated: the offset is still `0`.

So neither reading is available, and the failure is not a matter of bookkeeping drift. It is also
not a gross mismatch — it fails by exactly one unit of width (`3 ≤ 2`), and at the sibling paths of
the same rectangle the one-step bound is *tight* rather than false. Whatever performs the round
boundary therefore has to change the two-block decomposition itself, not commute a staircase past an
operator; and re-decomposing by `HJO.Mellit.exists_decomp_piece` is not that, because it loses the
identification of the high block with the base's own partially computed vector, which is the whole
content of the identity being proved.
-/

section RoundStairRefuted

variable {L : Type*} [Field L]

/-- **The shift is not constant across rounds at `1 < a < b` either.** On the `2 × 3` path
`(0,2,3)` the round shifts are `δ_1 = 1` and `δ_2 = 2`. The lemma
`HJO.Paths.card_tailLiveSteps_ne_succ` says this at `a = 1`, where every north step is live in
exactly one round; this says it in the range the binder `hind` of
`HJO.Mellit.shuffle_of_lhs_and_induction` actually quantifies over, where a step is live for `a`
consecutive rounds. Consequence: `HJO.Sweep.stairWord_succ_shift` cannot fold the accumulated
correction back into one staircase, since it requires the fresh block to carry the same `δ`. -/
@[hjo "not_sweep_round_stair_single"]
theorem card_tailLiveSteps_baseTwoThreeA_ne_succ :
    #(tailLiveSteps baseTwoThreeA 1) ≠ #(tailLiveSteps baseTwoThreeA (1 + 1)) := by decide

/-- **The two shifts of the round boundary differ.** The base layer's index shift is
`δ_e = #(HJO.Paths.tailLiveSteps w e)` and the tail layer's is
`β_e = #(HJO.Paths.baseLiveSteps z e)`; at `z = w = HJO.Mellit.baseTwoThreeA` and `e = 1` they are
`1` and `2`. This is the mismatch the block exchange has to cross, and it is not a degeneracy: the
two windows are `[e-a, e)` and `(e-a, e]`, so they differ whenever the excesses `e - a` and `e` are
both attained. -/
@[hjo "not_sweep_round_stair_single"]
theorem card_tailLiveSteps_ne_card_baseLiveSteps :
    #(tailLiveSteps baseTwoThreeA 1) ≠ #(baseLiveSteps baseTwoThreeA 1) := by decide

/-- The staircase the base layer of round `6` of `HJO.Mellit.baseTwoThreeB` emits has `δ = 1`: its
`HJO.Paths.tailLiveSteps` at level `6` is a single north step. -/
theorem card_tailLiveSteps_baseTwoThreeB_six : #(tailLiveSteps baseTwoThreeB 6) = 1 := by decide

/-- **AT THE WITNESS PATH THE SHIFT IS CONSTANT, so the two halves of the refutation are
independent.** On `HJO.Mellit.baseTwoThreeB` the shift `δ_e` is `1` at *every* round the round
boundary sees — `HJO.Mellit.tailRoundWord_stairWord` requires `0 < e`, and `δ_e = 1` for all
`1 ≤ e ≤ 6`. Since `δ` depends only on the tail path, the same holds for both ordered pairs whose
tail is this path.

So the `HJO.Sweep.stairWord_succ_shift` folding obstruction is **absent here**: it needs `δ` to
vary, and `HJO.Mellit.card_tailLiveSteps_baseTwoThreeA_ne_succ` supplies a path where it does — the
*other* one, `(0,2,3)`. The refutation of carrying outward
(`HJO.Mellit.not_tailRoundWord_stairWord_bound`) therefore does not rest on non-constancy of `δ` and
stands on its own; conversely a treatment that only repaired the folding would still fail here. -/
theorem card_tailLiveSteps_baseTwoThreeB_const (e : ℕ) (h1 : 1 ≤ e) (h6 : e ≤ 6) :
    #(tailLiveSteps baseTwoThreeB (e : ℤ)) = 1 := by
  interval_cases e <;> decide

/-- The witness path is legitimate: `HJO.Mellit.baseTwoThreeB` is one of the two above-diagonal
paths of the `2 × 3` rectangle with return composition `(1)`
(`HJO.Mellit.aboveReturnPaths_two_three_one`), so `HJO.Paths.appendHeights` of it with itself is an
above-diagonal path of the `4 × 6` rectangle and every hypothesis of
`HJO.Mellit.tailRoundWord_stairWord` other than the pass bound is met. -/
theorem isAboveDiagonal_baseTwoThreeB : IsAboveDiagonal baseTwoThreeB :=
  hasAboveReturns_baseTwoThreeB.1

/-- The separating level `HJO.Mellit.sepLevel 2 1` cuts the swept region of
`HJO.Mellit.baseTwoThreeB` at the diagonal, which is the decidable form of the index set
(`HJO.Mellit.sweptAbove_eq_filter`). Everything below is a kernel computation through this. -/
theorem sweptAbove_baseTwoThreeB :
    sweptAbove baseTwoThreeB (sepLevel 2 1)
      = {P ∈ sweptRegion baseTwoThreeB | 3 * P.1 < 2 * P.2} :=
  sweptAbove_eq_filter (separatesDiagonal_sepLevel (by norm_num)) _

/-- …and height `m = 1`: the base layer of round `6` is a single type-`A` event. This is
`HJO.Mellit.acCount` in its `Finset` form, the one
`HJO.Mellit.acCount_le_sweepRight` translates to. -/
theorem card_baseRound_ac_baseTwoThreeB_six :
    #{P ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 P = 6 ∧
        (eventType baseTwoThreeB P = EventType.A ∨
          eventType baseTwoThreeB P = EventType.C)} = 1 := by
  rw [sweptAbove_baseTwoThreeB]; decide

/-- Round `5` of `HJO.Mellit.baseTwoThreeB` is empty, so the staircase emitted at round `6` reaches
round `4` with its offset still `0`. -/
theorem round_five_baseTwoThreeB_empty :
    {P ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 P = 5} = ∅ := by
  rw [sweptAbove_baseTwoThreeB]; decide

/-- **The arrival point.** Round `4` of `HJO.Mellit.baseTwoThreeB` is the single point `(0,2)`, a
type-`C` event, and the index its raised operator is read at — its own width plus
`β_4 = #(HJO.Paths.baseLiveSteps z 4)` — is `2`. -/
theorem tailRound_four_baseTwoThreeB :
    {p ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 p = 4} = {(0, 2)} ∧
      eventType baseTwoThreeB ((0, 2) : ℕ × ℕ) = EventType.C ∧
      sweepWidth baseTwoThreeB ((0, 2) : ℕ × ℕ) + #(baseLiveSteps baseTwoThreeB 4) = 2 := by
  refine ⟨?_, by decide, by decide⟩
  rw [sweptAbove_baseTwoThreeB]; decide

/-- **THE ROUND-BOUNDARY PASS BOUND IS FALSE.** The side condition of
`HJO.Mellit.tailRoundWord_stairWord` fails at round `4` of `z = w = HJO.Mellit.baseTwoThreeB`, for
**every** staircase of positive height and positive `δ` — in particular for the one the base layer
of round `6` emits, whose `m` and `δ` are both `1` by
`HJO.Mellit.card_baseRound_ac_baseTwoThreeB_six` and
`HJO.Mellit.card_tailLiveSteps_baseTwoThreeB_six`, and which arrives at offset `0` because round `5`
is empty (`HJO.Mellit.round_five_baseTwoThreeB_empty`).

So the base layer's staircases **cannot be carried outward across the following layers**: unlike the
base layer's own width condition, this one is not discharged by the geometry, and it is not
discharged because it is untrue. The correction has to be absorbed into the two-block decomposition
round by round instead. Nothing is assumed of `q` or `u`: this is a fact about the two paths. -/
@[hjo "not_sweep_round_stair_single"]
theorem not_tailRoundWord_stairWord_bound {m δ : ℕ} (hm : 1 ≤ m) (hδ : 1 ≤ δ) :
    ¬ ∀ p ∈ sortByRank 2 3 1
          {p ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 p = 4},
        0 + acCount baseTwoThreeB (sortByRank 2 3 1
              {p ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 p = 4})
            + m + δ + 1 ≤ sweepWidth baseTwoThreeB p + #(baseLiveSteps baseTwoThreeB 4) := by
  intro h
  have hmem : ((0, 2) : ℕ × ℕ) ∈ sortByRank 2 3 1
      {p ∈ sweptAbove baseTwoThreeB (sepLevel 2 1) | diagExcess 2 3 p = 4} :=
    mem_sortByRank.2 (by rw [sweptAbove_baseTwoThreeB]; decide)
  have hgrad : sweepWidth baseTwoThreeB ((0, 2) : ℕ × ℕ)
      + #(baseLiveSteps baseTwoThreeB 4) = 2 := by decide
  have := h _ hmem
  omega

/-- **The failure overlaps the grading, so it is not removable.** The arriving staircase
`HJO.Sweep.stairWord q 1 0 1` is the single letter `T_1` (`HJO.Sweep.stairWord_one`,
`HJO.Sweep.cmAscWord_self`). For `HJO.Sweep.swapAux_of_mem_piece` to make it act as the identity on
the grading at the arrival point it would need `k + 1 ≤ 1` with `k = 2`, and that is false. So the
staircase that cannot be carried is not one that could have been dropped. -/
@[hjo "not_sweep_round_stair_single"]
theorem not_swapAux_bound_baseTwoThreeB :
    ¬ sweepWidth baseTwoThreeB ((0, 2) : ℕ × ℕ) + #(baseLiveSteps baseTwoThreeB 4) + 1 ≤ 1 := by
  decide

/-- The letter that has to cross, named: at `δ = 1` and height `1` the staircase is `T_1`. -/
theorem stairWord_one_one_zero (q : L) : stairWord q 1 0 1 = braidEnd q 1 := by
  rw [stairWord_one]; simp

end RoundStairRefuted

end HJO.Mellit
