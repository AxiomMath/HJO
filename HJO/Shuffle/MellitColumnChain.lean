/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitDopCommutator
public meta import HJO.Attr

/-! # The `(a,1)` column inside the `D_n`-algebra at every `b`

`HJO/Shuffle/MellitVertexStepClosed.lean` closes one step of the `(a,1)` column's tower inside
the integer-indexed basic operators of `HJO.Sym.DopInt`
(`HJO.Sweep.dminus_auxVar_pow_mul_vertexStep_auxVar_pow_mul_dplusStar_C`) and iterates it once, to
`ψ_1 = ∑_{l ≥ 0}(qu)^lD_{1+l}D_{-l}` (`HJO.Sweep.psiCol_one_eq_sum_dopInt`). **This file iterates it
`b` times, at every `b`.**

## The chain

The composition law `HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum` says `T` acts on the
pairs `(j, g)` by `(j,g) ↦ ∑_{l ≥ 0}(qu)^l(l, D_{j-l}g)`, so the `b`-fold iterate is a `b`-fold
nested sum. `HJO.Sweep.chain` is that nest written as a recursion rather than as a sum over `ℕ^b`:

`chain 0 K j g = D_{K+j}g`,   `chain (b+1) K j g = ∑_{l ≥ 0}(qu)^l chain b K l (D_{j-l}g)`,

and `HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain` is

`d_-(y_1^KT^b(y_1^jd^*_+(Cg))) = C(chain b K j g)`

for every large enough truncation `R`. Unfolded, `chain b R 1 0 f` is

`∑_{l_1,…,l_b}(qu)^{l_1+⋯+l_b}D_{1+l_b}D_{l_{b-1}-l_b}⋯D_{l_1-l_2}D_{-l_1}f`,

the display of the module docstring of `HJO/Shuffle/MellitVertexStepClosed.lean`, and
`HJO.Sweep.psiCol_eq_chain` identifies it with `ψ_b`:

**`ψ_bf = C(chain b R 1 0 f)` for every large enough `R`.**

`HJO.Sweep.chain_zero_apply` and `HJO.Sweep.chain_one_apply` check the nest against the two known
values `ψ_0 = D_1` and `ψ_1 = ∑_l(qu)^lD_{1+l}D_{-l}`.

## Why the truncation is an existential

The composition law needs a range `[0,R]` large enough that `HJO.Sweep.bopExt` has already died on
the argument, and the argument changes at every level of the nest: level `b-1` is entered at the
`y_1`-degree `l` produced by level `b`, which ranges over the whole of `[0,R]`. A single `R` chosen
in advance therefore cannot be justified level by level. What makes the nest finite is instead that
`D_n` kills a fixed `g` once `n` is far enough below zero (`HJO.Sym.dopInt_eq_zero_of_lt`), so all
but finitely many `l` contribute `chain b R K l 0 = 0` (`HJO.Sweep.chain_zero_right`) on both sides.
The induction therefore takes a maximum over that finite set together with the one bound the outer
step needs, which is why every statement here reads `∃ R₀, ∀ R ≥ R₀`.

## What this is and is not

This is an **evaluation of `ψ_b`, not a proof of anything about it**: `HJO.Sweep.psiCol_eq_chain` is
the iterate of `HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain`, and it
carries the same hypotheses (`q ≠ 0`, `u ≠ 0`, `q ≠ 1`) as `HJO.Sweep.psiCol_eq`, from which it
inherits them. `HJO.Sweep.columnCommutes_at_iff_chain` then translates the clause of
`HJO.Sweep.ColumnCommutes` at a general `b` into an identity with no sweep operator in it,

`M·chain (b+1) R 1 0 f = chain b R 1 0 (D_0f) - D_0(chain b R 1 0 f)`,

**and that is an equivalence** — the same clause, restated with no sweep operator in it. It is the
exact statement the `χ`-telescope of
`HJO.Sym.smul_sum_sum_dopInt_dopInt`
is about, and **it is not proved here**: it is proved in
`HJO/Shuffle/MellitColumnChainTelescope.lean`, by an induction on `b` rather than by that
lemma's global telescope, which closes `HJO.Sweep.ColumnCommutes` (`HJO.Sweep.columnCommutes`) and
with it the `(a,1)` column of `HJO.Mellit.lhsRewrite_sweepWitness` at a general `f`
(`HJO.Sweep.lhsSlope_succ_one`).

## Genericity

`HJO.Sym.dopInt_eq_zero_of_lt`, `HJO.Sweep.chain` and `HJO.Sweep.chain_zero_right` carry no
hypothesis on `q` or `u`. `q ≠ 1` enters through the composition law, and `q ≠ 0`, `u ≠ 0` only
through `HJO.Sweep.psiCol_eq`, exactly as at `b ≤ 1`. Nothing here divides by `M`.

## Implementation notes

`HJO.Sweep.psiCol_eq_chain` iterates the one-step composition law, and
`HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain` is the iterate.
`HJO.Mellit.lhsRewrite_sweepWitness` is **not** proved here.
`HJO.Mellit.shuffle_of_lhs_and_induction` has two binders, `hlhs` and `hind`; nothing here touches
either, and `hlhs` is quantified over `1 < a < b`, so the `(a,1)` column is not an instance of it.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sym

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **`D_k` kills `f` once `k` is far enough below zero**: every term of the pairing carries
`c_{k+j}` with `j ≤ natDegree δ(f) < -k`, and the alternating elementary family
`HJO.Sym.esymmSigned` vanishes below `0`. The companion of
`HJO.Sym.bop_eq_zero_of_lt_neg_natDegree` for `HJO.Sym.DopInt`'s family, and what makes the `b`-fold
nest of the `(a,1)` column finite. -/
theorem dopInt_eq_zero_of_lt (q u : K) (f : Lambda K) {k : ℤ}
    (hk : k < -((plethShift q u f).natDegree : ℤ)) : DopInt q u k f = 0 := by
  have hN : ∀ j : ℕ, (plethShift q u f).natDegree + 1 ≤ j → (plethShift q u f).coeff j = 0 :=
    fun j hj => Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  change coeffPairing (fun j : ℕ => esymmSigned K (k + j)) (plethShift q u f) = 0
  rw [coeffPairing_eq_sum_range _ _ hN]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  have hjz : (j : ℤ) ≤ ((plethShift q u f).natDegree : ℤ) := by exact_mod_cast hj
  rw [esymmSigned_of_neg (by omega : k + (j : ℤ) < 0), mul_zero]

/-- The index below which `D_n` kills `f`, as an existential. -/
theorem exists_dopInt_eq_zero (q u : K) (f : Lambda K) :
    ∃ N : ℕ, ∀ k : ℤ, k < -(N : ℤ) → DopInt q u k f = 0 :=
  ⟨(plethShift q u f).natDegree, fun _ hk => dopInt_eq_zero_of_lt q u f hk⟩

end HJO.Sym

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The nest -/

/-- **The `b`-fold iterate of the composition law, as a recursion.**

`chain 0 K j g = D_{K+j}g` is the outer `d_-(y_1^{K+j}·)` of
`HJO.Sweep.dminus_auxVar_pow_mul_dplusStar_C`, and

`chain (b+1) K j g = ∑_{l ≤ R}(qu)^l chain b K l (D_{j-l}g)`

is one application of `HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum`, which sends the pair
`(j,g)` to `∑_l(qu)^l(l, D_{j-l}g)`. `R` is the truncation of every level; the sum is independent of
it once it is large enough (`HJO.Sweep.psiCol_eq_chain`). -/
noncomputable def chain (q u : L) (R K : ℕ) : ℕ → ℕ → Sym.Lambda L → Sym.Lambda L
  | 0, j, g => Sym.DopInt q u ((K : ℤ) + (j : ℤ)) g
  | b + 1, j, g => ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
      chain q u R K b l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)

theorem chain_zero (q u : L) (R K j : ℕ) (g : Sym.Lambda L) :
    chain q u R K 0 j g = Sym.DopInt q u ((K : ℤ) + (j : ℤ)) g := rfl

theorem chain_succ (q u : L) (R K b j : ℕ) (g : Sym.Lambda L) :
    chain q u R K (b + 1) j g
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          chain q u R K b l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g) := rfl

/-- **The nest is zero on the zero function**, at every depth. This is what lets the induction
ignore the levels entered at a `y_1`-degree so high that `D_{j-l}` has already killed the
argument. -/
theorem chain_zero_right (q u : L) (R K : ℕ) (b : ℕ) : ∀ j : ℕ, chain q u R K b j 0 = 0 := by
  induction b with
  | zero => intro j; rw [chain_zero, map_zero]
  | succ c ih =>
      intro j
      rw [chain_succ]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [map_zero, ih l, smul_zero]

/-! ### The iterate -/

/-- **The `b`-fold tower of the `(a,1)` column, closed inside the integer-indexed basic
operators.** For every `K, j, b` and every large enough truncation `R`,

`d_-(y_1^KT^b(y_1^jd^*_+(Cg))) = C(chain b K j g)`.

The induction is on `b`. The outer step is the composition law
`HJO.Sweep.vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum`, whose hypothesis is supplied by
`HJO.Sweep.exists_forall_bopExt_dplusStar_coeff_eq_zero`; the inner steps are the inductive
hypothesis at the finitely many `l` for which `D_{j-l}g ≠ 0` (`HJO.Sym.dopInt_eq_zero_of_lt`), all
higher `l` contributing `0 = C(chain b K l 0)` on both sides
(`HJO.Sweep.chain_zero_right`). -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain (hq1 : q ≠ 1) (b K j : ℕ)
    (g : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      dminus q 1 ((auxVar 1 : Total L) ^ K
          * (vertexStep q u ^ b) ((auxVar 1 : Total L) ^ j
              * dplusStar q u 0 (MvPolynomial.C g : Total L)))
        = MvPolynomial.C (chain q u R K b j g) := by
  induction b generalizing j g with
  | zero =>
      refine ⟨0, fun R _ => ?_⟩
      rw [pow_zero, Module.End.one_apply, ← mul_assoc, ← pow_add,
        dminus_auxVar_pow_mul_dplusStar_C, chain_zero, ← Sym.dopInt_natCast,
        show ((K + j : ℕ) : ℤ) = (K : ℤ) + (j : ℤ) from by push_cast; ring]
  | succ c ih =>
      classical
      obtain ⟨R₁, hR₁⟩ := exists_forall_bopExt_dplusStar_coeff_eq_zero q u j
        (dplusStar q u 0 (MvPolynomial.C g : Total L))
      set N : ℕ := (Sym.plethShift q u g).natDegree with hN
      choose R₂ hR₂ using fun l : ℕ => ih (j := l) (g := Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)
      refine ⟨max R₁ ((Finset.range (j + N + 1)).sup R₂), fun R hR => ?_⟩
      have hRone : R₁ ≤ R := le_trans (le_max_left _ _) hR
      have hRtwo : ∀ l : ℕ, l ≤ j + N → R₂ l ≤ R :=
        fun l hl => le_trans (Finset.le_sup (f := R₂) (Finset.mem_range.2 (by omega)))
          (le_trans (le_max_right _ _) hR)
      have hstep := vertexStep_auxVar_pow_mul_dplusStar_C_eq_sum (q := q) (u := u) hq1 j R g
        (hR₁ R hRone)
      rw [pow_succ, Module.End.mul_apply, hstep, map_sum, Finset.mul_sum, map_sum, chain_succ,
        map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, mul_smul_comm, map_smul, C_smul]
      refine congrArg (fun x => ((q * u) ^ l) • x) ?_
      rcases le_or_gt l (j + N) with hl | hl
      · exact hR₂ l R (hRtwo l hl)
      · have hz : Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g = 0 :=
          Sym.dopInt_eq_zero_of_lt q u g (by
            rw [← hN]
            omega)
        rw [hz]
        simp [chain_zero_right]

/-- **`ψ_b` inside the `D_n`-algebra, at every `b`:** for every large enough truncation `R`,

`ψ_bf = C(chain b 1 0 f)`
`     = C(∑_{l_1,…,l_b}(qu)^{l_1+⋯+l_b}D_{1+l_b}D_{l_{b-1}-l_b}⋯D_{l_1-l_2}D_{-l_1}f)`.

The case `K = 1`, `j = 0` of the iterate, composed with
`HJO.Sweep.psiCol_eq`. `HJO.Sweep.psiCol_one_eq_sum_dopInt` is the case `b = 1`. -/
@[hjo "lem_mellit_vertex_closed_form"]
theorem psiCol_eq_chain (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ) (f : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      psiCol q u b f = MvPolynomial.C (chain q u R 1 b 0 f) := by
  obtain ⟨R₀, hR₀⟩ :=
    exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain (q := q) (u := u) hq1 b 1 0 f
  refine ⟨R₀, fun R hR => ?_⟩
  have h := hR₀ R hR
  rw [pow_zero, one_mul, pow_one] at h
  rw [psiCol_eq hq0 hu0 hq1 b f]
  exact h

/-! ### The nest against the two known values -/

/-- `chain 0 1 0 = D_1`, which is `HJO.Sweep.psiCol_zero`. -/
theorem chain_zero_apply (q u : L) (R : ℕ) (f : Sym.Lambda L) :
    chain q u R 1 0 0 f = Sym.Dop q u 1 f := by
  rw [chain_zero, Nat.cast_one, Nat.cast_zero, add_zero, ← Sym.dopInt_natCast]
  norm_num

/-- `chain 1 1 0 = ∑_{l ≤ R}(qu)^lD_{1+l}D_{-l}`, which is
`HJO.Sweep.psiCol_one_eq_sum_dopInt`. -/
theorem chain_one_apply (q u : L) (R : ℕ) (f : Sym.Lambda L) :
    chain q u R 1 1 0 f
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          Sym.DopInt q u (1 + (l : ℤ)) (Sym.DopInt q u (-(l : ℤ)) f) := by
  rw [chain_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [chain_zero, Nat.cast_one, Nat.cast_zero, zero_sub]

/-! ### The clause of the commutation at a general `b`, with no sweep operator in it -/

/-- **The clause of `HJO.Sweep.ColumnCommutes` at a general `b` is an identity in the
`D_n`-algebra:**

`M·chain (b+1) 1 0 f = chain b 1 0 (D_0f) - D_0(chain b 1 0 f)`.

`ψ_b` and `ψ_{b+1}` are the nest (`HJO.Sweep.psiCol_eq_chain`) and `A = d^*_+d_-` computes `D_0` on
`V_0` (`HJO.Sweep.dop_zero_eq_dminus_dplusStar`), so nothing of the sweep module survives.

**This is an equivalence.** It is the `b`-fold generalisation of
`HJO.Sweep.columnCommutes_zero_at_iff_dopInt`, and like it, it is a translation rather than a proof.
What it buys is that the statement now lives where `HJO.Sym.smul_sum_sum_dopInt_dopInt` --- the
commutator of a single pair at every pair of integer indices --- is available. That it holds at
`b ≥ 1` is proved in `HJO/Shuffle/MellitColumnChainTelescope.lean`. -/
theorem columnCommutes_at_iff_chain (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ)
    (f : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ((((1 - q) * (1 - u)) • psiCol q u (b + 1) f
          = psiCol q u b (Sym.Dop q u 0 f)
            - dminus q 1 (dplusStar q u 0 (psiCol q u b f)))
        ↔ ((1 - q) * (1 - u)) • chain q u R 1 (b + 1) 0 f
            = chain q u R 1 b 0 (Sym.Dop q u 0 f)
              - Sym.Dop q u 0 (chain q u R 1 b 0 f)) := by
  obtain ⟨R₁, hR₁⟩ := psiCol_eq_chain (q := q) (u := u) hq0 hu0 hq1 (b + 1) f
  obtain ⟨R₂, hR₂⟩ := psiCol_eq_chain (q := q) (u := u) hq0 hu0 hq1 b f
  obtain ⟨R₃, hR₃⟩ := psiCol_eq_chain (q := q) (u := u) hq0 hu0 hq1 b (Sym.Dop q u 0 f)
  refine ⟨max R₁ (max R₂ R₃), fun R hR => ?_⟩
  have h1 := hR₁ R (le_trans (le_max_left _ _) hR)
  have h2 := hR₂ R (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR)
  have h3 := hR₃ R (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR)
  rw [h1, h2, h3, ← dop_zero_eq_dminus_dplusStar, ← C_smul, ← map_sub]
  exact ⟨fun h => MvPolynomial.C_injective ℕ (Sym.Lambda L) h, fun h => congrArg MvPolynomial.C h⟩

end HJO.Sweep

end
