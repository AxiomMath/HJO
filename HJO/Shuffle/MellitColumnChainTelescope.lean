/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitColumnChainLeibniz
public meta import HJO.Attr

/-! # The commutation of the `(a,1)` column, at every `b`

`HJO/Shuffle/MellitColumnChain.lean` puts `ψ_b` inside the `D_n`-algebra as the nest
`HJO.Sweep.chain`, and `HJO/Shuffle/MellitColumnChainLeibniz.lean` commutes `D_0` past it: with
`HJO.Sweep.chainComm` for `ψ_bD_0 - D_0ψ_b` read in the nest, the clause of
`HJO.Sweep.ColumnCommutes` at `b` is `M·chain (b+1) 1 0 f = chainComm b 1 0 f`, and `chainComm`
satisfies the Leibniz recursion `HJO.Sweep.chainComm_succ`. **This file closes that clause, at every
`b`.** Hence `HJO.Sweep.ColumnCommutes` (`HJO.Sweep.columnCommutes`), and hence the `(a,1)`
column of `HJO.Mellit.lhsRewrite_sweepWitness` at a general `f` (`HJO.Sweep.lhsSlope_succ_one`).

## Not the `χ`-telescope: an induction on `b`

The usual argument is a **global** collection: Leibniz produces one term per position
of the word, the coefficient of a fixed target word gets a contribution
`∑_e χ_{p+1}(χ_p - χ_{p+2})(qu)^e` from position `p`, and the sum over `p = 0,…,b` telescopes. That
is a reindexing across all `b+1` levels of the nest at once, and it is not what is done here.

What is done here is an **induction on `b`**, which the global shape of the telescope seemed to rule
out --- and which the obvious generalisation does rule out: the clause read at a general starting
index, `chainComm b 1 j g = M·chain (b+1) 1 j g`, is **false at every `j ≥ 1`**. The generalisation
that works keeps the index and changes the **coefficient**, from the single power `(qu)^l` to the
geometric run `HJO.Sweep.chainGeomCoeff`

`c(l,j) = (qu)^{l-min(j,l)} + ⋯ + (qu)^l`,

giving `HJO.Sweep.chainGeom` and
**`HJO.Sweep.exists_forall_chainComm_eq_smul_chainGeom`: `chainComm b 1 j g = M·chainGeom b j g`**
for every `b`, every `j` and every large enough truncation. At `j = 0` the run is the single power
again (`HJO.Sweep.chainGeom_zero_eq_chain`), so this *is* the clause; at `j ≥ 1` the `min` is the
whole difference, and it is already visible at `b = 0`
(`HJO.Sweep.chainComm_zero_eq_smul_chainGeom`, proved in the Leibniz file).

## Why the induction closes

Leibniz (`HJO.Sweep.chainComm_succ`) writes `chainComm (b+1) 1 j g` as
`∑_l(qu)^l(chain b 1 l (dopComm (j-l) g) + chainComm b 1 l (D_{j-l}g))`. The inductive hypothesis
turns the second summand into `M·chainGeom b l (D_{j-l}g)`, and both it and the target then run over
the same words `HJO.Sweep.chainWord`, indexed by the **two adjacent levels** `(l_1,l_2)` at which
the new letter is inserted. So the `b`-fold global collection is replaced by a two-level one, done
once: `HJO.Sweep.chain_dopComm_eq` expands the pair commutator at `(j-l_2,0)` --- above, below,
or the vanishing case `l_2 = j` --- and regroups its geometric double sum by the total index
(`HJO.Sweep.sum_range_sum_range_smul_shift`).

What is left is a scalar identity in one variable `qu`: for every `(l_1,l_2,j)`,

`ε·(qu)^{l_2}·Γ + (qu)^{l_1}·c(l_2,l_1) = (qu)^{l_2}·c(l_1,j)`,

with `Γ` the coefficient the commutator contributes and `ε` the sign of the branch. Every term is a
contiguous run of powers of `qu` (`HJO.Sweep.powRun`), and the identity is in each of its cases one
application of `HJO.Sweep.powRun_add`, `G(m+n) = G(m) + (qu)^m·G(n)`
--- `HJO.Sweep.pow_mul_chainGeomCoeff_comm` where `Γ` is absent,
`HJO.Sweep.chainGeomCoeff_step_pos` and `HJO.Sweep.chainGeomCoeff_step_neg` where it is not. The
signs of the two branches are not a case distinction in the result: both produce the same run, which
is why the identity is uniform in the position of `l_2` relative to `j`.

## Genericity

The induction itself carries **no hypothesis on `q`, `u` or `M`**: `M` is a coefficient throughout,
produced by the pair commutator, and nothing divides by it. `HJO.Sweep.columnCommutes` carries
`q ≠ 0`, `u ≠ 0` and `q ≠ 1`, all three inherited from `HJO.Sweep.psiCol_eq` --- `q ≠ 1` from
`HJO.Sweep.zop`'s scalar `q/(1-q)`, and `q ≠ 0`, `u ≠ 0` because `Z = (qu)^{-1}z_1` is the zero map
there. `M ≠ 0` enters only at `HJO.Sweep.lhsSlope_succ_one`, where `HJO.Sym.Qop` divides by `M` to
define `Q_{b+2,1}`, and it is not removable there.

## What this closes and what it does not

`HJO.Sweep.ColumnCommutes` is closed, and with it `HJO.Mellit.LhsSlope q u (b+1) 1` at every `b` ---
the whole `(a,1)` column of `HJO.Mellit.lhsRewrite_sweepWitness` at a general `f`, not only
`b ≤ 1` (and `f = e_1`, `f = e_2` in low degree). **`HJO.Mellit.lhsRewrite_sweepWitness` itself is
not proved here** (it is proved in `HJO/Shuffle/ShuffleClosed.lean`): it is stated at a general
slope, and the `(a,1)` column is one column of it.
**`HJO.Mellit.shuffle_of_lhs_and_induction` has exactly two binders, `hlhs` and `hind`, and neither
is touched**: `hind` is untouched outright, and `hlhs` is quantified over `1 < a → a < b`, so its
slopes have `b ≥ 3` while this column has `b = 1` --- **no slope of this column is an instance of
`hlhs`.**

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3, for `HJO.Sym.DopInt`, `HJO.Sym.Qop`,
`HJO.Sweep.zop`, `HJO.Sym.smul_sum_sum_dopInt_dopInt`, `HJO.Sweep.dop_zero_eq_dminus_dplusStar` and
`HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain`.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The nest is linear in its argument (continued) -/


theorem chain_smul (q u : L) (R K : ℕ) (b : ℕ) : ∀ (j : ℕ) (a : L) (g : Sym.Lambda L),
    chain q u R K b j (a • g) = a • chain q u R K b j g := by
  induction b with
  | zero => intro j a g; rw [chain_zero, chain_zero, map_smul]
  | succ c ih =>
      intro j a g
      rw [chain_succ, chain_succ, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, ih, smul_comm]

theorem chain_sum (q u : L) (R K b j : ℕ) {ι : Type*} (s : Finset ι) (F : ι → Sym.Lambda L) :
    chain q u R K b j (∑ x ∈ s, F x) = ∑ x ∈ s, chain q u R K b j (F x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, chain_zero_right]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, chain_add, ih]

theorem chain_neg (q u : L) (R K b j : ℕ) (g : Sym.Lambda L) :
    chain q u R K b j (-g) = -chain q u R K b j g := by
  have h := chain_sub q u R K b j 0 g
  rwa [zero_sub, chain_zero_right, zero_sub] at h

theorem chainGeom_zero_right (q u : L) (R b j : ℕ) : chainGeom q u R b j 0 = 0 := by
  rw [chainGeom]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [map_zero, chain_zero_right, smul_zero]

theorem chainComm_zero_right (q u : L) (R K b j : ℕ) : chainComm q u R K b j 0 = 0 := by
  rw [chainComm, map_zero, chain_zero_right, map_zero, sub_self]



/-! ### Runs of powers, and the scalar identity behind the step -/


/-- A contiguous run of `n` powers of `t` starting at `t^a`. -/
noncomputable def powRun (t : L) (a n : ℕ) : L := ∑ r ∈ Finset.range n, t ^ (a + r)

omit [Algebra ℚ L] in
theorem powRun_add (t : L) (a m n : ℕ) :
    powRun t a (m + n) = powRun t a m + powRun t (a + m) n := by
  rw [powRun, powRun, powRun, Finset.sum_range_add]
  refine congrArg (fun x => (∑ r ∈ Finset.range m, t ^ (a + r)) + x) ?_
  exact Finset.sum_congr rfl fun r _ => by rw [Nat.add_assoc]

omit [Algebra ℚ L] in
theorem pow_mul_powRun (t : L) (k a n : ℕ) : t ^ k * powRun t a n = powRun t (k + a) n := by
  rw [powRun, powRun, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [← pow_add, Nat.add_assoc]

omit [Algebra ℚ L] in
theorem chainGeomCoeff_eq_powRun (q u : L) (j l : ℕ) :
    chainGeomCoeff q u j l = powRun (q * u) (l - min j l) (min j l + 1) := rfl

omit [Algebra ℚ L] in
/-- The guard-false case of the step's scalar identity. -/
theorem pow_mul_chainGeomCoeff_comm (q u : L) (j l₁ l₂ : ℕ)
    (hmin : min j l₁ = min l₁ l₂) :
    (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂ = (q * u) ^ l₂ * chainGeomCoeff q u j l₁ := by
  rw [chainGeomCoeff_eq_powRun, chainGeomCoeff_eq_powRun, pow_mul_powRun, pow_mul_powRun, hmin]
  have h1 : min l₁ l₂ ≤ l₂ := min_le_right l₁ l₂
  have h2 : min l₁ l₂ ≤ l₁ := min_le_left l₁ l₂
  congr 1
  omega

omit [Algebra ℚ L] in
/-- The guard-true case above `0`. -/
theorem chainGeomCoeff_step_pos (q u : L) (j l₁ l₂ : ℕ) (hj : l₂ < j) (hl : l₂ < l₁) :
    (q * u) ^ l₂ * chainGeomCoeff q u (j - l₂ - 1) (l₁ - l₂ - 1)
        + (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂
      = (q * u) ^ l₂ * chainGeomCoeff q u j l₁ := by
  rw [chainGeomCoeff_eq_powRun, chainGeomCoeff_eq_powRun, chainGeomCoeff_eq_powRun,
    pow_mul_powRun, pow_mul_powRun, pow_mul_powRun]
  have hm : min (j - l₂ - 1) (l₁ - l₂ - 1) = min j l₁ - l₂ - 1 := by omega
  have hml : min l₁ l₂ = l₂ := by omega
  have hmu : min j l₁ ≤ l₁ := min_le_right j l₁
  have hmu2 : l₂ < min j l₁ := by omega
  have hsplit := powRun_add (q * u) (l₁ + l₂ - min j l₁) (min j l₁ - l₂) (l₂ + 1)
  rw [show l₁ + l₂ - min j l₁ + (min j l₁ - l₂) = l₁ from by omega] at hsplit
  rw [hm, hml]
  rw [show l₂ + (l₁ - l₂ - 1 - (min j l₁ - l₂ - 1)) = l₁ + l₂ - min j l₁ from by omega,
    show min j l₁ - l₂ - 1 + 1 = min j l₁ - l₂ from by omega,
    show l₁ + (l₂ - l₂) = l₁ from by omega,
    show l₂ + (l₁ - min j l₁) = l₁ + l₂ - min j l₁ from by omega,
    show min j l₁ + 1 = (min j l₁ - l₂) + (l₂ + 1) from by omega]
  exact hsplit.symm

omit [Algebra ℚ L] in
/-- The guard-true case below `0`, with its sign. -/
theorem chainGeomCoeff_step_neg (q u : L) (j l₁ l₂ : ℕ) (hj : j < l₂) (hl : j < l₁) :
    -((q * u) ^ l₂ * chainGeomCoeff q u (l₂ - j - 1) (l₁ - j - 1))
        + (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂
      = (q * u) ^ l₂ * chainGeomCoeff q u j l₁ := by
  rw [chainGeomCoeff_eq_powRun, chainGeomCoeff_eq_powRun, chainGeomCoeff_eq_powRun,
    pow_mul_powRun, pow_mul_powRun, pow_mul_powRun]
  have hm : min (l₂ - j - 1) (l₁ - j - 1) = min l₁ l₂ - j - 1 := by omega
  have hmj : min j l₁ = j := by omega
  have hnu : min l₁ l₂ ≤ l₂ := min_le_right l₁ l₂
  have hnu2 : j < min l₁ l₂ := by omega
  have hsplit := powRun_add (q * u) (l₁ + l₂ - min l₁ l₂) (min l₁ l₂ - j) (j + 1)
  rw [show l₁ + l₂ - min l₁ l₂ + (min l₁ l₂ - j) = l₁ + l₂ - j from by omega] at hsplit
  rw [hm, hmj]
  rw [show l₂ + (l₁ - j - 1 - (min l₁ l₂ - j - 1)) = l₁ + l₂ - min l₁ l₂ from by omega,
    show min l₁ l₂ - j - 1 + 1 = min l₁ l₂ - j from by omega,
    show l₁ + (l₂ - min l₁ l₂) = l₁ + l₂ - min l₁ l₂ from by omega,
    show l₂ + (l₁ - j) = l₁ + l₂ - j from by omega,
    show min l₁ l₂ + 1 = (min l₁ l₂ - j) + (j + 1) from by omega, hsplit]
  ring



/-! ### Regrouping a geometric double sum after a shift -/


omit [Algebra ℚ L] in
theorem sum_range_smul_shift_eq (A : ℕ → L) (m R : ℕ) (F : ℕ → Sym.Lambda L)
    (hF : ∀ l : ℕ, R < l → F l = 0) :
    ∑ s ∈ Finset.range (R + 1), (A s) • F (m + s)
      = ∑ l ∈ Finset.range (R + 1), (if m ≤ l then A (l - m) else 0) • F l := by
  classical
  have hIco : ∑ l ∈ Finset.Ico m (m + (R + 1)), (A (l - m)) • F l
      = ∑ s ∈ Finset.range (R + 1), (A s) • F (m + s) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun s _ => by rw [Nat.add_sub_cancel_left]
  have hcut : ∑ l ∈ Finset.Ico m (m + (R + 1)), (A (l - m)) • F l
      = ∑ l ∈ Finset.Ico m (R + 1), (A (l - m)) • F l := by
    refine (Finset.sum_subset (fun l hl => ?_) (fun l hl hnl => ?_)).symm
    · rw [Finset.mem_Ico] at hl ⊢
      omega
    · rw [Finset.mem_Ico] at hl hnl
      rw [hF l (by omega), smul_zero]
  have hfilter : (Finset.range (R + 1)).filter (fun l => m ≤ l) = Finset.Ico m (R + 1) := by
    refine Finset.ext fun l => ?_
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← hIco, hcut, ← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · rw [zero_smul]

omit [Algebra ℚ L] in
theorem sum_range_sum_range_smul_shift (t : L) (m J R : ℕ) (F : ℕ → Sym.Lambda L)
    (hF : ∀ l : ℕ, R < l → F l = 0) :
    ∑ i ∈ Finset.range (J + 1), ∑ c ∈ Finset.range (R + 1), (t ^ c) • F (m + 1 + i + c)
      = ∑ l ∈ Finset.range (R + 1),
          (if m + 1 ≤ l then ∑ i ∈ Finset.range (min J (l - (m + 1)) + 1), t ^ (l - (m + 1) - i)
            else 0) • F l := by
  have hF' : ∀ s : ℕ, R < s → F (m + 1 + s) = 0 := fun s hs => hF _ (by omega)
  have hA := sum_range_sum_range_smul_eq_sum_range t J R (fun s => F (m + 1 + s)) hF'
  have hA' : ∑ i ∈ Finset.range (J + 1), ∑ c ∈ Finset.range (R + 1), (t ^ c) • F (m + 1 + i + c)
      = ∑ s ∈ Finset.range (R + 1),
          (∑ i ∈ Finset.range (min J s + 1), t ^ (s - i)) • F (m + 1 + s) := by
    refine Eq.trans ?_ hA
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show m + 1 + i + c = m + 1 + (i + c) from by omega]
  rw [hA', sum_range_smul_shift_eq _ (m + 1) R F hF]



/-! ### The two-level collection, and the induction -/



/-- One word of the nest of depth `c+1`, indexed by the two adjacent levels it splits at. -/
noncomputable def chainWord (q u : L) (R c j l₁ l₂ : ℕ) (g : Sym.Lambda L) : Sym.Lambda L :=
  chain q u R 1 c l₂ (Sym.DopInt q u ((l₁ : ℤ) - (l₂ : ℤ))
    (Sym.DopInt q u ((j : ℤ) - (l₁ : ℤ)) g))

theorem chain_dopComm_eq (q u : L) (g : Sym.Lambda L) {T : ℕ}
    (hT : (Sym.plethShift q u g).natDegree < T) (c j : ℕ) {R : ℕ} (hR : j + T + 1 ≤ R)
    (hvan : ∀ l : ℕ, R < l → Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g = 0) (l₂ : ℕ) :
    ((q * u) ^ l₂) • chain q u R 1 c l₂ (dopComm q u ((j : ℤ) - (l₂ : ℤ)) g)
      = ((1 - q) * (1 - u)) • ∑ l₁ ∈ Finset.range (R + 1),
          (chainGeomCoeff q u j l₁ * (q * u) ^ l₂
              - (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂)
            • chainWord q u R c j l₁ l₂ g := by
  have hvanW : ∀ l₁ : ℕ, R < l₁ → chainWord q u R c j l₁ l₂ g = 0 := by
    intro l₁ hl₁
    rw [chainWord, hvan l₁ hl₁, map_zero, chain_zero_right]
  rcases lt_trichotomy l₂ j with hlt | heq | hgt
  · -- l₂ < j : the commutator above zero
    have hexp := dopComm_eq_smul_sum_sum q u g hT
      (n := (j : ℤ) - (l₂ : ℤ)) (by omega) (R := R) (by omega) (by omega)
    have hrange : ((j : ℤ) - (l₂ : ℤ)).toNat = (j - l₂ - 1) + 1 := by omega
    have hin : ∀ i ∈ Finset.range ((j - l₂ - 1) + 1),
        chain q u R 1 c l₂ (∑ cc ∈ Finset.range (R + 1), ((q * u) ^ cc) •
            Sym.DopInt q u (1 + (i : ℤ) + (cc : ℤ))
              (Sym.DopInt q u ((j : ℤ) - (l₂ : ℤ) - 1 - (i : ℤ) - (cc : ℤ)) g))
          = ∑ cc ∈ Finset.range (R + 1), ((q * u) ^ cc) •
              chainWord q u R c j (l₂ + 1 + i + cc) l₂ g := by
      intro i _
      rw [chain_sum]
      refine Finset.sum_congr rfl fun cc _ => ?_
      rw [chain_smul, chainWord,
        show (1 : ℤ) + (i : ℤ) + (cc : ℤ) = ((l₂ + 1 + i + cc : ℕ) : ℤ) - (l₂ : ℤ) from by
          push_cast; ring,
        show (j : ℤ) - (l₂ : ℤ) - 1 - (i : ℤ) - (cc : ℤ)
            = (j : ℤ) - ((l₂ + 1 + i + cc : ℕ) : ℤ) from by push_cast; ring]
    rw [hexp, hrange, chain_smul, chain_sum, Finset.sum_congr rfl hin,
      sum_range_sum_range_smul_shift (q * u) l₂ (j - l₂ - 1) R
        (fun l₁ => chainWord q u R c j l₁ l₂ g) hvanW]
    conv_lhs => rw [smul_comm ((q * u) ^ l₂) ((1 - q) * (1 - u)), Finset.smul_sum]
    refine congrArg (fun x => ((1 - q) * (1 - u)) • x)
      (Finset.sum_congr rfl fun l₁ _ => ?_)
    rw [smul_smul]
    refine congrArg (fun a : L => a • chainWord q u R c j l₁ l₂ g) ?_
    split_ifs with hl
    · rw [show (∑ i ∈ Finset.range (min (j - l₂ - 1) (l₁ - (l₂ + 1)) + 1),
            (q * u) ^ (l₁ - (l₂ + 1) - i))
          = chainGeomCoeff q u (j - l₂ - 1) (l₁ - l₂ - 1) from by
        rw [chainGeomCoeff_eq_sum]
        exact Finset.sum_congr (by rw [show l₁ - (l₂ + 1) = l₁ - l₂ - 1 from by omega])
          fun i _ => by rw [show l₁ - (l₂ + 1) - i = l₁ - l₂ - 1 - i from by omega]]
      linear_combination chainGeomCoeff_step_pos q u j l₁ l₂ hlt (by omega)
    · rw [mul_zero]
      linear_combination pow_mul_chainGeomCoeff_comm q u j l₁ l₂ (by omega)
  · -- l₂ = j : the commutator sits at index 0 and vanishes
    subst heq
    rw [show (l₂ : ℤ) - (l₂ : ℤ) = 0 from by ring, dopComm, sub_self, chain_zero_right, smul_zero,
      show (0 : Sym.Lambda L) = ((1 - q) * (1 - u)) • (0 : Sym.Lambda L) from by rw [smul_zero]]
    refine congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_
    refine (Finset.sum_eq_zero fun l₁ _ => ?_).symm
    rw [show chainGeomCoeff q u l₂ l₁ * (q * u) ^ l₂
          - (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂ = 0 from by
        linear_combination -pow_mul_chainGeomCoeff_comm q u l₂ l₁ l₂ (by omega), zero_smul]
  · -- j < l₂ : the commutator below zero
    have hexp := dopComm_eq_neg_smul_sum_sum q u g hT
      (n := (j : ℤ) - (l₂ : ℤ)) (by omega) (R := R) (by omega)
    have hrange : (-((j : ℤ) - (l₂ : ℤ))).toNat = (l₂ - j - 1) + 1 := by omega
    have hin : ∀ i ∈ Finset.range ((l₂ - j - 1) + 1),
        chain q u R 1 c l₂ (∑ cc ∈ Finset.range (R + 1), ((q * u) ^ cc) •
            Sym.DopInt q u ((j : ℤ) - (l₂ : ℤ) + 1 + (i : ℤ) + (cc : ℤ))
              (Sym.DopInt q u (-1 - (i : ℤ) - (cc : ℤ)) g))
          = ∑ cc ∈ Finset.range (R + 1), ((q * u) ^ cc) •
              chainWord q u R c j (j + 1 + i + cc) l₂ g := by
      intro i _
      rw [chain_sum]
      refine Finset.sum_congr rfl fun cc _ => ?_
      rw [chain_smul, chainWord,
        show (j : ℤ) - (l₂ : ℤ) + 1 + (i : ℤ) + (cc : ℤ)
            = ((j + 1 + i + cc : ℕ) : ℤ) - (l₂ : ℤ) from by push_cast; ring,
        show (-1 : ℤ) - (i : ℤ) - (cc : ℤ)
            = (j : ℤ) - ((j + 1 + i + cc : ℕ) : ℤ) from by push_cast; ring]
    rw [hexp, hrange, chain_neg, chain_smul, chain_sum, Finset.sum_congr rfl hin,
      sum_range_sum_range_smul_shift (q * u) j (l₂ - j - 1) R
        (fun l₁ => chainWord q u R c j l₁ l₂ g) hvanW]
    conv_lhs => rw [smul_neg, smul_comm ((q * u) ^ l₂) ((1 - q) * (1 - u)), Finset.smul_sum,
      ← smul_neg, ← Finset.sum_neg_distrib]
    refine congrArg (fun x => ((1 - q) * (1 - u)) • x)
      (Finset.sum_congr rfl fun l₁ _ => ?_)
    rw [smul_smul, ← neg_smul]
    refine congrArg (fun a : L => a • chainWord q u R c j l₁ l₂ g) ?_
    split_ifs with hl
    · rw [show (∑ i ∈ Finset.range (min (l₂ - j - 1) (l₁ - (j + 1)) + 1),
            (q * u) ^ (l₁ - (j + 1) - i))
          = chainGeomCoeff q u (l₂ - j - 1) (l₁ - j - 1) from by
        rw [chainGeomCoeff_eq_sum]
        exact Finset.sum_congr (by rw [show l₁ - (j + 1) = l₁ - j - 1 from by omega])
          fun i _ => by rw [show l₁ - (j + 1) - i = l₁ - j - 1 - i from by omega]]
      linear_combination chainGeomCoeff_step_neg q u j l₁ l₂ hgt (by omega)
    · rw [mul_zero, neg_zero]
      linear_combination pow_mul_chainGeomCoeff_comm q u j l₁ l₂ (by omega)



theorem exists_forall_chainComm_eq_smul_chainGeom (q u : L) (b : ℕ) :
    ∀ (j : ℕ) (g : Sym.Lambda L), ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      chainComm q u R 1 b j g = ((1 - q) * (1 - u)) • chainGeom q u R b j g := by
  induction b with
  | zero =>
      intro j g
      refine ⟨j + (Sym.plethShift q u g).natDegree + 2, fun R hR => ?_⟩
      exact chainComm_zero_eq_smul_chainGeom q u g
        (T := (Sym.plethShift q u g).natDegree + 1) (by omega) j (by omega)
  | succ c ih =>
      intro j g
      classical
      set N := (Sym.plethShift q u g).natDegree with hN
      choose S hS using fun l : ℕ => ih l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)
      refine ⟨max (j + N + 2) ((Finset.range (j + N + 1)).sup S), fun R hR => ?_⟩
      have hRb : j + N + 2 ≤ R := le_trans (le_max_left _ _) hR
      have hvanN : ∀ l : ℕ, j + N < l → Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g = 0 := by
        intro l hl
        refine Sym.dopInt_eq_zero_of_lt q u g ?_
        rw [← hN]
        omega
      have hvan : ∀ l : ℕ, R < l → Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g = 0 :=
        fun l hl => hvanN l (by omega)
      have hIH : ∀ l : ℕ,
          chainComm q u R 1 c l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)
            = ((1 - q) * (1 - u)) •
                chainGeom q u R c l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g) := by
        intro l
        rcases le_or_gt l (j + N) with hl | hl
        · refine hS l R (le_trans (le_trans ?_ (le_max_right _ _)) hR)
          exact Finset.le_sup (f := S) (Finset.mem_range.2 (by omega))
        · rw [hvanN l hl, chainComm_zero_right, chainGeom_zero_right, smul_zero]
      rw [chainComm_succ]
      have hsplit : ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
            (chain q u R 1 c l (dopComm q u ((j : ℤ) - (l : ℤ)) g)
              + chainComm q u R 1 c l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g))
          = (∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
              chain q u R 1 c l (dopComm q u ((j : ℤ) - (l : ℤ)) g))
            + ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
                chainComm q u R 1 c l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => smul_add _ _ _
      have hP1 : ∑ l₂ ∈ Finset.range (R + 1), ((q * u) ^ l₂) •
            chain q u R 1 c l₂ (dopComm q u ((j : ℤ) - (l₂ : ℤ)) g)
          = ((1 - q) * (1 - u)) • ∑ l₂ ∈ Finset.range (R + 1), ∑ l₁ ∈ Finset.range (R + 1),
              (chainGeomCoeff q u j l₁ * (q * u) ^ l₂
                  - (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂)
                • chainWord q u R c j l₁ l₂ g := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l₂ _ =>
          chain_dopComm_eq q u g (T := N + 1) (by omega) c j (by omega) hvan l₂
      have hswap : ∑ l₂ ∈ Finset.range (R + 1), ∑ l₁ ∈ Finset.range (R + 1),
            (chainGeomCoeff q u j l₁ * (q * u) ^ l₂
                - (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂) • chainWord q u R c j l₁ l₂ g
          = ∑ l₁ ∈ Finset.range (R + 1), ∑ l₂ ∈ Finset.range (R + 1),
            (chainGeomCoeff q u j l₁ * (q * u) ^ l₂
                - (q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂) • chainWord q u R c j l₁ l₂ g :=
        Finset.sum_comm
      have hP2 : ∑ l₁ ∈ Finset.range (R + 1), ((q * u) ^ l₁) •
            chainComm q u R 1 c l₁ (Sym.DopInt q u ((j : ℤ) - (l₁ : ℤ)) g)
          = ((1 - q) * (1 - u)) • ∑ l₁ ∈ Finset.range (R + 1), ∑ l₂ ∈ Finset.range (R + 1),
              ((q * u) ^ l₁ * chainGeomCoeff q u l₁ l₂) • chainWord q u R c j l₁ l₂ g := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l₁ _ => ?_
        conv_lhs => rw [hIH l₁, chainGeom, smul_comm ((q * u) ^ l₁) ((1 - q) * (1 - u)),
          Finset.smul_sum]
        refine congrArg (fun x => ((1 - q) * (1 - u)) • x) (Finset.sum_congr rfl fun l₂ _ => ?_)
        rw [smul_smul, chainWord]
      rw [hsplit, hP1, hswap, hP2, ← smul_add]
      refine congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_
      rw [← Finset.sum_add_distrib, chainGeom]
      refine Finset.sum_congr rfl fun l₁ _ => ?_
      rw [← Finset.sum_add_distrib, chain_succ, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l₂ _ => ?_
      rw [← add_smul, smul_smul, chainWord]
      refine congrArg (fun a : L => a • chain q u R 1 c l₂
        (Sym.DopInt q u ((l₁ : ℤ) - (l₂ : ℤ)) (Sym.DopInt q u ((j : ℤ) - (l₁ : ℤ)) g))) ?_
      ring


/-! ### The commutation, and the `(a,1)` column at a general `f` -/

/-- **`HJO.Sweep.ColumnCommutes` at every `b` and every `f`:**

`M·ψ_{b+1}f = ψ_b(D_0f) - d_-(d^*_+(ψ_bf))`.

`HJO.Sweep.columnCommutes_at_iff_chainComm` turns the clause into
`M·chain (b+1) 1 0 f = chainComm b 1 0 f`;
`HJO.Sweep.exists_forall_chainComm_eq_smul_chainGeom` at `j = 0` gives
`chainComm b 1 0 f = M·chainGeom b 0 f`, and `HJO.Sweep.chainGeom_zero_eq_chain` identifies
`chainGeom b 0` with `chain (b+1) 1 0`.

`q ≠ 0`, `u ≠ 0` and `q ≠ 1` are `HJO.Sweep.psiCol_eq`'s and are real; **`M ≠ 0` is not needed.** -/
theorem columnCommutes_at (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ) (f : Sym.Lambda L) :
    ((1 - q) * (1 - u)) • psiCol q u (b + 1) f
      = psiCol q u b (Sym.Dop q u 0 f) - dminus q 1 (dplusStar q u 0 (psiCol q u b f)) := by
  obtain ⟨R₁, hR₁⟩ := columnCommutes_at_iff_chainComm (q := q) (u := u) hq0 hu0 hq1 b f
  obtain ⟨R₂, hR₂⟩ := exists_forall_chainComm_eq_smul_chainGeom q u b 0 f
  refine (hR₁ (max R₁ R₂) (le_max_left _ _)).mpr ?_
  rw [← chainGeom_zero_eq_chain]
  exact (hR₂ (max R₁ R₂) (le_max_right _ _)).symm

/-- **The commutation the `(a,1)` column asks for, discharged.** -/
theorem columnCommutes (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) : ColumnCommutes q u :=
  fun b f => columnCommutes_at hq0 hu0 hq1 b f

/-- **The sweep side of the `(a,1)` column is the `Λ`-side operator, at every `b` and every `f`:**
`ψ_bf = ι(Q_{b+1,1}f)`. -/
theorem psiCol_eq_qop (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (b : ℕ) (f : Sym.Lambda L) :
    psiCol q u b f = MvPolynomial.C (Sym.Qop q u (b + 1) 1 f) :=
  psiCol_eq_qop_of_columnCommutes hM (columnCommutes hq0 hu0 hq1) b f

/-! ### Cross-checks against the two independently proved instances -/

/-- **Cross-check: the general commutation reproves the known `b = 0` clause**
(`HJO.Sweep.columnCommutes_zero_at`), whose route is entirely different --- the translation
`HJO.Sweep.columnCommutes_zero_at_iff_dopInt` against
`HJO.Sym.smul_sum_pow_smul_dopInt_dopInt`, the single-row identity. The statement is written out
here rather than cited, so that its agreement with the earlier one is what the kernel checks. -/
theorem columnCommutes_zero_at_of_general (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (f : Sym.Lambda L) :
    ((1 - q) * (1 - u)) • psiCol q u 1 f
      = psiCol q u 0 (Sym.Dop q u 0 f) - dminus q 1 (dplusStar q u 0 (psiCol q u 0 f)) :=
  columnCommutes_at hq0 hu0 hq1 0 f

/-- **Cross-check: the general commutation reproves the known `f = e_2` instance**
(`HJO.Sweep.columnCommutes_zero_at_elemSymm_two`) --- the first `f` that probes the commutation at
all, since `D_0e_2` leaves the line `Le_2`, and the one instance that was established through
`HJO.Sym.Qop`'s own commutator on the `Λ` side and two Hall--Littlewood values on the sweep side.
Note that the general commutation does **not** need the `M ≠ 0` the earlier route carries. -/
theorem columnCommutes_zero_at_elemSymm_two_of_general (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) :
    ((1 - q) * (1 - u)) • psiCol q u 1 (Sym.elemSymm L 2)
      = psiCol q u 0 (Sym.Dop q u 0 (Sym.elemSymm L 2))
        - dminus q 1 (dplusStar q u 0 (psiCol q u 0 (Sym.elemSymm L 2))) :=
  columnCommutes_at hq0 hu0 hq1 0 (Sym.elemSymm L 2)

/-- **The clause of `HJO.Mellit.lhsRewrite_sweepWitness` on the whole `(a,1)` column, at a general
`f`.**

`M ≠ 0` is needed and is not removable: `HJO.Sym.Qop` defines `Q_{b+2,1}` by dividing by `M`. -/
@[hjo "lem_mellit_lhs_slope_column"]
theorem lhsSlope_succ_one (hM : (1 - q) * (1 - u) ≠ 0) (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1)
    (b : ℕ) : Mellit.LhsSlope q u (b + 1) 1 :=
  lhsSlope_succ_one_of_columnCommutes hM (columnCommutes hq0 hu0 hq1) b

end HJO.Sweep

end
