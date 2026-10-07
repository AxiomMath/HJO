/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.ThetaHsymmComp
public import HJO.CarlssonMellit.GesselSchur
public import HJO.Classical.OmegaGessel
public meta import HJO.Attr

/-! # The superization formula

The superization formula and its Schur case: the plethysm `θ₀` acts on a fundamental quasisymmetric
expansion of a realised symmetric function by replacing each Gessel fundamental `F_{n,S}` by the
super fundamental `F̃_{n,S}`, and the special case of a Schur series says `ι(θ₀ f) = sch̃(D)`
whenever `ι(f) = sch(D)`.

## Main definitions

* `HJO.ParkingFunctions.superCompat`: the symmetric functions of a fixed degree admitting one family
  of coefficients that expands both `ι f` in the Gessel fundamentals and `ι(θ₀ f)` in the super
  fundamentals.

## Main results

* `HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel`: the superization formula, if
  `ι(f) = ∑_i c_i F_{n,S_i}` for `f ∈ Λ_n` then `ι(θ₀(f)) = ∑_i c_i F̃_{n,S_i}`.
* `HJO.ParkingFunctions.realisation_thetaLambda_schurSeries`: `ι(θ₀ f) = sch̃(D)` whenever
  `ι(f) = sch(D)`.
* `HJO.ParkingFunctions.realisation_thetaLambda_sum_superFundamental`: the superization formula for
  a Schur series, `ι(θ₀(f)) = ∑_{S ∈ SYT(D)} F̃_{#D, Des(S)}` whenever `ι(f) = sch(D)`.

## Implementation notes

*The chain is proved general case first, and is shorter for it.* The route through Schur series
proves the Schur case `HJO.ParkingFunctions.realisation_thetaLambda_schurSeries` first, by hand from
`HJO.ParkingFunctions.realisation_thetaLambda_completeHomogComp`,
`HJO.Sym.lambdaComp_le_completeHomogCompSpan` and
`HJO.ParkingFunctions.sum_filter_eq_sum_filter_of_sum_smul_gessel_eq`, and then derives the general
result `HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` from it through
`HJO.Sym.exists_eq_sum_smul_schurSeries`. But the general
result is what the spanning argument proves
directly: the Schur series never enters it, and the detour through
`HJO.Sym.exists_eq_sum_smul_schurSeries` — and so through the Schur basis of a graded piece, and the
field it needs — is not required. So
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` is proved first here, and the
Schur case is the two-line corollary of it that `HJO.Sym.schurSeries_eq_sum_gessel` and
`HJO.Sym.superSchurSeries_eq_sum_superFundamental` make: the hypothesis `ι(f) = sch(D)` *is* a
fundamental expansion, at the descent sets of the standard tableaux. Neither statement is weakened.

*The general result is proved by exhibiting a submodule*, exactly as
`HJO.ParkingFunctions.omegaCompat` proves `HJO.ParkingFunctions.realisation_omegaStd_of_component`:
`HJO.ParkingFunctions.superCompat` is the set of `f` admitting *some* coefficient family witnessing
both the expansion of `ι f` in the `F_{n,T}` and that of `ι(θ₀ f)` in the `F̃_{n,T}`, over the
subsets `T` of the window `{1, …, n-1}`. Two witnesses add and scale, so it is a submodule, and it
contains every `h_α` because `HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.ParkingFunctions.realisation_thetaLambda_completeHomogComp` expand `ι(h_α)` and `ι(θ₀(h_α))`
over the *same* permutations, so one regrouping (`HJO.ParkingFunctions.sum_perm_eq_sum_powerset`,
reused from the `ω` chain) serves for both. Then `HJO.Sym.lambdaComp_le_completeHomogCompSpan` puts
every element of `Λ_n` in it, and `HJO.ParkingFunctions.linearIndepOn_gessel` identifies the witness
with the given family. That is the one place independence is spent, exactly as in
`HJO.ParkingFunctions.sum_filter_eq_sum_filter_of_sum_smul_gessel_eq`.

*The grouping lemma is stated once, for an arbitrary family indexed by the sets of steps.* It is
used twice with the same index map, once at `G = F_{n,·}` and once at `G = F̃_{n,·}`;
`HJO.ParkingFunctions.sum_smul_gessel_eq_sum_fiberwise` is the `G = F_{n,·}` instance of it and is
not general enough to serve the second use.

*Hypotheses dropped.* The customary hypothesis `n ≥ 1` is nowhere needed, in any of the results
here: at `n = 0` the window `{1, …, n-1}` is empty, so the only set of steps is `∅`, and every
statement reduces to an identity between the constants `F_{0,∅} = F̃_{0,∅} = 1`. In the Schur case
`HJO.ParkingFunctions.realisation_thetaLambda_sum_superFundamental` the customary `n ≥ 1` is
likewise idle — it would serve only to name the number of cells of `D`, which is `D.card` here.
`HJO.ParkingFunctions.realisation_thetaLambda_schurSeries` needs no separate treatment of the empty
diagram either, `HJO.Sym.lambdaComp_le_completeHomogCompSpan` holding at `0` as well.

*The formulation with `f[X - Y]` is the same declaration.* In it, "`f` homogeneous of degree `n`"
is `f ∈ Λ_n` by `HJO.Sym.LambdaComp`, the assertion about `f[X - Y]` is
`ι(θ₀(f)) = ∑_i c_i F̃_{n,S_i}` by `HJO.Sym.superVar`, and what is left is
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` verbatim.

## References

J. Haglund, M. Haiman, N. Loehr, J. B. Remmel and A. Ulyanov, *A
combinatorial formula for the character of the diagonal coinvariants*, Duke Math. J. **126** (2005)
195--232, Corollary 2.4.3.
-/

@[expose] public section

open Finset

namespace HJO.ParkingFunctions

open HJO.Sym

/-! ### Grouping a combination by the value of the index map -/

/-- **Regrouping a combination by the value of the index map.** A finite combination
`∑_{i ∈ s} c_i G(h i)` of members of a family indexed by sets of steps, rewritten as a combination
indexed by any finite set `t` containing every `h i`, the coefficient of `G T` being the total
`∑_{i ∈ s, h i = T} c_i` over the fibre of `T`.

`HJO.ParkingFunctions.sum_smul_gessel_eq_sum_fiberwise` is the instance of this at
`G = F_{n,·}`; the point of the general form is that the *same* regrouping, with the same index
map, serves at `G = F̃_{n,·}` too, which is what makes the two sides of a superization identity
comparable term by term. -/
theorem sum_smul_eq_sum_fiberwise_of_maps_to {R M J κ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [DecidableEq κ] {s : Finset J} {t : Finset κ} (c : J → R) (h : J → κ)
    (G : κ → M) (hst : ∀ i ∈ s, h i ∈ t) :
    ∑ i ∈ s, c i • G (h i) = ∑ T ∈ t, (∑ i ∈ s with h i = T, c i) • G T := by
  rw [← Finset.sum_fiberwise_of_maps_to hst fun i => c i • G (h i)]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]

/-! ### The superization formula -/

section Superization

variable {K : Type*} [CommRing K] [Algebra ℚ K] {ι : Lambda K →ₐ[K] AlphabetSeries K}

/-- The symmetric functions whose degree-`n` canonical fundamental expansion `θ₀` superizes: those
admitting *one* family of coefficients that expands both `ι f` in the Gessel fundamentals and
`ι(θ₀ f)` in the super fundamentals. Two such witnesses add and scale, so this is a submodule, and
that is what lets `HJO.Sym.lambdaComp_le_completeHomogCompSpan` reduce the theorem below to the
generators `h_α`. -/
noncomputable def superCompat (ι : Lambda K →ₐ[K] AlphabetSeries K) (q : K) (n : ℕ) :
    Submodule K (Lambda K) where
  carrier := {f : Lambda K | ∃ c : Finset ℕ → K,
    ι f = ∑ T ∈ (Ico 1 n).powerset, c T • gessel K n T ∧
      ι (thetaLambda q f) = ∑ T ∈ (Ico 1 n).powerset, c T • superFundamental K q n T}
  add_mem' := by
    rintro f g ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
    refine ⟨c + c', ?_, ?_⟩
    · rw [map_add, h1, h1', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => (add_smul _ _ _).symm
    · rw [map_add, map_add, h2, h2', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun T _ => (add_smul _ _ _).symm
  zero_mem' := ⟨0, by simp, by simp⟩
  smul_mem' := by
    rintro r f ⟨c, h1, h2⟩
    refine ⟨r • c, ?_, ?_⟩
    · rw [map_smul, h1, Finset.smul_sum]
      exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_assoc]
    · rw [map_smul, map_smul, h2, Finset.smul_sum]
      exact Finset.sum_congr rfl fun T _ => by rw [Pi.smul_apply, smul_assoc]

/-- **A complete homogeneous product is compatible.**
`HJO.ParkingFunctions.realisation_completeHomogComp` and
`HJO.ParkingFunctions.realisation_thetaLambda_completeHomogComp` expand `ι(h_α)` and `ι(θ₀(h_α))`
over the *same* permutations, so grouping both by the inverse descent set produces one family of
coefficients serving for both. -/
theorem completeHomogComp_mem_superCompat (hι : IsRealisation ι) (q : K) {n : ℕ} {α : List ℕ}
    (hα : α.sum = n) : completeHomogComp K α ∈ superCompat ι q n := by
  classical
  refine ⟨fun T => ((#{σ ∈ {σ : Equiv.Perm (Fin n) | permDescentSet σ ⊆ compDescent α} |
      invDescentSet σ = T} : ℕ) : K), ?_, ?_⟩
  · rw [realisation_completeHomogComp hι hα]
    exact sum_perm_eq_sum_powerset _ fun T => gessel K n T
  · rw [realisation_thetaLambda_completeHomogComp hι q hα]
    exact sum_perm_eq_sum_powerset _ fun T => superFundamental K q n T

/-- Every symmetric function of degree `n` is compatible: the graded piece is spanned by the
complete homogeneous products of compositions of `n`. -/
theorem lambdaComp_le_superCompat (hι : IsRealisation ι) (q : K) (n : ℕ) :
    LambdaComp K n ≤ superCompat ι q n := by
  refine le_trans (lambdaComp_le_completeHomogCompSpan K n) ?_
  rw [completeHomogCompSpan]
  refine Submodule.span_le.2 ?_
  rintro f ⟨β, -, hβ, rfl⟩
  exact completeHomogComp_mem_superCompat hι q hβ

/-- **The superization formula.** For a realisation `ι`, a finite index set, scalars `c_i` and sets
of steps `S_i` inside the window `{1, …, n-1}`, and `f ∈ Λ_n` with `ι(f) = ∑_i c_i F_{n,S_i}`, one
has `ι(θ₀(f)) = ∑_i c_i F̃_{n,S_i}`.

`HJO.Sym.lambdaComp_le_completeHomogCompSpan` puts `f` in `HJO.ParkingFunctions.superCompat`, which
produces a canonical family `a` expanding `ι f` over the subsets of the window and `ι(θ₀ f)` over
the same subsets with `F̃` in place of `F`. Grouping the given expansion by the value of `S_i` turns
it into a canonical one, so `HJO.ParkingFunctions.linearIndepOn_gessel` identifies `a T` with the
fibre total `∑_{i, S_i = T} c_i`; the *same* grouping, read at `F̃` instead of `F`, then turns the
canonical conclusion into the one asserted.

The customary hypothesis `n ≥ 1` is not used: at `n = 0` the window is empty, the only set of steps
is `∅`, and both sides are combinations of the constant `1`.

The formulation with `f[X - Y]` is this statement: its "`f ∈ Λ` homogeneous of degree `n`" is
`f ∈ Λ_n` by `HJO.Sym.LambdaComp`, and its assertion about `f[X - Y]` is the displayed identity by
`HJO.Sym.superVar`. -/
@[hjo "lem_cm_hhl_superization"]
theorem realisation_thetaLambda_of_sum_smul_gessel (hι : IsRealisation ι) (q : K) (n : ℕ)
    {I : Type*} (s : Finset I) (c : I → K) (S : I → Finset ℕ) (hS : ∀ i ∈ s, S i ⊆ Ico 1 n)
    {f : Lambda K} (hf : f ∈ LambdaComp K n)
    (hfe : ι f = ∑ i ∈ s, c i • gessel K n (S i)) :
    ι (thetaLambda q f) = ∑ i ∈ s, c i • superFundamental K q n (S i) := by
  classical
  obtain ⟨a, ha1, ha2⟩ := lambdaComp_le_superCompat hι q n hf
  have hmaps : ∀ i ∈ s, S i ∈ (Ico 1 n).powerset := fun i hi => mem_powerset.2 (hS i hi)
  have hcoeff : ∀ T ∈ (Ico 1 n).powerset, (∑ i ∈ s with S i = T, c i) = a T :=
    eq_of_sum_gessel_eq K
      (((hfe.trans (sum_smul_eq_sum_fiberwise_of_maps_to c S
        (fun T => gessel K n T) hmaps)).symm.trans ha1))
  rw [ha2, sum_smul_eq_sum_fiberwise_of_maps_to c S
    (fun T => superFundamental K q n T) hmaps]
  exact (Finset.sum_congr rfl fun T hT => by rw [hcoeff T hT]).symm

attribute [hjo "lem_cm_superization"] realisation_thetaLambda_of_sum_smul_gessel

/-- **The super Schur series is the plethysm of the Schur series.**
For a realisation `ι`, a Young diagram `D` and `f ∈ Λ` with `ι(f) = sch(D)`, one has
`ι(θ₀(f)) = sch̃(D)`.

`HJO.Sym.schurSeries_eq_sum_gessel` makes the hypothesis a fundamental expansion, at the descent
sets of the standard tableaux of `D`; those sets lie in the window, and every monomial of `sch(D)`
has total degree `#D` (`HJO.Sym.kostka_eq_zero_of_degHom_ne`), so
`HJO.Sym.mem_lambdaComp_of_coeff_iota` puts `f` in `Λ_{#D}` and
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel` applies. What it returns is the
super fundamental expansion `HJO.Sym.superSchurSeries_eq_sum_superFundamental` identifies with
`sch̃(D)`.

A separate treatment of the empty diagram is unnecessary:
`HJO.Sym.lambdaComp_le_completeHomogCompSpan`, behind
`HJO.ParkingFunctions.realisation_thetaLambda_of_sum_smul_gessel`, holds at degree `0` as well. -/
@[hjo "lem_cm_super_schur_theta"]
theorem realisation_thetaLambda_schurSeries [CharZero K] [NoZeroDivisors K] (hι : IsRealisation ι)
    (q : K) (D : YoungDiagram) {f : Lambda K} (hf : ι f = schurSeries K D) :
    ι (thetaLambda q f) = superSchurSeries K q D := by
  classical
  have hmem : f ∈ LambdaComp K D.card := by
    refine mem_lambdaComp_of_coeff_iota hι fun d hd => ?_
    by_contra hne
    rw [hf, coeff_schurSeries, kostka_eq_zero_of_degHom_ne D rfl hne, Nat.cast_zero] at hd
    exact hd rfl
  have hfe : ι f = ∑ T : SYT D, (1 : K) • gessel K D.card (sytDescentSet T.1) := by
    rw [hf, schurSeries_eq_sum_gessel]
    exact Finset.sum_congr rfl fun T _ => (one_smul K _).symm
  rw [realisation_thetaLambda_of_sum_smul_gessel hι q D.card univ (fun _ => (1 : K))
      (fun T : SYT D => sytDescentSet T.1) (fun T _ => sytDescentSet_subset_Ico T.1) hmem hfe,
    superSchurSeries_eq_sum_superFundamental]
  exact Finset.sum_congr rfl fun T _ => one_smul K _

/-- **The superization formula for a Schur series.** For a realisation
`ι`, a Young diagram `D` and `f ∈ Λ` with `ι(f) = sch(D)`,
`ι(θ₀(f)) = ∑_{S ∈ SYT(D)} F̃_{#D, Des(S)}`.

`HJO.ParkingFunctions.realisation_thetaLambda_schurSeries` makes the left side `sch̃(D)`, and
`HJO.Sym.superSchurSeries_eq_sum_superFundamental` makes that the right side. The customary
hypothesis `n ≥ 1` is idle: it names the number of cells of `D`, which is `D.card` here, and nothing
reads its positivity. -/
@[hjo "lem_cm_superization_schur"]
theorem realisation_thetaLambda_sum_superFundamental [CharZero K] [NoZeroDivisors K]
    (hι : IsRealisation ι) (q : K) (D : YoungDiagram) {f : Lambda K}
    (hf : ι f = schurSeries K D) :
    ι (thetaLambda q f) = ∑ T : SYT D, superFundamental K q D.card (sytDescentSet T.1) := by
  rw [realisation_thetaLambda_schurSeries hι q D hf, superSchurSeries_eq_sum_superFundamental]

end Superization

end HJO.ParkingFunctions
