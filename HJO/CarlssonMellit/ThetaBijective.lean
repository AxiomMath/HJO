/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CarlssonMellit.SweepCM
public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # The `(q-1)`-plethysm is a bijection of `V_k`

The normalisation `HJO.Dyck.IsSigmaCharacter` of a character of a partial Dyck path reads `θ_k(G)`
rather than `G`, and the paper writes `F[X/(q-1)]` for the image of `F` under the inverse of `θ_k`.
Both need `θ_k` to be a bijection of `V_k`, which is `HJO.Sweep.theta_bijOn_piece` and what this
file proves.

## Main definitions

* `HJO.Sweep.alphabetScale`: the diagonal substitution `p_r ↦ c_{r-1} p_r` of the total space, of
  which `HJO.Sweep.theta` is the instance at `c_{r-1} = q^r - 1`.
* `HJO.Sweep.thetaInv`: the inverse plethysm, the paper's `F ↦ F[X/(q-1)]`.

## Main results

* `HJO.Sweep.theta_bijOn_piece`, that `θ_k` is a bijection from `V_k` onto
  `V_k`.
* `HJO.Sweep.theta_bijective`: the same on the whole total space, of which the statement
  is the restriction.
* `HJO.Sweep.theta_bijOn_piece_of_ne_one`: the field hypothesis, `q^r ≠ 1` for `r ≥ 1`
  over a field, discharging the general one.

## Implementation notes

**The hypothesis is that each `q^r - 1` is a unit, and over a general ring `≠ 0` would not do.**
The usual proof builds the inverse from the scalars `(q^r - 1)^{-1}`, and argues that they
exist because `𝕜 = ℚ(q,u)` is a field in which `q^r - 1 ≠ 0`. The statement here is over a
`CommRing` base, where those two conditions part company: a diagonal substitution scaling `p_r` by a
nonzero non-unit is injective and *not* surjective, exactly the distinction
`Module.Basis.exists_basis_of_triangular` is stated with. So the hypothesis carried is
`∀ r, IsUnit (q^(r+1) - 1)`, which is what the field argument supplies and no less;
`theta_bijOn_piece_of_ne_one` records that over a field the `q^r ≠ 1` gives it.

**The proof is the standard one, with the scalars packaged once.** Rather than build the inverse of
`θ` by hand, `alphabetScale` names the diagonal substitution of the total space attached to an
arbitrary family of scalars, and two facts about it do all the work: two such substitutions compose
into the one whose scalars are the products (`alphabetScale_alphabetScale`), and the constant family
`1` is the identity (`alphabetScale_one`). `HJO.Sweep.theta` *is* an `alphabetScale`
(`theta_eq_alphabetScale`, by definitional unfolding), so its inverse is the substitution by the
inverse scalars and the two composites are the identity by those two facts. This is the usual
argument — "the composites fix each `p_r`, hence are the identity" — with the ext step spent once.

**`V_k` is a subset of one total space here**, as throughout `HJO.Shuffle.SweepModule`, so a
"bijection from `V_k` onto `V_k`" is `Set.BijOn` on `HJO.Sweep.piece L k` and not the
bijectivity of a map between two types. Bijectivity on the total space
(`HJO.Sweep.theta_bijective`) gives the injectivity for free; the surjectivity onto `V_k` is the
statement that the inverse substitution preserves the piece, which it does for the same reason `θ`
does — it fixes every auxiliary variable and moves only the coefficients.

## References

Characteristic functions of partial Dyck paths: `HJO.Sweep.theta`, `HJO.Sweep.theta_bijOn_piece`,
`HJO.Dyck.IsSigmaCharacter`. Transcribing E. Carlsson and A. Mellit, *A proof of the shuffle
conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section AlphabetScale

variable {L : Type*} [CommRing L]

/-- **The diagonal substitution of the alphabet.** The `𝕜[y]`-algebra endomorphism of the total
space sending the power sum `p_{j+1}` to `c_j p_{j+1}` and fixing every auxiliary variable.

`HJO.Sweep.theta` is the instance at `c_j = q^{j+1} - 1` (`theta_eq_alphabetScale`), and the
inverse plethysm `HJO.Sweep.thetaInv` is the instance at the inverse scalars. Naming the family
once is what lets the "the composites fix each `p_r`, hence are the identity" be spent
on a single extensionality step. -/
noncomputable def alphabetScale (L : Type*) [CommRing L] (c : ℕ → L) : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (algebraMap L (Total L) (c j) * MvPolynomial.C (MvPolynomial.X j) : Total L))
    MvPolynomial.X

/-- The diagonal substitution fixes every auxiliary variable, so it is a `𝕜[y]`-algebra map. -/
@[simp]
theorem alphabetScale_auxVar (c : ℕ → L) (j : ℕ) :
    alphabetScale L c (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [alphabetScale]

/-- The diagonal substitution scales `p_{r+1}` by `c_r`. -/
theorem alphabetScale_powerSum (c : ℕ → L) (r : ℕ) :
    alphabetScale L c (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = algebraMap L (Total L) (c r) * MvPolynomial.C (Sym.powerSum L (r + 1)) := by
  simp [alphabetScale, Sym.powerSum]

/-- **`θ_k` is a diagonal substitution**, the one whose scalar at `p_{r+1}` is `q^{r+1} - 1`: this
is `HJO.Sweep.theta` read through `alphabetScale`, and it holds by unfolding both definitions. -/
theorem theta_eq_alphabetScale (q : L) :
    theta q = alphabetScale L fun j => q ^ (j + 1) - 1 := rfl

/-- **Two diagonal substitutions compose into one**, with the scalars multiplied. Both sides are
`𝕜`-algebra endomorphisms of the total space, so it is enough to compare on the power sums, where
the scalars multiply, and on the auxiliary variables, which all three maps fix. -/
theorem alphabetScale_alphabetScale (c c' : ℕ → L) (F : Total L) :
    alphabetScale L c (alphabetScale L c' F) = alphabetScale L (fun j => c j * c' j) F := by
  have key : (alphabetScale L c).comp (alphabetScale L c')
      = alphabetScale L (fun j => c j * c' j) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, alphabetScale_powerSum,
        map_mul, AlgHom.commutes]
      ring
    · simp only [AlgHom.comp_apply, alphabetScale_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **The diagonal substitution by the constant family `1` is the identity.** -/
theorem alphabetScale_one (F : Total L) : alphabetScale L (fun _ : ℕ => (1 : L)) F = F := by
  have key : alphabetScale L (fun _ : ℕ => (1 : L)) = AlgHom.id L (Total L) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        simp [Sym.powerSum]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, alphabetScale_powerSum,
        AlgHom.id_apply, map_one, one_mul]
    · simp only [AlgHom.id_apply, alphabetScale_auxVar]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

/-- **Two diagonal substitutions with reciprocal scalars undo one another**, the step
"the composites fix each `p_r`, hence are the identity". -/
theorem alphabetScale_alphabetScale_of_mul_eq_one {c c' : ℕ → L} (h : ∀ j, c j * c' j = 1)
    (F : Total L) : alphabetScale L c (alphabetScale L c' F) = F := by
  have hcc : (fun j => c j * c' j) = fun _ : ℕ => (1 : L) := funext h
  rw [alphabetScale_alphabetScale, hcc, alphabetScale_one]

/-- **A diagonal substitution preserves every graded piece**: it fixes the auxiliary variables and
multiplies the coefficients by scalars, so it creates no variable the argument did not use. -/
theorem alphabetScale_mem_piece (c : ℕ → L) {k m : ℕ} (hk : k ≤ m) {F : Total L}
    (hF : F ∈ piece L k) : alphabetScale L c F ∈ piece L m := by
  refine mem_piece_of_algHom (φ := alphabetScale L c) (fun a => ?_) (fun j hj => ?_) hF
  · rw [alphabetScale, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) a
    rw [IsScalarTower.algebraMap_apply L (Sym.Lambda L) (Total L)]
    exact mul_mem ((piece L m).algebraMap_mem _) ((piece L m).algebraMap_mem _)
  · rw [alphabetScale_auxVar]
    exact X_mem_piece (by omega)

/-- **`θ_k` preserves every graded piece**, which is the reading of `θ_k` as an
endomorphism of `V_k`. -/
theorem theta_mem_piece (q : L) {k m : ℕ} (hk : k ≤ m) {F : Total L} (hF : F ∈ piece L k) :
    theta q F ∈ piece L m := by
  rw [theta_eq_alphabetScale]
  exact alphabetScale_mem_piece _ hk hF

end AlphabetScale

section Bijective

variable {L : Type*} [CommRing L] {q : L}

/-- **The inverse plethysm**, the paper's `F ↦ F[X/(q-1)]`: the diagonal substitution scaling
`p_{r+1}` by `(q^{r+1} - 1)^{-1}`. It is a two-sided inverse of `HJO.Sweep.theta`
(`thetaInv_theta`, `theta_thetaInv`) as soon as each `q^{r+1} - 1` is a unit, which is the
hypothesis it takes. -/
noncomputable def thetaInv (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) : Total L →ₐ[L] Total L :=
  alphabetScale L fun j => (((hq j).unit⁻¹ : Lˣ) : L)

/-- The scalars of `HJO.Sweep.thetaInv` are the inverses of those of `HJO.Sweep.theta`. -/
theorem thetaInv_scalar_mul (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (j : ℕ) :
    (((hq j).unit⁻¹ : Lˣ) : L) * (q ^ (j + 1) - 1) = 1 := by
  have key := Units.inv_mul ((hq j).unit)
  rw [(hq j).unit_spec] at key
  exact key

/-- `F[X/(q-1)][(q-1)X] = F`: the inverse plethysm undoes `θ_k`. -/
theorem thetaInv_theta (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (F : Total L) :
    thetaInv hq (theta q F) = F := by
  rw [theta_eq_alphabetScale, thetaInv]
  exact alphabetScale_alphabetScale_of_mul_eq_one (thetaInv_scalar_mul hq) F

/-- `F[(q-1)X][X/(q-1)] = F`: `θ_k` undoes the inverse plethysm. -/
theorem theta_thetaInv (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (F : Total L) :
    theta q (thetaInv hq F) = F := by
  rw [theta_eq_alphabetScale, thetaInv]
  refine alphabetScale_alphabetScale_of_mul_eq_one (fun j => ?_) F
  rw [mul_comm]
  exact thetaInv_scalar_mul hq j

/-- **`θ` is a bijection of the total space** once each `q^{r+1} - 1` is a unit, off the inverse
plethysm. The statement about `V_k` is the restriction of this one
(`theta_bijOn_piece`). -/
theorem theta_bijective (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) :
    Function.Bijective (theta q : Total L → Total L) :=
  ⟨fun F G h => by rw [← thetaInv_theta hq F, h, thetaInv_theta hq G],
    fun F => ⟨thetaInv hq F, theta_thetaInv hq F⟩⟩

/-- **`HJO.Sweep.theta_bijOn_piece`: `θ_k` is a bijection from `V_k` onto `V_k`.**

The hypothesis is the invertibility of each `q^r - 1`, carried over a `CommRing` base: the inverse
is built from the scalars `(q^r - 1)^{-1}`, which over `𝕜 = ℚ(q,u)` exist because it is a field in
which `q^r - 1 ≠ 0`. Over a general ring invertibility is strictly more than nonvanishing — a
diagonal substitution scaling `p_r` by a nonzero non-unit is injective and not surjective — and it
is invertibility that is needed; `theta_bijOn_piece_of_ne_one` discharges it from `q^r ≠ 1` over a
field. -/
@[hjo "lem_cm_theta_bijective"]
theorem theta_bijOn_piece (hq : ∀ r : ℕ, IsUnit (q ^ (r + 1) - 1)) (k : ℕ) :
    Set.BijOn (theta q) (piece L k : Set (Total L)) (piece L k) := by
  refine ⟨fun F hF => theta_mem_piece q le_rfl hF, (theta_bijective hq).injective.injOn,
    fun F hF => ⟨thetaInv hq F, ?_, theta_thetaInv hq F⟩⟩
  exact alphabetScale_mem_piece _ le_rfl hF

end Bijective

/-- **`HJO.Sweep.theta_bijOn_piece` under the field hypothesis.** Over a field, `q^r - 1` is a unit
as soon as it is nonzero, so the genericity condition `q^r ≠ 1` for `r ≥ 1` — the shape in which
this library carries it — gives the bijectivity of `θ_k` on `V_k`. -/
theorem theta_bijOn_piece_of_ne_one {L : Type*} [Field L] {q : L}
    (hq : ∀ r : ℕ, 1 ≤ r → q ^ r ≠ 1) (k : ℕ) :
    Set.BijOn (theta q) (piece L k : Set (Total L)) (piece L k) :=
  theta_bijOn_piece
    (fun r => isUnit_iff_ne_zero.2 (sub_ne_zero_of_ne (hq (r + 1) (by omega)))) k

end HJO.Sweep
