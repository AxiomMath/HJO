/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # Adding the genuine letter `y_k` to the alphabet

The raising recursion of Carlsson and Mellit expands `χ'_{Id_k}(π)` in powers of the last auxiliary
variable and reads each coefficient as `g_j(π)[X + y_k]`, the symmetric function `g_j(π)` evaluated
on the alphabet enlarged by the single letter `y_k`. This file builds that substitution, the
map `ρ_k` of `HJO.Sweep.addLetter`.

## Main definitions

* `HJO.Sweep.addLetter`: `ρ_k`, the `𝕜[y]`-algebra endomorphism of the total space with
  `ρ_k(p_r) = p_r + y_k^r`, the plethystic substitution `F ↦ F[X + y_k]`.

## Main results

* `HJO.Sweep.addLetter_powerSum`, `HJO.Sweep.addLetter_auxVar`: the two defining values, which
  together pin `ρ_k` among the `𝕜`-algebra endomorphisms of the total space.
* `HJO.Sweep.addLetter_mem_piece`, `HJO.Sweep.addLetter_mem_piece_succ`: the domain and
  codomain, `ρ_{k+1} : V_k → V_{k+1}`.

## Implementation notes

**The coefficient is `1` and not `q^r - 1`.** This is the one difference from
`HJO.Sweep.qshift`: `ρ_k` adds the
*genuine* letter `y_k`, whose `r`-th power sum is `y_k^r`, where `τ_{k,i}` adds the virtual letter
`(q-1)y_i`, whose `r`-th power sum is `(q^r - 1)y_i^r`. So the two maps are built by the same
`MvPolynomial.aevalTower` with the scalar deleted, and nothing else changes.

**The map lives on the total space, not on one piece.** The `ρ_k` goes from `V_{k-1}` to
`V_k`, and the letter it adds is the `k`-th auxiliary variable. Here, as for `HJO.Sweep.qshift`,
`HJO.Sweep.theta` and `HJO.Sweep.cycleShift`, the constant is a single endomorphism of
`HJO.Sweep.Total` carrying the *letter index* `i` as its argument, and the domain and
codomain become the membership statement `addLetter_mem_piece`. That is what the consuming lemma
`HJO.Sweep.addLetter_theta` forces: it reads
`ρ_{k+1}(θ_k(G)) = θ_{k+1}(τ_{k+1,k+1}(G))`, and `θ` and `τ` are already endomorphisms of the one
total space, so a `ρ` of any other shape would make neither composite typecheck without a
coercion. The `ρ_{k+1}` is `addLetter L (k + 1)`, whose letter is `y_{k+1}`, i.e.
`MvPolynomial.X k` under the index convention of `HJO.Sweep.auxVar`; writing the level as `k + 1`
keeps the truncated subtraction of `auxVar` out of every statement below.

**`𝕜[y]`-linearity is `addLetter_auxVar`.** The raising recursion asks only that `ρ_k` be a
`𝕜[y_1, …, y_{k-1}]`-algebra map, i.e. that it fix the auxiliary variables *other than* the letter
it adds. The map built here fixes **every** auxiliary variable, the added letter included: the
letter enters through the image of `p_r` and not through a rename. So `addLetter_auxVar` is stated
for every index and the linearity is the instance at `j < k - 1`. Nothing is weakened —
fixing more generators is a stronger property of the same map, and it is what
`HJO.Sweep.addLetter_theta` compares against, `θ_{k+1}` fixing `y_{k+1}` too.

Only `CommRing` is asked of the base, as for `HJO.Sweep.theta`: no scalar is inverted and no
elementary symmetric function is read, so neither a field nor `ℚ ⊆ 𝕜` is needed here.

**The other model.** The same substitution can be presented as a map
`AuxLambda K k →ₐ[K] AuxLambda K (k + 1)` between the *per-`k`* types with the auxiliary variables
indexed by `Fin k` inside the coefficient ring, so that the added letter is `Fin.last k` and the
`𝕜[y_1, …, y_k]`-linearity is along `Fin.castSucc`. That is the same object read in the second
encoding, and the encoding of this layer is the one total space — auxiliary variables outside, `Λ`
in the coefficients — as it is for `HJO.Sweep.piece` and `HJO.Sweep.swapAux`.

## References

`HJO.Sweep.addLetter`, with its consumers `HJO.Dyck.insertFront_realisation`,
`HJO.Sweep.addLetter_theta`, `HJO.Dyck.existsUnique_eq_sum_pow_mul_realiseAddLetter` and
`HJO.Dyck.realiseAddLetter_mem_zSymmSubring`. Following E. Carlsson and A. Mellit, *A proof of
the shuffle conjecture*, §5.
-/

@[expose] public section

namespace HJO.Sweep

section AddLetter

variable {L : Type*} [CommRing L]

/-- **Adding the letter `y_i`.** `HJO.Sweep.addLetter`: the `𝕜[y]`-algebra
endomorphism `ρ_k` with `ρ_k(p_r) = p_r + y_k^r` for every `r ≥ 1`, the plethystic substitution
`F ↦ F[X + y_k]`. The map from `V_{k-1}` to `V_k` is the restriction of
`addLetter L k` (`addLetter_mem_piece`), written below at the level `k + 1` so that no truncated
subtraction appears.

**The coefficient is `1`, not `q^r - 1`**: unlike `HJO.Sweep.qshift`, which adds the virtual letter
`(q-1)y_i`, this adds the genuine letter `y_i`, whose `r`-th power sum is `y_i^r`. -/
@[hjo "def_cm_addletter"]
noncomputable def addLetter (L : Type*) [CommRing L] (i : ℕ) : Total L →ₐ[L] Total L :=
  MvPolynomial.aevalTower
    (MvPolynomial.aeval fun j : ℕ =>
      (MvPolynomial.C (MvPolynomial.X j) + auxVar i ^ (j + 1) : Total L))
    MvPolynomial.X

/-- **The defining value of `ρ_k` on the alphabet**: `ρ_k(p_{r+1}) = p_{r+1} + y_k^{r+1}`. -/
@[hjo "def_cm_addletter"]
theorem addLetter_powerSum (i r : ℕ) :
    addLetter L i (MvPolynomial.C (Sym.powerSum L (r + 1)))
      = MvPolynomial.C (Sym.powerSum L (r + 1)) + auxVar i ^ (r + 1) := by
  simp [addLetter, Sym.powerSum]

/-- **`ρ_k` fixes every auxiliary variable**, so it is in particular a `𝕜[y_1, …, y_{k-1}]`-algebra
map, as the raising recursion asks: the new letter enters through the image of the power sums and
not through a rename of the variables. -/
@[hjo "def_cm_addletter", simp]
theorem addLetter_auxVar (i j : ℕ) :
    addLetter L i (MvPolynomial.X j : Total L) = MvPolynomial.X j := by
  simp [addLetter]

/-- `ρ_k` fixes the auxiliary variable `y_j`, the index convention of
`HJO.Sweep.auxVar` read on `addLetter_auxVar`. -/
theorem addLetter_auxVar' (i j : ℕ) : addLetter L i (auxVar j : Total L) = auxVar j := by
  rw [auxVar, addLetter_auxVar]

/-- **`ρ_k` lands in `V_m` as soon as `y_k` does.** It adds the letter `y_k` to the alphabet and
fixes every auxiliary variable, so the only new variable in the image is `y_k`, whose index
condition is `i - 1 < m`. This is the assertion that `ρ_k` maps `V_{k-1}` into `V_k`,
stated as for `HJO.Sweep.qshift_mem_piece`. -/
@[hjo "def_cm_addletter"]
theorem addLetter_mem_piece {i k m : ℕ} (hi : i - 1 < m) (hk : k ≤ m) {F : Total L}
    (hF : F ∈ piece L k) : addLetter L i F ∈ piece L m := by
  refine mem_piece_of_algHom (φ := addLetter L i) (fun c => ?_) (fun j hj => ?_) hF
  · rw [addLetter, MvPolynomial.aevalTower_C]
    refine aeval_mem_piece (fun j => ?_) c
    refine add_mem ((piece L m).algebraMap_mem _) (pow_mem ?_ _)
    rw [auxVar]
    exact X_mem_piece hi
  · rw [addLetter_auxVar]
    exact X_mem_piece (by omega)

/-- **`ρ_{k+1} : V_k → V_{k+1}`**, the domain and codomain at the level the raising
recursion reads them: the letter added is `y_{k+1}`, the last variable of the larger piece. -/
@[hjo "def_cm_addletter"]
theorem addLetter_mem_piece_succ (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    addLetter L (k + 1) F ∈ piece L (k + 1) :=
  addLetter_mem_piece (by omega) (by omega) hF

end AddLetter

end HJO.Sweep
