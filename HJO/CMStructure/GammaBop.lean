/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.AlphabetShift
public import HJO.CarlssonMellit.BopModule
public import HJO.Collinear.EsymmAlphabet
public meta import HJO.Attr

/-! # Shifting the alphabet past a Hall--Littlewood operator

`HJO.Sweep.alphabetShift_bopExt`: for a letter `w` free of the alphabet `X` and every `i ∈ ℤ`,

  `Γ₊(w)B_i = (B_i - wB_{i-1})Γ₊(w)`   and   `B_iΓ₊(-w) = Γ₊(-w)(B_i - wB_{i-1})`.

## The argument, and what has to be built for it

`B_i` extracts the coefficient of `z^i` from `β(F)Ω(z)`, and `Γ₊(w)` adds one letter to `X`. Adding
a letter multiplies `Ω(z) = ∑_n(-1)^ne_nz^n` by `1 - wz`, because `e_n[X + w] = e_n + we_{n-1}` for
a one-letter alphabet; and extracting `z^i` from `(1 - wz)` times a series is extracting `z^i` minus
`w` times extracting `z^{i-1}`. That is the first identity, and the second follows by multiplying it
on both sides by the inverse `Γ₊(-w)`.

Two constructions are needed to run that on the module `V_k`, where `B_i` is the coefficientwise
`HJO.Sweep.bopExt` and `Γ₊` is an algebra endomorphism mixing the two factors.

* **`HJO.Sweep.plethTotal`**, the displacement `β` extended to the total space by fixing every
  auxiliary variable. With it, `HJO.Sweep.bopExt_eq_coeffPair` says `B_i` on `V_k` is the same
  pairing of the same family that `HJO.Sym.Bop` is on `Λ` — the statement that makes the
  argument above a computation rather than an analogy.
* **`HJO.Sweep.coeffPair`**, the pairing `∑_jA_jc_j` for a family in an arbitrary commutative ring.
  `HJO.Sym.coeffPairing` is its instance at `Λ` with the scalars restricted to `𝕜`
  (`HJO.Sweep.coeffPairing_eq_coeffPair`); the generality is needed because the family here has
  coefficients in `V_k` and the pairing must be linear over `V_k`, not just over `𝕜`.

## `w` need not be a monomial, but it must be free of `X`

The natural statement is "for every monomial `w` in the `y`-variables". What the argument uses is
that the letter datum is `p_r ↦ w^r` — the *one-letter* alphabet with letter `w`, whatever `w` is as
a ring element, which is what makes `e_n` of it vanish above degree `1` — and that each `w^r` is
free of `X` (`w ∈ HJO.Sweep.auxSubalg`), without which `HJO.Sweep.plethTotal` does not commute with
the shift and `Γ₊(-w)` is not inverse to `Γ₊(w)`. Every monomial in the `y`-variables has the
latter, so the statement below generalises the one for monomials. The former is *not* a consequence
of `w` being a monomial and is not an extra hypothesis either: it is the reading of `Γ₊` recorded on
`HJO.Sweep.alphabetShift`, that the shift is parameterised by the power sums of the virtual alphabet
and not by its sum.

## References

This file proves `HJO.Sweep.alphabetShift_bopExt`, used by `HJO.Sweep.dminusCM_starCommCM_braidInv`,
from the definitions `HJO.Sweep.alphabetShift`, `HJO.Sym.Bop`, `HJO.Sweep.bopExt`,
`HJO.Sym.plethHallLittlewood`.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The coefficient pairing over an arbitrary ring -/

section CoeffPair

variable {R : Type*} [CommRing R]

/-- **The pairing `∑_jA_jc_j`** of a polynomial against a family, for a family in an arbitrary
commutative ring, and linear over that ring. `HJO.Sym.coeffPairing` is the instance at `Λ` with the
scalars restricted to `𝕜`; the extra generality is what lets the same pairing be read with
coefficients in `V_k`. -/
noncomputable def coeffPair (c : ℕ → R) : Polynomial R →ₗ[R] R where
  toFun P := P.sum fun j A => A * c j
  map_add' P Q := Polynomial.sum_add_index P Q _ (fun _ => by simp) (fun _ _ _ => by ring)
  map_smul' r P := by
    simp only [RingHom.id_apply]
    rw [Polynomial.sum_smul_index' _ _ _ (fun _ => by simp), Polynomial.smul_sum]
    simp only [smul_mul_assoc]

@[simp]
theorem coeffPair_monomial (c : ℕ → R) (j : ℕ) (a : R) :
    coeffPair c (Polynomial.monomial j a) = a * c j :=
  Polynomial.sum_monomial_index a (fun j A => A * c j) (by simp)

/-- The pairing of `HJO.Sym.coeffPairing` is this one: both are `∑_jA_jc_j`. -/
theorem coeffPairing_eq_coeffPair {K : Type*} [CommRing K] (c : ℕ → Sym.Lambda K)
    (P : Polynomial (Sym.Lambda K)) : Sym.coeffPairing c P = coeffPair c P := rfl

/-- **A ring homomorphism passes the pairing**, moving the coefficients and the family alike. -/
theorem map_coeffPair {S : Type*} [CommRing S] (φ : R →+* S) (c : ℕ → R) (P : Polynomial R) :
    φ (coeffPair c P) = coeffPair (fun j => φ (c j)) (P.map φ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.map_add, map_add, hP, hQ]
  | monomial j a => rw [coeffPair_monomial, Polynomial.map_monomial, coeffPair_monomial, map_mul]

/-- The pairing is additive in the family. -/
theorem coeffPair_sub_family (c d : ℕ → R) (P : Polynomial R) :
    coeffPair (fun j => c j - d j) P = coeffPair c P - coeffPair d P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]; abel
  | monomial j a => rw [coeffPair_monomial, coeffPair_monomial, coeffPair_monomial, mul_sub]

/-- The pairing is homogeneous in the family. -/
theorem coeffPair_mul_family (x : R) (c : ℕ → R) (P : Polynomial R) :
    coeffPair (fun j => x * c j) P = x * coeffPair c P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, mul_add]
  | monomial j a => rw [coeffPair_monomial, coeffPair_monomial]; ring

end CoeffPair

/-! ### The displacement on the total space -/

section PlethTotal

variable {L : Type*} [Field L]

/-- The Hall--Littlewood displacement read into `Λ[w][z⁻¹]`, with the coefficients of the target
polynomial ring taken in the total space: the `𝕜`-algebra homomorphism from `Λ` sending `p_r` to
`p_r + (1-q^r)z^{-r}`, both summands sitting in the constants of the total space. -/
noncomputable def plethLift (q : L) : Sym.Lambda L →ₐ[L] Polynomial (Total L) :=
  MvPolynomial.aeval fun i : ℕ =>
    (Polynomial.C (MvPolynomial.C (Sym.powerSum L (i + 1)))
      + Polynomial.C (scal (1 - q ^ (i + 1))) * Polynomial.X ^ (i + 1) : Polynomial (Total L))

/-- **`plethLift` is the displacement `HJO.Sym.plethHallLittlewood` with its coefficients included
in the total space.** -/
theorem plethLift_eq_map (q : L) (f : Sym.Lambda L) :
    plethLift q f = (Sym.plethHallLittlewood q f).map (MvPolynomial.C : Sym.Lambda L →+* Total L) :=
  by
  have key : plethLift q
      = (Polynomial.mapAlgHom (IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L))).comp
        (Sym.plethHallLittlewood q) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [plethLift, MvPolynomial.aeval_X, AlgHom.comp_apply, Sym.plethHallLittlewood_X,
      Polynomial.coe_mapAlgHom, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
    rfl
  rw [congrArg (fun g : Sym.Lambda L →ₐ[L] Polynomial (Total L) => g f) key]
  rfl

/-- **The displacement `β` extended to the total space**: the `𝕜`-algebra homomorphism from `V_*` to
`V_*[z⁻¹]` sending `p_r` to `p_r + (1-q^r)z^{-r}` and fixing every auxiliary variable. It is the map
that turns the coefficientwise `HJO.Sweep.bopExt` into a pairing, which is what
`HJO.Sweep.alphabetShift_bopExt` computes with. -/
noncomputable def plethTotal (q : L) : Total L →ₐ[L] Polynomial (Total L) :=
  MvPolynomial.aevalTower (plethLift q) fun j => Polynomial.C (MvPolynomial.X j : Total L)

@[simp]
theorem plethTotal_C (q : L) (f : Sym.Lambda L) :
    plethTotal q (MvPolynomial.C f) = plethLift q f :=
  MvPolynomial.aevalTower_C _ _ f

@[simp]
theorem plethTotal_X (q : L) (j : ℕ) :
    plethTotal q (MvPolynomial.X j : Total L) = Polynomial.C (MvPolynomial.X j : Total L) :=
  MvPolynomial.aevalTower_X _ _ j

/-- **`plethTotal` fixes everything free of the alphabet**, sending it to the constant it is: the
displacement moves `X` and nothing else, so on the subalgebra generated by the `y`-variables it is
the inclusion of the constants. -/
theorem plethTotal_of_mem_auxSubalg (q : L) {Z : Total L} (hZ : Z ∈ auxSubalg L) :
    plethTotal q Z = Polynomial.C Z := by
  refine Algebra.adjoin_induction (p := fun Z _ => plethTotal q Z = Polynomial.C Z) ?_ ?_ ?_ ?_ hZ
  · rintro _ ⟨j, rfl⟩
    exact plethTotal_X q j
  · intro x
    rw [AlgHom.commutes, Polynomial.algebraMap_apply]
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, map_add]
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy, map_mul]

/-- A `y`-monomial lies in the subalgebra generated by the `y`-variables. -/
theorem monomial_one_mem_auxSubalg (d : ℕ →₀ ℕ) :
    (MvPolynomial.monomial d 1 : Total L) ∈ auxSubalg L := by
  have hX : ∀ j : ℕ, (MvPolynomial.X j : Total L) ∈ auxSubalg L := fun j => by
    have h : (MvPolynomial.X j : Total L) = auxVar (j + 1) := by rw [auxVar, Nat.add_sub_cancel]
    rw [h]
    exact auxVar_mem_auxSubalg (j + 1)
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
  exact prod_mem fun j _ => pow_mem (hX j) _

/-- The displacement of a monomial `f y^d`: the `y`-monomial comes out as a constant and the
displacement of the coefficient is left. -/
theorem plethTotal_monomial (q : L) (d : ℕ →₀ ℕ) (f : Sym.Lambda L) :
    plethTotal q (MvPolynomial.monomial d f)
      = Polynomial.C (MvPolynomial.monomial d (1 : Sym.Lambda L))
        * (Sym.plethHallLittlewood q f).map (MvPolynomial.C : Sym.Lambda L →+* Total L) := by
  rw [show (MvPolynomial.monomial d f : Total L)
      = MvPolynomial.monomial d 1 * MvPolynomial.C f from by
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one], map_mul,
    plethTotal_of_mem_auxSubalg q (monomial_one_mem_auxSubalg d), plethTotal_C, plethLift_eq_map]

variable [Algebra ℚ L]

/-- **The Hall--Littlewood operators on the module, as a pairing.** `B_i` on `V_k` extracts the
coefficient of `z^i` from `β(F)Ω(z)` exactly as `HJO.Sym.Bop` does on `Λ`: the same family
`(-1)^ne_n` at the index `i + j`, paired against the coefficients of the *extended* displacement
`HJO.Sweep.plethTotal`.

This is what makes `HJO.Sweep.alphabetShift_bopExt` a computation on the module rather than an
analogy with the computation on `Λ`. -/
theorem bopExt_eq_coeffPair (q : L) (i : ℤ) (G : Total L) :
    bopExt q i G
      = coeffPair (fun j => MvPolynomial.C (Sym.elemSymmAlt L (i + j))) (plethTotal q G) := by
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | monomial d f =>
    rw [bopExt_monomial, plethTotal_monomial,
      show (Polynomial.C (MvPolynomial.monomial d (1 : Sym.Lambda L))
            * (Sym.plethHallLittlewood q f).map (MvPolynomial.C : Sym.Lambda L →+* Total L))
          = (MvPolynomial.monomial d (1 : Sym.Lambda L) : Total L) •
            (Sym.plethHallLittlewood q f).map (MvPolynomial.C : Sym.Lambda L →+* Total L) from by
        rw [Polynomial.smul_eq_C_mul], map_smul,
      ← map_coeffPair (MvPolynomial.C : Sym.Lambda L →+* Total L)
        (fun j => Sym.elemSymmAlt L (i + j)) (Sym.plethHallLittlewood q f),
      ← coeffPairing_eq_coeffPair]
    have hBop : Sym.coeffPairing (fun j => Sym.elemSymmAlt L (i + j))
        (Sym.plethHallLittlewood q f) = Sym.Bop q i f := rfl
    rw [hBop, smul_eq_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]

end PlethTotal

/-! ### The shift commutes with the displacement -/

section Commute

variable {L : Type*} [Field L]

/-- **`Γ₊` commutes with the extended displacement.** `β(F[X + Z]) = (βF)[X + Z]`, the outer shift
being applied to every coefficient: the two substitutions touch disjoint data, `Γ₊` the alphabet and
`β` the variable `z⁻¹`, once each `p_r[Z]` is free of `X`.

That hypothesis is load-bearing: without it the displacement would move the letters of `Z` too. -/
theorem plethTotal_alphabetShift (q : L) {P : ℕ → Total L} (hP : ∀ r, P r ∈ auxSubalg L)
    (G : Total L) :
    plethTotal q (alphabetShift P G) = (plethTotal q G).map (alphabetShift P) := by
  have key : (plethTotal q).comp (alphabetShift P)
      = (Polynomial.mapAlgHom (alphabetShift P)).comp (plethTotal q) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hgen : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := rfl
      have hpl : plethTotal q (MvPolynomial.C (Sym.powerSum L (r + 1)))
          = Polynomial.C (MvPolynomial.C (Sym.powerSum L (r + 1)))
            + Polynomial.C (scal (1 - q ^ (r + 1))) * Polynomial.X ^ (r + 1) := by
        rw [plethTotal_C]
        change plethLift q (MvPolynomial.X r) = _
        rw [plethLift, MvPolynomial.aeval_X]
      have hL : plethTotal q (alphabetShift P (MvPolynomial.C (Sym.powerSum L (r + 1))))
          = Polynomial.C (MvPolynomial.C (Sym.powerSum L (r + 1)))
            + Polynomial.C (scal (1 - q ^ (r + 1))) * Polynomial.X ^ (r + 1)
            + Polynomial.C (P (r + 1)) := by
        rw [alphabetShift_powerSum, map_add, hpl,
          plethTotal_of_mem_auxSubalg q (hP (r + 1))]
      have hR : Polynomial.map (alphabetShift P : Total L →+* Total L)
            (plethTotal q (MvPolynomial.C (Sym.powerSum L (r + 1))))
          = Polynomial.C (MvPolynomial.C (Sym.powerSum L (r + 1)))
            + Polynomial.C (scal (1 - q ^ (r + 1))) * Polynomial.X ^ (r + 1)
            + Polynomial.C (P (r + 1)) := by
        rw [hpl, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
          Polynomial.map_pow, Polynomial.map_X]
        rw [show (alphabetShift P : Total L →+* Total L)
              (MvPolynomial.C (Sym.powerSum L (r + 1)))
            = MvPolynomial.C (Sym.powerSum L (r + 1)) + P (r + 1) from alphabetShift_powerSum P r,
          show (alphabetShift P : Total L →+* Total L) (scal (1 - q ^ (r + 1)) : Total L)
            = scal (1 - q ^ (r + 1)) from alphabetShift_scal P _, map_add]
        ring
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hgen, Polynomial.coe_mapAlgHom]
      rw [hL, hR]
    · have hX : (alphabetShift P : Total L →+* Total L) (MvPolynomial.X n) = MvPolynomial.X n :=
        alphabetShift_X P n
      simp only [AlgHom.comp_apply, alphabetShift_X, plethTotal_X, Polynomial.coe_mapAlgHom,
        Polynomial.map_C, hX]
  exact congrArg (fun g : Total L →ₐ[L] Polynomial (Total L) => g G) key

end Commute

/-! ### The shift on the alternating elementary family -/

section Letter

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The one-letter alphabet `w`, as a homomorphism out of `Λ`: `p_r ↦ w^r`. -/
noncomputable def oneLetter (w : Total L) : Sym.Lambda L →ₐ[L] Total L :=
  MvPolynomial.aeval fun i : ℕ => w ^ (i + 1)

omit [Algebra ℚ L] in
theorem oneLetter_powerSum (w : Total L) {j : ℕ} (hj : 0 < j) :
    oneLetter w (Sym.powerSum L j) = w ^ j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [CopPower.powerSum_succ, oneLetter, MvPolynomial.aeval_X]

/-- **Adding one letter to the alphabet**: `e_n[X + w] = e_n + we_{n-1}` for `n ≥ 1`, and `e_0 = 1`.
This is `HJO.Bglx.map_elemSymm_add` at the two alphabets `X` and `w`, with
`HJO.Bglx.map_elemSymm_geom` killing every elementary function of the one-letter alphabet above
degree `1`. -/
theorem alphabetShift_C_elemSymm_succ (w : Total L) (m : ℕ) :
    alphabetShift (fun r => w ^ r) (MvPolynomial.C (Sym.elemSymm L (m + 1)))
      = MvPolynomial.C (Sym.elemSymm L (m + 1)) + w * MvPolynomial.C (Sym.elemSymm L m) := by
  set φ : Sym.Lambda L →ₐ[L] Total L := IsScalarTower.toAlgHom L (Sym.Lambda L) (Total L) with hφ
  set χ : Sym.Lambda L →ₐ[L] Total L := (alphabetShift (fun r => w ^ r)).comp φ with hχ
  have hφC : ∀ f : Sym.Lambda L, φ f = MvPolynomial.C f := fun f => rfl
  have hsplit : ∀ j : ℕ, 1 ≤ j →
      χ (Sym.powerSum L j) = φ (Sym.powerSum L j) + oneLetter w (Sym.powerSum L j) := by
    intro j hj
    obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
    rw [hχ, AlgHom.comp_apply, hφC, alphabetShift_powerSum, oneLetter_powerSum w (by omega)]
  have hgeom : ∀ s : ℕ, oneLetter w (Sym.elemSymm L s)
      = if s = 0 then 1 else if s = 1 then w else 0 :=
    HJO.Bglx.map_elemSymm_geom w (oneLetter w) (fun j hj => oneLetter_powerSum w hj)
  have hconv := HJO.Bglx.map_elemSymm_add φ (oneLetter w) χ hsplit (m + 1)
  have hcut : ∑ s ∈ Finset.range (m + 1 + 1),
        φ (Sym.elemSymm L (m + 1 - s)) * oneLetter w (Sym.elemSymm L s)
      = φ (Sym.elemSymm L (m + 1)) + φ (Sym.elemSymm L m) * w := by
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (m + 1 + 1) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      simp only [Finset.mem_range]
      omega
    have hvan : ∀ t ∈ Finset.range (m + 1 + 1), t ∉ ({0, 1} : Finset ℕ) →
        φ (Sym.elemSymm L (m + 1 - t)) * oneLetter w (Sym.elemSymm L t) = 0 := by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      rw [hgeom t, ite_eq_right ht.1, ite_eq_right ht.2, mul_zero]
    rw [← Finset.sum_subset hsub hvan, Finset.sum_pair (by omega : (0 : ℕ) ≠ 1), hgeom 0, hgeom 1,
      Nat.sub_zero, Nat.add_sub_cancel]
    simp
  rw [hχ, AlgHom.comp_apply, hφC] at hconv
  rw [hconv, hcut, hφC, hφC]
  ring

/-- **`Γ₊(w)` multiplies the alternating elementary series by `1 - wz`.** Read coefficientwise:
`Γ₊(w)(Ω_n) = Ω_n - wΩ_{n-1}` for every `n ∈ ℤ`, with `Ω_n = (-1)^ne_n` above `0` and `0` below.
The negative and zero indices are not decoration — they are what makes the operators `B_i` of
negative index right — and the identity holds at each of them. -/
theorem alphabetShift_C_elemSymmAlt (w : Total L) (n : ℤ) :
    alphabetShift (fun r => w ^ r) (MvPolynomial.C (Sym.elemSymmAlt L n))
      = MvPolynomial.C (Sym.elemSymmAlt L n) - w * MvPolynomial.C (Sym.elemSymmAlt L (n - 1)) := by
  have hCpow : ∀ (k : ℕ) (f : Sym.Lambda L),
      (MvPolynomial.C ((-1 : Sym.Lambda L) ^ k * f) : Total L)
        = (-1 : Total L) ^ k * MvPolynomial.C f := by
    intro k f
    rw [map_mul, map_pow, map_neg, map_one]
  rcases lt_or_ge n 0 with hn | hn
  · rw [Sym.elemSymmAlt_of_neg hn,
      Sym.elemSymmAlt_of_neg (show n - 1 < 0 by omega)]
    simp
  lift n to ℕ using hn with m
  match m with
  | 0 =>
    have he0 : Sym.elemSymm L 0 = 1 := by rw [Sym.elemSymm]
    have h0 : Sym.elemSymmAlt L ((0 : ℕ) : ℤ) = 1 := by
      rw [Sym.elemSymmAlt_natCast, pow_zero, he0, mul_one]
    have h1 : Sym.elemSymmAlt L (((0 : ℕ) : ℤ) - 1) = 0 :=
      Sym.elemSymmAlt_of_neg (by norm_num)
    rw [h0, h1, map_one, map_one, map_zero, mul_zero, sub_zero]
  | r + 1 =>
    have hcast : (((r + 1 : ℕ)) : ℤ) - 1 = ((r : ℕ) : ℤ) := by push_cast; ring
    rw [Sym.elemSymmAlt_natCast, hcast, Sym.elemSymmAlt_natCast, hCpow, hCpow, map_mul, map_pow,
      map_neg, map_one, alphabetShift_C_elemSymm_succ]
    ring

end Letter

/-! ### Shifting the alphabet past a Hall--Littlewood operator -/

section GammaBop

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The first identity**: `Γ₊(w)B_i = (B_i - wB_{i-1})Γ₊(w)`.

`B_i` is the pairing of the family `Ω_{i+j}` against the coefficients of the extended displacement
(`HJO.Sweep.bopExt_eq_coeffPair`); `Γ₊(w)` commutes with that displacement
(`HJO.Sweep.plethTotal_alphabetShift`) and turns the family into `Ω_{i+j} - wΩ_{i-1+j}`
(`HJO.Sweep.alphabetShift_C_elemSymmAlt`). Splitting the pairing along that difference is the claim.

The hypothesis is that `w` is free of the alphabet, which every monomial in the `y`-variables is. -/
@[hjo "lem_cm_gamma_bop"]
theorem alphabetShift_bopExt (q : L) (i : ℤ) {w : Total L} (hw : w ∈ auxSubalg L) (G : Total L) :
    alphabetShift (fun r => w ^ r) (bopExt q i G)
      = bopExt q i (alphabetShift (fun r => w ^ r) G)
        - w * bopExt q (i - 1) (alphabetShift (fun r => w ^ r) G) := by
  have hP : ∀ r : ℕ, (fun r => w ^ r) r ∈ auxSubalg L := fun r => pow_mem hw r
  have hfam : (fun j : ℕ => alphabetShift (fun r => w ^ r)
        (MvPolynomial.C (Sym.elemSymmAlt L (i + j))))
      = fun j : ℕ => MvPolynomial.C (Sym.elemSymmAlt L (i + j))
        - w * MvPolynomial.C (Sym.elemSymmAlt L (i - 1 + j)) := by
    funext j
    rw [alphabetShift_C_elemSymmAlt, show i + (j : ℤ) - 1 = i - 1 + j from by ring]
  calc alphabetShift (fun r => w ^ r) (bopExt q i G)
      = alphabetShift (fun r => w ^ r)
          (coeffPair (fun j => MvPolynomial.C (Sym.elemSymmAlt L (i + j))) (plethTotal q G)) := by
        rw [bopExt_eq_coeffPair]
    _ = coeffPair (fun j => alphabetShift (fun r => w ^ r)
            (MvPolynomial.C (Sym.elemSymmAlt L (i + j))))
          ((plethTotal q G).map (alphabetShift (fun r => w ^ r) : Total L →+* Total L)) :=
        map_coeffPair _ _ _
    _ = coeffPair (fun j => MvPolynomial.C (Sym.elemSymmAlt L (i + j))
            - w * MvPolynomial.C (Sym.elemSymmAlt L (i - 1 + j)))
          (plethTotal q (alphabetShift (fun r => w ^ r) G)) := by
        rw [hfam, plethTotal_alphabetShift q hP]
    _ = coeffPair (fun j => MvPolynomial.C (Sym.elemSymmAlt L (i + j)))
          (plethTotal q (alphabetShift (fun r => w ^ r) G))
        - coeffPair (fun j => w * MvPolynomial.C (Sym.elemSymmAlt L (i - 1 + j)))
          (plethTotal q (alphabetShift (fun r => w ^ r) G)) :=
        coeffPair_sub_family _ _ _
    _ = bopExt q i (alphabetShift (fun r => w ^ r) G)
        - w * bopExt q (i - 1) (alphabetShift (fun r => w ^ r) G) := by
        rw [coeffPair_mul_family, ← bopExt_eq_coeffPair, ← bopExt_eq_coeffPair]

/-- **`HJO.Sweep.alphabetShift_bopExt`, the second identity**: `B_iΓ₊(-w) = Γ₊(-w)(B_i - wB_{i-1})`.

The first identity multiplied on both sides by the inverse `Γ₊(-w)`, which
`HJO.Sweep.alphabetShift_neg_alphabetShift` supplies. Note that
substituting `-w` for `w` in the first identity does *not* give this one: that
yields `Γ₊(-w)B_i = (B_i + wB_{i-1})Γ₊(-w)`, whose sign is the opposite one and whose two operators
stand in the other order. -/
@[hjo "lem_cm_gamma_bop"]
theorem bopExt_alphabetShift_neg (q : L) (i : ℤ) {w : Total L} (hw : w ∈ auxSubalg L)
    (G : Total L) :
    bopExt q i (alphabetShift (fun r => -w ^ r) G)
      = alphabetShift (fun r => -w ^ r)
        (bopExt q i G - w * bopExt q (i - 1) G) := by
  have hP : ∀ r : ℕ, (fun r => w ^ r) r ∈ auxSubalg L := fun r => pow_mem hw r
  set Γ : Total L →ₐ[L] Total L := alphabetShift (fun r => w ^ r) with hΓ
  set Γn : Total L →ₐ[L] Total L := alphabetShift (fun r => -w ^ r) with hΓn
  have hGn : ∀ F : Total L, Γ (Γn F) = F := fun F => alphabetShift_alphabetShift_neg hP F
  have hkey := alphabetShift_bopExt q i hw (Γn G)
  rw [← hΓ] at hkey
  rw [hGn G] at hkey
  calc bopExt q i (Γn G)
      = Γn (Γ (bopExt q i (Γn G))) := by
        rw [alphabetShift_neg_alphabetShift hP]
    _ = Γn (bopExt q i G - w * bopExt q (i - 1) G) := by rw [hkey]

end GammaBop

end HJO.Sweep
