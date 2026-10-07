/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.CMStructure.DminusBraid
public import HJO.CMStructure.GammaBop
public import HJO.CMStructure.TwistedIntertwine
public meta import HJO.Attr

/-! # The last variable from the commutator of the two operators

`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`: for every `k ≥ 1` and every `F ∈ V_k`,

`(d_-d_+ - d_+d_-)F = (1-q)T_1(T_2(⋯T_{k-1}(y_kF)⋯))`,

the composite of the braid operators being the identity at `k = 1`. Read here at `k = m + 1`, so
that the word is `T_{[1,m]}` and the empty case is `m = 0` with nothing truncated.

## Main results

* `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`: the main result.
* `HJO.Sweep.qshift_C_elemSymmAlt`: `τ_{k,i}(Ω_n) = Ω_n + (1-q)∑_{j=1}^{n}y_i^jΩ_{n-j}`, the
  substitution on the alternating elementary family, which is the whole arithmetic of the proof.
* `HJO.Sweep.braid_auxVar_pow`: `T_i(y_i^n) = y_{i+1}^n + (1-q)∑_{j=1}^{n}y_i^jy_{i+1}^{n-j}`.
* `HJO.Sweep.dminusCM_braid_auxVar_pow`: the reduced identity
  `d_-(T_ky_k^n) - τ_{k,k}(d_-y_k^n) = (1-q)y_k^{n+1}`.

## Implementation notes

**The reduction is run in two stages, and each is a spanning statement.** Both sides are
`𝕜`-linear and both are linear over the image of the twisting homomorphism `tw_k` — the left because
the two operators intertwine the twisted action (`HJO.Sweep.cmDPlus_twistedAction`,
`HJO.Sweep.dminusCM_twistedAction`), the right because `tw_k(c)` is symmetric in `y_1, …, y_k`
(`HJO.Sweep.swapAux_twist`) so it passes every letter of the word and the factor `y_k`. And every
`F ∈ V_k` is a `tw_k(Λ)`-combination of `y`-monomials: the substitution `Γ₊` adding the alphabet
`(q-1)(y_1+⋯+y_k)` is an automorphism of the total space carrying `V_k` to `V_k` and `Λ` to
`tw_k(Λ)`, so expanding `Γ₊⁻¹(F)` in `y`-monomials and applying `Γ₊` is the expansion wanted. So it
suffices to treat `F` a `y`-monomial supported in `y_1, …, y_k`, and then — the operators being
linear over `𝕜[y_1, …, y_{k-1}]` — a power of `y_k` alone.

**The prefix comes off before any computation.** Splitting `T_{[1,k]} = T_{[1,k-1]}T_k` and
commuting `d_-` past the short word (`HJO.Sweep.dminusCM_cmAscWord`, off
`HJO.Sweep.dminusCM_braid`) puts the prefix `T_{[1,k-1]}` in front of both terms of the commutator
and of the right-hand side, leaving the `d_-(T_kF) - τ_{k,k}(d_-F) = (1-q)y_kF`.

**`τ_{k,i}` on the alternating elementary family is proved by inverting `Γ₊(y_i)`, not by a
plethystic expansion.** `Γ₊(y_i)τ_{k,i} = Γ₊(qy_i)`, and `Γ₊` of a single letter multiplies the
series `Ω(z) = ∑(-1)^ne_nz^n` by `1 - wz`, i.e. sends `Ω_n` to `Ω_n - wΩ_{n-1}` — this is
`HJO.Sweep.alphabetShift_C_elemSymmAlt`. So the candidate closed form is checked by applying
`Γ₊(y_i)` to it, where the sum telescopes, and `Γ₊(y_i)` is injective because `Γ₊(-y_i)` inverts it.

**`F ∈ V_k` is load-bearing and is kept.** At `k = 1` and `F = y_2` the left-hand side acquires the
terms `qe_1y_1 - e_1y_2` that the right-hand side has no counterpart for, so the membership is not
decoration: the reduction spends it twice, once to expand `F` over `tw_k(Λ)` and once to make
`τ_{k+1,k+1}` fix the `y`-monomials of `F`.

## References

E. Carlsson and A. Mellit, *A proof of the shuffle conjecture*, §5. -/

@[expose] public section

namespace HJO.Sweep

/-! ### Small facts about the graded pieces and the substitutions -/

section Pieces

variable {L : Type*} [Field L]

/-- A `y`-monomial whose exponents live below `k` lies in `V_k`: it is a product of the variables
`y_1, …, y_k`. -/
theorem monomial_one_mem_piece {k : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < k) :
    (MvPolynomial.monomial d (1 : Sym.Lambda L) : Total L) ∈ piece L k := by
  rw [MvPolynomial.monomial_eq, map_one, one_mul, Finsupp.prod]
  exact prod_mem fun j hj => pow_mem (X_mem_piece (hd j hj)) _

/-- **`s_i` fixes everything in a piece it cannot reach**: an element of `V_k` with `k + 1 ≤ i`
involves none of `y_i, y_{i+1}`, so the transposition leaves it alone. -/
theorem swapAux_of_mem_piece {i k : ℕ} (hki : k + 1 ≤ i) {F : Total L} (hF : F ∈ piece L k) :
    swapAux L i F = F := by
  set A : Total L →ₐ[L] Total L := (swapAux L i).toAlgHom.restrictScalars L with hA
  have hAapp : ∀ G : Total L, A G = swapAux L i G := fun _ => rfl
  have key : A F = AlgHom.id L (Total L) F := by
    refine algHom_eq_of_mem_piece (k := k) (fun c => ?_) (fun j hj => ?_) hF
    · rw [hAapp, swapAux_C, AlgHom.id_apply]
    · rw [hAapp, swapAux_X, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), AlgHom.id_apply]
  rw [← hAapp, key, AlgHom.id_apply]

/-- `τ_{k,i}` fixes a `y`-monomial: the substitution moves the alphabet and nothing else. -/
theorem qshift_monomial (q : L) (i : ℕ) (d : ℕ →₀ ℕ) :
    qshift q i (MvPolynomial.monomial d (1 : Sym.Lambda L)) = MvPolynomial.monomial d 1 := by
  rw [qshift_eq_alphabetShift, alphabetShift_of_mem_auxSubalg _ (monomial_one_mem_auxSubalg d)]

/-- **`Γ₊` carries `V_k` to `V_k`** as soon as every power sum of the added alphabet lies in `V_k`:
it fixes `y_1, …, y_k` and moves `p_r` by an element of `V_k`. This is
`HJO.Sweep.twistedMult_mem_piece` with the family left free, which is what the inverse shift
needs. -/
theorem alphabetShift_mem_piece {P : ℕ → Total L} {k : ℕ} (hP : ∀ r, P r ∈ piece L k)
    {F : Total L} (hF : F ∈ piece L k) : alphabetShift P F ∈ piece L k := by
  refine mem_piece_of_algHom (fun c => ?_) (fun j hj => ?_) hF
  · induction c using MvPolynomial.induction_on with
    | C a =>
      rw [show (MvPolynomial.C (MvPolynomial.C a : Sym.Lambda L) : Total L) = scal a from rfl,
        alphabetShift_scal]
      exact Subalgebra.algebraMap_mem _ _
    | add p r hp hr => rw [map_add, map_add]; exact add_mem hp hr
    | mul_X p j hp =>
      rw [map_mul, map_mul]
      refine mul_mem hp ?_
      rw [show (MvPolynomial.X j : Sym.Lambda L) = Sym.powerSum L (j + 1) from by
        rw [Sym.powerSum, Nat.add_sub_cancel], alphabetShift_powerSum]
      exact add_mem (Subalgebra.algebraMap_mem _ _) (hP (j + 1))
  · rw [alphabetShift_X]
    exact X_mem_piece hj

/-- A word of braid operators is linear over the scalars of `𝕜`. -/
theorem cmAscWord_scal_mul (q : L) (a b : ℕ) (x : L) (F : Total L) :
    cmAscWord q a b (scal x * F) = scal x * cmAscWord q a b F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def, map_smul, Algebra.smul_def, ← scal_eq_algebraMap]

end Pieces

/-! ### The braid operator on a power of the variable it moves -/

section BraidPow

variable {L : Type*} [Field L]

/-- **`T_i(y_i^n) = y_{i+1}^n + (1-q)∑_{j=1}^{n}y_i^jy_{i+1}^{n-j}`**, the
computation inside the proof of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`:
`s_i(y_i^n) = y_{i+1}^n` and the divided difference is the geometric sum
`-∑_{j<n}y_i^jy_{i+1}^{n-1-j}`, pinned by `HJO.Sweep.dividedDiff_unique` off `geom_sum₂_mul`. -/
theorem braid_auxVar_pow (q : L) {i : ℕ} (hi : 1 ≤ i) (n : ℕ) :
    braid q i ((auxVar i : Total L) ^ n)
      = (auxVar (i + 1) : Total L) ^ n
        + scal (1 - q) * ∑ j ∈ Finset.range n,
            (auxVar i : Total L) ^ (j + 1) * (auxVar (i + 1) : Total L) ^ (n - 1 - j) := by
  have hav : (MvPolynomial.X i : Total L) = auxVar (i + 1) := by
    rw [auxVar, Nat.add_sub_cancel]
  have hav' : (MvPolynomial.X (i - 1) : Total L) = auxVar i := rfl
  have hswap : swapAux L i ((auxVar i : Total L) ^ n) = (auxVar (i + 1) : Total L) ^ n := by
    rw [map_pow, swapAux_auxVar_self hi]
  have hdd : dividedDiff i ((auxVar i : Total L) ^ n)
      = -∑ j ∈ Finset.range n,
          (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (n - 1 - j) := by
    refine (dividedDiff_unique hi ?_).symm
    have hg := geom_sum₂_mul (auxVar i : Total L) ((auxVar (i + 1)) : Total L) n
    rw [hswap, hav, hav']
    linear_combination hg
  have hfac : ∀ x : Total L,
      (scal (q - 1) : Total L) * auxVar i * (-x) = scal (1 - q) * (auxVar i * x) := by
    intro x
    have h1 : (scal (1 - q) : Total L) = -scal (q - 1) := by
      rw [show (1 : L) - q = -(q - 1) from by ring, scal_neg]
    rw [h1]
    ring
  have hsum : (auxVar i : Total L) * ∑ j ∈ Finset.range n,
        (auxVar i : Total L) ^ j * (auxVar (i + 1) : Total L) ^ (n - 1 - j)
      = ∑ j ∈ Finset.range n,
        (auxVar i : Total L) ^ (j + 1) * (auxVar (i + 1) : Total L) ^ (n - 1 - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [braid_apply, hswap, hdd, hfac, hsum]

end BraidPow

/-! ### The substitution on the alternating elementary family -/

section QshiftOmega

variable {L : Type*} [Field L]

/-- **`Γ₊(y_i)τ_{k,i} = Γ₊(qy_i)`**: the substitution `τ_{k,i}` adds the virtual alphabet
`qy_i - y_i`, so composing it with the addition of the letter `y_i` leaves the single letter `qy_i`.
Both sides are `𝕜`-algebra endomorphisms of the total space, so they are compared on the power sums
and on the auxiliary variables. -/
theorem alphabetShift_qshift (q : L) (i : ℕ) (F : Total L) :
    alphabetShift (fun r => (auxVar i : Total L) ^ r) (qshift q i F)
      = alphabetShift (fun r => (scal q * auxVar i : Total L) ^ r) F := by
  have key : (alphabetShift (fun r => (auxVar i : Total L) ^ r)).comp (qshift q i)
      = alphabetShift (fun r => (scal q * auxVar i : Total L) ^ r) := by
    refine MvPolynomial.algHom_ext' ?_ fun n => ?_
    · refine MvPolynomial.algHom_ext fun r => ?_
      have hC : (algebraMap (Sym.Lambda L) (Total L)) (MvPolynomial.X r)
          = MvPolynomial.C (Sym.powerSum L (r + 1)) := by
        rw [MvPolynomial.algebraMap_eq, Sym.powerSum, Nat.add_sub_cancel]
      have hsp : (scal q : Total L) ^ (r + 1) = scal (q ^ (r + 1)) := by
        rw [scal_eq_algebraMap, scal_eq_algebraMap, map_pow]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hC, qshift_powerSum, map_add,
        map_mul, map_pow, map_sub, map_one, alphabetShift_powerSum, alphabetShift_scal,
        alphabetShift_auxVar_apply, mul_pow, hsp, scal_sub, scal_one]
      ring
    · simp only [AlgHom.comp_apply, qshift_auxVar, alphabetShift_X]
  exact congrArg (fun f : Total L →ₐ[L] Total L => f F) key

variable [Algebra ℚ L]

/-- `Ω_0 = 1`: the constant term of the alternating elementary series. -/
theorem C_elemSymmAlt_zero : (MvPolynomial.C (Sym.elemSymmAlt L 0) : Total L) = 1 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, Sym.elemSymmAlt_natCast, pow_zero,
    Sym.elemSymm_zero, mul_one, map_one]

/-- **`τ_{k,i}(Ω_n) = Ω_n + (1-q)∑_{j=1}^{n}y_i^jΩ_{n-j}`**, with `Ω_n = (-1)^ne_n` the coefficients
of the alternating elementary series. This is the whole arithmetic of
`HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM`.

It is proved by applying the injective `Γ₊(y_i)` to both sides:
`Γ₊(y_i)τ_{k,i} = Γ₊(qy_i)` (`HJO.Sweep.alphabetShift_qshift`), and adding one letter multiplies the
series by `1 - wz`, i.e. sends `Ω_n` to `Ω_n - wΩ_{n-1}`
(`HJO.Sweep.alphabetShift_C_elemSymmAlt`), so the right-hand side telescopes to
`Ω_n - qy_iΩ_{n-1}`. -/
theorem qshift_C_elemSymmAlt (q : L) (i n : ℕ) :
    qshift q i (MvPolynomial.C (Sym.elemSymmAlt L (n : ℤ)))
      = MvPolynomial.C (Sym.elemSymmAlt L (n : ℤ))
        + scal (1 - q) * ∑ j ∈ Finset.range n,
            (auxVar i : Total L) ^ (j + 1)
              * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (j : ℤ))) := by
  have hy : (auxVar i : Total L) ∈ auxSubalg L := auxVar_mem_auxSubalg i
  have hP : ∀ r, ((auxVar i : Total L) ^ r) ∈ auxSubalg L := fun r => pow_mem hy r
  have hterm : ∀ j ∈ Finset.range n,
      alphabetShift (fun r => (auxVar i : Total L) ^ r)
          ((auxVar i : Total L) ^ (j + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (j : ℤ))))
        = (auxVar i : Total L) ^ (j + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (j : ℤ)))
          - (auxVar i : Total L) ^ (j + 1 + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))) := by
    intro j _
    rw [map_mul, map_pow, alphabetShift_auxVar_apply, alphabetShift_C_elemSymmAlt,
      show ((n : ℤ) - 1 - (j : ℤ)) - 1 = (n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ) from by push_cast; ring]
    ring
  have htel : ∑ j ∈ Finset.range n,
        ((auxVar i : Total L) ^ (j + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (j : ℤ)))
          - (auxVar i : Total L) ^ (j + 1 + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))))
      = (auxVar i : Total L) ^ (0 + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - ((0 : ℕ) : ℤ)))
        - (auxVar i : Total L) ^ (n + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (n : ℤ))) :=
    Finset.sum_range_sub' (fun t : ℕ => (auxVar i : Total L) ^ (t + 1)
      * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - 1 - (t : ℤ)))) n
  refine alphabetShift_injective hP ?_
  rw [alphabetShift_qshift, alphabetShift_C_elemSymmAlt, map_add, alphabetShift_C_elemSymmAlt,
    map_mul, alphabetShift_scal, map_sum, Finset.sum_congr rfl hterm, htel,
    show ((n : ℤ) - 1 - (n : ℤ)) = -1 from by ring,
    Sym.elemSymmAlt_of_neg (by norm_num : (-1 : ℤ) < 0), map_zero, mul_zero, sub_zero,
    Nat.cast_zero, sub_zero, zero_add, pow_one, scal_sub, scal_one]
  ring

end QshiftOmega

/-! ### The reduced identity on a power of the last variable -/

section Reduced

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `B_r(1) = Ω_r` read on the module: the extension of the Hall--Littlewood operator to `V_k` acts
on the `Λ`-coefficient, and `HJO.Sym.bop_one` gives its value at `1`. -/
theorem bopExt_one (q : L) (r : ℤ) :
    bopExt q r (1 : Total L) = MvPolynomial.C (Sym.elemSymmAlt L r) := by
  rw [show (1 : Total L) = MvPolynomial.C (1 : Sym.Lambda L) from (map_one _).symm, bopExt_C,
    Sym.bop_one]

/-- `d_-` is linear over the scalars of `𝕜`. -/
theorem dminusCM_scal_mul (q : L) (k : ℕ) (x : L) (F : Total L) :
    dminusCM q k (scal x * F) = scal x * dminusCM q k F := by
  rw [scal_eq_algebraMap, ← Algebra.smul_def, map_smul, Algebra.smul_def, ← scal_eq_algebraMap]

/-- **The reduced identity of the proof, on a power of the last variable**:
`d_-(T_k(y_k^n)) - τ_{k,k}(d_-(y_k^n)) = (1-q)y_k^{n+1}`, read at `k = m + 1`.

`T_k(y_k^n)` is `HJO.Sweep.braid_auxVar_pow`; `d_-` on each term is
`HJO.Sweep.dminusCM_auxVar_pow_mul` together with the `𝕜[y]`-linearity of `B_r`, giving
`-Ω_{n+1} - (1-q)∑_{j=1}^{n}y_k^jΩ_{n+1-j}`; and `τ_{k,k}(d_-(y_k^n)) = -τ_{k,k}(Ω_{n+1})` is
`HJO.Sweep.qshift_C_elemSymmAlt`, whose sum runs one term further. The two sums cancel term by term
and the surviving term is `(1-q)y_k^{n+1}Ω_0`. -/
theorem dminusCM_braid_auxVar_pow (q : L) (m n : ℕ) :
    dminusCM q (m + 2) (braid q (m + 1) ((auxVar (m + 1) : Total L) ^ n))
      - qshift q (m + 1) (dminusCM q (m + 1) ((auxVar (m + 1) : Total L) ^ n))
      = scal (1 - q) * (auxVar (m + 1) : Total L) ^ (n + 1) := by
  have hmono : ∀ t : ℕ, ((auxVar (m + 1) : Total L)) ^ t
      = MvPolynomial.monomial (Finsupp.single m t) (1 : Sym.Lambda L) := by
    intro t
    rw [auxVar, Nat.add_sub_cancel, MvPolynomial.X_pow_eq_monomial]
  have hpow : ∀ t : ℕ, ((auxVar (m + 1) : Total L)) ^ t ∈ piece L (m + 1) :=
    fun t => pow_mem (auxVar_mem_piece (by omega) le_rfl) t
  have hbopmono : ∀ (t : ℕ) (r : ℤ),
      bopExt q r (MvPolynomial.monomial (Finsupp.single m t) (1 : Sym.Lambda L) : Total L)
        = MvPolynomial.monomial (Finsupp.single m t) (1 : Sym.Lambda L)
          * MvPolynomial.C (Sym.elemSymmAlt L r) := by
    intro t r
    rw [bopExt_monomial, Sym.bop_one, mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  have h1 : dminusCM q (m + 2) ((auxVar (m + 2) : Total L) ^ n)
      = -MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) + 1)) := by
    have h := dminusCM_auxVar_pow_mul q (m + 1) n (F := (1 : Total L)) (one_mem _)
    rw [mul_one, bopExt_one] at h
    rw [show m + 1 + 1 = m + 2 from rfl] at h
    exact h
  have h2 : ∀ j ∈ Finset.range n,
      dminusCM q (m + 2) ((auxVar (m + 1) : Total L) ^ (j + 1)
          * (auxVar (m + 2) : Total L) ^ (n - 1 - j))
        = -((auxVar (m + 1) : Total L) ^ (j + 1)
            * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - (j : ℤ)))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hidx : ((n - 1 - j : ℕ) : ℤ) + 1 = (n : ℤ) - (j : ℤ) := by omega
    have h := dminusCM_auxVar_pow_mul q (m + 1) (n - 1 - j)
      (F := (auxVar (m + 1) : Total L) ^ (j + 1)) (hpow (j + 1))
    rw [show m + 1 + 1 = m + 2 from rfl] at h
    rw [show ((auxVar (m + 1) : Total L)) ^ (j + 1) * (auxVar (m + 2) : Total L) ^ (n - 1 - j)
        = (auxVar (m + 2) : Total L) ^ (n - 1 - j) * (auxVar (m + 1) : Total L) ^ (j + 1) from by
      ring, h, hidx, hmono (j + 1), hbopmono]
  have h3 : dminusCM q (m + 1) ((auxVar (m + 1) : Total L) ^ n)
      = -MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) + 1)) := by
    have h := dminusCM_auxVar_pow_mul q m n (F := (1 : Total L)) (one_mem _)
    rw [mul_one, bopExt_one] at h
    exact h
  have h4 : ∀ j ∈ Finset.range (n + 1),
      (auxVar (m + 1) : Total L) ^ (j + 1)
          * MvPolynomial.C (Sym.elemSymmAlt L (((n + 1 : ℕ) : ℤ) - 1 - (j : ℤ)))
        = (auxVar (m + 1) : Total L) ^ (j + 1)
          * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - (j : ℤ))) := by
    intro j _
    rw [show ((n + 1 : ℕ) : ℤ) - 1 - (j : ℤ) = (n : ℤ) - (j : ℤ) from by push_cast; ring]
  have hT1 : dminusCM q (m + 2) (braid q (m + 1) ((auxVar (m + 1) : Total L) ^ n))
      = -MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) + 1))
        - scal (1 - q) * ∑ j ∈ Finset.range n,
            (auxVar (m + 1) : Total L) ^ (j + 1)
              * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - (j : ℤ))) := by
    rw [braid_auxVar_pow q (by omega : 1 ≤ m + 1) n, show m + 1 + 1 = m + 2 from rfl, map_add,
      dminusCM_scal_mul, map_sum, Finset.sum_congr rfl h2, h1, Finset.sum_neg_distrib]
    ring
  have hT2 : qshift q (m + 1) (dminusCM q (m + 1) ((auxVar (m + 1) : Total L) ^ n))
      = -(MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) + 1))
          + scal (1 - q) * (∑ j ∈ Finset.range n,
              (auxVar (m + 1) : Total L) ^ (j + 1)
                * MvPolynomial.C (Sym.elemSymmAlt L ((n : ℤ) - (j : ℤ)))
            + (auxVar (m + 1) : Total L) ^ (n + 1))) := by
    rw [h3, map_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) from by push_cast; ring,
      qshift_C_elemSymmAlt, Finset.sum_congr rfl h4, Finset.sum_range_succ,
      show ((n : ℤ) - (n : ℤ)) = 0 from by ring, C_elemSymmAlt_zero, mul_one]
  rw [hT1, hT2]
  ring

end Reduced

/-! ### The word commutation and the monomial case -/

section Monomial

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d_-` commutes with the word `T_{[1,b]}`** for `b ≤ m`, read on `V_{m+2}`: every letter of the
word is one `HJO.Sweep.dminusCM_braid` covers
(`HJO.Sweep.dminusCM_mul_braidEnd`), and an element commuting with every letter commutes with the
product. -/
theorem dminusCM_mul_cmAscWord (q : L) {b m : ℕ} (hbm : b ≤ m) :
    dminusCM q (m + 2) * cmAscWord q 1 b = cmAscWord q 1 b * dminusCM q (m + 2) := by
  rw [cmAscWord_eq_ascendingWord q (by omega), Braid.ascendingWord]
  refine Braid.mul_prod_comm fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_range'_1] at hj
  exact dminusCM_mul_braidEnd q (by omega)

/-- `d_-(T_{[1,b]}F) = T_{[1,b]}(d_-F)` for `b ≤ m`, the applied form. -/
theorem dminusCM_cmAscWord (q : L) {b m : ℕ} (hbm : b ≤ m) (F : Total L) :
    dminusCM q (m + 2) (cmAscWord q 1 b F) = cmAscWord q 1 b (dminusCM q (m + 2) F) :=
  LinearMap.congr_fun (dminusCM_mul_cmAscWord q hbm) F

/-- `d_-` is linear over a `y`-monomial it cannot reach: the substitution `τ^-_{k+1,k+1}` fixes the
monomial and the coefficient extraction passes it. -/
theorem dminusCM_monomial_mul (q : L) {k : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < k)
    (H : Total L) :
    dminusCM q (k + 1) (MvPolynomial.monomial d (1 : Sym.Lambda L) * H)
      = MvPolynomial.monomial d 1 * dminusCM q (k + 1) H := by
  rw [dminusCM_succ_apply, map_mul, qshiftNeg_monomial,
    lowerCoeffShift_mul_of_mem_piece (monomial_one_mem_piece hd), ← dminusCM_succ_apply]

/-- **The reduced identity on a `y`-monomial of `V_k`**, `k = m + 1`:
`d_-(T_k(y^d)) - τ_{k,k}(d_-(y^d)) = (1-q)y_ky^d`.

Splitting `y^d = y^e y_k^n` with `e` supported below `k - 1` and pulling `y^e` out of every operator
— out of `T_k` because `s_k` fixes it, out of both readings of `d_-` because the extractions do not
read its variables, and out of `τ_{k,k}` because it is free of the alphabet — reduces the claim to
`HJO.Sweep.dminusCM_braid_auxVar_pow`. -/
theorem dminusCM_braid_sub_qshift_monomial (q : L) (m : ℕ) {d : ℕ →₀ ℕ}
    (hd : ∀ j ∈ d.support, j < m + 1) :
    dminusCM q (m + 2) (braid q (m + 1) (MvPolynomial.monomial d (1 : Sym.Lambda L)))
      - qshift q (m + 1) (dminusCM q (m + 1) (MvPolynomial.monomial d 1))
      = scal (1 - q) * ((auxVar (m + 1) : Total L) * MvPolynomial.monomial d 1) := by
  have hadd : Finsupp.erase m d + Finsupp.single m (d m) = d := Finsupp.erase_add_single m d
  have he : ∀ j ∈ (Finsupp.erase m d).support, j < m := by
    intro j hj
    rw [Finsupp.support_erase, Finset.mem_erase] at hj
    have := hd j hj.2
    omega
  have hGp : (MvPolynomial.monomial (Finsupp.erase m d) (1 : Sym.Lambda L) : Total L)
      ∈ piece L m := monomial_one_mem_piece he
  have hsplit : (MvPolynomial.monomial d (1 : Sym.Lambda L) : Total L)
      = MvPolynomial.monomial (Finsupp.erase m d) 1 * (auxVar (m + 1) : Total L) ^ (d m) := by
    rw [auxVar, Nat.add_sub_cancel, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
      one_mul, hadd]
  have hP : swapAux L (m + 1) (MvPolynomial.monomial (Finsupp.erase m d) (1 : Sym.Lambda L))
      = MvPolynomial.monomial (Finsupp.erase m d) 1 :=
    swapAux_of_mem_piece (by omega) hGp
  have hA : ∀ H : Total L,
      dminusCM q (m + 2) (MvPolynomial.monomial (Finsupp.erase m d) (1 : Sym.Lambda L) * H)
        = MvPolynomial.monomial (Finsupp.erase m d) 1 * dminusCM q (m + 2) H := by
    intro H
    have h := dminusCM_monomial_mul q (k := m + 1)
      (fun j hj => by have := he j hj; omega) H
    rw [show m + 1 + 1 = m + 2 from rfl] at h
    exact h
  have hB : ∀ H : Total L,
      dminusCM q (m + 1) (MvPolynomial.monomial (Finsupp.erase m d) (1 : Sym.Lambda L) * H)
        = MvPolynomial.monomial (Finsupp.erase m d) 1 * dminusCM q (m + 1) H :=
    fun H => dminusCM_monomial_mul q (k := m) he H
  rw [hsplit, braid_mul_of_swapAux_eq q hP, hA, hB, map_mul, qshift_monomial]
  linear_combination (MvPolynomial.monomial (Finsupp.erase m d) (1 : Sym.Lambda L) : Total L)
    * dminusCM_braid_auxVar_pow q m (d m)

/-- **The main result on a `y`-monomial of `V_k`**, `k = m + 1`. Splitting the word
`T_{[1,k]} = T_{[1,k-1]}T_k` and commuting `d_-` past the prefix puts `T_{[1,k-1]}` in front of
everything, and what is left is `HJO.Sweep.dminusCM_braid_sub_qshift_monomial`. -/
theorem cmCommutator_monomial (q : L) (m : ℕ) {d : ℕ →₀ ℕ} (hd : ∀ j ∈ d.support, j < m + 1) :
    dminusCM q (m + 2) (cmDPlus q (m + 1) (MvPolynomial.monomial d (1 : Sym.Lambda L)))
      - cmDPlus q m (dminusCM q (m + 1) (MvPolynomial.monomial d 1))
      = scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L)
          * MvPolynomial.monomial d 1) := by
  have hword : ∀ H : Total L,
      cmAscWord q 1 (m + 1) H = cmAscWord q 1 m (braid q (m + 1) H) := by
    intro H
    rw [cmAscWord_split q (c := m) (by omega) (by omega), cmAscWord_self]
    rfl
  have hdp : cmDPlus q (m + 1) (MvPolynomial.monomial d (1 : Sym.Lambda L))
      = cmAscWord q 1 m (braid q (m + 1) (MvPolynomial.monomial d 1)) := by
    rw [cmDPlus_apply, qshift_monomial, hword]
  rw [hdp, dminusCM_cmAscWord q (le_refl m), cmDPlus_apply, ← map_sub,
    dminusCM_braid_sub_qshift_monomial q m hd, cmAscWord_scal_mul]

end Monomial

/-! ### The twisted reduction and the main result -/

section Main

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **Both sides of `HJO.Sweep.dminusCM_cmDPlus_sub_cmDPlus_dminusCM` are linear over the image of
`tw_k`.** The left because the two operators intertwine the twisted action
(`HJO.Sweep.cmDPlus_twistedAction`, `HJO.Sweep.dminusCM_twistedAction`), which moves the rank of the
twist up and back down; the right because `tw_k(c)` is symmetric in `y_1, …, y_k`
(`HJO.Sweep.swapAux_twist`), hence passes every letter of the word `T_{[1,k-1]}`. -/
theorem cmCommutator_twist_mul (q : L) (m : ℕ) (c : Sym.Lambda L) {H : Total L}
    (hH : dminusCM q (m + 2) (cmDPlus q (m + 1) H) - cmDPlus q m (dminusCM q (m + 1) H)
      = scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * H)) :
    dminusCM q (m + 2) (cmDPlus q (m + 1) (twist L q (m + 1) c * H))
      - cmDPlus q m (dminusCM q (m + 1) (twist L q (m + 1) c * H))
      = scal (1 - q) * cmAscWord q 1 m
          ((auxVar (m + 1) : Total L) * (twist L q (m + 1) c * H)) := by
  have e1 : cmDPlus q (m + 1) (twist L q (m + 1) c * H)
      = twist L q (m + 2) c * cmDPlus q (m + 1) H := by
    have h := cmDPlus_twistedAction q (m + 1) c H
    rw [twistedAction_apply, twistedAction_apply, show m + 1 + 1 = m + 2 from rfl] at h
    exact h
  have e2 : ∀ Z : Total L, dminusCM q (m + 2) (twist L q (m + 2) c * Z)
      = twist L q (m + 1) c * dminusCM q (m + 2) Z := by
    intro Z
    have h := dminusCM_twistedAction q (m + 1) c Z
    rw [twistedAction_apply, twistedAction_apply, show m + 1 + 1 = m + 2 from rfl] at h
    exact h
  have e3 : dminusCM q (m + 1) (twist L q (m + 1) c * H)
      = twist L q m c * dminusCM q (m + 1) H := by
    have h := dminusCM_twistedAction q m c H
    rw [twistedAction_apply, twistedAction_apply] at h
    exact h
  have e4 : ∀ W : Total L, cmDPlus q m (twist L q m c * W)
      = twist L q (m + 1) c * cmDPlus q m W := by
    intro W
    have h := cmDPlus_twistedAction q m c W
    rw [twistedAction_apply, twistedAction_apply] at h
    exact h
  have e5 : cmAscWord q 1 m (twist L q (m + 1) c * ((auxVar (m + 1) : Total L) * H))
      = twist L q (m + 1) c * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * H) :=
    cmAscWord_mul_of_swapAux_eq q (by omega)
      (fun j hj1 hjm => swapAux_twist q hj1 (by omega) c) _
  rw [e1, e2, e3, e4, show (auxVar (m + 1) : Total L) * (twist L q (m + 1) c * H)
      = twist L q (m + 1) c * ((auxVar (m + 1) : Total L) * H) from by ring, e5]
  linear_combination (twist L q (m + 1) c : Total L) * hH

/-- **The last variable from the commutator.** For every `k ≥ 1` and every
`F ∈ V_k`,

`(d_-d_+ - d_+d_-)F = (1-q)T_1(T_2(⋯T_{k-1}(y_kF)⋯))`,

read at `k = m + 1`, so that the braid word is `T_{[1,m]}` of `HJO.Sweep.cmAscWord` and the
convention "the composite is the identity at `k = 1`" is the empty word at `m = 0`
(`HJO.Sweep.cmAscWord_self_pred`) with no truncated subtraction.

Three reductions, in the order. The word `T_{[1,k]}` inside `d_+` splits as
`T_{[1,k-1]}T_k` and `d_-` commutes with the prefix, which factors `T_{[1,k-1]}` out of everything;
both sides are linear over `tw_k(Λ)` (`HJO.Sweep.cmCommutator_twist_mul`) and `V_k` is generated by
`tw_k(Λ)` and the `y`-monomials, the substitution adding the alphabet `(q-1)(y_1+⋯+y_k)` being an
automorphism of the total space that preserves `V_k`; and on a `y`-monomial the operators are linear
over `𝕜[y_1, …, y_{k-1}]`, leaving a power of `y_k` and the computation
`HJO.Sweep.dminusCM_braid_auxVar_pow`.

`F ∈ V_k` is not decoration: at `k = 1`, `F = y_2` the identity fails. -/
@[hjo "lem_cm_commutator"]
theorem dminusCM_cmDPlus_sub_cmDPlus_dminusCM (q : L) (m : ℕ) {F : Total L}
    (hF : F ∈ piece L (m + 1)) :
    dminusCM q (m + 2) (cmDPlus q (m + 1) F) - cmDPlus q m (dminusCM q (m + 1) F)
      = scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * F) := by
  have hPaux : ∀ r, twistPowerSums q 1 0 (m + 1) r ∈ auxSubalg L :=
    fun r => twistPowerSums_mem_auxSubalg q 1 0 (m + 1) r
  have hPpiece : ∀ r, -twistPowerSums q 1 0 (m + 1) r ∈ piece L (m + 1) :=
    fun r => neg_mem (twistPowerSums_mem_piece q 1 (Nat.zero_le _) r)
  obtain ⟨G, hGmem, hGF⟩ : ∃ G : Total L, G ∈ piece L (m + 1) ∧
      alphabetShift (twistPowerSums q 1 0 (m + 1)) G = F :=
    ⟨alphabetShift (fun r => -twistPowerSums q 1 0 (m + 1) r) F,
      alphabetShift_mem_piece hPpiece hF, alphabetShift_alphabetShift_neg hPaux F⟩
  have hsub : ↑G.vars ⊆ Set.Iio (m + 1) := by
    have h := hGmem
    rw [piece, MvPolynomial.mem_supported] at h
    exact h
  have hdk : ∀ d ∈ G.support, ∀ j ∈ d.support, j < m + 1 := fun d hd j hj =>
    hsub ((MvPolynomial.mem_vars_iff_mem_support j).2 ⟨d, hd, hj⟩)
  have hexp : F = ∑ d ∈ G.support,
      twist L q (m + 1) (MvPolynomial.coeff d G) * MvPolynomial.monomial d 1 := by
    rw [← hGF]
    conv_lhs => rw [G.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [show (MvPolynomial.monomial d (MvPolynomial.coeff d G) : Total L)
        = MvPolynomial.C (MvPolynomial.coeff d G) * MvPolynomial.monomial d 1 from by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul,
      alphabetShift_of_mem_auxSubalg _ (monomial_one_mem_auxSubalg d)]
    congr 1
    exact twistedMult_C q 1 (m + 1) (MvPolynomial.coeff d G)
  obtain ⟨Δ, happ⟩ : ∃ Δ : Module.End L (Total L), ∀ H : Total L, Δ H
      = dminusCM q (m + 2) (cmDPlus q (m + 1) H) - cmDPlus q m (dminusCM q (m + 1) H)
        - scal (1 - q) * cmAscWord q 1 m ((auxVar (m + 1) : Total L) * H) :=
    ⟨dminusCM q (m + 2) * cmDPlus q (m + 1) - cmDPlus q m * dminusCM q (m + 1)
      - LinearMap.mulLeft L (scal (1 - q) : Total L) * cmAscWord q 1 m
        * LinearMap.mulLeft L (auxVar (m + 1) : Total L), fun H => rfl⟩
  have hzero : Δ F = 0 := by
    rw [hexp, map_sum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [happ, sub_eq_zero]
    exact cmCommutator_twist_mul q m (MvPolynomial.coeff d G)
      (cmCommutator_monomial q m (hdk d hd))
  exact sub_eq_zero.1 ((happ F).symm.trans hzero)

end Main

end HJO.Sweep
