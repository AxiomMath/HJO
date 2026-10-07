/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.HAlphabet
public import HJO.Collinear.Vocabulary
public meta import HJO.Attr

/-! # The two plethystic displacements on a single basis element

The displacement `δ` sends `p_j` to `p_j + (1 - qʲ)(1 - uʲ) wʲ`, so it adds to the alphabet the
four letters `(1 - q)(1 - u) w` -- one positive, one doubly scaled, two negated. Applying it to
`hₙ` therefore convolves `hₙ` against the complete homogeneous functions of that four-letter
alphabet, and those are known in closed form: in degree `s ≥ 1` the alphabet contributes the
single monomial `(1 - q)(1 - u)(1 - (q u)^s)/(1 - q u) · w^s`. The result is the whole content of
this file's first theorem,
`δ(hₙ) = hₙ + ∑_{j=1}^{n} (1 - q)(1 - u)(1 - (q u)ʲ)/(1 - q u) · h_{n-j} wʲ`,
a polynomial in `w` of degree at most `n` whose coefficients are again complete homogeneous
functions.

The starred displacement `δ*` subtracts the conjugate alphabet `(1 - q⁻¹)(1 - u⁻¹) w`, and the
corresponding statement is about the *elementary* functions rather than the complete homogeneous
ones. The bridge is the sign involution `ω₋`, the substitution scaling every `p_j` by `-1`: it
carries `hₙ` to `(-1)ⁿ eₙ`, and it also flips the sign of the `p`-part of `δ*`, turning the
subtraction into an addition of alphabets. Composing `δ*` with `ω₋` is thus again a sum of two
homomorphisms, the convolution formula applies verbatim, and conjugating back by `(-1)ⁿ` gives
`δ*(eₙ) = eₙ - ∑_{j=1}^{n} (-1)ʲ (1 - q)(1 - u)(1 - (q u)^{-j})/(1 - q u) · e_{n-j} wʲ`.

The whole analytic input is `Sym.completeHomog_scaled`, which computes the `h`-values of
`(1 - x)(1 - y) ζ` with the geometric denominator `1 - x y` cleared; the work here is to divide
by that denominator and to arrange the two homomorphisms whose sum the displacement is.

Over a general field this division needs hypotheses that come for free when working in
`ℚ(q, u)`: `q u ≠ 1` throughout, and in addition `q ≠ 0` and `u ≠ 0` for the starred statement,
whose scalars are inverse powers. They are necessary and not merely convenient. At `q u = 1` the
denominator `1 - q u` of the closed form vanishes while the coefficients
`(1 - qʲ)(1 - uʲ)` of the displacement itself are perfectly finite and not all zero, so no
closed form of this shape can hold there.
-/

@[expose] public section

open Finset

namespace HJO.Sym

variable {L : Type*} [Field L] [Algebra ℚ L]

/-! ### The four-letter alphabet the displacements add -/

/-- The alphabet the displacements attach to `w`: the `L`-algebra map `Λ → Λ[w]` sending `p_j` to
`(1 - xʲ)(1 - yʲ) wʲ`. It is the difference between a displacement and the inclusion
`Λ → Λ[w]`, taken as a homomorphism in its own right so that the convolution formula for the
complete homogeneous functions of a sum of alphabets can be applied to it. Nothing about `x` and
`y` is assumed; the unstarred displacement uses `x = q`, `y = u` and the starred one the inverses
`x = q⁻¹`, `y = u⁻¹`. -/
noncomputable def shiftPart (x y : L) : Lambda L →ₐ[L] Polynomial (Lambda L) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (MvPolynomial.C ((1 - x ^ (i + 1)) * (1 - y ^ (i + 1)))) * Polynomial.X ^ (i + 1)

omit [Algebra ℚ L] in
/-- The value of the four-letter alphabet on the generator of index `i`, which stands for
`p_{i+1}`. -/
theorem shiftPart_X (x y : L) (i : ℕ) :
    shiftPart x y (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.C ((1 - x ^ (i + 1)) * (1 - y ^ (i + 1)))) *
        Polynomial.X ^ (i + 1) :=
  MvPolynomial.aeval_X _ i

/-- **The complete homogeneous functions of the four-letter alphabet.** For `m ≥ 1` the alphabet
`(1 - x)(1 - y) w` has a single term in degree `m`, namely
`(1 - x)(1 - y)(1 - (x y)^m)/(1 - x y) · w^m`.

This is `completeHomog_scaled` read in `Λ[w]`, with the scalars `x`, `y` and the letter `w`
substituted, and with the denominator `1 - x y` divided out -- which is what `x y ≠ 1` is for.
In degree `0` the value is instead `1`, since every homomorphism sends `h₀ = 1` to `1`. -/
theorem shiftPart_completeHomog (x y : L) (hxy : x * y ≠ 1) {m : ℕ} (hm : 1 ≤ m) :
    shiftPart x y (completeHomog L m) =
      Polynomial.C (MvPolynomial.C ((1 - x) * (1 - y) * (1 - (x * y) ^ m) / (1 - x * y))) *
        Polynomial.X ^ m := by
  have hd : (1 : L) - x * y ≠ 0 := sub_ne_zero_of_ne (Ne.symm hxy)
  -- the two nested constant inclusions `L → Λ → Λ[w]` are the structure map of `Λ[w]` over `L`
  have hCC : ∀ c : L, (Polynomial.C (MvPolynomial.C c) : Polynomial (Lambda L)) =
      algebraMap L (Polynomial (Lambda L)) c := fun _ => rfl
  have hA : ∀ c : L, (1 : Polynomial (Lambda L)) - algebraMap L (Polynomial (Lambda L)) c =
      algebraMap L (Polynomial (Lambda L)) (1 - c) := fun c => by rw [map_sub, map_one]
  have hX : ∀ i : ℕ, shiftPart x y (MvPolynomial.X i) =
      (1 - algebraMap L (Polynomial (Lambda L)) x ^ (i + 1)) *
        (1 - algebraMap L (Polynomial (Lambda L)) y ^ (i + 1)) * Polynomial.X ^ (i + 1) := by
    intro i
    rw [shiftPart_X]
    congr 1
    change algebraMap L (Polynomial (Lambda L)) ((1 - x ^ (i + 1)) * (1 - y ^ (i + 1))) = _
    simp only [map_mul, map_sub, map_one, map_pow]
  have key := completeHomog_scaled (K := L) (shiftPart x y)
    (algebraMap L (Polynomial (Lambda L)) x) (algebraMap L (Polynomial (Lambda L)) y)
    Polynomial.X hX hm
  simp only [← map_mul, ← map_pow, hA] at key
  -- clear the denominator by multiplying with the scalar `(1 - x y)⁻¹`
  rw [hCC, ← one_mul (shiftPart x y (completeHomog L m)),
    ← show algebraMap L (Polynomial (Lambda L)) ((1 - x * y)⁻¹ * (1 - x * y)) = 1 from by
      rw [inv_mul_cancel₀ hd, map_one],
    map_mul, mul_assoc, key, ← mul_assoc, ← map_mul,
    show ((1 - x * y)⁻¹ * ((1 - x) * (1 - y) * (1 - (x * y) ^ m)) : L) =
      (1 - x) * (1 - y) * (1 - (x * y) ^ m) / (1 - x * y) from by rw [div_eq_mul_inv]; ring]

/-! ### The sign involution -/

/-- The sign involution `ω₋`: the diagonal substitution scaling every power sum by `-1`. It is
the plethysm by the negated alphabet `-X` up to the sign `(-1)ⁿ` in each degree, and it is what
exchanges the complete homogeneous and the elementary functions. -/
noncomputable def signFlip (L : Type*) [Field L] : Lambda L →ₐ[L] Lambda L :=
  diagScale fun _ => -1

omit [Algebra ℚ L] in
/-- The sign involution negates the generator of index `i`, which stands for `p_{i+1}`. -/
theorem signFlip_X (i : ℕ) : signFlip L (MvPolynomial.X i) = -MvPolynomial.X i := by
  rw [signFlip, diagScale_X, map_neg, map_one, neg_one_mul]

/-- **The sign involution exchanges the two bases.** `ω₋(hₙ) = (-1)ⁿ eₙ`: Newton's identity for
the complete homogeneous functions, read after scaling every `p_j` by `-1`, is Newton's identity
for the elementary ones. -/
theorem signFlip_completeHomog (n : ℕ) :
    signFlip L (completeHomog L n) = (-1) ^ n * elemSymm L n := by
  rw [completeHomog_neg_scale (signFlip L) 1 (fun i => by
    rw [signFlip_X, one_pow, map_one, one_mul]) n, one_pow, map_one, mul_one]

/-! ### The scalar identity behind the starred displacement -/

omit [Algebra ℚ L] in
/-- **The conjugate scalar is the original one with a sign.** For any `t`,
`(1 - q⁻¹)(1 - u⁻¹) t/(1 - (q u)⁻¹) = -(1 - q)(1 - u) t/(1 - q u)`.

Both sides are the same rational function: `(1 - q⁻¹)(1 - u⁻¹) = (q u)⁻¹ (1 - q)(1 - u)` and
`1 - (q u)⁻¹ = -(q u)⁻¹ (1 - q u)`, so the factor `(q u)⁻¹` cancels and a single sign is left
over. Inverting `q`, `u` and `1 - (q u)⁻¹` is what the three hypotheses are for. -/
theorem shiftStar_scalar (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (hqu : q * u ≠ 1) (t : L) :
    (1 - q⁻¹) * (1 - u⁻¹) * t / (1 - (q * u)⁻¹)
      = -((1 - q) * (1 - u) * t / (1 - q * u)) := by
  have hd : (1 : L) - q * u ≠ 0 := sub_ne_zero_of_ne (Ne.symm hqu)
  have hdi : (1 : L) - (q * u)⁻¹ ≠ 0 :=
    sub_ne_zero_of_ne fun h => hqu (inv_eq_one.mp h.symm)
  rw [neg_div', div_eq_div_iff hdi hd]
  field_simp
  ring

/-! ### The displacements on a single basis element -/

/-- **The displacement of a complete homogeneous function.** For `q u ≠ 1`,
`hₙ[X + M/z] = hₙ + ∑_{j=1}^{n} (1 - q)(1 - u)(1 - (q u)ʲ)/(1 - q u) · h_{n-j} wʲ`, written in
`w = z⁻¹`.

The displacement is the inclusion `Λ → Λ[w]` plus the four-letter alphabet
`(1 - q)(1 - u) w`, so its value on `hₙ` is the convolution of the two families of complete
homogeneous functions; the alphabet's are a single monomial in each positive degree and `1` in
degree zero, which is the term split off in front of the sum. The hypothesis `q u ≠ 1` is what
lets the closed form be divided by `1 - q u`: at `q u = 1` the displacement's coefficients
`(1 - qʲ)(1 - uʲ)` are still there while the denominator is gone. -/
@[hjo "lem_shift_h"]
theorem plethShift_completeHomog (q u : L) (hqu : q * u ≠ 1) (n : ℕ) :
    plethShift q u (completeHomog L n)
      = Polynomial.C (completeHomog L n)
        + ∑ j ∈ Finset.Icc 1 n,
            Polynomial.C (MvPolynomial.C
                ((1 - q) * (1 - u) * (1 - (q * u) ^ j) / (1 - q * u))
              * completeHomog L (n - j)) * Polynomial.X ^ j := by
  -- the displacement is the inclusion plus the four-letter alphabet
  have hadd : ∀ i : ℕ, plethShift q u (MvPolynomial.X i)
      = (Polynomial.C : Lambda L →+* Polynomial (Lambda L)) (MvPolynomial.X i)
        + shiftPart q u (MvPolynomial.X i) := by
    intro i
    rw [show plethShift q u (MvPolynomial.X i) = Polynomial.C (powerSum L (i + 1)) +
      Polynomial.C (MvPolynomial.C ((1 - q ^ (i + 1)) * (1 - u ^ (i + 1)))) *
        Polynomial.X ^ (i + 1) from MvPolynomial.aeval_X _ i, shiftPart_X,
      CopPower.powerSum_succ]
  -- convolve, then split off the degree-zero term of the alphabet
  rw [completeHomog_of_add (Polynomial.C : Lambda L →+* Polynomial (Lambda L)) (shiftPart q u)
    (plethShift q u) hadd n, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n),
    show Finset.Ico 1 (n + 1) = Finset.Icc 1 n from by ext s; simp,
    Nat.sub_zero, CopPower.completeHomog_zero, map_one, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [shiftPart_completeHomog q u hqu (Finset.mem_Icc.mp hs).1, map_mul]
  ring

/-- **The starred displacement of an elementary function.** For `q`, `u` nonzero with `q u ≠ 1`,
`eₙ[X - M̃/z] = eₙ - ∑_{j=1}^{n} (-1)ʲ (1 - q)(1 - u)(1 - (q u)^{-j})/(1 - q u) · e_{n-j} wʲ`,
written in `w = z⁻¹`.

Conjugating by the sign involution `ω₋` turns this into the unstarred statement: `ω₋` carries
`hₘ` to `(-1)ᵐ eₘ`, and `δ* ∘ ω₋` sends `p_j` to `-p_j + (1 - q^{-j})(1 - u^{-j}) wʲ`, a genuine
sum of the negated inclusion and the four-letter alphabet of the inverted parameters. The
convolution formula then applies, and the scalar of that alphabet is the unstarred scalar with a
sign, which is where the extra `(-1)ʲ` comes from.

Both `q ≠ 0` and `u ≠ 0` are needed for the inverse powers `q^{-j}`, `u^{-j}` to be what they
say, and `q u ≠ 1` again for the division by `1 - q u`. -/
@[hjo "lem_shift_star_e"]
theorem plethShiftStar_elemSymm (q u : L) (hq : q ≠ 0) (hu : u ≠ 0) (hqu : q * u ≠ 1) (n : ℕ) :
    plethShiftStar q u (elemSymm L n)
      = Polynomial.C (elemSymm L n)
        - ∑ j ∈ Finset.Icc 1 n,
            Polynomial.C (MvPolynomial.C
                ((-1) ^ j * ((1 - q) * (1 - u) * (1 - ((q * u) ^ j)⁻¹) / (1 - q * u)))
              * elemSymm L (n - j)) * Polynomial.X ^ j := by
  have hCC : ∀ c : L, (Polynomial.C (MvPolynomial.C c) : Polynomial (Lambda L))
      = algebraMap L (Polynomial (Lambda L)) c := fun _ => rfl
  have hqu' : q⁻¹ * u⁻¹ ≠ 1 := by
    rw [← mul_inv]
    exact fun h => hqu (inv_eq_one.mp h)
  -- the negated inclusion and the alphabet of the inverted parameters
  set φ : Lambda L →+* Polynomial (Lambda L) :=
    (Polynomial.C : Lambda L →+* Polynomial (Lambda L)).comp (signFlip L).toRingHom with hφdef
  set χ : Lambda L →+* Polynomial (Lambda L) :=
    (plethShiftStar q u).toRingHom.comp (signFlip L).toRingHom with hχdef
  have hφ : ∀ m : ℕ, φ (completeHomog L m)
      = (-1 : Polynomial (Lambda L)) ^ m * Polynomial.C (elemSymm L m) := by
    intro m
    change Polynomial.C (signFlip L (completeHomog L m)) = _
    rw [signFlip_completeHomog, map_mul, map_pow, map_neg, map_one]
  have hadd : ∀ i : ℕ, χ (MvPolynomial.X i)
      = φ (MvPolynomial.X i) + shiftPart q⁻¹ u⁻¹ (MvPolynomial.X i) := by
    intro i
    change plethShiftStar q u (signFlip L (MvPolynomial.X i))
      = Polynomial.C (signFlip L (MvPolynomial.X i)) + shiftPart q⁻¹ u⁻¹ (MvPolynomial.X i)
    rw [signFlip_X, map_neg, map_neg, plethShiftStar_X, shiftPart_X, inv_pow, inv_pow,
      CopPower.powerSum_succ]
    ring
  have hchi : χ (completeHomog L n)
      = (-1 : Polynomial (Lambda L)) ^ n * plethShiftStar q u (elemSymm L n) := by
    change plethShiftStar q u (signFlip L (completeHomog L n)) = _
    rw [signFlip_completeHomog, map_mul, map_pow, map_neg, map_one]
  have hneg2 : ((-1 : Polynomial (Lambda L)) ^ 2) = 1 := by ring
  have hsq : ((-1 : Polynomial (Lambda L)) ^ n) * ((-1) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hneg2, one_pow]
  -- the statement's sum reassembled out of the two nested constant inclusions
  have hR : ∀ (c : L) (m : ℕ) (f : Lambda L),
      (Polynomial.C (MvPolynomial.C ((-1 : L) ^ m * c) * f) : Polynomial (Lambda L))
        = (-1) ^ m * (algebraMap L (Polynomial (Lambda L)) c * Polynomial.C f) := by
    intro c m f
    rw [map_mul, map_mul, map_mul, hCC, hCC, map_pow, map_neg, map_one]
    ring
  have hmain := completeHomog_of_add φ (shiftPart q⁻¹ u⁻¹) χ hadd n
  rw [hchi] at hmain
  -- conjugate back: `(-1)ⁿ` is its own inverse
  have hstar : plethShiftStar q u (elemSymm L n)
      = ∑ s ∈ range (n + 1), (-1 : Polynomial (Lambda L)) ^ n *
          (φ (completeHomog L (n - s)) * shiftPart q⁻¹ u⁻¹ (completeHomog L s)) := by
    rw [← Finset.mul_sum, ← hmain, ← mul_assoc, hsq, one_mul]
  rw [hstar, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n),
    show Finset.Ico 1 (n + 1) = Finset.Icc 1 n from by ext s; simp,
    Nat.sub_zero, CopPower.completeHomog_zero, map_one, mul_one, hφ, ← mul_assoc, hsq, one_mul,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨hs1, hsn⟩ := Finset.mem_Icc.mp hs
  -- the two signs collapse to the single sign `(-1)ˢ` of the statement
  have hsign : ((-1 : Polynomial (Lambda L)) ^ n) * (-1) ^ (n - s) = (-1) ^ s := by
    rw [← pow_add, show n + (n - s) = 2 * (n - s) + s by omega, pow_add, pow_mul, hneg2,
      one_pow, one_mul]
  rw [hφ, shiftPart_completeHomog q⁻¹ u⁻¹ hqu' hs1, ← mul_inv, inv_pow,
    shiftStar_scalar q u hq hu hqu, map_neg, map_neg, hCC, hR, ← hsign]
  ring

end HJO.Sym
