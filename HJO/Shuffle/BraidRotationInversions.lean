/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.BraidInversions
public import HJO.Shuffle.BraidRotation
public meta import HJO.Attr

/-! # What a rigid rotation does to the `q`-exponent of
`HJO.Mellit.braidValueColouring_eq_dsc_floor`

`HJO.Mellit.braidValueColouring_eq_dsc_floor` reads `D_{\eta,c} = q^{e(v,\alpha)}R` with
`e(v,\alpha) = \frac12(\mathrm{inv_{fin}}(v,\alpha) - \mathrm{inv_{ini}}(v,\alpha))`, and
`HJO.Mellit.braidValueColouring_sweepRecursionsFloor` asserts that `R_-` and `R_+` are related by
the factor `\Phi_{\widehat P}(P)` **alone**. `HJO/Shuffle/BraidSweepRecursions.lean` shows that this
carries the unstated obligation `e_- = e_+`, that the obligation is not formal, and that the natural
argument for it — "at a separating level `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal` zeroes
both counts" — is false, because a bracketing pair of levels never both separate the diagonal.

This file computes `e_- - e_+` instead of assuming it away.

## The rotation formula

By `HJO.Mellit.sweepTheta_eq_div` a level drop acts on the position tuple as a **rigid rotation** of
the circle `\mathbb{R}/\mathbb{Z}` by one common amount `c`. A rotation splits the indices in two:
the **wrap set** `S := \{i : 1 - c \le v_i\}`, which lands in `[0, c)`, and its complement, which
lands in `[c, 1)`. Before the rotation every entry of `S` was above every entry of the complement;
after it, below. So the relative order inside each block survives and the order of every *cross*
pair is reversed, whence `HJO.Braid.tupleInversions_fract_add`:

```
inv(rotated) + crossPairs S = inv(v) + crossPairs Sᶜ,
```

with `crossPairs S` the number of pairs `i < j` with `i \in S`, `j \notin S`. Stated as two
`\mathbb{N}`-additions, so that no truncated subtraction enters.

Applying it to both members of `HJO.Braid.positionPair` gives
`HJO.Braid.invFin_sub_invIni_fract_add`:

```
2(e_- - e_+) = (crossPairs T ᶜ - crossPairs T) - (crossPairs S ᶜ - crossPairs S),
```

`S` the wrap set of the initial tuple and `T` that of the final tuple. **The exponent is not a
rotation invariant, and its defect is a difference of two cross-pair counts — the initial tuple's
and the final tuple's.** It vanishes only when the rotation wraps the two tuples across the same
pattern of pairs, which is a condition on the colouring.

## Why both tuples rotate, and only at type `E` for free

The hypotheses of the formula are that *both* members of the position pair rotate by the same `c`.
`HJO.Braid.iterate_nextCrossing_fract_add` supplies the second from the first: a rotation commutes
with the walk down a trajectory, both sides being `fract(x + c - j\theta)`, subject to the clause of
`HJO.Braid.IsAdmissibleMoveSeq` that keeps each `HJO.Braid.nextCrossing` honest. So at an event of
type `E`, where `HJO.Mellit.Isolates.notMem_colouringNorth_lo` leaves the crossed east steps and
every multiplicity unchanged, the final tuple rotates by the same `c` and the formula applies
outright. At types `C` and
`D` one entry moves beyond the rotation — a multiplicity rises at `C`, a top crossing rises at `D` —
so each needs one entry-local correction on top of this; at type `A` an entry is inserted as well.

## It is a genuine half-integer

`HJO.Braid.exists_crossPairs_defect_eq_neg_one` evaluates the defect at `\theta = 2/5`,
`\alpha = (2,1)`, `v = (1/5, 3/5)` rotated by `c = 3/5` — the witness of
`HJO.Braid.exists_rotation_invFin_sub_invIni_ne` — and gets `-1`. The wrap set of the initial tuple
is `\{1\}` and that of the final tuple `(4/5, 3/5)` is `\{0, 1\}`, so the two cross-pair defects are
`1` and `0`. Since `-1` is odd (`HJO.Braid.exists_crossPairs_defect_odd`), `e_+ - e_-` is a half
integer and **no clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` can be stated over
`\kk` alone**: the `q^{1/2}` extension of `HJO.Mellit.braidValueColouring_eq_dsc_floor` is
load-bearing at a sweep-internal level, and the claim that no extension of scalars by `\sqrt q` is
required is exactly what fails.

## References

This file concerns `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`,
`HJO.Mellit.braidValueColouring_eq_dsc_floor`, `HJO.Mellit.invFin_eq_invIni_of_separatesDiagonal`,
`HJO.Mellit.sweepTheta_eq_div`, using `HJO.Braid.positionPair`, `HJO.Braid.invIni`,
`HJO.Braid.invFin`, `HJO.Braid.IsAdmissibleMoveSeq`, `HJO.Braid.nextCrossing`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, section 5.
-/

@[expose] public section

open Finset

namespace HJO.Braid

variable {k : ℕ}

/-! ### The wrap set of a rotation -/

/-- **The wrap set of a rotation by `c`**: the indices the rotation carries past the top of the
circle, `1 - c ≤ v_i`. These are exactly the entries whose rotated value is `v_i + c - 1` rather
than `v_i + c`. -/
def wrapSet (v : Fin k → ℚ) (c : ℚ) : Finset (Fin k) :=
  {i ∈ (univ : Finset (Fin k)) | 1 - c ≤ v i}

@[simp]
theorem mem_wrapSet {v : Fin k → ℚ} {c : ℚ} {i : Fin k} : i ∈ wrapSet v c ↔ 1 - c ≤ v i := by
  simp [wrapSet]

/-- **The cross pairs of a set of indices**: the pairs `i < j` with `i` in the set and `j` out of
it. A rotation flips the order of exactly these pairs, in one direction for `S` and in the other for
its complement, so the two counts are the whole change in the inversion number. -/
def crossPairs (S : Finset (Fin k)) : ℕ :=
  #{p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S}

/-! ### The rotated entry -/

/-- Above the wrap the rotated entry is `v + c - 1`. -/
theorem fract_add_eq_sub_one {v c : ℚ} (hv1 : v < 1) (hc1 : c < 1) (h : 1 - c ≤ v) :
    Int.fract (v + c) = v + c - 1 := by
  have h1 : Int.fract (v + c) = Int.fract (v + c - 1) := by
    rw [show v + c - 1 = (v + c) + (((-1 : ℤ)) : ℚ) by push_cast; ring, Int.fract_add_intCast]
  rw [h1, Int.fract_eq_self]
  exact ⟨by linarith, by linarith⟩

/-- Below the wrap the rotated entry is `v + c`. -/
theorem fract_add_eq_self {v c : ℚ} (hv0 : 0 ≤ v) (hc0 : 0 ≤ c) (h : ¬ (1 - c ≤ v)) :
    Int.fract (v + c) = v + c := by
  rw [Int.fract_eq_self]
  exact ⟨by linarith, by linarith [not_le.1 h]⟩

/-! ### A rotation commutes with the move down the trajectory -/

/-- `fract` absorbs an inner `fract`. -/
private theorem fract_fract_add' (x d : ℚ) :
    Int.fract (Int.fract x + d) = Int.fract (x + d) := by
  have h : Int.fract x + d = (x + d) + (((-⌊x⌋ : ℤ)) : ℚ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_add_intCast]

/-- **A rigid rotation commutes with the whole walk down a trajectory**, so the *final* position
tuple of `HJO.Braid.positionPair` rotates by the same amount as the initial one. Both sides are
`fract (x + c - m\theta)`, by `HJO.Braid.iterate_nextCrossing_eq_fract` on each of them; the side
conditions are the `ne_theta` clause of `HJO.Braid.IsSpecialBraidData` on the original walk and on
the rotated one. -/
theorem iterate_nextCrossing_fract_add {θ c x : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (hf0 : 0 < Int.fract (x + c)) (m : ℕ)
    (hne : ∀ j < m, (nextCrossing θ)^[j] x ≠ θ)
    (hne' : ∀ j < m, (nextCrossing θ)^[j] (Int.fract (x + c)) ≠ θ) :
    (nextCrossing θ)^[m] (Int.fract (x + c)) = Int.fract ((nextCrossing θ)^[m] x + c) := by
  rw [iterate_nextCrossing_eq_fract hθ0 hθ1 hf0 (Int.fract_lt_one _) m
      (fun j hj => hne' j hj),
    iterate_nextCrossing_eq_fract hθ0 hθ1 hx0 hx1 m (fun j hj => hne j hj),
    show Int.fract (x + c) - (m : ℚ) * θ = Int.fract (x + c) + (-((m : ℚ) * θ)) by ring,
    fract_fract_add', fract_fract_add']
  congr 1
  ring

/-! ### The inversion count across a rotation -/

/-- **THE ROTATION FORMULA: a rigid rotation changes the inversion count by the signed cross-pair
count of its wrap set.** For entries in `[0, 1)` and a rotation `c ∈ [0, 1)`,

```
inv(rotated) + crossPairs (wrapSet v c) = inv(v) + crossPairs (wrapSet v c)ᶜ.
```

The reason is that the rotation splits the indices in two, `S := wrapSet v c` landing in `[0, c)`
and its complement in `[c, 1)`, whereas *before* the rotation every entry of `S` was above every
entry of the complement. So the relative order inside each block is untouched and the order of
every cross pair is reversed: an inversion `i < j` with `i ∈ S`, `j ∉ S` is destroyed and one with
`i ∉ S`, `j ∈ S` is created. Both counts are stated as `ℕ`-additions to avoid truncated
subtraction.

This is the missing bookkeeping of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`: by
`HJO.Mellit.sweepTheta_eq_div` a level drop rotates the position tuple rigidly, so this computes the
change in `HJO.Braid.invIni` and `HJO.Braid.invFin`, and hence in the exponent
`\frac12(\mathrm{inv_{fin}} - \mathrm{inv_{ini}})` that
`HJO.Mellit.braidValueColouring_eq_dsc_floor` carries. -/
@[hjo "lem_braid_rotation_inversions"]
theorem tupleInversions_fract_add (v : Fin k → ℚ) {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i < 1) :
    tupleInversions (fun i => Int.fract (v i + c)) + crossPairs (wrapSet v c)
      = tupleInversions v + crossPairs (wrapSet v c)ᶜ := by
  classical
  -- the value of each rotated entry, and the two blocks it lands in
  have hvalin : ∀ i, i ∈ wrapSet v c → Int.fract (v i + c) = v i + c - 1 := by
    intro i hi
    exact fract_add_eq_sub_one (hv1 i) hc1 (mem_wrapSet.1 hi)
  have hvalout : ∀ i, i ∉ wrapSet v c → Int.fract (v i + c) = v i + c := by
    intro i hi
    exact fract_add_eq_self (hv0 i) hc0 (by simpa using hi)
  have hin : ∀ i, i ∈ wrapSet v c → Int.fract (v i + c) < c := by
    intro i hi
    rw [hvalin i hi]
    linarith [hv1 i]
  have hout : ∀ i, i ∉ wrapSet v c → c ≤ Int.fract (v i + c) := by
    intro i hi
    rw [hvalout i hi]
    linarith [hv0 i]
  have hordin : ∀ i j, i ∈ wrapSet v c → j ∈ wrapSet v c →
      (Int.fract (v j + c) < Int.fract (v i + c) ↔ v j < v i) := by
    intro i j hi hj
    rw [hvalin i hi, hvalin j hj]
    constructor <;> intro h <;> linarith
  have hordout : ∀ i j, i ∉ wrapSet v c → j ∉ wrapSet v c →
      (Int.fract (v j + c) < Int.fract (v i + c) ↔ v j < v i) := by
    intro i j hi hj
    rw [hvalout i hi, hvalout j hj]
    constructor <;> intro h <;> linarith
  -- the four finsets
  set A : Finset (Fin k × Fin k) :=
    {p ∈ (univ : Finset (Fin k × Fin k)) |
      p.1 < p.2 ∧ Int.fract (v p.2 + c) < Int.fract (v p.1 + c)} with hA
  set B : Finset (Fin k × Fin k) :=
    {p ∈ (univ : Finset (Fin k × Fin k)) |
      p.1 < p.2 ∧ p.1 ∈ wrapSet v c ∧ p.2 ∉ wrapSet v c} with hB
  set C : Finset (Fin k × Fin k) :=
    {p ∈ (univ : Finset (Fin k × Fin k)) | p.1 < p.2 ∧ v p.2 < v p.1} with hC
  set D : Finset (Fin k × Fin k) :=
    {p ∈ (univ : Finset (Fin k × Fin k)) |
      p.1 < p.2 ∧ p.1 ∉ wrapSet v c ∧ p.2 ∈ wrapSet v c} with hD
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    obtain ⟨-, -, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨-, -, h1, h2'⟩ := Finset.mem_filter.1 hp'
    exact absurd h2 (by linarith [hin _ h1, hout _ h2'])
  have hCD : Disjoint C D := by
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    obtain ⟨-, -, h2⟩ := Finset.mem_filter.1 hp
    obtain ⟨-, -, h1, h2'⟩ := Finset.mem_filter.1 hp'
    have hv1' := mem_wrapSet.1 h2'
    have hv2' := not_le.1 (by simpa using h1)
    exact absurd h2 (by linarith)
  have hunion : A ∪ B = C ∪ D := by
    ext p
    simp only [Finset.mem_union, hA, hB, hC, hD, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hlt, hfr⟩ | ⟨hlt, h1, h2⟩)
      · by_cases h1 : p.1 ∈ wrapSet v c <;> by_cases h2 : p.2 ∈ wrapSet v c
        · exact Or.inl ⟨hlt, (hordin _ _ h1 h2).1 hfr⟩
        · exact absurd hfr (by linarith [hin _ h1, hout _ h2])
        · exact Or.inr ⟨hlt, h1, h2⟩
        · exact Or.inl ⟨hlt, (hordout _ _ h1 h2).1 hfr⟩
      · refine Or.inl ⟨hlt, ?_⟩
        have := mem_wrapSet.1 h1
        have := not_le.1 (by simpa using h2)
        linarith
    · rintro (⟨hlt, hlt'⟩ | ⟨hlt, h1, h2⟩)
      · by_cases h1 : p.1 ∈ wrapSet v c <;> by_cases h2 : p.2 ∈ wrapSet v c
        · exact Or.inl ⟨hlt, (hordin _ _ h1 h2).2 hlt'⟩
        · exact Or.inr ⟨hlt, h1, h2⟩
        · refine absurd hlt' (by
            have := mem_wrapSet.1 h2
            have := not_le.1 (by simpa using h1)
            linarith)
        · exact Or.inl ⟨hlt, (hordout _ _ h1 h2).2 hlt'⟩
      · exact Or.inl ⟨hlt, by linarith [hin _ h2, hout _ h1]⟩
  -- identify the four cards
  have hcardA : tupleInversions (fun i => Int.fract (v i + c)) = #A := by
    rw [tupleInversions_eq_card_lt, hA]
  have hcardC : tupleInversions v = #C := by rw [tupleInversions_eq_card_lt, hC]
  have hcardB : crossPairs (wrapSet v c) = #B := by rw [crossPairs, hB]
  have hcardD : crossPairs (wrapSet v c)ᶜ = #D := by
    rw [crossPairs, hD]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_not]
  rw [hcardA, hcardB, hcardC, hcardD, ← Finset.card_union_of_disjoint hAB,
    ← Finset.card_union_of_disjoint hCD, hunion]

/-! ### The exponent of `HJO.Mellit.braidValueColouring_eq_dsc_floor` across a level drop -/

/-- **THE `q`-EXPONENT OF `HJO.Mellit.braidValueColouring_eq_dsc_floor` ACROSS ONE LEVEL DROP.**
Write `e(v, α) := \frac12(\mathrm{inv_{fin}}(v,α) - \mathrm{inv_{ini}}(v,α))`, the exponent
`HJO.Mellit.braidValueColouring_eq_dsc_floor` carries. If the level drop rotates the initial
position tuple by `c` and the final position tuple by the same `c` — which is what
`HJO.Mellit.sweepTheta_eq_div` gives at an event of type `C` or `E`, both tuples being read off
crossing abscissae of the same antidiagonal indices — then, doubled to stay in `ℤ`,

```
2(e_- - e_+) = (X(v^fin)ᶜ - X(v^fin)) - (X(v)ᶜ - X(v)),
```

where `X(w) := crossPairs (wrapSet w c)`. So the exponent is **not** a rotation invariant, and the
defect is a difference of two cross-pair counts: the initial tuple's and the final tuple's. It
vanishes exactly when the rotation wraps the two tuples across the same pattern of pairs, which is
a condition on the colouring and not a formality — `HJO.Braid.exists_rotation_invFin_sub_invIni_ne`
exhibits a rotation where it fails.

Consequence for `HJO.Mellit.braidValueColouring_sweepRecursionsFloor`: since
`D_{η_±,c_±} = q^{e_±}R_±`, each of its clauses carries the factor `q^{e_+ - e_-}` on top of `Φ`,
and `e_+ - e_-` is the number above with the sign reversed and halved. It is a half-integer in
general, which is exactly why the `q^{1/2}` extension of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` cannot be dropped at a sweep-internal level. -/
@[hjo "lem_braid_rotation_exponent"]
theorem invFin_sub_invIni_fract_add (θ : ℚ) {v v' : Fin k → ℚ} {α : Fin k → ℕ} {c : ℚ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i < 1)
    (hf0 : ∀ i, 0 ≤ (positionPair θ v α).2 i) (hf1 : ∀ i, (positionPair θ v α).2 i < 1)
    (hrot : ∀ i, v' i = Int.fract (v i + c))
    (hrotf : ∀ i, (positionPair θ v' α).2 i = Int.fract ((positionPair θ v α).2 i + c)) :
    (((invFin θ v' α : ℤ) - (invIni θ v' α : ℤ))
        - ((invFin θ v α : ℤ) - (invIni θ v α : ℤ)))
      = (((crossPairs (wrapSet (positionPair θ v α).2 c)ᶜ : ℤ)
            - (crossPairs (wrapSet (positionPair θ v α).2 c) : ℤ))
          - ((crossPairs (wrapSet v c)ᶜ : ℤ) - (crossPairs (wrapSet v c) : ℤ))) := by
  have hini := tupleInversions_fract_add v hc0 hc1 hv0 hv1
  have hfin := tupleInversions_fract_add (positionPair θ v α).2 hc0 hc1 hf0 hf1
  have hini' : tupleInversions v' = tupleInversions (fun i => Int.fract (v i + c)) := by
    congr 1
    exact funext hrot
  have hfin' : tupleInversions (positionPair θ v' α).2
      = tupleInversions (fun i => Int.fract ((positionPair θ v α).2 i + c)) := by
    congr 1
    exact funext hrotf
  rw [invIni_eq_tupleInversions, invIni_eq_tupleInversions, invFin, invFin, hini', hfin']
  omega

/-- **THE DEFECT IS ODD IN AN INSTANCE, so the `q^{1/2}` of
`HJO.Mellit.braidValueColouring_eq_dsc_floor` is not removable at a sweep-internal level.** The
witness is the one of `HJO.Braid.exists_rotation_invFin_sub_invIni_ne`, read through
`HJO.Braid.invFin_sub_invIni_fract_add`: at `θ = 2/5`, `α = (2, 1)`, `v = (1/5, 3/5)` and `c = 3/5`,
the initial tuple has wrap set `{1}` and the final tuple `(4/5, 3/5)` has wrap set `{0, 1}`, so the
doubled defect is `(0 - 0) - (1 - 0) = -1`. Since that is odd, `e_+ - e_-` is a genuine half-integer
and no clause of `HJO.Mellit.braidValueColouring_sweepRecursionsFloor` can be stated over `\kk`
alone.

The two tuples here really are the two tuples of the cited witness, and the *final* tuple really is
the `c`-rotation of the original final tuple — `fract(4/5 + 3/5) = 2/5`, `fract(3/5 + 3/5) = 1/5` —
so this is the formula's hypothesis satisfied, not a coincidence of two unrelated tuples. -/
@[hjo "lem_braid_rotation_exponent"]
theorem exists_crossPairs_defect_eq_neg_one :
    ∃ (θ c : ℚ) (v : Fin 2 → ℚ) (α : Fin 2 → ℕ), 0 ≤ c ∧ c < 1 ∧
      (∀ i, 0 ≤ v i ∧ v i < 1) ∧
      (∀ i, 0 ≤ (positionPair θ v α).2 i ∧ (positionPair θ v α).2 i < 1) ∧
      (((crossPairs (wrapSet (positionPair θ v α).2 c)ᶜ : ℤ)
            - (crossPairs (wrapSet (positionPair θ v α).2 c) : ℤ))
          - ((crossPairs (wrapSet v c)ᶜ : ℤ) - (crossPairs (wrapSet v c) : ℤ))) = -1 := by
  refine ⟨2 / 5, 3 / 5, fun i => if i = 0 then 1 / 5 else 3 / 5,
    fun i => if i = 0 then 2 else 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The doubled defect of `HJO.Braid.exists_crossPairs_defect_eq_neg_one` is odd, so `e_+ - e_-` is
a half-integer there and the `q^{1/2}` extension of `HJO.Mellit.braidValueColouring_eq_dsc_floor` is
not removable. -/
@[hjo "lem_braid_rotation_exponent"]
theorem exists_crossPairs_defect_odd :
    ∃ (θ c : ℚ) (v : Fin 2 → ℚ) (α : Fin 2 → ℕ), 0 ≤ c ∧ c < 1 ∧
      (∀ i, 0 ≤ v i ∧ v i < 1) ∧
      (∀ i, 0 ≤ (positionPair θ v α).2 i ∧ (positionPair θ v α).2 i < 1) ∧
      ¬ (2 ∣ (((crossPairs (wrapSet (positionPair θ v α).2 c)ᶜ : ℤ)
            - (crossPairs (wrapSet (positionPair θ v α).2 c) : ℤ))
          - ((crossPairs (wrapSet v c)ᶜ : ℤ) - (crossPairs (wrapSet v c) : ℤ)))) := by
  obtain ⟨θ, c, v, α, h1, h2, h3, h4, h5⟩ := exists_crossPairs_defect_eq_neg_one
  exact ⟨θ, c, v, α, h1, h2, h3, h4, by rw [h5]; decide⟩

end HJO.Braid

end
