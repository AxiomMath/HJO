/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepIndexShift
public import HJO.Shuffle.SweepAppendBandRounds
public import HJO.Shuffle.MellitShiftGenerators
public import HJO.CMStructure.VmodCommutatorMod
public import HJO.CMStructure.TwistedStarMult
public meta import HJO.Attr

/-!
# The index shift of the three sweep generators IS the variable shift

`HJO.Mellit.baseRoundWord_appendHeights` leaves the round-grouping with one residual: the base layer
of round `e` of an extension is the base's own point list, in the base's own order, read with every
width raised by the single integer `δ = #(tailLiveSteps w e)`. So one must relate `d^♭_-`, `d^♭_+`
and `Δ` at index `k + δ` to the same operators at index `k`.

The comparisons in `HJO/Shuffle/SweepIndexShift.lean` all do this by asking for a
**graded piece of the incoming vector**, and they ask for the wrong one:
`HJO.Sweep.dminus_eq_of_mem_piece` needs `F ∈ V_{k-1}` to move the index, whereas the vector
arriving
at a base event of the extension genuinely reads the `δ` variables the tail's live north steps
opened, so only `F ∈ V_{k+δ}` is available. The gap is `δ + 1` pieces and no count of lattice points
closes it.

**That gap is an artefact of asking for an equality.** The three operators do not become equal; they
become *conjugate*, by the variable shift, and the conjugation costs no hypothesis at all — no `q`,
no `u`, no membership, no coprimality. This file computes it.

## Main results

Write `Σ_δ` for `HJO.Sweep.shiftAux`, the `Λ`-algebra map `y_i ↦ y_{i+δ}`, and `T_{[1,δ]}` for
`HJO.Sweep.cmAscWord q 1 δ`.

* `HJO.Sweep.dminus_shiftAux`: **`d^♭_-` shifts freely.**
  `d^♭_-{}^{(k+δ)}(Σ_δ F) = Σ_δ(d^♭_-{}^{(k)}F)` for every `F`, on `1 ≤ k`. No correction term.
* `HJO.Sweep.dplus_shiftAux`: **`d^♭_+` shifts at the cost of one prefix word.**
  `d^♭_+{}^{(k+δ)}(Σ_δ F) = T_{[1,δ]}(Σ_δ(d^♭_+{}^{(k)}F))` for every `F` and every `k`, with no
hypothesis whatsoever. The correction is the **same** word `T_{[1,δ]}` at every `k` — it reads only
  the shift, not the index — which is what makes it usable on a whole layer of a round, where by
  `HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` the shift is one integer while the widths
  vary.
* `HJO.Sweep.corner_shiftAux`: **`Δ` shifts at the cost of the same prefix word.**
  `Δ^{(k+δ)}(Σ_δ F) = T_{[1,δ]}(Σ_δ(Δ^{(k)}F))` on `1 ≤ k`, again with no hypothesis on `q` or `F` —
  in particular not `q ≠ 1`, which the closed form `HJO.Sweep.corner_transport_eq` needs.
* `HJO.Sweep.dminus_shiftAux_mul`, `HJO.Sweep.dplus_shiftAux_mul`,
  `HJO.Sweep.corner_shiftAux_mul`: the same three statements **off the image of `Σ_δ`**, on
  `g · Σ_δ F` with `g` a `y`-polynomial with scalar coefficients in the `δ` variables the tail
  opened (`g ∈ HJO.Sweep.auxSubalg L` and `g ∈ V_δ`). That this reaches the whole of `V_{k+δ}` —
  where the vector at a base event actually lives — is
  `HJO.Sweep.exists_mul_shiftAux_of_monomial`: every `y`-monomial of the piece splits as such a
  product.
* `HJO.Mellit.sweepOperator_shiftAux_appendHeights_A` and its four siblings `_B`, `_C`, `_D`, `_E`:
  the resulting statement at a base event of the extension, one per rule of
  `HJO.Mellit.sweepOperator`. Rules `B` and `E` shift freely, rule `D` pays the scalar `q^δ`, and
  rules `A` and `C` pay the one word `T_{[1,δ]}`; rule `C` additionally pays `q^{-δ}`, which cancels
  rule `D`'s and is the only clause needing `q ≠ 0`.

The supporting intertwiners are `HJO.Sweep.shiftAux_qshift`, `HJO.Sweep.shiftAux_qshiftNeg`,
`HJO.Sweep.lowerCoeff_shiftAux`, `HJO.Sweep.shiftAux_dividedDiff`, `HJO.Sweep.shiftAux_braid` and
`HJO.Sweep.shiftAux_cmAscWord`: every constituent of the three generators reads its index through a
variable, so relabelling the variables relabels the index.

Two of those comparisons are also freed of their hypotheses, which is where the `δ + 1`-piece gap is
visibly not irreducible: `HJO.Sweep.dminus_succ_eq_swapAux` and
`HJO.Sweep.dplus_succ_eq_dplus_swapAux_add` are `HJO.Sweep.dminus_succ_eq_of_mem_piece` and
`HJO.Sweep.dplus_succ_eq_dplus_add` with `F ∈ V_k` deleted and `s_{k+1}F` written where the
hypothesis used to let one write `F`.

## What this does and does not close

It computes the residual of the round-grouping **at a single event**, exactly, on the whole graded
piece the incoming vector lies in, and with no genericity beyond `q ≠ 0` at rule `C`. So the
residual
that `HJO.Mellit.baseRoundWord_appendHeights` left is no longer an obstruction but a formula.

It does **not** close the band identity, and what is missing is now a different thing and a visible
one. The low factor `g` does not survive the correction: `T_{[1,δ]}` acts on exactly the `δ`
variables
`g` is built from, so it cannot be moved past `g`, and the answer at a type-`A` or type-`C` event is
`T_{[1,δ]}(g · Σ_δ(…))` with the low factor **inside** the word. Applying the next event's
comparison
needs its argument back in the form `g' · Σ_δ(F')`, and `T_{[1,δ]}(g · Σ_δ H)` is not of that form:
the word mixes `y_δ` and `y_{δ+1}`, hence the top of the low factor with the bottom of the shifted
one. So what remains is a **propagation** along the layer, not a comparison at an event:

* push the `T_{[1,δ]}` produced at each type-`A` or type-`C` event leftwards past the operators of
  the events applied after it — `HJO.Sweep.dminus_cmAscWord` does this for `d^♭_-` at a high enough
  index and is what makes `HJO.Sweep.corner_shiftAux` work, so the letter-commutation half is not
  hypothetical;
* and then match the accumulated words, together with the tail layers of
`HJO.Mellit.roundSweepWord_split_fst`, against `HJO.Mellit.stageTotal` on the other side — whose own
  `HJO.Sweep.dplusStar` carries a letter shift of the same kind (`HJO.Sweep.cycleShift`,
  `y_i ↦ y_{i+1}`), which is the reason to expect the match rather than merely to hope for it.

Note that the `δ` of one round is not the `δ` of the next
(`HJO.Paths.card_liveSteps_high_appendHeights_ne`
exhibits two tails of one fibre with corrections `2` and `1`), so the propagation is genuinely per
round and the tail layers between rounds are what reconcile consecutive shifts.

## References

A. Mellit, *Toric braids and `(m, n)`-parking functions*, sections 4 and 6.
-/

@[expose] public section

namespace HJO.Sweep

/-! ### The variable shift -/

section Shift

variable {L : Type*} [CommRing L]

/-- **The variable shift `Σ_δ : y_i ↦ y_{i+δ}`**, a `Λ`-algebra endomorphism of the total space.

This is the map the index shift of the three sweep generators turns out to be a conjugation by. It
is
injective, its image being the `Λ`-subalgebra on `y_{δ+1}, y_{δ+2}, …`, and it carries `V_k` into
`V_{k+δ}`; what it is *not* is surjective, which is the whole of what `HJO.Sweep.dminus_shiftAux`
and
its siblings leave open. -/
@[hjo "def_sweep_var_shift"]
noncomputable def shiftAux (L : Type*) [CommRing L] (δ : ℕ) :
    Total L →ₐ[Sym.Lambda L] Total L :=
  MvPolynomial.rename (· + δ)

@[simp] theorem shiftAux_X (δ j : ℕ) :
    shiftAux L δ (MvPolynomial.X j) = MvPolynomial.X (j + δ) := by
  simp [shiftAux]

@[hjo "def_sweep_var_shift", simp] theorem shiftAux_C (δ : ℕ) (c : Sym.Lambda L) :
    shiftAux L δ (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [shiftAux]

theorem shiftAux_monomial (δ : ℕ) (d : ℕ →₀ ℕ) (c : Sym.Lambda L) :
    shiftAux L δ (MvPolynomial.monomial d c)
      = MvPolynomial.monomial (Finsupp.mapDomain (· + δ) d) c := by
  rw [shiftAux, MvPolynomial.rename_monomial]

/-- **`Σ_δ` shifts the auxiliary variables**: `Σ_δ(y_i) = y_{i+δ}` for `i ≥ 1`. The hypothesis is
`HJO.Sweep.auxVar`'s convention `y_0 = y_1`, at which the statement is false. -/
@[hjo "def_sweep_var_shift"]
theorem shiftAux_auxVar (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    shiftAux L δ (auxVar i : Total L) = auxVar (i + δ) := by
  have h : i - 1 + δ = i + δ - 1 := by omega
  rw [auxVar, auxVar, shiftAux_X, h]

/-- **`Σ_δ` moves the index of an adjacent interchange**: `Σ_δ s_i = s_{i+δ} Σ_δ` for `i ≥ 1`. Both
sides are relabellings, so all that is checked is the identity of maps `ℕ → ℕ` that renames the two
indices the transposition reads. -/
theorem shiftAux_swapAux (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (swapAux L i F) = swapAux L (i + δ) (shiftAux L δ F) := by
  have h : (shiftAux L δ).comp (swapAux L i).toAlgHom
      = (swapAux L (i + δ)).toAlgHom.comp (shiftAux L δ) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    rw [swapAux_X, shiftAux_X, shiftAux_X, swapAux_X]
    congr 1
    by_cases h1 : j = i - 1
    · subst h1
      rw [Equiv.swap_apply_left, show i - 1 + δ = i + δ - 1 from by omega, Equiv.swap_apply_left]
    · by_cases h2 : j = i
      · subst h2
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
  exact congrArg (fun f : Total L →ₐ[Sym.Lambda L] Total L => f F) h

end Shift

/-! ### The shift moves the index of the divided difference and the braid operator -/

section Braid

variable {L : Type*} [Field L]

@[simp] theorem shiftAux_scal (δ : ℕ) (x : L) : shiftAux L δ (scal x : Total L) = scal x := by
  rw [scal, shiftAux_C]

/-- `Σ_δ` is `L`-linear, `L` acting through `Λ`. -/
theorem shiftAux_smul (δ : ℕ) (x : L) (F : Total L) :
    shiftAux L δ (x • F) = x • shiftAux L δ F := by
  have h : ∀ G : Total L, x • G = (scal x : Total L) * G := fun G => by
    rw [scal_eq_algebraMap]
    exact Algebra.smul_def x G
  rw [h, h, map_mul, shiftAux_scal]

/-- **`Σ_δ` moves the index of the divided difference**: `Σ_δ(∂_i F) = ∂_{i+δ}(Σ_δ F)` for `i ≥ 1`.
By `HJO.Sweep.dividedDiff_unique` it is enough that `Σ_δ` carries the numerator and the denominator
of `∂_i` to those of `∂_{i+δ}`, and both are read off `HJO.Sweep.shiftAux_X` and
`HJO.Sweep.shiftAux_swapAux`. -/
theorem shiftAux_dividedDiff (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (dividedDiff i F) = dividedDiff (i + δ) (shiftAux L δ F) := by
  refine dividedDiff_unique (show 1 ≤ i + δ by omega) ?_
  have hsub : (MvPolynomial.X (i + δ) - MvPolynomial.X (i + δ - 1) : Total L)
      = shiftAux L δ (MvPolynomial.X i - MvPolynomial.X (i - 1)) := by
    rw [map_sub, shiftAux_X, shiftAux_X, show i - 1 + δ = i + δ - 1 from by omega]
  rw [hsub, ← map_mul, dividedDiff_spec, map_sub, shiftAux_swapAux δ hi]

/-- **`Σ_δ` moves the index of the braid operator**: `Σ_δ(T_i F) = T_{i+δ}(Σ_δ F)` for `i ≥ 1`.
Every letter of `HJO.Sweep.braid_apply` moves: the interchange by `HJO.Sweep.shiftAux_swapAux`, the
variable by `HJO.Sweep.shiftAux_auxVar`, the divided difference by
`HJO.Sweep.shiftAux_dividedDiff`, and the scalar not at all. -/
theorem shiftAux_braid (q : L) (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (braid q i F) = braid q (i + δ) (shiftAux L δ F) := by
  rw [braid_apply, braid_apply, map_add, map_mul, map_mul, shiftAux_scal,
    shiftAux_auxVar δ hi, shiftAux_dividedDiff δ hi, shiftAux_swapAux δ hi]

/-- `HJO.Sweep.shiftAux_braid` for the `L`-linear form of the braid operator. -/
theorem shiftAux_braidEnd (q : L) (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (braidEnd q i F) = braidEnd q (i + δ) (shiftAux L δ F) :=
  shiftAux_braid q δ hi F

/-- **`Σ_δ` moves the index range of an ascending word**:
`Σ_δ(T_{[c+1,c+d]}F) = T_{[c+1+δ,c+d+δ]}(Σ_δ F)`.

Stated in the shape `a = c+1`, `b = c+d` because the empty convention
`HJO.Sweep.cmAscWord_self_pred` is `T_{[c+1,c]} = 1` and the induction is on the length `d`. Each
step peels the rightmost letter with `HJO.Sweep.cmAscWord_split` and moves it with
`HJO.Sweep.shiftAux_braidEnd`. -/
theorem shiftAux_cmAscWord (q : L) (δ c d : ℕ) (F : Total L) :
    shiftAux L δ (cmAscWord q (c + 1) (c + d) F)
      = cmAscWord q (c + 1 + δ) (c + d + δ) (shiftAux L δ F) := by
  induction d generalizing F with
  | zero =>
    simp only [Nat.add_zero]
    rw [cmAscWord_self_pred, show c + 1 + δ = (c + δ) + 1 from by omega, cmAscWord_self_pred]
    simp
  | succ n ih =>
    have hsplit : cmAscWord q (c + 1) (c + (n + 1))
        = cmAscWord q (c + 1) (c + n) * braidEnd q (c + n + 1) := by
      rw [show c + (n + 1) = c + n + 1 from by omega,
        cmAscWord_split q (a := c + 1) (b := c + n + 1) (c := c + n) (by omega) (by omega),
        cmAscWord_self]
    have hsplit' : cmAscWord q (c + 1 + δ) (c + (n + 1) + δ)
        = cmAscWord q (c + 1 + δ) (c + n + δ) * braidEnd q (c + n + 1 + δ) := by
      rw [show c + (n + 1) + δ = (c + n + δ) + 1 from by omega,
        cmAscWord_split q (a := c + 1 + δ) (b := (c + n + δ) + 1) (c := c + n + δ) (by omega)
          (by omega),
        cmAscWord_self, show c + n + δ + 1 = c + n + 1 + δ from by omega]
    rw [hsplit, hsplit']
    change shiftAux L δ (cmAscWord q (c + 1) (c + n) (braidEnd q (c + n + 1) F)) = _
    rw [ih, shiftAux_braidEnd q δ (show 1 ≤ c + n + 1 from by omega)]
    rfl

/-- `HJO.Sweep.shiftAux_cmAscWord` at `c = 0`: `Σ_δ(T_{[1,k]}F) = T_{[δ+1,k+δ]}(Σ_δ F)`. -/
theorem shiftAux_cmAscWord_one (q : L) (δ k : ℕ) (F : Total L) :
    shiftAux L δ (cmAscWord q 1 k F) = cmAscWord q (δ + 1) (k + δ) (shiftAux L δ F) := by
  have h := shiftAux_cmAscWord q δ 0 k F
  rw [Nat.zero_add, Nat.zero_add, show 0 + 1 + δ = δ + 1 from by omega] at h
  exact h

end Braid

/-! ### The lowering operator shifts freely -/

section Lowering

variable {L : Type*} [Field L]

/-- **`Σ_δ` moves the index of the adding substitution**: `Σ_δ(τ_{k,i}F) = τ_{k,i+δ}(Σ_δ F)` for
`i ≥ 1`. The substitution reads its index only through the letter `y_i`
(`HJO.Sweep.qshift_powerSum`), which `Σ_δ` renames to `y_{i+δ}`, and it fixes every auxiliary
variable, which is where `Σ_δ` acts. -/
theorem shiftAux_qshift (q : L) (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (qshift q i F) = qshift q (i + δ) (shiftAux L δ F) := by
  have hav : shiftAux L δ (auxVar i : Total L) = auxVar (i + δ) := shiftAux_auxVar δ hi
  have hC : ∀ c : Sym.Lambda L, shiftAux L δ (qshift q i (MvPolynomial.C c))
      = qshift q (i + δ) (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      rw [hx, qshift_scal, shiftAux_scal, qshift_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
    | mul_X p j hp =>
      have hps : (MvPolynomial.C (p * MvPolynomial.X j) : Total L)
          = MvPolynomial.C p * MvPolynomial.C (Sym.powerSum L (j + 1)) := by
        rw [Sym.powerSum, Nat.add_sub_cancel, map_mul]
      have hgen : shiftAux L δ (qshift q i (MvPolynomial.C (Sym.powerSum L (j + 1)) : Total L))
          = qshift q (i + δ) (MvPolynomial.C (Sym.powerSum L (j + 1))) := by
        rw [qshift_powerSum, qshift_powerSum, map_add, map_mul, map_pow, shiftAux_scal,
          shiftAux_C, hav]
      rw [hps, map_mul, map_mul, hp, hgen, map_mul]
  induction F using MvPolynomial.induction_on with
  | C c => rw [shiftAux_C, hC c]
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
  | mul_X p n hp =>
    rw [map_mul, qshift_auxVar, map_mul, hp, shiftAux_X, map_mul, map_mul, shiftAux_X,
      qshift_auxVar]

/-- **`Σ_δ` moves the index of the subtracting substitution**, the same statement for
`τ^-_{k,i}`. -/
theorem shiftAux_qshiftNeg (q : L) (δ : ℕ) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    shiftAux L δ (qshiftNeg q i F) = qshiftNeg q (i + δ) (shiftAux L δ F) := by
  have hav : shiftAux L δ (auxVar i : Total L) = auxVar (i + δ) := shiftAux_auxVar δ hi
  have hC : ∀ c : Sym.Lambda L, shiftAux L δ (qshiftNeg q i (MvPolynomial.C c))
      = qshiftNeg q (i + δ) (MvPolynomial.C c) := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C x =>
      have hx : (MvPolynomial.C (MvPolynomial.C x : Sym.Lambda L) : Total L) = scal x := rfl
      rw [hx, qshiftNeg_scal, shiftAux_scal, qshiftNeg_scal]
    | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
    | mul_X p j hp =>
      have hps : (MvPolynomial.C (p * MvPolynomial.X j) : Total L)
          = MvPolynomial.C p * MvPolynomial.C (Sym.powerSum L (j + 1)) := by
        rw [Sym.powerSum, Nat.add_sub_cancel, map_mul]
      have hgen : shiftAux L δ (qshiftNeg q i (MvPolynomial.C (Sym.powerSum L (j + 1)) : Total L))
          = qshiftNeg q (i + δ) (MvPolynomial.C (Sym.powerSum L (j + 1))) := by
        rw [qshiftNeg_powerSum, qshiftNeg_powerSum, map_sub, map_mul, map_pow, shiftAux_scal,
          shiftAux_C, hav]
      rw [hps, map_mul, map_mul, hp, hgen, map_mul]
  induction F using MvPolynomial.induction_on with
  | C c => rw [shiftAux_C, hC c]
  | add p r hp hr => rw [map_add, map_add, map_add, hp, hr, map_add]
  | mul_X p n hp =>
    rw [map_mul, qshiftNeg_auxVar, map_mul, hp, shiftAux_X, map_mul, map_mul, shiftAux_X,
      qshiftNeg_auxVar]

variable [Algebra ℚ L]

/-- A shift moves the exponent it reads along with itself. -/
theorem mapDomain_add_apply (δ j : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.mapDomain (· + δ) d (j + δ) = d j :=
  Finsupp.mapDomain_apply (fun _ _ h => Nat.add_right_cancel h) d j

/-- A shift carries erasure at `j` to erasure at `j + δ`. -/
theorem erase_mapDomain_add (δ j : ℕ) (d : ℕ →₀ ℕ) :
    Finsupp.erase (j + δ) (Finsupp.mapDomain (· + δ) d)
      = Finsupp.mapDomain (· + δ) (Finsupp.erase j d) := by
  have hinj : Function.Injective (fun x : ℕ => x + δ) := fun _ _ h => Nat.add_right_cancel h
  refine Finsupp.ext fun m => ?_
  by_cases hm : δ ≤ m
  · obtain ⟨c, rfl⟩ : ∃ c, m = c + δ := ⟨m - δ, by omega⟩
    by_cases hc : c = j
    · subst hc
      rw [Finsupp.erase_same, Finsupp.mapDomain_apply hinj, Finsupp.erase_same]
    · rw [Finsupp.erase_ne (by omega), Finsupp.mapDomain_apply hinj,
        Finsupp.mapDomain_apply hinj, Finsupp.erase_ne hc]
  · have hnr : m ∉ Set.range (fun x : ℕ => x + δ) := by
      rintro ⟨c, hc⟩
      have hc' : c + δ = m := hc
      omega
    rw [Finsupp.erase_ne (by omega), Finsupp.mapDomain_of_notMem_range _ _ hnr,
      Finsupp.mapDomain_of_notMem_range _ _ hnr]

/-- **`Σ_δ` moves the index of the coefficient extraction**:
`lowerCoeff_{j+δ}(Σ_δ H) = Σ_δ(lowerCoeff_j H)`, for every `H` and every `δ`.

The extraction reads the exponent of one variable and deletes it, so relabelling before extracting
at
`j + δ` is extracting at `j` and relabelling after. This is the companion of
`HJO.Sweep.lowerCoeff_swapAux_self` for the shift rather than an adjacent interchange, and unlike
that one it needs no hypothesis on the index at all. -/
theorem lowerCoeff_shiftAux (δ j : ℕ) (H : Total L) :
    lowerCoeff L (j + δ) (shiftAux L δ H) = shiftAux L δ (lowerCoeff L j H) := by
  induction H using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [shiftAux_monomial, lowerCoeff_monomial', lowerCoeff_monomial', mapDomain_add_apply,
      erase_mapDomain_add]
    simp only [map_mul, map_pow, map_neg, map_one, shiftAux_C, shiftAux_monomial]
  | add p r hp hr => rw [map_add, map_add, map_add, map_add, hp, hr]

/-- **`d^♭_-` SHIFTS FREELY.** For every `F` and every `δ`, on `1 ≤ k`,

`d^♭_-{}^{(k+δ)}(Σ_δ F) = Σ_δ(d^♭_-{}^{(k)}F)`.

No hypothesis on `F`, none on `q`: the lowering operator's index shift *is* the variable shift, with
no correction term. Both halves of `HJO.Sweep.dminus` move their index under `Σ_δ`
(`HJO.Sweep.shiftAux_qshiftNeg`, `HJO.Sweep.lowerCoeff_shiftAux`), and that is all there is to it.

This is the statement `HJO.Sweep.dminus_eq_of_mem_piece` was reaching for. That one asks for
`F ∈ V_{k-1}` — `δ + 1` pieces below what a base event of an extension supplies — and gets an
*equality* of operators; this one asks for nothing and gets a *conjugation*. So the `δ + 1`-piece
gap
that lemma leaves is not irreducible: it is the cost of demanding equality where the truth is
conjugacy. -/
@[hjo "lem_sweep_dminus_shift"]
theorem dminus_shiftAux (q : L) {k : ℕ} (hk : 1 ≤ k) (δ : ℕ) (F : Total L) :
    dminus q (k + δ) (shiftAux L δ F) = shiftAux L δ (dminus q k F) := by
  rw [dminus_apply, dminus_apply, show k + δ - 1 = (k - 1) + δ from by omega,
    ← shiftAux_qshiftNeg q δ hk, lowerCoeff_shiftAux]

/-- **`d^♭_-` passes a low variable through untouched**: for `1 ≤ i ≤ δ` and `1 ≤ k`,

`d^♭_-{}^{(k+δ)}(y_i^m · Σ_δ F) = y_i^m · Σ_δ(d^♭_-{}^{(k)}F)`.

With `HJO.Sweep.dminus_shiftAux` this carries rule `B` across the one gap that statement leaves: the
vector at a base event of an extension reads the `δ` variables the tail's live north steps opened,
and is therefore not in the image of `Σ_δ`, but `d^♭_-` neither moves those variables
(`HJO.Sweep.qshiftNeg_auxVar_apply`) nor reads them (`HJO.Sweep.lowerCoeff_mul_of_mem_piece`, the
extraction index `k + δ - 1` being at least `δ`).

`d^♭_+` and `Δ` admit no such statement, their correction word `T_{[1,δ]}` acting on exactly these
`δ` variables. That asymmetry is the next obstruction, and it is not about graded pieces. -/
theorem dminus_shiftAux_auxVar_pow_mul (q : L) {k : ℕ} (hk : 1 ≤ k) {δ i : ℕ} (hi : 1 ≤ i)
    (hiδ : i ≤ δ) (m : ℕ) (F : Total L) :
    dminus q (k + δ) ((auxVar i : Total L) ^ m * shiftAux L δ F)
      = (auxVar i : Total L) ^ m * shiftAux L δ (dminus q k F) := by
  have hmem : ((auxVar i : Total L) ^ m) ∈ piece L ((k - 1) + δ) :=
    pow_mem (auxVar_mem_piece hi (by omega)) m
  have hqs : qshiftNeg q (k + δ) ((auxVar i : Total L) ^ m * shiftAux L δ F)
      = (auxVar i : Total L) ^ m * qshiftNeg q (k + δ) (shiftAux L δ F) := by
    rw [map_mul, map_pow, qshiftNeg_auxVar_apply]
  have hkey : lowerCoeff L (k - 1 + δ) (qshiftNeg q (k + δ) (shiftAux L δ F))
      = shiftAux L δ (dminus q k F) := by
    have h := dminus_shiftAux q hk δ F
    rw [dminus_apply, show k + δ - 1 = (k - 1) + δ from by omega] at h
    exact h
  rw [dminus_apply, hqs, show k + δ - 1 = (k - 1) + δ from by omega,
    lowerCoeff_mul_of_mem_piece hmem, hkey]

end Lowering

/-! ### The raising operator shifts at the cost of a prefix word -/

section Raising

variable {L : Type*} [Field L]

/-- **`d^♭_+` SHIFTS AT THE COST OF ONE PREFIX WORD.** For every `F`, every `k` and every `δ`,

`d^♭_+{}^{(k+δ)}(Σ_δ F) = T_{[1,δ]}(Σ_δ(d^♭_+{}^{(k)}F))`.

No hypothesis at all. The raising operator carries its index in the ascending word `T_{[1,k]}` as
well as in the variable `y_{k+1}`, and `Σ_δ` moves the variable and the tail of the word together
(`HJO.Sweep.shiftAux_cmAscWord_one`, `HJO.Sweep.shiftAux_qshift`); what it cannot move is the word's
**left end**, which is pinned at `1`. So the two operators differ by exactly the `δ` letters
`T_1 ⋯ T_δ` that the shifted word has and the shifted conjugate does not, split off by
`HJO.Sweep.cmAscWord_split`.

**The correction reads only `δ`, not `k`.** That is what makes this usable on a whole layer of a
round of `HJO.Mellit.roundSweepWord`: by
`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` the shift is one integer for the entire base
layer while the widths `k` vary along it, so a correction depending on `k` would not factor out of
the layer and this one does.

Compare `HJO.Sweep.dplus_succ_eq_dplus_add`, which pays one Demazure term per unit of shift and
needs
`F ∈ V_k`; the price here is a single braid word, and it is free. -/
@[hjo "lem_sweep_dplus_shift"]
theorem dplus_shiftAux (q : L) (k δ : ℕ) (F : Total L) :
    dplus q (k + δ) (shiftAux L δ F) = cmAscWord q 1 δ (shiftAux L δ (dplus q k F)) := by
  have hqs : (auxVar (k + δ + 1) : Total L) * qshift q (k + δ + 1) (shiftAux L δ F)
      = shiftAux L δ ((auxVar (k + 1) : Total L) * qshift q (k + 1) F) := by
    rw [map_mul, shiftAux_auxVar δ (show 1 ≤ k + 1 from by omega),
      shiftAux_qshift q δ (show 1 ≤ k + 1 from by omega),
      show k + 1 + δ = k + δ + 1 from by omega]
  rw [dplus_eq_ascWord, hqs, dplus_eq_ascWord, map_neg, map_neg,
    shiftAux_cmAscWord_one q δ k, cmAscWord_split q (a := 1) (b := k + δ) (c := δ) (by omega)
      (by omega)]
  rfl

end Raising

/-! ### The corner operator shifts at the cost of the same prefix word -/

section Corner

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`Δ` SHIFTS AT THE COST OF THE SAME PREFIX WORD.** For every `F` and every `δ`, on `1 ≤ k`,

`Δ^{(k+δ)}(Σ_δ F) = T_{[1,δ]}(Σ_δ(Δ^{(k)}F))`.

No hypothesis on `q` — in particular **not** `q ≠ 1`, which the closed form
`HJO.Sweep.corner_transport_eq` needs and which the refutation
`HJO.Mellit.not_sweepAppend_one_left` shows the band identity itself needs. `HJO.Sweep.corner` is
`(q-1)^{-1}` times a commutator of the other two generators, and at `q = 1` both sides are the zero
map, so the statement survives the degeneration rather than excluding it.

Both terms of the commutator come out carrying the one word `T_{[1,δ]}`, which is why it factors
out:
in `d^♭_-{}^{(k+δ+1)}d^♭_+{}^{(k+δ)}` the word is produced by `HJO.Sweep.dplus_shiftAux` and then
commutes leftwards past `d^♭_-` by `HJO.Sweep.dminus_cmAscWord`, whose hypothesis
`δ ≤ k + δ - 1` is exactly `1 ≤ k`; in `d^♭_+{}^{(k+δ-1)}d^♭_-{}^{(k+δ)}` the lowering half
shifts freely and the word is produced on the outside by the raising half. So the corner needs no
argument of its own beyond the order in which its two halves are read. -/
@[hjo "lem_sweep_corner_shift"]
theorem corner_shiftAux (q : L) {k : ℕ} (hk : 1 ≤ k) (δ : ℕ) (F : Total L) :
    corner q (k + δ) (shiftAux L δ F) = cmAscWord q 1 δ (shiftAux L δ (corner q k F)) := by
  have h1 : dminus q (k + δ + 1) (dplus q (k + δ) (shiftAux L δ F))
      = cmAscWord q 1 δ (shiftAux L δ (dminus q (k + 1) (dplus q k F))) := by
    rw [dplus_shiftAux, show k + δ + 1 = (k + δ - 1) + 2 from by omega,
      dminus_cmAscWord q (show δ ≤ k + δ - 1 from by omega),
      show k + δ - 1 + 2 = (k + 1) + δ from by omega, dminus_shiftAux q (by omega)]
  have h2 : dplus q (k + δ - 1) (dminus q (k + δ) (shiftAux L δ F))
      = cmAscWord q 1 δ (shiftAux L δ (dplus q (k - 1) (dminus q k F))) := by
    rw [dminus_shiftAux q hk, show k + δ - 1 = (k - 1) + δ from by omega, dplus_shiftAux]
  rw [corner_of_pos q (show k + δ ≠ 0 from by omega), corner_of_pos q (show k ≠ 0 from by omega)]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [h1, h2, ← map_sub, ← map_sub, ← map_smul, ← shiftAux_smul]

end Corner

/-! ### Off the image of the shift: the low factor the tail opened -/

section LowFactor

variable {L : Type*} [Field L]

/-- **`τ_{k,i}` fixes a `y`-polynomial with scalar coefficients.** `HJO.Sweep.auxSubalg` is the
`L`-subalgebra generated by the auxiliary variables, and the substitution moves the alphabet and
nothing else (`HJO.Sweep.alphabetShift_of_mem_auxSubalg`). -/
theorem qshift_of_mem_auxSubalg (q : L) (i : ℕ) {g : Total L} (hg : g ∈ auxSubalg L) :
    qshift q i g = g := by
  rw [qshift_eq_alphabetShift, alphabetShift_of_mem_auxSubalg _ hg]

/-- **`τ^-_{k,i}` fixes a `y`-polynomial with scalar coefficients**, by the same reading of
`HJO.Sweep.qshiftNeg_eq_alphabetShift`. -/
theorem qshiftNeg_of_mem_auxSubalg (q : L) (i : ℕ) {g : Total L} (hg : g ∈ auxSubalg L) :
    qshiftNeg q i g = g := by
  rw [qshiftNeg_eq_alphabetShift, alphabetShift_of_mem_auxSubalg _ hg]

/-- **An ascending word whose letters all sit above `V_δ` is linear over `V_δ`**:
`T_{[c+1,c+d]}(gF) = g·T_{[c+1,c+d]}F` for `g ∈ V_δ` and `δ ≤ c`.

Every letter is one `HJO.Sweep.braid_mul_of_swapAux_eq` covers, the interchange `s_j` fixing `V_δ`
for `j ≥ δ + 1` (`HJO.Sweep.swapAux_of_mem_piece`). This is what carries the correction words of
`HJO.Sweep.dplus_shiftAux` and `HJO.Sweep.corner_shiftAux` past the low factor. -/
theorem cmAscWord_mul_of_mem_piece (q : L) {δ : ℕ} {g : Total L} (hg : g ∈ piece L δ) {c : ℕ}
    (hc : δ ≤ c) (d : ℕ) (F : Total L) :
    cmAscWord q (c + 1) (c + d) (g * F) = g * cmAscWord q (c + 1) (c + d) F := by
  induction d generalizing F with
  | zero =>
    simp only [Nat.add_zero]
    rw [cmAscWord_self_pred]
    simp
  | succ n ih =>
    have hsplit : cmAscWord q (c + 1) (c + (n + 1))
        = cmAscWord q (c + 1) (c + n) * braidEnd q (c + n + 1) := by
      rw [show c + (n + 1) = c + n + 1 from by omega,
        cmAscWord_split q (a := c + 1) (b := c + n + 1) (c := c + n) (by omega) (by omega),
        cmAscWord_self]
    have hfix : swapAux L (c + n + 1) g = g := swapAux_of_mem_piece (by omega) hg
    have hbr : ∀ G : Total L, braidEnd q (c + n + 1) (g * G) = g * braidEnd q (c + n + 1) G :=
      fun G => braid_mul_of_swapAux_eq q hfix G
    rw [hsplit]
    change cmAscWord q (c + 1) (c + n) (braidEnd q (c + n + 1) (g * F)) = _
    rw [hbr, ih]
    rfl

/-- **EVERY `y`-MONOMIAL OF `V_{k+δ}` IS A LOW FACTOR TIMES A SHIFT.** For `d` supported below
`k + δ`, the monomial `y^d·λ` is `g · Σ_δ(F)` with `g` a `y`-monomial with coefficient `1` in
`y_1, …, y_δ` (so `g ∈ HJO.Sweep.auxSubalg L` and `g ∈ V_δ`) and `F ∈ V_k`.

This is what makes the `_mul` statements below say something about the whole graded piece rather
than about a subspace of it. The exponent splits at `δ`: the part below goes into `g`, the part
above is pulled down by `δ` into `F`, and the `Λ`-coefficient goes with `F` because `Σ_δ` fixes
`Λ`. -/
@[hjo "lem_sweep_shift_split"]
theorem exists_mul_shiftAux_of_monomial (δ k : ℕ) {d : ℕ →₀ ℕ} (hd : ∀ j, k + δ ≤ j → d j = 0)
    (c : Sym.Lambda L) :
    ∃ g F : Total L, g ∈ auxSubalg L ∧ g ∈ piece L δ ∧ F ∈ piece L k ∧
      (MvPolynomial.monomial d c : Total L) = g * shiftAux L δ F := by
  classical
  have hinj : Function.Injective (fun x : ℕ => x + δ) := fun _ _ h => Nat.add_right_cancel h
  refine ⟨MvPolynomial.monomial (Finsupp.filter (· < δ) d) 1,
    MvPolynomial.monomial (Finsupp.comapDomain (fun x : ℕ => x + δ) d hinj.injOn) c,
    monomial_one_mem_auxSubalg _, ?_, ?_, ?_⟩
  · rw [piece, MvPolynomial.mem_supported, MvPolynomial.vars_monomial one_ne_zero]
    intro j hj
    simp only [Finset.mem_coe, Finsupp.support_filter, Finset.mem_filter] at hj
    exact hj.2
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [piece, MvPolynomial.mem_supported, MvPolynomial.vars_monomial hc]
      intro j hj
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at hj
      simp only [Set.mem_Iio]
      by_contra hcon
      exact hj (hd _ (by omega))
  · have hsum : Finsupp.filter (· < δ) d
        + Finsupp.mapDomain (fun x : ℕ => x + δ)
            (Finsupp.comapDomain (fun x : ℕ => x + δ) d hinj.injOn) = d := by
      refine Finsupp.ext fun j => ?_
      rw [Finsupp.add_apply]
      by_cases hjd : j < δ
      · have hnr : j ∉ Set.range (fun x : ℕ => x + δ) := by
          rintro ⟨e, he⟩
          have he' : e + δ = j := he
          omega
        rw [Finsupp.mapDomain_of_notMem_range _ _ hnr, add_zero]
        simp [hjd]
      · obtain ⟨e, rfl⟩ : ∃ e, j = e + δ := ⟨j - δ, by omega⟩
        rw [Finsupp.mapDomain_apply hinj, Finsupp.comapDomain_apply]
        simp [hjd]
    rw [shiftAux_monomial, MvPolynomial.monomial_mul, one_mul, hsum]

variable [Algebra ℚ L]

/-- **`d^♭_-` SHIFTS FREELY ON ALL OF `V_{k+δ}`.** For `g ∈ V_δ` with scalar coefficients,

`d^♭_-{}^{(k+δ)}(g · Σ_δ F) = g · Σ_δ(d^♭_-{}^{(k)}F)`, on `1 ≤ k`.

`HJO.Sweep.dminus_shiftAux` reads the operator only on `Σ_δ(V_k)`, and the vector arriving at a base
event of an extension is not there: it reads the `δ` variables the tail's live north steps opened.
This removes that restriction. Every `y`-monomial of `V_{k+δ}` is such a product
(`HJO.Sweep.exists_mul_shiftAux_of_monomial`), so the two statements together determine
`d^♭_-{}^{(k+δ)}` on the whole piece.

Neither half of `d^♭_-` touches the low factor: the substitution fixes it
(`HJO.Sweep.qshiftNeg_of_mem_auxSubalg`) and the extraction, reading the index `k+δ-1 ≥ δ`, is
linear
over it (`HJO.Sweep.lowerCoeff_mul_of_mem_piece`). -/
theorem dminus_shiftAux_mul (q : L) {k : ℕ} (hk : 1 ≤ k) {δ : ℕ} {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L δ) (F : Total L) :
    dminus q (k + δ) (g * shiftAux L δ F) = g * shiftAux L δ (dminus q k F) := by
  have hqs : qshiftNeg q (k + δ) (g * shiftAux L δ F)
      = g * qshiftNeg q (k + δ) (shiftAux L δ F) := by
    rw [map_mul, qshiftNeg_of_mem_auxSubalg q _ hgaux]
  have hmem : g ∈ piece L (k - 1 + δ) := piece_mono (by omega) hgp
  have hkey : lowerCoeff L (k - 1 + δ) (qshiftNeg q (k + δ) (shiftAux L δ F))
      = shiftAux L δ (dminus q k F) := by
    have h := dminus_shiftAux q hk δ F
    rw [dminus_apply, show k + δ - 1 = (k - 1) + δ from by omega] at h
    exact h
  rw [dminus_apply, hqs, show k + δ - 1 = (k - 1) + δ from by omega,
    lowerCoeff_mul_of_mem_piece hmem, hkey]

omit [Algebra ℚ L] in
/-- **`d^♭_+` SHIFTS ON ALL OF `V_{k+δ}`, at the cost of the same prefix word.** For `g ∈ V_δ` with
scalar coefficients and every `k`,

`d^♭_+{}^{(k+δ)}(g · Σ_δ F) = T_{[1,δ]}(g · Σ_δ(d^♭_+{}^{(k)}F))`.

The low factor passes through everything but the correction: the substitution fixes it
(`HJO.Sweep.qshift_of_mem_auxSubalg`) and the *inner* word `T_{[δ+1,k+δ]}` is linear over it
(`HJO.Sweep.cmAscWord_mul_of_mem_piece`). What it does not pass through is `T_{[1,δ]}`, whose
letters act on exactly the variables `g` is built from — so the low factor stays **inside** the
correction, and that is the precise shape of what the propagation across a whole layer has to
contend with. -/
theorem dplus_shiftAux_mul (q : L) (k : ℕ) {δ : ℕ} {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L δ) (F : Total L) :
    dplus q (k + δ) (g * shiftAux L δ F)
      = cmAscWord q 1 δ (g * shiftAux L δ (dplus q k F)) := by
  set H : Total L := (auxVar (k + δ + 1) : Total L) * qshift q (k + δ + 1) (shiftAux L δ F) with hH
  have hbase : shiftAux L δ (dplus q k F) = -cmAscWord q (δ + 1) (δ + k) H := by
    rw [dplus_eq_ascWord, map_neg, shiftAux_cmAscWord_one, hH, map_mul,
      shiftAux_auxVar δ (show 1 ≤ k + 1 from by omega),
      shiftAux_qshift q δ (show 1 ≤ k + 1 from by omega),
      show k + 1 + δ = k + δ + 1 from by omega, show k + δ = δ + k from by omega]
  have harg : (auxVar (k + δ + 1) : Total L) * qshift q (k + δ + 1) (g * shiftAux L δ F)
      = g * H := by
    rw [map_mul, qshift_of_mem_auxSubalg q _ hgaux, hH]
    ring
  rw [dplus_eq_ascWord, harg, show k + δ = δ + k from by omega,
    cmAscWord_split q (a := 1) (b := δ + k) (c := δ) (by omega) (by omega)]
  change -cmAscWord q 1 δ (cmAscWord q (δ + 1) (δ + k) (g * H)) = _
  rw [cmAscWord_mul_of_mem_piece q hgp le_rfl, hbase, mul_neg, map_neg]

/-- **`Δ` SHIFTS ON ALL OF `V_{k+δ}`, at the cost of the same prefix word.** For `g ∈ V_δ` with
scalar coefficients, on `1 ≤ k`,

`Δ^{(k+δ)}(g · Σ_δ F) = T_{[1,δ]}(g · Σ_δ(Δ^{(k)}F))`.

The same bookkeeping as `HJO.Sweep.corner_shiftAux`, with the low factor carried along by
`HJO.Sweep.dminus_shiftAux_mul` and `HJO.Sweep.dplus_shiftAux_mul`. No hypothesis on `q`. -/
theorem corner_shiftAux_mul (q : L) {k : ℕ} (hk : 1 ≤ k) {δ : ℕ} {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L δ) (F : Total L) :
    corner q (k + δ) (g * shiftAux L δ F)
      = cmAscWord q 1 δ (g * shiftAux L δ (corner q k F)) := by
  have h1 : dminus q (k + δ + 1) (dplus q (k + δ) (g * shiftAux L δ F))
      = cmAscWord q 1 δ (g * shiftAux L δ (dminus q (k + 1) (dplus q k F))) := by
    rw [dplus_shiftAux_mul q k hgaux hgp, show k + δ + 1 = (k + δ - 1) + 2 from by omega,
      dminus_cmAscWord q (show δ ≤ k + δ - 1 from by omega),
      show k + δ - 1 + 2 = (k + 1) + δ from by omega,
      dminus_shiftAux_mul q (show 1 ≤ k + 1 from by omega) hgaux hgp]
  have h2 : dplus q (k + δ - 1) (dminus q (k + δ) (g * shiftAux L δ F))
      = cmAscWord q 1 δ (g * shiftAux L δ (dplus q (k - 1) (dminus q k F))) := by
    rw [dminus_shiftAux_mul q hk hgaux hgp, show k + δ - 1 = (k - 1) + δ from by omega,
      dplus_shiftAux_mul q (k - 1) hgaux hgp]
  rw [corner_of_pos q (show k + δ ≠ 0 from by omega), corner_of_pos q (show k ≠ 0 from by omega)]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [h1, h2, ← map_sub, ← mul_sub, ← map_sub, ← map_smul]
  congr 1
  rw [shiftAux_smul, mul_smul_comm]

end LowFactor

/-! ### The two earlier comparisons, freed of their hypotheses -/

section Unconditional

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **`d^♭_-` one index higher is its own conjugate by the adjacent interchange**, with no
hypothesis on `F`: `d^♭_-{}^{(i+1)}F = s_i(d^♭_-{}^{(i)}(s_iF))` for `i ≥ 1`.

`HJO.Sweep.dminus_succ_eq_of_mem_piece` is the case `s_iF = F`, and its `F ∈ V_k` is used for
nothing
but that. So the hypothesis is removable, and the reason the earlier index shift stalls `δ+1` pieces
short of a base event is not that anything is missing but that an equality was asked for where the
truth is a conjugation. -/
theorem dminus_succ_eq_swapAux (q : L) {i : ℕ} (hi : 1 ≤ i) (F : Total L) :
    dminus q (i + 1) F = swapAux L i (dminus q i (swapAux L i F)) := by
  have h1 : qshiftNeg q (i + 1) F = swapAux L i (qshiftNeg q i (swapAux L i F)) := by
    rw [swapAux_qshiftNeg_self q hi (swapAux L i F), swapAux_swapAux]
  rw [dminus_apply, Nat.add_sub_cancel, h1, lowerCoeff_swapAux_self, ← dminus_apply]

omit [Algebra ℚ L] in
/-- **`d^♭_+` one index higher, with its correction, and with no hypothesis on `F`**:

`d^♭_+{}^{(k+1)}F = d^♭_+{}^{(k)}(s_{k+1}F) +
T_{[1,k]}((q-1)y_{k+1}∂_{k+1}(y_{k+1}τ_{k+1,k+1}(s_{k+1}F)))`.

`HJO.Sweep.dplus_succ_eq_dplus_add` is the case `s_{k+1}F = F`, which is what its `F ∈ V_k` buys;
the identity itself never reads the hypothesis. Both this and `HJO.Sweep.dminus_succ_eq_swapAux` are
one-step statements — the `δ`-step ones a base event needs are `HJO.Sweep.dplus_shiftAux` and
`HJO.Sweep.dminus_shiftAux`, where the conjugating map is the shift rather than a product of
interchanges. -/
theorem dplus_succ_eq_dplus_swapAux_add (q : L) (k : ℕ) (F : Total L) :
    dplus q (k + 1) F
      = dplus q k (swapAux L (k + 1) F)
        + cmAscWord q 1 k (scal (q - 1) * (auxVar (k + 1) : Total L)
            * dividedDiff (k + 1) ((auxVar (k + 1) : Total L)
              * qshift q (k + 1) (swapAux L (k + 1) F))) := by
  set G : Total L := (auxVar (k + 1) : Total L) * qshift q (k + 1) (swapAux L (k + 1) F) with hG
  have hswap : (auxVar (k + 2) : Total L) * qshift q (k + 2) F = swapAux L (k + 1) G := by
    rw [hG, map_mul, swapAux_auxVar_self (show 1 ≤ k + 1 by omega),
      swapAux_qshift_self q (show 1 ≤ k + 1 by omega), swapAux_swapAux]
  have hword : cmAscWord q 1 (k + 1) = cmAscWord q 1 k * braidEnd q (k + 1) := by
    rw [cmAscWord_split q (a := 1) (b := k + 1) (c := k) (by omega) (by omega), cmAscWord_self]
  have hletter : braid q (k + 1) (swapAux L (k + 1) G)
      = G - scal (q - 1) * (auxVar (k + 1) : Total L) * dividedDiff (k + 1) G := by
    rw [braid_apply, swapAux_swapAux, dividedDiff_swapAux]
    ring
  rw [dplus_eq_ascWord, show k + 1 + 1 = k + 2 from rfl, hswap, hword]
  change -cmAscWord q 1 k (braid q (k + 1) (swapAux L (k + 1) G)) = _
  rw [hletter, map_sub, dplus_eq_ascWord, ← hG]
  abel

end Unconditional

end HJO.Sweep

/-! ### The residual of the round-grouping at a base event, computed -/

namespace HJO.Mellit

open HJO.Sweep HJO.Paths Finset

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L} {a b N A : ℕ}

section Append

variable {z : Heights a b N} {w : Heights a b A}

/-- **Rule `A` at a base event of an extension: the base's own operator, shifted, times one prefix
word.** With `δ = #(tailLiveSteps w (diagExcess a b P))` — the width shift
`HJO.Paths.sweepWidth_appendHeights_eq` applies at `P`, and by
`HJO.Mellit.sweepWidth_appendHeights_of_diagExcess_eq` the *same* integer for the whole base layer
of
the round through `P` — the extension's type-`A` operator on `g·Σ_δ F` is `T_{[1,δ]}` applied to `g`
times `Σ_δ` of the base's own value.

No hypothesis on `q`, on `u`, on `F`, or on the width. This is
`HJO.Mellit.sweepOperator_appendHeights_of_eventType_A` — which records the shift and says nothing
about how to undo it — composed with `HJO.Sweep.dplus_shiftAux_mul`, which says exactly what it
costs. -/
@[hjo "lem_sweep_operator_shift_append"]
theorem sweepOperator_shiftAux_appendHeights_A (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w)
    (hN : 0 < N) {P : ℕ × ℕ} (hP : P.1 < a * N) (hA : eventType z P = EventType.A) {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L (#(tailLiveSteps w (diagExcess a b P))))
    (F : Total L) :
    sweepOperator q u (appendHeights z w) P
        (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) F)
      = cmAscWord q 1 (#(tailLiveSteps w (diagExcess a b P)))
          (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) (sweepOperator q u z P F)) := by
  rw [sweepOperator_appendHeights_of_eventType_A hz hw hN hP hA,
    sweepOperator_of_eventType_A z hA, dplus_shiftAux_mul q _ hgaux hgp]

/-- **Rule `B` at a base event of an extension: the base's own operator, shifted, and nothing
else.** The lowering operator's index shift is the variable shift outright
(`HJO.Sweep.dminus_shiftAux_mul`), so a type-`B` event of the extension is the base's own type-`B`
event read through `Σ_δ`, with no correction — and this holds on the whole of `V_{k+δ}`, the low
factor passing through untouched.

`1 ≤ sweepWidth z P` is real: `HJO.Sweep.dminus` has no index `0`, `d^♭_-{}^{(0)}` reading
`lowerCoeff_{0-1}`. -/
@[hjo "lem_sweep_operator_shift_append"]
theorem sweepOperator_shiftAux_appendHeights_B (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w)
    (hN : 0 < N) {P : ℕ × ℕ} (hP : P.1 < a * N) (hk : 1 ≤ sweepWidth z P)
    (hB : eventType z P = EventType.B) {g : Total L} (hgaux : g ∈ auxSubalg L)
    (hgp : g ∈ piece L (#(tailLiveSteps w (diagExcess a b P)))) (F : Total L) :
    sweepOperator q u (appendHeights z w) P
        (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) F)
      = g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) (sweepOperator q u z P F) := by
  rw [sweepOperator_appendHeights_of_eventType_B hz hw hN hP hB,
    sweepOperator_of_eventType_B z hB, dminus_shiftAux_mul q hk hgaux hgp]

/-- **Rule `C` at a base event of an extension: the base's own operator, shifted, times the same
prefix word and `q^{-δ}`.** The corner operator shifts at the same price as the raising operator
(`HJO.Sweep.corner_shiftAux_mul`), and rule `C` additionally reads `HJO.Paths.sweepRight`, which
`HJO.Paths.sweepRight_appendHeights_eq` raises by the same `δ` — so the scalar `q^{-δ}` appears,
exactly inverse to the one rule `D` pays.

`q ≠ 0` is the one genericity hypothesis in this family, and it is needed only to split the negative
power; it is real for the band identity anyway
(`HJO.Mellit.not_band_one_left_one_one_of_q_zero`, at `a = 1` and every `b ≥ 2`). Note that `q ≠ 1`
is *not* needed, unlike in `HJO.Sweep.corner_transport_eq`. -/
@[hjo "lem_sweep_operator_shift_append"]
theorem sweepOperator_shiftAux_appendHeights_C (hq : q ≠ 0) (hz : IsAboveDiagonal z)
    (hw : IsAboveDiagonal w) (hN : 0 < N) {P : ℕ × ℕ} (hP : P.1 < a * N)
    (hk : 1 ≤ sweepWidth z P) (hC : eventType z P = EventType.C) {g : Total L}
    (hgaux : g ∈ auxSubalg L) (hgp : g ∈ piece L (#(tailLiveSteps w (diagExcess a b P))))
    (F : Total L) :
    sweepOperator q u (appendHeights z w) P
        (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) F)
      = q ^ (-(#(tailLiveSteps w (diagExcess a b P)) : ℤ)) •
          cmAscWord q 1 (#(tailLiveSteps w (diagExcess a b P)))
            (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P)))
              (sweepOperator q u z P F)) := by
  rw [sweepOperator_appendHeights_of_eventType_C hz hw hN hP hC,
    sweepOperator_of_eventType_C z hC]
  simp only [LinearMap.smul_apply]
  rw [corner_shiftAux_mul q hk hgaux hgp, shiftAux_smul, mul_smul_comm, map_smul, smul_smul,
    ← zpow_add₀ hq]
  congr 2
  push_cast
  ring

/-- **Rule `D` at a base event of an extension: the base's own scalar, shifted, times `q^δ`.** The
only rule whose discrepancy is a scalar, `q^{a}id` reading `HJO.Paths.sweepRight` and not
`HJO.Paths.sweepWidth`; the scalar is inverse to rule `C`'s. No hypothesis on `q`, on the width, or
on the low factor: the exponent is a natural number here and the operator is a scalar. -/
@[hjo "lem_sweep_operator_shift_append"]
theorem sweepOperator_shiftAux_appendHeights_D (hz : IsAboveDiagonal z) (hw : IsAboveDiagonal w)
    (hN : 0 < N) {P : ℕ × ℕ} (hP : P.1 < a * N) (hD : eventType z P = EventType.D) (g : Total L)
    (F : Total L) :
    sweepOperator q u (appendHeights z w) P
        (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) F)
      = q ^ (#(tailLiveSteps w (diagExcess a b P))) •
          (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) (sweepOperator q u z P F)) := by
  rw [sweepOperator_of_eventType_D (appendHeights z w)
      (by rw [eventType_appendHeights (show P.1 + 1 ≤ a * N from by omega)]; exact hD),
    sweepOperator_of_eventType_D z hD, sweepRight_appendHeights_eq hz hw hN hP]
  simp only [LinearMap.smul_apply, Module.End.one_apply]
  rw [shiftAux_smul, mul_smul_comm, smul_smul, pow_add, mul_comm]

/-- **Rule `E` at a base event of an extension: unchanged.** Multiplication by `u` reads neither the
width nor the right count, so it commutes with `Σ_δ` and with the low factor outright. -/
@[hjo "lem_sweep_operator_shift_append"]
theorem sweepOperator_shiftAux_appendHeights_E {P : ℕ × ℕ} (hP : P.1 + 1 ≤ a * N)
    (hE : eventType z P = EventType.E) (g : Total L) (F : Total L) :
    sweepOperator q u (appendHeights z w) P
        (g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) F)
      = g * shiftAux L (#(tailLiveSteps w (diagExcess a b P))) (sweepOperator q u z P F) := by
  rw [sweepOperator_appendHeights_of_eventType_E hP hE, sweepOperator_of_eventType_E q u z P hE]
  simp only [LinearMap.smul_apply, Module.End.one_apply]
  rw [shiftAux_smul, mul_smul_comm]

end Append

end HJO.Mellit

end
