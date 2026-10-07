/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitThm58Transfer
public meta import HJO.Attr

/-! # The `BE` partner: it exists at every bracketed swept point but the origin, and never there

`HJO.Mellit.HasBEPartner` is the existence statement rule `BE` of Mellit's Theorem 4.2 needs and
Mellit asserts in passing — his "if `P` is inside `c`, then `c` can be obtained in `2` ways: from
`c' ∈ 𝒞_{h_+}` by rule B) or from `c'' ∈ 𝒞_{h_+}` by rule E)". It is the one hypothesis of
`HJO.Mellit.eq_dsc_of_recursion_step`, the transfer theorem that measures what Mellit's closing
sentence for his Theorem 5.8 actually needs. This file settles it, and the answer is a dichotomy.

## The verdict

**At a bracketed swept point other than the origin the partner exists**, in complete generality —
every coprime `1 < a < b`, every `N`, every above-diagonal path, both directions of the conjunction.
That is `HJO.Mellit.hasBEPartner_of_isolates`, and
`HJO.Mellit.eq_dsc_of_recursion_step_of_ne_origin` is the transfer with the hypothesis discharged.

**At the origin the partner does not exist, ever.** That is
`HJO.Mellit.not_hasBEPartner_origin`, and the reason is one line:
`HJO.Mellit.not_eventType_origin_eq_E` — a type-`E` event at `(0,0)` says `0 < ŷ_0`, and every
above-diagonal path has `ŷ_0 = 0`. The two facts together are
`HJO.Mellit.hasBEPartner_iff_ne_origin`.

The second half is not a corner case, because `HJO.Mellit.beClause_unavoidable` shows the origin is
a type-`B` event of *every* above-diagonal path, so the `BE` clause is forced there at every sweep.
The hypothesis of `HJO.Mellit.eq_dsc_of_recursion_step` is therefore false exactly at the one point
where that theorem cannot avoid using it. What follows is that Mellit's "`2` ways" cannot be read as
a statement about the origin — there `c` is obtained in one way only, by rule `B`, which is what his
own parenthesis "in the very end, when we cross the point `(0,0)` we have to apply B)" says. The
level recursion does not determine the value at the origin, and on Mellit's route
`HJO.Mellit.braidValueColouring_eq_dsc_floor` needs that point supplied from the initial conditions
rather than from the recursion. Note also that `HJO.Mellit.SweepRecursionBE`, and hence the proved
`HJO.Mellit.dsc_eq_dminus_add_smul`, is
*vacuous* at the origin for the same reason: its type-`E` premise cannot be met.

## The two constructions

Both are local, and both are the obvious picture.

For a type-`B` event at `(X, Y)` with `X > 0` the type-`E` partner raises the single column `X` from
`Y` to `Y + 1`, which is `HJO.Mellit.raiseFrom` at the ordinate `Y + 1` from the abscissa `X - 1`:
every column strictly right of `X` already has height over `Y`, so nothing else moves.
`HJO.Mellit.exists_eventType_E_partner`.

For a type-`E` event at `(X, Y)` the type-`B` partner *clamps* the path down to `Y` on every column
weakly left of `X` — the new `HJO.Mellit.lowerUpto`, mirror of the splice. A single-column lowering
does not work: the columns left of `X` can be higher than `Y` and monotonicity would break. The
clamp stays above the diagonal because a clamped column `r ≤ X` needs only `br ≤ bX ≤ aY`, whose
last inequality is part of `P ∈ Sw(ŷ)`. `HJO.Mellit.exists_eventType_B_partner`.

Neither construction preserves the colouring by accident, and neither preserves it for an arbitrary
level. What makes the colouring at `ηlo` immune is that `ηlo` sits *under* the rank of `(X, Y)`, so
by `HJO.Mellit.levelIndex_lt_of_fst_le` the level index of every column weakly left of `X` is under
`Y`; and `HJO.Mellit.mem_colouring_iff_levelIndex` then says the crossed north step of such a column
sits under `Y` and its crossed east step does not exist. Every height either construction moves is
at `Y` or above, so no crossing changes. Both `ηlo < rk̂(X, Y)` and the admissibility of `ηlo` come
from `HJO.Mellit.Isolates`, so both are available wherever the transfer is applied — but neither is
carried by `HJO.Mellit.HasBEPartner` itself, which is a second, smaller defect of that definition:
`HJO.Mellit.not_hasBEPartner_two_three_one_unswept` refutes it at an unswept point, where its
type-`E` half asks the partner to sweep a point no path sweeps.

`HJO.Mellit.lowerUpto_two_three_one` and `HJO.Mellit.raiseFrom_two_three_one` check by `decide` that
the two constructions return exactly the witnesses `HJO.Mellit.hasBEPartner_two_three_one_B` and
`HJO.Mellit.hasBEPartner_two_three_one_E` exhibit by hand on the `2 × 3` rectangle.

No genericity is spent, no field element appears, and nothing here is specific to small `a` or `b`.
-/

@[expose] public section

open Finset

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The level index weakly left of a point whose rank is over the level -/

/-- **Weakly left of a point whose rank is over the level, the level index is under the point's
ordinate.** The level index is monotone in the column by `HJO.Mellit.levelIndex_le_of_fst_le`, and
at the column of the point itself it is under `Y` because the rank there exceeds the level. -/
theorem levelIndex_lt_of_fst_le (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {η : ℚ} {X Y x : ℕ}
    (hlt : η < ((pointRank a b N (X, Y) : ℤ) : ℚ)) (hx : x ≤ X) :
    levelIndex a b N η x < (Y : ℤ) :=
  lt_of_le_of_lt (levelIndex_le_of_fst_le ha hb hN η hx)
    ((lt_cast_pointRank_iff ha hN η X Y).1 hlt)

/-! ### The clamp: a path lowered to an ordinate up to an abscissa -/

/-- The path `ŷ` lowered to the ordinate `Y` from the abscissa `X` leftwards: the pointwise minimum
of `ŷ` with the path that sits at `Y` up to `X` and at `bN` afterwards. This is the mirror of the
splice `HJO.Mellit.raiseFrom`, and it is what rule `E` needs: it changes `ŷ` only over the level
line, so it leaves the colouring below the level alone, while forcing a type-`B` event at `(X, Y)`.
-/
def lowerUpto (y : Heights a b N) (X : ℕ) (Y : Fin (b * N + 1)) : Heights a b N :=
  fun r => if (r : ℕ) ≤ X then min (y r) Y else y r

/-- Left of the clamp each height is lowered to at most `Y`. -/
theorem ht_lowerUpto_of_le (y : Heights a b N) {X : ℕ} (Y : Fin (b * N + 1)) {r : ℕ}
    (hr : r ≤ X) (hX : X ≤ a * N) : ht (lowerUpto y X Y) r = min (ht y r) (Y : ℕ) := by
  have h : r < a * N + 1 := by omega
  rw [show r = ((⟨r, h⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe, ht_coe]
  simp [lowerUpto, hr]

/-- Right of the clamp the heights are untouched. -/
theorem ht_lowerUpto_of_gt (y : Heights a b N) {X : ℕ} (Y : Fin (b * N + 1)) {r : ℕ}
    (hr : X < r) : ht (lowerUpto y X Y) r = ht y r := by
  by_cases h : r < a * N + 1
  · rw [show r = ((⟨r, h⟩ : Fin (a * N + 1)) : ℕ) from rfl, ht_coe, ht_coe]
    simp [lowerUpto, Nat.not_le.2 hr]
  · rw [ht_of_gt _ (by omega), ht_of_gt _ (by omega)]

/-- **The clamp of an above-diagonal path is an above-diagonal path.** Lowering keeps the heights
monotone, and it keeps the right endpoint where it was because the clamp stops strictly left of
`aN`. Staying over the diagonal is the one clause that costs something: a clamped column `r ≤ X`
needs `br ≤ aY`, and that is `br ≤ bX ≤ aY`, the last inequality being the hypothesis. -/
theorem isAboveDiagonal_lowerUpto {y : Heights a b N} (hy : IsAboveDiagonal y) {X : ℕ}
    (hX : X < a * N) (Y : Fin (b * N + 1)) (hdiag : b * X ≤ a * (Y : ℕ)) :
    IsAboveDiagonal (lowerUpto y X Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht_lowerUpto_of_le y Y (Nat.zero_le _) hX.le, hy.1]
    simp
  · rw [ht_lowerUpto_of_gt y Y hX]
    exact hy.2.1
  · intro r hr
    rcases Nat.lt_or_ge X (r + 1) with h | h
    · rcases Nat.lt_or_ge X r with h2 | h2
      · rw [ht_lowerUpto_of_gt y Y h2, ht_lowerUpto_of_gt y Y h]
        exact hy.2.2.1 r hr
      · rw [ht_lowerUpto_of_le y Y h2 hX.le, ht_lowerUpto_of_gt y Y h]
        have := hy.2.2.1 r hr
        omega
    · rw [ht_lowerUpto_of_le y Y (by omega) hX.le, ht_lowerUpto_of_le y Y (by omega) hX.le]
      have := hy.2.2.1 r hr
      omega
  · intro r hr
    rcases Nat.lt_or_ge X r with h | h
    · rw [ht_lowerUpto_of_gt y Y h]
      exact hy.2.2.2 r hr
    · rw [ht_lowerUpto_of_le y Y h hX.le]
      have h1 := hy.2.2.2 r hr
      have h2 : b * r ≤ b * X := Nat.mul_le_mul (le_refl b) h
      rcases le_total (ht y r) (Y : ℕ) with hc | hc
      · rw [min_eq_left hc]; exact h1
      · rw [min_eq_right hc]; omega

/-! ### The type-`B` partner of a type-`E` event -/

/-- **A type-`E` event at a bracketed swept point has a type-`B` partner.** The partner is the clamp
`HJO.Mellit.lowerUpto` of `ŷ` at the ordinate `Y` up to the abscissa `X`: it brings the path down to
`Y` exactly at the column `X`, turning the interior point into the foot of a north step, and it
never needs to touch the column `aN` because a swept point strictly under the path has `X < aN`.

The colouring below the level does not move. Every column the clamp touches is weakly left of `X`,
and weakly left of `X` the level index is under `Y` by `HJO.Mellit.levelIndex_lt_of_fst_le`; so by
`HJO.Mellit.mem_colouring_iff_levelIndex` the crossed north step of such a column sits at an
ordinate under `Y`, which the clamp leaves in place, and its crossed east step would have to sit at
an ordinate at most the level index of the next column, again under `Y`, so there is none on either
path. -/
theorem exists_eventType_B_partner (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {X Y : ℕ} {ηlo : ℚ}
    (hlo : IsAdmissibleLevel ηlo) (hrk : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hPsw : (X, Y) ∈ sweptRegion y)
    (hev : eventType y (X, Y) = EventType.E) :
    ∃ z : Heights a b N, IsAboveDiagonal z ∧ colouring z ηlo = colouring y ηlo ∧
      (X, Y) ∈ sweptRegion z ∧ eventType z (X, Y) = EventType.B := by
  obtain ⟨hX, hdiag, hYsw⟩ := mem_sweptRegion.1 hPsw
  simp only at hX hdiag hYsw
  have hYlt : Y < ht y X := by simpa using eventType_eq_E_iff.1 hev
  have hXlt : X < a * N := by
    rcases Nat.lt_or_ge X (a * N) with h | h
    · exact h
    · have hXeq : X = a * N := le_antisymm hX h
      rw [hXeq, hy.2.1] at hYlt
      rw [hXeq] at hdiag
      have h1 : a * (Y + 1) ≤ a * (b * N) :=
        Nat.mul_le_mul (le_refl a) (show Y + 1 ≤ b * N by omega)
      have h2 : b * (a * N) = a * (b * N) := by ring
      have h3 : a * (Y + 1) = a * Y + a := by ring
      omega
  have hYb : Y < b * N + 1 := by have := ht_le_mul y X; omega
  obtain ⟨Y', hY'⟩ : ∃ Y' : Fin (b * N + 1), (Y' : ℕ) = Y := ⟨⟨Y, hYb⟩, rfl⟩
  have hymono : Monotone (ht y) := ht_mono hy.2.2.1
  have hzX : ht (lowerUpto y X Y') X = Y := by
    rw [ht_lowerUpto_of_le y Y' (le_refl X) hXlt.le, hY']
    omega
  have hzsucc : ht (lowerUpto y X Y') (X + 1) = ht y (X + 1) :=
    ht_lowerUpto_of_gt y Y' (Nat.lt_succ_self X)
  refine ⟨lowerUpto y X Y', isAboveDiagonal_lowerUpto hy hXlt Y' (by rw [hY']; exact hdiag),
    ?_, ?_, ?_⟩
  · refine Finset.ext fun p => ?_
    obtain ⟨x, i⟩ := p
    rw [mem_colouring_iff_levelIndex ha hN hlo, mem_colouring_iff_levelIndex ha hN hlo]
    rcases lt_trichotomy x X with hx | hx | hx
    · have e1 : ht (lowerUpto y X Y') x = min (ht y x) Y := by
        rw [ht_lowerUpto_of_le y Y' (by omega) hXlt.le, hY']
      have e2 : ht (lowerUpto y X Y') (x + 1) = min (ht y (x + 1)) Y := by
        rw [ht_lowerUpto_of_le y Y' (by omega) hXlt.le, hY']
      have l1 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk hx.le
      have l2 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk
        (show x + 1 ≤ X by omega)
      rw [e1, e2]
      omega
    · subst hx
      have l1 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk (le_refl x)
      rw [hzX, hzsucc]
      omega
    · have e1 : ht (lowerUpto y X Y') x = ht y x := ht_lowerUpto_of_gt y Y' hx
      have e2 : ht (lowerUpto y X Y') (x + 1) = ht y (x + 1) :=
        ht_lowerUpto_of_gt y Y' (by omega)
      rw [e1, e2]
  · exact mem_sweptRegion.2 ⟨hX, hdiag, by rw [hzsucc]; exact hYsw⟩
  · refine eventType_eq_B_iff.2 ⟨?_, hXlt, ?_⟩
    · simpa using hzX.symm
    · have h3 : Y < ht y (X + 1) := lt_of_lt_of_le hYlt (hymono (Nat.le_succ X))
      simpa [hzsucc] using h3

/-! ### The type-`E` partner of a type-`B` event, away from the origin -/

/-- **A type-`B` event at a bracketed point with a positive abscissa has a type-`E` partner.** The
partner is the splice `HJO.Mellit.raiseFrom` of `ŷ` at the ordinate `Y + 1` from the abscissa `X`
rightwards. It raises the single column `X`, because every column strictly right of `X` already has
height over `Y`, so the corner of the path at `(X, Y)` becomes an interior point.

The colouring below the level does not move, for the reason of
`HJO.Mellit.exists_eventType_B_partner`: the only two columns that can read the raise are `X - 1`
and `X`, both have level index under `Y` by `HJO.Mellit.levelIndex_lt_of_fst_le`, and the raise
moves the path only from `Y` to `Y + 1`.

The hypothesis `0 < X` is not a convenience. At `X = 0` a type-`B` event forces `Y = ŷ_0 = 0`, and
`HJO.Mellit.not_hasBEPartner_origin` shows that at the origin the partner does not exist at all. -/
theorem exists_eventType_E_partner (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {X Y : ℕ} {ηlo : ℚ}
    (hlo : IsAdmissibleLevel ηlo) (hrk : ηlo < ((pointRank a b N (X, Y) : ℤ) : ℚ))
    {y : Heights a b N} (hy : IsAboveDiagonal y) (hX0 : 0 < X)
    (hev : eventType y (X, Y) = EventType.B) :
    ∃ z : Heights a b N, IsAboveDiagonal z ∧ colouring y ηlo = colouring z ηlo ∧
      eventType z (X, Y) = EventType.E := by
  obtain ⟨hYfoot, hXlt, hYsucc⟩ := eventType_eq_B_iff.1 hev
  simp only at hYfoot hXlt hYsucc
  have hYb : Y + 1 < b * N + 1 := by have := ht_le_mul y (X + 1); omega
  obtain ⟨Y', hY'⟩ : ∃ Y' : Fin (b * N + 1), (Y' : ℕ) = Y + 1 := ⟨⟨Y + 1, hYb⟩, rfl⟩
  have hymono : Monotone (ht y) := ht_mono hy.2.2.1
  have hzlt : ∀ r, r < X → ht (raiseFrom y (X - 1) Y') r = ht y r := fun r hr =>
    ht_raiseFrom_of_le y Y' (by omega) (by omega)
  have hzgt : ∀ r, X < r → ht (raiseFrom y (X - 1) Y') r = ht y r := fun r hr => by
    rw [ht_raiseFrom_of_gt y Y' (by omega), hY']
    have h4 : Y + 1 ≤ ht y r := lt_of_lt_of_le hYsucc (hymono (show X + 1 ≤ r by omega))
    omega
  have hzX : ht (raiseFrom y (X - 1) Y') X = Y + 1 := by
    rw [ht_raiseFrom_of_gt y Y' (by omega), hY', ← hYfoot]
    omega
  refine ⟨raiseFrom y (X - 1) Y', isAboveDiagonal_raiseFrom hy (by omega) Y', ?_, ?_⟩
  · refine Finset.ext fun p => ?_
    obtain ⟨x, i⟩ := p
    rw [mem_colouring_iff_levelIndex ha hN hlo, mem_colouring_iff_levelIndex ha hN hlo]
    rcases lt_trichotomy (x + 1) X with hx | hx | hx
    · rw [hzlt x (by omega), hzlt (x + 1) (by omega)]
    · have l1 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk
        (show x ≤ X by omega)
      have l2 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk (le_refl X)
      have e1 : ht (raiseFrom y (X - 1) Y') x = ht y x := hzlt x (by omega)
      have e2 : ht (raiseFrom y (X - 1) Y') (x + 1) = Y + 1 := by rw [hx]; exact hzX
      have e3 : ht y (x + 1) = Y := by rw [hx, ← hYfoot]
      have e4 : levelIndex a b N ηlo (x + 1) = levelIndex a b N ηlo X := by rw [hx]
      rw [e1, e2, e3, e4]
      omega
    · rcases Nat.lt_or_ge X x with hx3 | hx3
      · rw [hzgt x hx3, hzgt (x + 1) (by omega)]
      · have hxX : x = X := by omega
        have l2 := levelIndex_lt_of_fst_le (a := a) (b := b) (N := N) ha hb hN hrk
          (show x ≤ X by omega)
        have e1 : ht (raiseFrom y (X - 1) Y') x = Y + 1 := by rw [hxX]; exact hzX
        have e2 : ht (raiseFrom y (X - 1) Y') (x + 1) = ht y (x + 1) := hzgt (x + 1) (by omega)
        have e3 : ht y x = Y := by rw [hxX, ← hYfoot]
        rw [e1, e2, e3]
        omega
  · exact eventType_eq_E_iff.2 (by simp [hzX])

/-! ### The origin: no type-`E` event, hence no partner, ever -/

/-- **No above-diagonal path has a type-`E` event at the origin.** A type-`E` event at `(0, 0)` says
`0 < ŷ_0`, and every above-diagonal path starts at `ŷ_0 = 0`.

This is the whole obstruction. It is not a smallness condition on `a`, `b` or `N` and no choice of
level or of path evades it: the existential that `HJO.Mellit.HasBEPartner` asks for at the origin
ranges over an empty set, and so does the type-`E` premise of `HJO.Mellit.SweepRecursionBE`. -/
theorem not_eventType_origin_eq_E {y : Heights a b N} (hy : IsAboveDiagonal y) :
    eventType y ((0 : ℕ), (0 : ℕ)) ≠ EventType.E := by
  intro h
  have h1 : (0 : ℕ) < ht y 0 := by simpa using eventType_eq_E_iff.1 h
  rw [hy.1] at h1
  exact absurd h1 (lt_irrefl 0)

/-- **The `BE` partner does not exist at the origin, for any path, any level and any `a`, `b`,
`N`.** The type-`B` half of `HJO.Mellit.HasBEPartner` asks for an above-diagonal path with a
type-`E` event at `(0, 0)`, and by `HJO.Mellit.not_eventType_origin_eq_E` there is none; the
antecedent is supplied by `HJO.Mellit.eventType_origin_eq_B`, which says every above-diagonal path
has a type-`B` event there.

Read against `HJO.Mellit.beClause_unavoidable`, which shows that the `BE` clause of the recursion is
forced at the origin at every sweep, this says that the hypothesis of
`HJO.Mellit.eq_dsc_of_recursion_step` is *false* exactly where that theorem needs it. So Mellit's
"`c` can be obtained in `2` ways" cannot be read as a statement about the origin: there `c` is
obtained in one way only, by rule `B`, which is what his own parenthesis "in the very end, when we
cross the point `(0,0)` we have to apply B)" says. The level recursion therefore does not determine
the value at the origin, and closing `HJO.Mellit.braidValueColouring_eq_dsc_floor` on Mellit's route
needs the origin supplied from the initial conditions rather than from the recursion. -/
@[hjo "lem_mellit_be_partner"]
theorem not_hasBEPartner_origin (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (ηlo : ℚ)
    {y : Heights a b N} (hy : IsAboveDiagonal y) :
    ¬ HasBEPartner a b N ηlo ((0 : ℕ), (0 : ℕ)) y := by
  intro h
  obtain ⟨z, hz, -, hzev⟩ := h.1 (eventType_origin_eq_B ha hb hN hy)
  exact not_eventType_origin_eq_E hz hzev

/-! ### The obligation, settled: the origin and nothing else -/

/-- **The `BE` partner exists at every bracketed swept point other than the origin.** Both halves of
`HJO.Mellit.HasBEPartner` together, from `HJO.Mellit.exists_eventType_E_partner` and
`HJO.Mellit.exists_eventType_B_partner`. The two hypotheses the definition does not carry and this
proof needs are supplied by `HJO.Mellit.Isolates`: admissibility of the lower level, and that the
lower level is under the rank of the point. Both are available wherever
`HJO.Mellit.eq_dsc_of_recursion_step` is applied.

The exclusion of the origin is exactly right, not a gap: `HJO.Mellit.not_hasBEPartner_origin` shows
the conclusion is false there. The type-`E` half needs no exclusion at all, since a type-`E` event
at `X = 0` would say `Y < ŷ_0 = 0`; the type-`B` half needs it, since a type-`B` event at `X = 0`
forces `Y = ŷ_0 = 0`, which is the origin. -/
@[hjo "lem_mellit_be_partner"]
theorem hasBEPartner_of_isolates (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {X Y : ℕ} {ηlo ηhi : ℚ}
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : (X, Y) ∈ sweptRegion y) (hne : (X, Y) ≠ ((0 : ℕ), (0 : ℕ))) :
    HasBEPartner a b N ηlo (X, Y) y := by
  refine ⟨fun hev => ?_, fun hev => exists_eventType_B_partner ha hb hN hI.lo hI.ltP hy hPsw hev⟩
  refine exists_eventType_E_partner ha hb hN hI.lo hI.ltP hy ?_ hev
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · obtain ⟨hYfoot, -, -⟩ := eventType_eq_B_iff.1 hev
    simp only at hYfoot
    rw [hy.1] at hYfoot
    exact absurd (show ((0 : ℕ), Y) = ((0 : ℕ), (0 : ℕ)) from by rw [hYfoot]) hne
  · exact hX

/-- **The obligation, settled: the `BE` partner exists at a bracketed swept point if and only if the
point is not the origin.** `HJO.Mellit.hasBEPartner_of_isolates` and
`HJO.Mellit.not_hasBEPartner_origin` in one statement. -/
theorem hasBEPartner_iff_ne_origin (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {X Y : ℕ} {ηlo ηhi : ℚ}
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : (X, Y) ∈ sweptRegion y) :
    HasBEPartner a b N ηlo (X, Y) y ↔ (X, Y) ≠ ((0 : ℕ), (0 : ℕ)) := by
  refine ⟨fun h hne => ?_, hasBEPartner_of_isolates ha hb hN hI hy hPsw⟩
  rw [hne] at h
  exact not_hasBEPartner_origin ha hb hN ηlo hy h

/-! ### The transfer, with the partner hypothesis discharged -/

/-- **One drop of the level transfers agreement at every event type and every point but the origin,
with no partner hypothesis.** `HJO.Mellit.eq_dsc_of_recursion_step` with
`HJO.Mellit.HasBEPartner` discharged by `HJO.Mellit.hasBEPartner_of_isolates`.

This is what discharging the hypothesis gives. Away from the origin Mellit's sentence needs nothing
beyond the two recursion clauses; at the origin, by `HJO.Mellit.not_hasBEPartner_origin`, the `BE`
clause has no type-`E` premise to be applied to and the recursion says nothing, so the value there
must come from the initial conditions. -/
theorem eq_dsc_of_recursion_step_of_ne_origin (q u : L) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N)
    {R : ℚ → Finset (ℕ × ℕ) → Total L} (hACD : SweepRecursionACD q u a b N R)
    (hBE : SweepRecursionBE q u a b N R) {X Y : ℕ} {ηlo ηhi : ℚ}
    (hI : Isolates a b N X Y ηlo ηhi) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (hPsw : (X, Y) ∈ sweptRegion y) (hne : (X, Y) ≠ ((0 : ℕ), (0 : ℕ)))
    (hhi : ∀ z : Heights a b N, IsAboveDiagonal z →
      R ηhi (colouring z ηhi) = dsc q u a b N ηhi (colouring z ηhi)) :
    R ηlo (colouring y ηlo) = dsc q u a b N ηlo (colouring y ηlo) :=
  eq_dsc_of_recursion_step q u ha hb hN hACD hBE hI hy hPsw
    (hasBEPartner_of_isolates ha hb hN hI hy hPsw hne) hhi

/-! ### A second defect, independent of the origin -/

/-- **`HJO.Mellit.HasBEPartner` is also false at a point the path does not sweep.** The definition
quantifies over every lattice point, and its type-`E` half asks the partner to *sweep* the point;
but sweeping requires `bX ≤ aY`, which is a condition on the point alone. On the `2 × 3` rectangle
the path `(0,3,3)` has a type-`E` event at `(1, 0)` — the point lies strictly under the path — and
no path whatever sweeps `(1, 0)`, since `3 · 1 ≤ 2 · 0` fails.

This is the lesser of the two defects and it is a defect of the statement, not of the mathematics:
`HJO.Mellit.eq_dsc_of_recursion_step` only ever applies the hypothesis at a swept point, and
`HJO.Mellit.hasBEPartner_of_isolates` assumes exactly that. The origin obstruction
(`HJO.Mellit.not_hasBEPartner_origin`) survives every side condition; this one does not. -/
theorem not_hasBEPartner_two_three_one_unswept :
    ¬ HasBEPartner 2 3 1 (7 / 2) (1, 0) (![0, 3, 3] : Heights 2 3 1) := by
  intro h
  obtain ⟨z, -, -, hzsw, -⟩ := h.2 (by decide)
  have h1 := (mem_sweptRegion.1 hzsw).2.1
  simp only at h1
  omega

/-! ### The two constructions, against the hand-built instance -/

/-- **The clamp recovers the hand-exhibited type-`B` partner.** On the `2 × 3` rectangle at the
point `(1, 2)` the path `(0,3,3)` has a type-`E` event, and
`HJO.Mellit.exists_eventType_B_partner` produces `HJO.Mellit.lowerUpto` of it at the ordinate `2` up
to the abscissa `1`. That path is `(0,2,3)`, which is exactly the partner
`HJO.Mellit.hasBEPartner_two_three_one_E` supplies by hand. -/
theorem lowerUpto_two_three_one :
    lowerUpto (![0, 3, 3] : Heights 2 3 1) 1 ⟨2, by omega⟩ = (![0, 2, 3] : Heights 2 3 1) := by
  decide

/-- **The splice recovers the hand-exhibited type-`E` partner.** On the `2 × 3` rectangle at the
point `(1, 2)` the path `(0,2,3)` has a type-`B` event, and
`HJO.Mellit.exists_eventType_E_partner` produces `HJO.Mellit.raiseFrom` of it at the ordinate `3`
from the abscissa `0`. That path is `(0,3,3)`, which is exactly the partner
`HJO.Mellit.hasBEPartner_two_three_one_B` supplies by hand. So the general constructions are the
geometric ones the worked instance was built from, and not some other pair that happens to satisfy
the definition. -/
theorem raiseFrom_two_three_one :
    raiseFrom (![0, 2, 3] : Heights 2 3 1) 0 ⟨3, by omega⟩ = (![0, 3, 3] : Heights 2 3 1) := by
  decide

end HJO.Mellit

end
