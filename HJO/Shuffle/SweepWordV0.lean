/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.SweepWidth
public import HJO.Shuffle.SweepWitness
public meta import HJO.Attr

/-! # The sweep word is an endomorphism of `V_0`

`HJO.Mellit.sweepWord_mem_piece_zero` asserts that the composite
`W(P̂) = Φ_{P̂}(P_M) ∘ ⋯ ∘ Φ_{P̂}(P_1)` is defined and is a `𝕜`-linear map from `V_0` to `V_0`.
Being defined and `𝕜`-linear is free here — `HJO.Mellit.sweepWord` is a product in
`Module.End L (HJO.Sweep.Total L)`, so it exists whatever the widths do — and the content of the
lemma is the grading: the composite carries `V_0` into `V_0`. This file proves that.

## Main results

* `HJO.Sweep.dplus_mem_piece`, `HJO.Sweep.corner_mem_piece`: the two graded operators of
  `HJO.Sweep.dplus` and `HJO.Sweep.corner` land in the pieces their definitions give them,
  `d_+ : V_k → V_{k+1}` and `Δ : V_k → V_k`. `d_- : V_k → V_{k-1}` is
  `HJO.Sweep.dminus_mem_piece`, proved earlier.
* `HJO.Mellit.sweepOperator_mem_piece`: the event operator `Φ_{P̂}(P)` carries `V_{k_{P̂}(P)}` into
  `V_{k'}`, with `k'` the index `HJO.Mellit.nextWidth` reads off the event type — the codomain
  `HJO.Mellit.sweepOperator` gives it.
* `HJO.Mellit.isChain_rankAdjacent_sortByRank`: consecutive points of the rank-order listing of the
  swept region are rank-adjacent, so `HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` applies
  along the listing.
* `HJO.Mellit.sweepWord_mem_piece_zero`.

## Implementation notes

### Where the grading chain comes from

The listing `HJO.Mellit.sortByRank a b N (Sw(P̂))` is the listing `P_M, …, P_1`, in *increasing*
rank, and `HJO.Mellit.sweepWord` is the `List.prod` along it, so the operator of the list's **last**
entry — the highest-ranked swept point `P_1` — is applied first and the operator of its **first**
entry — the lowest-ranked point — last. The induction therefore runs along `p :: t` with the input
entering at `t.getLast` and the output leaving through `p`, which is
`HJO.Mellit.prod_mem_piece_of_isChain`.

Between two consecutive entries the width is pinned by
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`: with `p` the lower and `r` the upper,
`k_{P̂}(p) - k_{P̂}(r)` is `+1`, `-1` or `0` according to the event type at `r`, which is exactly to
say that `HJO.Mellit.nextWidth y r = k_{P̂}(p)` — the codomain of `Φ_{P̂}(r)` is the domain of
`Φ_{P̂}(p)`. That is the whole content of "the composite is defined".

### The two ends

The highest-ranked swept point has width `0`: a north step live there would have its head — itself a
swept point, by `HJO.Paths.mem_sweptRegion_of_mem_northSteps` — ranked above it. The lowest-ranked
swept point is the origin, because the rank `M(a y - b x) + x` is nonnegative on the swept region
and vanishes only at `(0,0)`; there the event type is `B` and the width is `1`, the only live north
step being the origin itself, so `nextWidth` at that point is `1 - 1 = 0`. Those are the two end
identifications, and they are why `V_0` appears at both ends rather than once.

### The nondegeneracy hypotheses

`0 < a`, `0 < b` and `0 < N` are carried. They are not decoration: `0 < a` and `0 < N` are what make
the rank injective on the strip (`HJO.Paths.abovePointRank_injOn`), hence the rank-order listing
unambiguous, and `0 < b` is what puts a north step at the origin and so makes the event type there
`B` rather than `D`. At `b = 0` the path is flat, the origin is a type-`D` event of width `0`, and
the conclusion still holds — by a different route, which is not written out.

## References

The lemma `HJO.Mellit.sweepWord_mem_piece_zero`, using `HJO.Paths.IsAboveDiagonal`,
`HJO.Sweep.piece`, `HJO.Mellit.sweepWord`, `HJO.Sweep.braid`, `HJO.Sweep.dminus`, `HJO.Sweep.dplus`,
`HJO.Mellit.sweepOperator`, `HJO.Paths.sweepWidth`, `HJO.Sweep.dividedDiff_mem_piece` and
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`. Transcribing A. Mellit, *Toric braids and
`(m, n)`-parking functions*, section "The sweep process".
-/

@[expose] public section

open Finset

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in
/-- **`d_+` carries `V_k` into `V_{k+1}`**, the codomain `HJO.Sweep.dplus` gives it: `τ_{k+1}` and
the multiplication by `y_{k+1}` both land in `V_{k+1}`, and the ascending train reads only braid
letters of index at most `k + 1`. -/
theorem dplus_mem_piece (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    dplus q k F ∈ piece L (k + 1) := by
  rw [dplus_apply]
  refine neg_mem (trainUpEnd_mem_piece q (by omega) le_rfl (mul_mem ?_ ?_))
  · exact auxVar_mem_piece (by omega) le_rfl
  · exact qshift_mem_piece q (i := k + 1) (k := k) (m := k + 1) (by omega) (by omega) hF

/-- **`Δ` is an endomorphism of `V_k`**, the domain and codomain `HJO.Sweep.corner` gives it. Each
of its two composites returns to `V_k`: `d_-d_+` goes up then down, and `d_+d_-` down then up. The
unread index `k = 0` is the one-term branch `d_-d_+`, which returns to `V_0` for the same reason. -/
theorem corner_mem_piece (q : L) (k : ℕ) {F : Total L} (hF : F ∈ piece L k) :
    corner q k F ∈ piece L k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [corner_zero, LinearMap.smul_apply, Module.End.mul_apply]
    exact smul_mem_piece (by simpa using dminus_mem_piece q 1 (dplus_mem_piece q 0 hF))
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [corner_of_pos q (by omega), LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.mul_apply, Module.End.mul_apply]
    refine smul_mem_piece (sub_mem ?_ ?_)
    · simpa using dminus_mem_piece q (j + 2) (dplus_mem_piece q (j + 1) hF)
    · simpa using dplus_mem_piece q j (by simpa using dminus_mem_piece q (j + 1) hF)

end HJO.Sweep

namespace HJO.Mellit

open ParkingFunctions Paths Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {a b N : ℕ}

/-! ### The graded index the event operator leaves a point in -/

/-- The graded index `k'` of the codomain of `Φ_{P̂}(P)`: the width `k_{P̂}(P)` raised by one at a
type-`A` event, lowered by one at a type-`B` event, and unchanged at the other three. This is the
`k'` of `HJO.Mellit.sweepOperator`, named so that the chaining of the domains and codomains
along the swept region can be stated. -/
def nextWidth (y : Heights a b N) (P : ℕ × ℕ) : ℕ :=
  match eventType y P with
  | EventType.A => sweepWidth y P + 1
  | EventType.B => sweepWidth y P - 1
  | _ => sweepWidth y P

/-- **The event operator carries `V_{k_{P̂}(P)}` into `V_{k'}`.** This is the domain and codomain
clause of `HJO.Mellit.sweepOperator`, read on the graded pieces of the one total space: `d_+` raises
the index, `d_-` lowers it, and `Δ`, the scalar `q^{a_{P̂}(P)}` and the scalar `u` preserve it. -/
theorem sweepOperator_mem_piece (q u : L) (y : Heights a b N) (P : ℕ × ℕ) {F : Total L}
    (hF : F ∈ piece L (sweepWidth y P)) :
    sweepOperator q u y P F ∈ piece L (nextWidth y P) := by
  have key : ∀ e : EventType, eventType y P = e →
      sweepOperator q u y P F ∈ piece L (nextWidth y P) := by
    intro e he
    cases e with
    | A =>
      rw [show sweepOperator q u y P = dplus q (sweepWidth y P) from by rw [sweepOperator, he],
        show nextWidth y P = sweepWidth y P + 1 from by rw [nextWidth, he]]
      exact dplus_mem_piece q _ hF
    | B =>
      rw [show sweepOperator q u y P = dminus q (sweepWidth y P) from by rw [sweepOperator, he],
        show nextWidth y P = sweepWidth y P - 1 from by rw [nextWidth, he]]
      exact dminus_mem_piece q _ hF
    | C =>
      rw [show sweepOperator q u y P
            = q ^ (-(sweepRight y P : ℤ)) • corner q (sweepWidth y P) from by
          rw [sweepOperator, he],
        show nextWidth y P = sweepWidth y P from by rw [nextWidth, he], LinearMap.smul_apply]
      exact smul_mem_piece (corner_mem_piece q _ hF)
    | D =>
      rw [show sweepOperator q u y P = q ^ sweepRight y P • (1 : Module.End L (Total L)) from by
          rw [sweepOperator, he],
        show nextWidth y P = sweepWidth y P from by rw [nextWidth, he], LinearMap.smul_apply]
      exact smul_mem_piece (by simpa using hF)
    | E =>
      rw [sweepOperator_of_eventType_E q u y P he,
        show nextWidth y P = sweepWidth y P from by rw [nextWidth, he], LinearMap.smul_apply]
      exact smul_mem_piece (by simpa using hF)
  exact key _ rfl

/-! ### The rank-order listing is a chain of rank-adjacent points -/

/-- **Consecutive points of the rank-order listing of the swept region are rank-adjacent.** The
listing is sorted by rank (`HJO.Mellit.sortByRank_pairwise`), has no repetitions
(`HJO.Mellit.sortByRank_nodup`) and enumerates the region (`HJO.Mellit.mem_sortByRank`), and the
rank is injective on the strip, so consecutive ranks increase strictly and a swept point ranked
between two consecutive entries would have to sit at an index both below and above them. -/
theorem isChain_rankAdjacent_sortByRank {y : Heights a b N} (ha : 0 < a) (hN : 0 < N) :
    (sortByRank a b N (sweptRegion y)).IsChain (RankAdjacent a b N y) := by
  have hpw := sortByRank_pairwise a b N (sweptRegion y)
  have hnd := sortByRank_nodup a b N (sweptRegion y)
  simp only [pointRank, List.pairwise_iff_getElem] at hpw
  rw [List.isChain_iff_getElem]
  intro i hi
  have hmI : (sortByRank a b N (sweptRegion y))[i] ∈ sweptRegion y :=
    mem_sortByRank.1 (List.getElem_mem (by omega))
  have hmI1 : (sortByRank a b N (sweptRegion y))[i + 1] ∈ sweptRegion y :=
    mem_sortByRank.1 (List.getElem_mem hi)
  have hstrict : abovePointRank a b N (sortByRank a b N (sweptRegion y))[i].1
        (sortByRank a b N (sweptRegion y))[i].2 <
      abovePointRank a b N (sortByRank a b N (sweptRegion y))[i + 1].1
        (sortByRank a b N (sweptRegion y))[i + 1].2 := by
    rcases eq_or_lt_of_le (hpw i (i + 1) (by omega) hi (by omega)) with heq | hlt
    · obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN
        (mem_sweptRegion.1 hmI).1 (mem_sweptRegion.1 hmI1).1 heq
      have hij : (sortByRank a b N (sweptRegion y))[i]
          = (sortByRank a b N (sweptRegion y))[i + 1] := by
        rw [Prod.ext_iff]; exact ⟨e1, e2⟩
      exact absurd (hnd.getElem_inj_iff.1 hij) (by omega)
    · exact hlt
  refine ⟨hmI, hmI1, hstrict, fun R hR hbetween => ?_⟩
  obtain ⟨hb1, hb2⟩ := hbetween
  obtain ⟨j, hj, hjR⟩ := List.getElem_of_mem (mem_sortByRank.2 hR)
  have hRj : abovePointRank a b N R.1 R.2
      = abovePointRank a b N (sortByRank a b N (sweptRegion y))[j].1
          (sortByRank a b N (sweptRegion y))[j].2 := by rw [hjR]
  rcases Nat.lt_or_ge j i with hjlt | hjge
  · have := hpw j i hj (by omega) hjlt
    omega
  rcases eq_or_lt_of_le hjge with hje | hilt
  · subst hje
    omega
  rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with hje | hjgt
  · subst hje
    omega
  · have := hpw (i + 1) j hi hj hjgt
    omega

/-! ### The graded chain along a rank-adjacent listing -/

/-- **The product along a rank-adjacent listing carries the piece of its last entry's width into the
piece of its first entry's codomain index.** The list is in increasing rank, so `List.prod` applies
the operator of the *last* entry first, and
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent` is what makes each factor's codomain the next
factor's domain. -/
theorem prod_mem_piece_of_isChain (q u : L) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hN : 0 < N) : ∀ (t : List (ℕ × ℕ)) (p : ℕ × ℕ),
      (p :: t).IsChain (RankAdjacent a b N y) → ∀ {F : Total L},
      F ∈ piece L (sweepWidth y ((p :: t).getLast (List.cons_ne_nil p t))) →
        ((p :: t).map (sweepOperator q u y)).prod F ∈ piece L (nextWidth y p) := by
  intro t
  induction t with
  | nil =>
    intro p _ F hF
    simpa using sweepOperator_mem_piece q u y p hF
  | cons r t' ih =>
    intro p hchain F hF
    obtain ⟨h1, h2⟩ := List.isChain_cons.1 hchain
    have hadj : RankAdjacent a b N y p r := h1 r (by simp)
    have hnext : nextWidth y r = sweepWidth y p := by
      have hw := sweepWidth_sub_sweepWidth_of_rankAdjacent hy ha hN hadj
      cases hev : eventType y r with
      | A =>
        rw [show nextWidth y r = sweepWidth y r + 1 from by rw [nextWidth, hev]]
        rw [hev] at hw
        simp only [reduceIte] at hw
        omega
      | B =>
        rw [show nextWidth y r = sweepWidth y r - 1 from by rw [nextWidth, hev]]
        rw [hev] at hw
        simp only [reduceCtorEq, reduceIte] at hw
        omega
      | C =>
        rw [show nextWidth y r = sweepWidth y r from by rw [nextWidth, hev]]
        rw [hev] at hw
        simp only [reduceCtorEq, reduceIte] at hw
        omega
      | D =>
        rw [show nextWidth y r = sweepWidth y r from by rw [nextWidth, hev]]
        rw [hev] at hw
        simp only [reduceCtorEq, reduceIte] at hw
        omega
      | E =>
        rw [show nextWidth y r = sweepWidth y r from by rw [nextWidth, hev]]
        rw [hev] at hw
        simp only [reduceCtorEq, reduceIte] at hw
        omega
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    refine sweepOperator_mem_piece q u y p ?_
    rw [← hnext]
    exact ih r h2 hF

/-! ### The two ends of the listing -/

/-- The rank is nonnegative on the swept region: a swept point has `ay ≥ bx`, and the rank is
`M(ay - bx) + x` with `M > 0` and `x ≥ 0`. -/
theorem abovePointRank_nonneg_of_mem_sweptRegion {y : Heights a b N} {P : ℕ × ℕ}
    (hP : P ∈ sweptRegion y) : 0 ≤ abovePointRank a b N P.1 P.2 := by
  obtain ⟨-, hdiag, -⟩ := mem_sweptRegion.1 hP
  have hdz : (0 : ℤ) ≤ (a : ℤ) * P.2 - (b : ℤ) * P.1 := by
    have hc : ((b * P.1 : ℕ) : ℤ) ≤ ((a * P.2 : ℕ) : ℤ) := Int.ofNat_le.2 hdiag
    push_cast at hc
    linarith
  have hM : (0 : ℤ) ≤ ((a : ℤ) * N + 1) * N := by positivity
  have hX : (0 : ℤ) ≤ (P.1 : ℤ) := Int.natCast_nonneg _
  rw [abovePointRank]
  have := mul_nonneg hM hdz
  linarith

/-- The origin is swept, whatever the height vector: its abscissa and ordinate are both `0`. -/
theorem zero_mem_sweptRegion (y : Heights a b N) : ((0 : ℕ), (0 : ℕ)) ∈ sweptRegion y :=
  mem_sweptRegion.2 ⟨Nat.zero_le _, by simp, Nat.zero_le _⟩

/-- **The width at the origin is `1`**, the only live north step being the origin itself: a north
step has nonnegative rank, with equality only at `(0,0)`, so the half-open window
`rk̂(u) ≤ 0 < rk̂(u) + ω` at the origin selects that one step. -/
theorem sweepWidth_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b) (hN : 0 < N) :
    sweepWidth y ((0 : ℕ), (0 : ℕ)) = 1 := by
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ northSteps y := mem_northSteps_zero hy hb hN
  have ha : 0 < a := by
    obtain ⟨h1, -, -⟩ := mem_northSteps_iff.1 h00
    exact Nat.pos_of_ne_zero fun h => by simp [h] at h1
  have hω : 0 < attackWindow a N := attackWindow_pos_iff.2 (Nat.mul_pos ha hN)
  have hωz : (0 : ℤ) < (attackWindow a N : ℤ) := by exact_mod_cast hω
  have hz : abovePointRank a b N 0 0 = 0 := by simp [abovePointRank]
  have hzp : abovePointRank a b N ((0 : ℕ), (0 : ℕ)).1 ((0 : ℕ), (0 : ℕ)).2 = 0 := hz
  have hset : liveSteps y ((0 : ℕ), (0 : ℕ)) = {((0 : ℕ), (0 : ℕ))} := by
    ext u
    rw [liveSteps, Finset.mem_filter, Finset.mem_singleton, hzp]
    constructor
    · rintro ⟨hu, hu1, -⟩
      by_contra hne
      have hlt := abovePointRank_lt_of_mem_northSteps hy hu hne
      rw [hz] at hlt
      omega
    · rintro rfl
      refine ⟨h00, ?_, ?_⟩
      · rw [hzp]
      · rw [hzp]; omega
  rw [sweepWidth, hset, Finset.card_singleton]

/-- **The event type at the origin is `B`**: the origin is the foot of a north step, so its type is
`B` or `C` by `HJO.Paths.mem_northSteps_iff_eventType`, and it is the head of none — no north step
has a head of ordinate `0` — so its type is not `A` or `C` by
`HJO.Paths.isSweepHead_iff_eventType`. -/
theorem eventType_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b) (hN : 0 < N) :
    eventType y ((0 : ℕ), (0 : ℕ)) = EventType.B := by
  have hBC := (mem_northSteps_iff_eventType (zero_mem_sweptRegion y)).1
    (mem_northSteps_zero hy hb hN)
  have hnh : ¬IsSweepHead y ((0 : ℕ), (0 : ℕ)) := by
    rintro ⟨u, -, hu⟩
    have h := congrArg Prod.snd hu
    simp at h
  rcases hBC with h | h
  · exact h
  · exact absurd ((isSweepHead_iff_eventType hy (zero_mem_sweptRegion y)).2 (Or.inr h)) hnh

/-- **The codomain index at the origin is `0`.** The event type there is `B`, so the operator lowers
the index, and the width is `1`; this is the right-hand end of the identification, `V_0`
as the codomain of `Φ_{P̂}(P_M)`. -/
theorem nextWidth_zero {y : Heights a b N} (hy : IsAboveDiagonal y) (hb : 0 < b) (hN : 0 < N) :
    nextWidth y ((0 : ℕ), (0 : ℕ)) = 0 := by
  rw [nextWidth, eventType_zero hy hb hN, sweepWidth_zero hy hb hN]

/-- **Nothing is live at the highest-ranked swept point, so its width is `0`.** The head of a north
step is itself swept, and outranks the foot by `ω`, so a step live at a point that no swept point
outranks would have its head ranked above the maximum. This is the left-hand end of the
identification, `V_0` as the domain of `Φ_{P̂}(P_1)`. -/
theorem sweepWidth_eq_zero_of_maximal {y : Heights a b N} (hy : IsAboveDiagonal y) {P : ℕ × ℕ}
    (hmax : ∀ R ∈ sweptRegion y, abovePointRank a b N R.1 R.2 ≤ abovePointRank a b N P.1 P.2) :
    sweepWidth y P = 0 := by
  rw [sweepWidth, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.2 fun {u} hu hcon => ?_
  have hhead : abovePointRank a b N u.1 (u.2 + 1) ≤ abovePointRank a b N P.1 P.2 :=
    hmax (u.1, u.2 + 1) (mem_sweptRegion_of_mem_northSteps hy hu).2
  have hsucc : abovePointRank a b N u.1 (u.2 + 1) =
      abovePointRank a b N u.1 u.2 + attackWindow a N := abovePointRank_succ a b N u.1 u.2
  omega

/-- A sorted list's last entry is maximal for the sort key. This is the index-free form of
`List.Pairwise` at the right end, which is what identifies the domain of the sweep word's
first-applied factor. -/
private theorem le_getLast_of_pairwise {α : Type*} {f : α → ℤ} : ∀ (l : List α) (h : l ≠ []),
    l.Pairwise (fun x z => f x ≤ f z) → ∀ z ∈ l, f z ≤ f (l.getLast h) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons p t ih =>
    intro h hpw z hz
    rcases t with _ | ⟨r, t'⟩
    · rw [List.mem_singleton] at hz
      rw [hz]
      exact le_rfl
    · obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hpw
      rcases List.mem_cons.1 hz with rfl | hzt
      · exact h1 _ (List.getLast_mem (List.cons_ne_nil r t'))
      · exact ih (List.cons_ne_nil r t') h2 z hzt

/-! ### The sweep word on `V_0` -/

/-- **The sweep word carries `V_0` into `V_0`.** The statement that
`W(P̂)` "is defined and is a `𝕜`-linear map from `V_0` to `V_0`": existence and `L`-linearity are
carried by the type of `HJO.Mellit.sweepWord`, a product in `Module.End L (HJO.Sweep.Total L)`, and
the content is that the composite respects the grading and returns to the piece it starts in.

The proof runs as follows: the widths chain along the rank-order listing by
`HJO.Paths.sweepWidth_sub_sweepWidth_of_rankAdjacent`, the highest-ranked swept point has width `0`,
and the lowest-ranked one is the origin, a type-`B` event of width `1`, whose operator therefore
lands back in `V_0`. -/
@[hjo "lem_sweep_word_v0"]
theorem sweepWord_mem_piece_zero (q u : L) {y : Heights a b N} (hy : IsAboveDiagonal y)
    (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) {F : Total L} (hF : F ∈ piece L 0) :
    sweepWord q u y F ∈ piece L 0 := by
  have hne : sortByRank a b N (sweptRegion y) ≠ [] :=
    List.ne_nil_of_mem (mem_sortByRank.2 (zero_mem_sweptRegion y))
  obtain ⟨p, t, hlt⟩ := List.exists_cons_of_ne_nil hne
  have hpw : (p :: t).Pairwise fun P Q =>
      abovePointRank a b N P.1 P.2 ≤ abovePointRank a b N Q.1 Q.2 :=
    hlt ▸ sortByRank_pairwise a b N (sweptRegion y)
  have hmemcons : ∀ R, R ∈ sweptRegion y → R ∈ p :: t := fun R hR =>
    hlt ▸ mem_sortByRank.2 hR
  have hpmem : p ∈ sweptRegion y := mem_sortByRank.1 (by rw [hlt]; exact List.mem_cons_self ..)
  -- the first entry is ranked below every swept point, the last entry above every one
  have hmin : ∀ R ∈ sweptRegion y,
      abovePointRank a b N p.1 p.2 ≤ abovePointRank a b N R.1 R.2 := by
    intro R hR
    rcases List.mem_cons.1 (hmemcons R hR) with rfl | hRt
    · exact le_rfl
    · exact (List.pairwise_cons.1 hpw).1 R hRt
  have hmax : ∀ R ∈ sweptRegion y,
      abovePointRank a b N R.1 R.2 ≤
        abovePointRank a b N ((p :: t).getLast (List.cons_ne_nil p t)).1
          ((p :: t).getLast (List.cons_ne_nil p t)).2 := fun R hR =>
    le_getLast_of_pairwise (f := fun P => abovePointRank a b N P.1 P.2) (p :: t)
      (List.cons_ne_nil p t) hpw R (hmemcons R hR)
  -- the first entry is the origin
  have hp00 : p = ((0 : ℕ), (0 : ℕ)) := by
    have hple : abovePointRank a b N p.1 p.2 ≤ abovePointRank a b N 0 0 :=
      hmin _ (zero_mem_sweptRegion y)
    have hpge : 0 ≤ abovePointRank a b N p.1 p.2 :=
      abovePointRank_nonneg_of_mem_sweptRegion hpmem
    have hz : abovePointRank a b N 0 0 = 0 := by simp [abovePointRank]
    have heq : abovePointRank a b N p.1 p.2 = abovePointRank a b N 0 0 := by omega
    obtain ⟨e1, e2⟩ := abovePointRank_injOn (b := b) ha hN
      (mem_sweptRegion.1 hpmem).1 (Nat.zero_le (a * N)) heq
    rw [Prod.ext_iff]
    exact ⟨e1, e2⟩
  have hzero : nextWidth y p = 0 := by rw [hp00]; exact nextWidth_zero hy hb hN
  have hmain := prod_mem_piece_of_isChain q u hy ha hN t p
    (hlt ▸ isChain_rankAdjacent_sortByRank ha hN) (F := F)
    (by rw [sweepWidth_eq_zero_of_maximal hy hmax]; exact hF)
  rw [sweepWord, hlt]
  exact hzero ▸ hmain

end HJO.Mellit
