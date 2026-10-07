/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Shuffle.MellitColumnChain
public meta import HJO.Attr

/-! # Commuting `D_0` past the chain: the Leibniz half of the `χ`-telescope

`HJO/Shuffle/MellitColumnChain.lean` puts `ψ_b` inside the `D_n`-algebra as the nest
`HJO.Sweep.chain` and translates the clause of `HJO.Sweep.ColumnCommutes` at a general `b` into

`M·chain (b+1) 1 0 f = chain b 1 0 (D_0f) - D_0(chain b 1 0 f)`.

The standard argument for that identity has two halves. The first is **Leibniz plus the pair
commutator**: commuting `D_0` past a word of length `b+1` costs one term per letter, and each term
is the pair commutator `[D_{n_p}, D_0]` inserted at that letter, which
`HJO.Sym.smul_sum_sum_dopInt_dopInt` expands into words of length `b+2` carrying a factor `M`. The
second is a cancellation. **This file does the first half.** The second is
`HJO/Shuffle/MellitColumnChainTelescope.lean`, which does it by an induction on `b` rather than
by the global `χ`-telescope; the generalisation that carries that induction is set up at
the end of this file.

## Leibniz, for free, from the recursion

The nest is a recursion on the letter nearest the argument, so Leibniz is a recursion too. Writing
`HJO.Sweep.chainComm b K j g` for `chain b K j (D_0g) - D_0(chain b K j g)` and
`HJO.Sweep.dopComm n g` for the one-letter commutator `D_n(D_0g) - D_0(D_ng)`:

* `chainComm 0 K j g = dopComm (K+j) g`   (`HJO.Sweep.chainComm_zero_eq`),
* `chainComm (b+1) K j g = ∑_l(qu)^l(chain b K l (dopComm (j-l) g) + chainComm b K l (D_{j-l}g))`
  (`HJO.Sweep.chainComm_succ`).

Both are **unconditional** --- no hypothesis on `q`, `u` or the degree of `g`, and no truncation
condition --- because they are nothing but the linearity of the nest in its argument
(`HJO.Sweep.chain_sub`) together with the linearity of `D_0`. The first summand of the step is the
new letter inserted at the outermost position of the remaining nest; the second recurses, and
unfolding the recursion `b+1` times produces exactly one term per position `p = 0,…,b`.

## The pair commutator makes every term a multiple of `M`

`HJO.Sweep.dopComm_eq_smul_sum_sum` and `HJO.Sweep.dopComm_eq_neg_smul_sum_sum` are
`HJO.Sym.smul_sum_sum_dopInt_dopInt` read at the pair `(n, 0)` in its two orientations:

`dopComm n g = M·∑_{i<n}∑_{l ≥ 0}(qu)^lD_{1+i+l}(D_{n-1-i-l}g)`   for `n ≥ 0`,
`dopComm n g = -M·∑_{i<-n}∑_{l ≥ 0}(qu)^lD_{n+1+i+l}(D_{-1-i-l}g)`   for `n ≤ 0`.

The sign is the whole of the case split the standard argument makes on whether the letter being
commuted past is above or below `0`; the two readings are the same statement of
`HJO.Sym.smul_sum_sum_dopInt_dopInt` with `m` and `n` exchanged. Neither carries a hypothesis on `q`
or `u`, and in particular neither needs `M ≠ 0`: `M` is produced by the factor every member of the
displacement's kernel above the zeroth carries, and nothing here divides by it.

So the whole of `[ψ_b, D_0]` is `M` times an explicit nest of insertions, and
`HJO.Sweep.columnCommutes_at_iff_chainComm` states what is left:

**`M·chain (b+1) 1 0 f = chainComm b 1 0 f`**, with `chainComm` the recursion above.

## The `χ`-telescope: what is here and what is not

Collecting the insertions by target word turns the coefficient at position `p` into
`∑_e χ_{p+1}(χ_p - χ_{p+2})(qu)^e`, where a length-`b+2` word is the tuple `(m_1,…,m_{b+1})` with
`m_p - m_{p+1}` its letters, `T = ∑m_i`, `m_0 = 0`, `m_{b+2} = -1`, and
`χ_i = [m_i ≥ T - e]`. **That collection --- the deletion/insertion reindexing between
`(tuple of length b+1, position, i, l)` and `(tuple of length b+2, e)` --- is NOT formalised here**,
and it would be the bulk of that route.

What is formalised is the scalar identity it feeds, in three parts, on an arbitrary
`m : ℕ → ℤ` and an arbitrary threshold: the telescope
(`HJO.Sweep.sum_chi_mul_sub_chi`, which is `∑_p(a_p - a_{p+1})` at `a_p = χ_pχ_{p+1}`), the boundary
evaluation `χ_0χ_1 - χ_{b+1}χ_{b+2} = [e = T]` (`HJO.Sweep.chi_boundary_eq_ite`), and the vanishing
at a position whose letter is a local minimum (`HJO.Sweep.chi_mul_sub_chi_eq_zero`), which is why a
tuple with a negative entry contributes nothing. **These three are short, and they are not the
telescope**: they are the algebra the reindexing would reduce to.

That route is not the one that closed the clause. `HJO/Shuffle/MellitColumnChainTelescope.lean`
closes it by an **induction on `b`** instead, described next, so
`HJO.Sweep.ColumnCommutes` (`HJO.Sweep.columnCommutes`) and the `(a,1)` column of
`HJO.Mellit.lhsRewrite_sweepWitness` at a general `f` (`HJO.Sweep.lhsSlope_succ_one`) are
**proved**.

## The generalisation that does carry an induction

The `χ`-telescope above is a *global* collection over all `b+1` positions at once, and that is why
no induction on `b` is apparent: the obvious generalisation of the clause to a
starting index --- `chainComm b 1 j g = M·chain (b+1) 1 j g` --- is **false at every `j ≥ 1`**.

**It becomes true when the coefficient is generalised instead of the index.** With
`HJO.Sweep.chainGeomCoeff` the geometric run `c(l,j) = (qu)^{l-min(j,l)} + ⋯ + (qu)^l` and
`HJO.Sweep.chainGeom` the nest weighted by it,

`chainComm b 1 j g = M·chainGeom b j g`   for every `b` and every `j ≥ 0`,

which at `j = 0` is the clause itself, because `c(l,0) = (qu)^l`
(`HJO.Sweep.chainGeom_zero_eq_chain`). Its base is
`dopComm (1+j) g = M·∑_l c(l,j)·D_{1+l}(D_{j-l}g)`, and its step is the Leibniz recursion above,
after which the three nests run over the same words `chain b 1 l_2 (D_{l_1-l_2}(D_{j-l_1}g))` and
the identity reduces, pair by pair `(l_1,l_2)`, to the **exact** scalar identity

`(qu)^{l_2}·Γ(l_1,l_2,j) + (qu)^{l_1}·c(l_2,l_1) = (qu)^{l_2}·c(l_1,j)`,

with `Γ` the coefficient of `D_{l_1-l_2}D_{j-l_1}` in `[D_{j-l_2},D_0]` --- and that is nothing but
`G(m+n) = G(m) + (qu)^m·G(n)` for the geometric sums `G`, holding uniformly across the two sign
branches of `HJO.Sweep.dopComm_eq_smul_sum_sum` / `HJO.Sweep.dopComm_eq_neg_smul_sum_sum`.

So what is left is a reindexing of **two adjacent levels**, not the `b`-fold global collection.

**The base is here; the step is in
`HJO/Shuffle/MellitColumnChainTelescope.lean`.** `HJO.Sweep.chainComm_zero_eq_smul_chainGeom`
proves `chainComm 0 1 j g = M·chainGeom 0 j g` at every `j`, by regrouping the pair commutator's
geometric double sum by its total index (`HJO.Sweep.sum_range_sum_range_smul_eq_sum_range`) --- and
that is already the place where the naive weight `(qu)^l` fails, so the corrected coefficient is
checked in the kernel. The step, and with it the whole identity and
`HJO.Sweep.ColumnCommutes`, is `HJO.Sweep.exists_forall_chainComm_eq_smul_chainGeom`.

## Implementation notes

This file applies `HJO.Sym.smul_sum_sum_dopInt_dopInt` rather than adding to it;
`HJO.Mellit.lhsRewrite_sweepWitness` is proved elsewhere (`HJO.Mellit.lhsRewrite_sweepWitness`,
`HJO/Shuffle/ShuffleClosed.lean`). `HJO.Mellit.shuffle_of_lhs_and_induction` has two binders,
`hlhs` and `hind`; nothing here touches either, and `hlhs` is quantified over `1 < a < b`, so the
`(a,1)` column is not an instance of it.

## References

This file concerns `HJO.Sym.DopInt`, `HJO.Sym.smul_sum_sum_dopInt_dopInt`,
`HJO.Sweep.exists_forall_dminus_auxVar_pow_mul_vertexStep_pow_eq_chain`. Transcribing
A. Mellit, *Toric braids and `(m, n)`-parking functions*, §3.
-/

@[expose] public section

namespace HJO.Sweep

variable {L : Type*} [Field L] [Algebra ℚ L] {q u : L}

/-! ### The nest is linear in its argument -/

/-- The nest is additive in its argument, at every depth: a composite of the `D_n`, which are
linear. -/
theorem chain_add (q u : L) (R K : ℕ) (b : ℕ) : ∀ (j : ℕ) (g h : Sym.Lambda L),
    chain q u R K b j (g + h) = chain q u R K b j g + chain q u R K b j h := by
  induction b with
  | zero => intro j g h; rw [chain_zero, chain_zero, chain_zero, map_add]
  | succ c ih =>
      intro j g h
      rw [chain_succ, chain_succ, chain_succ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_add, ih, smul_add]

/-- The nest respects differences in its argument. This is all Leibniz needs. -/
theorem chain_sub (q u : L) (R K : ℕ) (b : ℕ) : ∀ (j : ℕ) (g h : Sym.Lambda L),
    chain q u R K b j (g - h) = chain q u R K b j g - chain q u R K b j h := by
  induction b with
  | zero => intro j g h; rw [chain_zero, chain_zero, chain_zero, map_sub]
  | succ c ih =>
      intro j g h
      rw [chain_succ, chain_succ, chain_succ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_sub, ih, smul_sub]

/-! ### Leibniz -/

/-- The one-letter commutator `[D_n, D_0]`, the only thing Leibniz produces. -/
noncomputable def dopComm (q u : L) (n : ℤ) (g : Sym.Lambda L) : Sym.Lambda L :=
  Sym.DopInt q u n (Sym.DopInt q u 0 g) - Sym.DopInt q u 0 (Sym.DopInt q u n g)

/-- **`[ψ_b, D_0]` in the nest's own terms**: `chain b K j (D_0g) - D_0(chain b K j g)`. At
`(K,j) = (1,0)` this is the right-hand side of the clause of `HJO.Sweep.ColumnCommutes` at `b`
(`HJO.Sweep.columnCommutes_at_iff_chainComm`). -/
noncomputable def chainComm (q u : L) (R K b j : ℕ) (g : Sym.Lambda L) : Sym.Lambda L :=
  chain q u R K b j (Sym.DopInt q u 0 g) - Sym.DopInt q u 0 (chain q u R K b j g)

/-- At depth `0` the nest is one letter, so commuting `D_0` past it is the one-letter
commutator. -/
theorem chainComm_zero_eq (q u : L) (R K j : ℕ) (g : Sym.Lambda L) :
    chainComm q u R K 0 j g = dopComm q u ((K : ℤ) + (j : ℤ)) g := by
  rw [chainComm, chain_zero, chain_zero, dopComm]

/-- **Leibniz for the nest, and it costs nothing.** One application of `D_0` past the outermost
letter of the nest splits into the new letter's commutator, with the rest of the nest wrapped around
it, plus the same problem one level down:

`chainComm (b+1) K j g = ∑_l(qu)^l(chain b K l (dopComm (j-l) g) + chainComm b K l (D_{j-l}g))`.

Unconditional: the only inputs are `HJO.Sweep.chain_sub` and the linearity of `D_0`. Unfolding it
`b+1` times gives one term per position of the word, which is the first half of the informal
argument for `HJO.Sweep.ColumnCommutes`. -/
theorem chainComm_succ (q u : L) (R K b j : ℕ) (g : Sym.Lambda L) :
    chainComm q u R K (b + 1) j g
      = ∑ l ∈ Finset.range (R + 1), ((q * u) ^ l) •
          (chain q u R K b l (dopComm q u ((j : ℤ) - (l : ℤ)) g)
            + chainComm q u R K b l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) := by
  rw [chainComm, chain_succ, chain_succ, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, ← smul_sub]
  refine congrArg (fun x => ((q * u) ^ l) • x) ?_
  rw [dopComm, chainComm, chain_sub]
  abel

/-! ### The pair commutator at `(n, 0)`, in both orientations -/

/-- **The one-letter commutator above `0`:**
`[D_n,D_0]g = M·∑_{i<n}∑_{l ≥ 0}(qu)^lD_{1+i+l}(D_{n-1-i-l}g)`.

`HJO.Sym.smul_sum_sum_dopInt_dopInt` at the pair `(m,n) = (n,0)`. No hypothesis on `q` or `u`, and
no `M ≠ 0`. -/
theorem dopComm_eq_smul_sum_sum (q u : L) (g : Sym.Lambda L) {T : ℕ}
    (hT : (Sym.plethShift q u g).natDegree < T) {n : ℤ} (hn : 0 ≤ n) {R : ℕ} (hR : T ≤ R)
    (hRn : n + (T : ℤ) ≤ (R : ℤ)) :
    dopComm q u n g
      = ((1 - q) * (1 - u)) • ∑ i ∈ Finset.range n.toNat, ∑ l ∈ Finset.range (R + 1),
          ((q * u) ^ l) • Sym.DopInt q u (1 + (i : ℤ) + (l : ℤ))
            (Sym.DopInt q u (n - 1 - (i : ℤ) - (l : ℤ)) g) := by
  have h := Sym.smul_sum_sum_dopInt_dopInt q u g hT n 0 hn (R := R) hR hRn
  rw [show (n - 0).toNat = n.toNat from by rw [sub_zero]] at h
  rw [dopComm, ← h]
  refine congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [show (0 : ℤ) + 1 + (i : ℤ) + (l : ℤ) = 1 + (i : ℤ) + (l : ℤ) from by ring]

/-- **The one-letter commutator below `0`:**
`[D_n,D_0]g = -M·∑_{i<-n}∑_{l ≥ 0}(qu)^lD_{n+1+i+l}(D_{-1-i-l}g)`.

The same `HJO.Sym.smul_sum_sum_dopInt_dopInt`, read at `(m,n) = (0,n)` instead; the sign is the
exchange of the two arguments. This is the whole of the case split the `χ`-telescope makes on the
letter being commuted past. -/
theorem dopComm_eq_neg_smul_sum_sum (q u : L) (g : Sym.Lambda L) {T : ℕ}
    (hT : (Sym.plethShift q u g).natDegree < T) {n : ℤ} (hn : n ≤ 0) {R : ℕ} (hR : T ≤ R) :
    dopComm q u n g
      = -(((1 - q) * (1 - u)) • ∑ i ∈ Finset.range (-n).toNat, ∑ l ∈ Finset.range (R + 1),
          ((q * u) ^ l) • Sym.DopInt q u (n + 1 + (i : ℤ) + (l : ℤ))
            (Sym.DopInt q u (-1 - (i : ℤ) - (l : ℤ)) g)) := by
  have h := Sym.smul_sum_sum_dopInt_dopInt q u g hT 0 n hn (R := R) hR (by
    have : (T : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
    omega)
  rw [show (0 - n).toNat = (-n).toNat from by rw [zero_sub]] at h
  rw [dopComm, ← neg_sub (Sym.DopInt q u 0 (Sym.DopInt q u n g)), ← h]
  refine congrArg Neg.neg (congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [show (0 : ℤ) - 1 - (i : ℤ) - (l : ℤ) = -1 - (i : ℤ) - (l : ℤ) from by ring]

/-! ### Cross-check: the known `b = 0` clause, through the Leibniz packaging -/

/-- **Cross-check that the packaging is oriented correctly**: at `b = 0` it reproduces the known
`b = 0` clause of `HJO.Sweep.ColumnCommutes`,

`chainComm 0 1 0 f = M·chain 1 1 0 f`,

which is `HJO.Sweep.columnCommutes_zero_at` read in the nest. The depth-`0` nest is the single
letter `D_1`, so `HJO.Sweep.chainComm_zero_eq` makes this `dopComm 1 f`, and
`HJO.Sweep.dopComm_eq_smul_sum_sum` at `n = 1` has the single row `i = 0`, which is
`HJO.Sweep.chain_one_apply`. Nothing new is proved --- the point is that the signs and the
orientation of `HJO.Sweep.dopComm` are the ones the commutation asks for, checked in the kernel
rather than by eye. -/
theorem chainComm_zero_eq_smul_chain_one (q u : L) (f : Sym.Lambda L) {T : ℕ}
    (hT : (Sym.plethShift q u f).natDegree < T) {R : ℕ} (hR : T + 1 ≤ R) :
    chainComm q u R 1 0 0 f = ((1 - q) * (1 - u)) • chain q u R 1 1 0 f := by
  rw [chainComm_zero_eq, Nat.cast_one, Nat.cast_zero, add_zero,
    dopComm_eq_smul_sum_sum q u f hT (n := 1) (by norm_num) (R := R) (by omega) (by
      have : (T : ℤ) + 1 ≤ (R : ℤ) := by exact_mod_cast hR
      omega),
    chain_one_apply]
  refine congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_
  rw [show (1 : ℤ).toNat = 1 from rfl, Finset.sum_range_one]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Nat.cast_zero, show (1 : ℤ) - 1 - 0 - (l : ℤ) = -(l : ℤ) from by ring,
    show (1 : ℤ) + 0 + (l : ℤ) = 1 + (l : ℤ) from by ring]

/-! ### What is left of the commutation -/

/-- **Exactly what the `(a,1)` column at a general `b` still costs**, with Leibniz already paid:
the clause of `HJO.Sweep.ColumnCommutes` at `b` is

`M·chain (b+1) 1 0 f = chainComm b 1 0 f`,

and `chainComm` is the recursion `HJO.Sweep.chainComm_zero_eq` / `HJO.Sweep.chainComm_succ` whose
every letter-commutator is `M` times an explicit pair of `D`'s
(`HJO.Sweep.dopComm_eq_smul_sum_sum`, `HJO.Sweep.dopComm_eq_neg_smul_sum_sum`).

**This is an equivalence**, exactly as
`HJO.Sweep.columnCommutes_at_iff_chain` is: what it buys is that the statement now
mentions no operator of the sweep module and no commutator, only the nest and the insertions. The
`χ`-telescope that would close it is not proved; the statement is proved instead by an induction on
`b` in `HJO/Shuffle/MellitColumnChainTelescope.lean`. -/
theorem columnCommutes_at_iff_chainComm (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hq1 : q ≠ 1) (b : ℕ)
    (f : Sym.Lambda L) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ((((1 - q) * (1 - u)) • psiCol q u (b + 1) f
          = psiCol q u b (Sym.Dop q u 0 f)
            - dminus q 1 (dplusStar q u 0 (psiCol q u b f)))
        ↔ ((1 - q) * (1 - u)) • chain q u R 1 (b + 1) 0 f = chainComm q u R 1 b 0 f) := by
  obtain ⟨R₀, hR₀⟩ := columnCommutes_at_iff_chain (q := q) (u := u) hq0 hu0 hq1 b f
  refine ⟨R₀, fun R hR => ?_⟩
  rw [hR₀ R hR, chainComm, show Sym.DopInt q u 0 = Sym.Dop q u 0 from by
    rw [← Sym.dopInt_natCast q u 0, Nat.cast_zero]]

/-! ### The generalisation of the commutation that an induction on `b` can carry -/

/-- **The coefficient of the generalised commutation**: the geometric run of `min(j,l) + 1`
consecutive powers of `qu` with top power `(qu)^l`,

`c(l,j) = (qu)^{l-min(j,l)} + ⋯ + (qu)^l`.

At `j = 0` it is the single power `(qu)^l` (`HJO.Sweep.chainGeomCoeff_zero`), which is the weight
the nest itself carries. The `min` is what the naive generalisation of the commutation to a general
starting index is missing. -/
noncomputable def chainGeomCoeff (q u : L) (j l : ℕ) : L :=
  ∑ r ∈ Finset.range (min j l + 1), (q * u) ^ (l - min j l + r)

omit [Algebra ℚ L] in
theorem chainGeomCoeff_zero (q u : L) (l : ℕ) : chainGeomCoeff q u 0 l = (q * u) ^ l := by
  rw [chainGeomCoeff, Nat.zero_min, Nat.add_zero, Finset.sum_range_one, Nat.sub_zero,
    Nat.add_zero]

/-- **The nest of depth `b+1` with the generalised weight**,
`∑_l c(l,j)·chain b 1 l (D_{j-l}g)`. -/
noncomputable def chainGeom (q u : L) (R b j : ℕ) (g : Sym.Lambda L) : Sym.Lambda L :=
  ∑ l ∈ Finset.range (R + 1),
    chainGeomCoeff q u j l • chain q u R 1 b l (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)

/-- **At `j = 0` the generalised nest is the nest**: `chainGeom b 0 = chain (b+1) 1 0`, because
`c(l,0) = (qu)^l`. So `chainComm b 1 0 f = M·chainGeom b 0 f` is exactly the clause of
`HJO.Sweep.ColumnCommutes` at `b` (`HJO.Sweep.columnCommutes_at_iff_chainComm`), and
`HJO.Sweep.chainGeom` is a genuine generalisation of the thing to be proved rather than a
restatement of it at other indices. -/
theorem chainGeom_zero_eq_chain (q u : L) (R b : ℕ) (g : Sym.Lambda L) :
    chainGeom q u R b 0 g = chain q u R 1 (b + 1) 0 g := by
  rw [chainGeom, chain_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [chainGeomCoeff_zero]

omit [Algebra ℚ L] in
/-- The geometric run written over the flanking index rather than over its length:
`c(l,j) = ∑_{i ≤ min(j,l)}(qu)^{l-i}`. This is the shape the regrouping produces. -/
theorem chainGeomCoeff_eq_sum (q u : L) (j l : ℕ) :
    chainGeomCoeff q u j l = ∑ i ∈ Finset.range (min j l + 1), (q * u) ^ (l - i) := by
  rw [chainGeomCoeff, ← Finset.sum_range_reflect (fun i => (q * u) ^ (l - i)) (min j l + 1)]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hr
  have h1 : min j l ≤ l := min_le_right j l
  congr 1
  omega

omit [Algebra ℚ L] in
/-- **The regrouping the base of the corrected induction runs on.** A geometric double sum
`∑_{i ≤ J}∑_{c ≤ R}(qu)^c·F(i+c)`, collected by the total index `l = i+c`, is
`∑_{l ≤ R}(∑_{i ≤ min(J,l)}(qu)^{l-i})·F(l)` --- the inner factor being exactly
`HJO.Sweep.chainGeomCoeff` by `HJO.Sweep.chainGeomCoeff_eq_sum`.

The hypothesis is that `F` has already died above `R`, which is what lets the reindexed range
`[i, i+R]` be cut back to `[0,R]`; on the nest it holds because `D_n` kills a fixed argument once
`n` is far enough below zero (`HJO.Sym.dopInt_eq_zero_of_lt`). -/
theorem sum_range_sum_range_smul_eq_sum_range (t : L) (J R : ℕ) (F : ℕ → Sym.Lambda L)
    (hF : ∀ l : ℕ, R < l → F l = 0) :
    ∑ i ∈ Finset.range (J + 1), ∑ c ∈ Finset.range (R + 1), (t ^ c) • F (i + c)
      = ∑ l ∈ Finset.range (R + 1),
          (∑ i ∈ Finset.range (min J l + 1), t ^ (l - i)) • F l := by
  classical
  have key : ∀ i : ℕ, ∑ c ∈ Finset.range (R + 1), (t ^ c) • F (i + c)
      = ∑ l ∈ Finset.range (R + 1), (if i ≤ l then t ^ (l - i) else 0) • F l := by
    intro i
    have hIco : ∑ l ∈ Finset.Ico i (i + (R + 1)), (t ^ (l - i)) • F l
        = ∑ c ∈ Finset.range (R + 1), (t ^ c) • F (i + c) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      exact Finset.sum_congr rfl fun c _ => by rw [Nat.add_sub_cancel_left]
    have hcut : ∑ l ∈ Finset.Ico i (i + (R + 1)), (t ^ (l - i)) • F l
        = ∑ l ∈ Finset.Ico i (R + 1), (t ^ (l - i)) • F l := by
      refine (Finset.sum_subset (fun l hl => ?_) (fun l hl hnl => ?_)).symm
      · rw [Finset.mem_Ico] at hl ⊢
        omega
      · rw [Finset.mem_Ico] at hl hnl
        rw [hF l (by omega), smul_zero]
    have hfilter : (Finset.range (R + 1)).filter (fun l => i ≤ l) = Finset.Ico i (R + 1) := by
      refine Finset.ext fun l => ?_
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← hIco, hcut, ← hfilter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · rw [zero_smul]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  refine congrArg (fun c : L => c • F l) ?_
  have hfil : (Finset.range (J + 1)).filter (fun i => i ≤ l)
      = Finset.range (min J l + 1) := by
    refine Finset.ext fun i => ?_
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, Nat.lt_succ_iff, Nat.lt_succ_iff,
      le_min_iff]
  rw [← hfil, Finset.sum_filter]

/-- **The base of the corrected induction, proved:**

`chainComm 0 1 j g = M·chainGeom 0 j g`   at every `j ≥ 0`.

At depth `0` the nest is the single letter `D_{1+j}`, so the left side is the pair commutator
`[D_{1+j},D_0]` (`HJO.Sweep.chainComm_zero_eq`), which
`HJO.Sweep.dopComm_eq_smul_sum_sum` expands as `M` times a geometric double sum over `(i,c)`;
collecting that by `l = i+c` (`HJO.Sweep.sum_range_sum_range_smul_eq_sum_range`) produces exactly
the weight `HJO.Sweep.chainGeomCoeff`.

**This is where the `min` earns its place.** At `j = 0` the weight is the single power `(qu)^l` and
the statement is the settled `b = 0` clause (`HJO.Sweep.chainGeom_zero_eq_chain`); at `j ≥ 1` it is
the run `(qu)^{l-min(j,l)} + ⋯ + (qu)^l`, and the clause read naively at a general starting
index --- the weight `(qu)^l` for every `j` --- is already false here. No hypothesis on `q` or `u`,
and no `M ≠ 0`. -/
theorem chainComm_zero_eq_smul_chainGeom (q u : L) (g : Sym.Lambda L) {T : ℕ}
    (hT : (Sym.plethShift q u g).natDegree < T) (j : ℕ) {R : ℕ} (hR : j + T + 1 ≤ R) :
    chainComm q u R 1 0 j g = ((1 - q) * (1 - u)) • chainGeom q u R 0 j g := by
  have hvan : ∀ l : ℕ, R < l →
      (fun l : ℕ => Sym.DopInt q u (1 + (l : ℤ))
        (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) l = 0 := by
    intro l hl
    have hz : Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g = 0 :=
      Sym.dopInt_eq_zero_of_lt q u g (by omega)
    change Sym.DopInt q u (1 + (l : ℤ)) (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g) = 0
    rw [hz, map_zero]
  have hstep := dopComm_eq_smul_sum_sum q u g hT (n := 1 + (j : ℤ)) (by omega) (R := R)
    (by omega) (by omega)
  rw [chainComm_zero_eq, Nat.cast_one, hstep, chainGeom]
  refine congrArg (fun x => ((1 - q) * (1 - u)) • x) ?_
  have hL : ∑ i ∈ Finset.range (1 + (j : ℤ)).toNat, ∑ l ∈ Finset.range (R + 1),
        ((q * u) ^ l) • Sym.DopInt q u (1 + (i : ℤ) + (l : ℤ))
          (Sym.DopInt q u (1 + (j : ℤ) - 1 - (i : ℤ) - (l : ℤ)) g)
      = ∑ i ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (R + 1), ((q * u) ^ c) •
          Sym.DopInt q u (1 + ((i + c : ℕ) : ℤ))
            (Sym.DopInt q u ((j : ℤ) - ((i + c : ℕ) : ℤ)) g) := by
    rw [show (1 + (j : ℤ)).toNat = j + 1 from by omega]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show 1 + (i : ℤ) + (c : ℤ) = 1 + ((i + c : ℕ) : ℤ) from by push_cast; ring,
      show 1 + (j : ℤ) - 1 - (i : ℤ) - (c : ℤ) = (j : ℤ) - ((i + c : ℕ) : ℤ) from by
        push_cast; ring]
  rw [hL, sum_range_sum_range_smul_eq_sum_range (q * u) j R
    (fun l => Sym.DopInt q u (1 + (l : ℤ)) (Sym.DopInt q u ((j : ℤ) - (l : ℤ)) g)) hvan]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← chainGeomCoeff_eq_sum, chain_zero, Nat.cast_one]

/-! ### The scalar core of the `χ`-telescope -/

section Chi

/-- The indicator `χ_i = [m_i ≥ s]` of the `χ`-telescope, at the threshold `s = T - e`. -/
def chi (m : ℕ → ℤ) (s : ℤ) (i : ℕ) : ℤ := if s ≤ m i then 1 else 0

/-- **The telescope.** `∑_{p ≤ b}χ_{p+1}(χ_p - χ_{p+2}) = χ_0χ_1 - χ_{b+1}χ_{b+2}`: the summand is
`a_p - a_{p+1}` at `a_p = χ_pχ_{p+1}`. This is the cancellation the standard argument for
`HJO.Sweep.ColumnCommutes` runs on, and it is only the scalar identity --- the reindexing that turns
the insertions of `HJO.Sweep.chainComm_succ` into these coefficients is not formalised. -/
theorem sum_chi_mul_sub_chi (m : ℕ → ℤ) (s : ℤ) (b : ℕ) :
    ∑ p ∈ Finset.range (b + 1), chi m s (p + 1) * (chi m s p - chi m s (p + 2))
      = chi m s 0 * chi m s 1 - chi m s (b + 1) * chi m s (b + 2) := by
  have hterm : ∀ p ∈ Finset.range (b + 1),
      chi m s (p + 1) * (chi m s p - chi m s (p + 2))
        = chi m s p * chi m s (p + 1) - chi m s (p + 1) * chi m s (p + 1 + 1) := by
    intro p _
    rw [show p + 1 + 1 = p + 2 from rfl]
    ring
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_range_sub' (fun p => chi m s p * chi m s (p + 1)) (b + 1)]

/-- **The boundary of the telescope is the indicator of `e = T`.** With `m_0 = 0`, `m_{b+2} = -1`
and the two flanking entries `m_1, m_{b+1}` non-negative --- which is what an admissible word of
`ψ_{b+1}` has --- the surviving term `χ_0χ_1 - χ_{b+1}χ_{b+2}` is `1` at the threshold `s = 0`, that
is at `e = T`, and `0` at every other threshold. That is the coefficient `M·ψ_{b+1}` carries. -/
theorem chi_boundary_eq_ite (m : ℕ → ℤ) (s : ℤ) (b : ℕ) (h0 : m 0 = 0) (hlast : m (b + 2) = -1)
    (h1 : 0 ≤ m 1) (hb : 0 ≤ m (b + 1)) :
    chi m s 0 * chi m s 1 - chi m s (b + 1) * chi m s (b + 2) = if s = 0 then 1 else 0 := by
  rw [chi, chi, chi, chi, h0, hlast]
  split_ifs <;> omega

/-- **A position whose letter is a local minimum contributes nothing.** If `m_{p+1}` is at most both
its neighbours then `χ_{p+1} = 1` forces `χ_p = χ_{p+2} = 1`, so the term of the telescope at `p`
vanishes. This is why a tuple with a negative entry `m_i` --- for which only the position `p = i-1`
is admissible at all, every other entry being non-negative --- contributes nothing to the identity:
the sole admissible term is exactly this one.

**On such a tuple it is this lemma and not `HJO.Sweep.sum_chi_mul_sub_chi` that applies.** The
boundary `χ_0χ_1 - χ_{b+1}χ_{b+2}` of the full telescope is generally *not* zero when some entry is
negative --- at `b = 1` and `(m_1,m_2) = (-2,2)` it is `-1` at the threshold `s = -1` --- and the
term carrying that value sits at the inadmissible position. The telescope over all positions is
available only where every entry is non-negative, which is where
`HJO.Sweep.chi_boundary_eq_ite` then evaluates it. -/
theorem chi_mul_sub_chi_eq_zero (m : ℕ → ℤ) (s : ℤ) (p : ℕ) (hlo : m (p + 1) ≤ m p)
    (hhi : m (p + 1) ≤ m (p + 2)) :
    chi m s (p + 1) * (chi m s p - chi m s (p + 2)) = 0 := by
  rw [chi, chi, chi]
  split_ifs <;> omega

end Chi

end HJO.Sweep

end
