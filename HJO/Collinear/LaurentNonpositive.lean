/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public meta import HJO.Attr

/-! # The nonpositive part of a Laurent ring

`HJO.Laurent.nonpositive`: in `R[z_1^{±1}, …, z_n^{±1}]` the elements every monomial of which has
nonpositive exponent in each variable form an `R`-subalgebra.

The Laurent ring is `AddMonoidAlgebra R (Fin n →₀ ℤ)`, which is how this library spells it
throughout -- `HJO.Sym.LaurentLambda K k` is that at `R = Λ` -- so the statement here is at an
arbitrary commutative ring and instantiates at the one the collinear chain uses with nothing to
transport. The `n ≥ 1` is absent: the argument never uses it, and at `n = 0` the claim
is the trivially true statement about the one exponent vector there is.

The whole content is the support calculus, and each of the four closure conditions is one fact
about supports:

* `1` and every `algebraMap R _ r` are supported on the single vector `0`, which is nonpositive.
* `Finsupp.support_add` puts `support (f + g)` inside the union, so a bound holding on each holds on
  the sum.
* `AddMonoidAlgebra.support_coeff_mul_subset` puts `support (f * g)` inside the pointwise SUM
  `support f + support g`, and a sum of two nonpositive integers is nonpositive. This is the only
  clause where the monoid structure of the exponents does any work, and it is why the set is a
  subalgebra and not merely a submodule.

No genericity, no field, and no parameters: `q` and `u` do not occur.
-/

@[expose] public section

namespace HJO.Laurent

open Finsupp

variable (R : Type*) [CommRing R] (n : ℕ)

/-- **The nonpositive part of a Laurent ring is a subalgebra.** The
elements of `R[z_1^{±1}, …, z_n^{±1}]` every monomial of which has nonpositive exponent in each
variable, as an `R`-subalgebra.

Membership is `∀ g ∈ f.coeff.support, ∀ i, g i ≤ 0` -- a condition on the exponent vectors carrying
a nonzero coefficient, which is exactly the `supp(F) ⊆ (-ℕ)^n`. -/
@[hjo "lem_laurent_nonpositive"]
def nonpositive : Subalgebra R (AddMonoidAlgebra R (Fin n →₀ ℤ)) where
  carrier := {f | ∀ g ∈ f.coeff.support, ∀ i, g i ≤ 0}
  mul_mem' := by
    classical
    intro f g hf hg c hc i
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hc)
    exact add_nonpos (hf a ha i) (hg b hb i)
  add_mem' := by
    intro f g hf hg c hc i
    rcases Finset.mem_union.mp (Finsupp.support_add (by simpa using hc)) with h | h
    · exact hf c h i
    · exact hg c h i
  algebraMap_mem' := by
    intro r c hc i
    have hcoeff : (algebraMap R (AddMonoidAlgebra R (Fin n →₀ ℤ)) r).coeff
        = Finsupp.single 0 r := rfl
    rw [hcoeff] at hc
    have : c = 0 := by simpa using Finsupp.support_single_subset hc
    simp [this]

variable {R n}

@[simp]
theorem mem_nonpositive {f : AddMonoidAlgebra R (Fin n →₀ ℤ)} :
    f ∈ nonpositive R n ↔ ∀ g ∈ f.coeff.support, ∀ i, g i ≤ 0 := Iff.rfl

end HJO.Laurent
