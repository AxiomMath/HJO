/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import HJO.Collinear.WordMap
public meta import HJO.Attr

/-! # Raising every index divides the symbol by the product of the variables
-/

@[expose] public section

namespace HJO.Sym

/-- Raising every index divides the symbol by the product of the variables. -/
@[hjo "lem_bglx_raise_symbol"]
theorem prod_single_mul_dopWordSymbol_dopWordRaise {K : Type*} [CommSemiring K] {k : ℕ}
    (c : (Fin k → ℕ) →₀ K) :
    (∏ i : Fin k, AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : K)) *
        dopWordSymbol K k (dopWordRaise K k c) = dopWordSymbol K k c := by
  have hprod : (∏ i : Fin k, AddMonoidAlgebra.single (Finsupp.single i (1 : ℤ)) (1 : K))
      = AddMonoidAlgebra.single (∑ i : Fin k, Finsupp.single i (1 : ℤ)) (1 : K) := by
    simp
  rw [hprod, dopWordRaise, Finsupp.lmapDomain_apply, dopWordSymbol,
    Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm]
  congr 1
  rw [Function.comp_apply, AddMonoidAlgebra.single_mul_single, one_mul]
  congr 1
  ext i
  simp

end HJO.Sym
