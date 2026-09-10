[![](logo.svg)](https://axiommath.ai/)

# Rogers-Ramanujan Identities from the Geometry of X^a=Y^b

This is a Lean formalization of the Huang–Jiang–Oblomkov conjecture on the point counts of pairs of commuting nilpotent matrices satisfying `A^a = B^b`.

## Main Results

* The finite identity: for coprime `1 < a < b` and every `N`, the HJO polynomial is `(q)_N` times the generating function of the balanced cylindric partitions with largest entry at most `N`, assuming seven results quoted from the literature.
* The Huang–Jiang–Oblomkov conjecture for every coprime `1 < a < b`, assuming those seven results together with the Foda–Welsh cylindric product formula.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and Axiom Math's repository [QSeriesLib](https://github.com/AxiomMath/QSeriesLib).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on the dependencies above. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
