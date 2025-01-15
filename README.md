# OrderPQ

This is an open-source project that formalises in the Lean theorem prover the classification of the groups of order `p * q` where `p` and `q` are prime numbers, using [mathlib](https://github.com/leanprover-community/mathlib4).
The main theorems are in [Main.lean](OrderPQ/Main.lean).

Also formalised as part of the project are some key properties of semidirect products of groups and a number of other group-theoretic results.

The authors are

- [Scott Harper](https://harper-scott.github.io) (scott.harper@st-andrews.ac.uk) and
- [Peiran Wu](https://github.com/wupr) (pw72@st-andrews.ac.uk).

## Upstream PRs

The following pull requests (PRs) to [mathlib](https://github.com/leanprover-community/mathlib4) and its dependencies were necessitated or inspired by this project.
Further PRs will be made in due course.

- leanprover/lean4#4037: Added `dite_some_none_eq_none` and `dite_some_none_eq_some` to the module `Init.ByCases`.
- leanprover-community/mathlib4#14097: Added `toAdd_eq_zero` and `toMul_eq_one` to the module `Mathlib.Algebra.Group.TypeTags`.
- leanprover-community/mathlib4#14104 and leanprover-community/mathlib4#14154: Added `Prod.orderOf_mk` to the module `Mathlib.GroupTheory.OrderOfElement`.
- leanprover-community/mathlib4#14365: Added lemmas on sufficient conditions for two `Set`s or `Subgroup`s to be equal.
- leanprover-community/mathlib4#17057: Added instances of `Finite`, `Fintype`, `DecidableEq` for `MulEquiv`.

## License

The source code of this project is distributed under the terms of the Apache License 2.0.
See [LICENSE](LICENSE) for more details.
