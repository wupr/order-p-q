import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

-- Bumping to Mathlib@v4.11.0:
--   Due to the new `AddSubgroup.torsionBy` in Mathlib (PR-ed by Peiran for a separate project),
--   we need to temporarily rename `Subgroup.torsionBy'` to `Subgroup.torsionBy` etc.

variable {α : Type*} [CommGroup α]

variable (α) in
@[to_additive (attr := simps)]
def Subgroup.torsionBy' (d : ℕ) : Subgroup α where
  carrier := {a | a ^ d = 1}
  mul_mem' {x y} hx hy := by
    rw [Set.mem_setOf_eq, mul_pow, hx, hy, mul_one]
  one_mem' := by
    rw [Set.mem_setOf_eq, one_pow]
  inv_mem' {x} hx := by
    rw [Set.mem_setOf_eq] at hx ⊢
    rwa [inv_pow, inv_eq_one]

@[to_additive (attr := simp)]
lemma Subgroup.mem_torsionBy' (d : ℕ) (a : α) :
    a ∈ Subgroup.torsionBy' α d ↔ a ^ d = 1 := Iff.rfl
