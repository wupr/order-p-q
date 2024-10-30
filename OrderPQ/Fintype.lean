import Mathlib.Data.Finite.Basic
import Mathlib.Data.Fintype.Perm

@[to_additive]
lemma MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] : Function.Injective (toEquiv : (α ≃* β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[to_additive]
instance MulEquiv.finite_left {α β : Type*} [Mul α] [Mul β] [Finite α] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

@[to_additive]
instance MulEquiv.finite_right {α β : Type*} [Mul α] [Mul β] [Finite β] : Finite (α ≃* β) :=
  Finite.of_injective toEquiv toEquiv_injective

@[to_additive]
instance MulEquiv.fintype
    {α β : Type*} [Mul α] [Mul β] [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    Fintype (α ≃* β) where
  elems := equivFintype.elems.filterMap
    (fun e => if h : ∀ a b : α, e (a * b) = e a * e b then (⟨e, h⟩ : α ≃* β) else none)
    (fun _ _ _ ha ha' => by
      simp only [Option.mem_def, dite_some_none_eq_some] at ha ha'
      rw [← mk.injEq]
      exact ha'.2.symm ▸ ha.2
    )
  complete me := (Finset.mem_filterMap ..).mpr ⟨me.toEquiv, Finset.mem_univ _, by {simp; rfl}⟩


open Function

namespace Fintype

@[to_additive]
instance decidableEqMulEquivFintype {α β : Type*} [DecidableEq β] [Fintype α] [Mul α] [Mul β] :
    DecidableEq (α ≃* β) :=
  fun a b => decidable_of_iff ((a : α → β) = b) (Injective.eq_iff DFunLike.coe_injective)

end Fintype
