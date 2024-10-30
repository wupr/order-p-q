import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

lemma Set.nat_card_range_of_injective {f : α → β} (hf : Function.Injective f) :
    Nat.card (range f) = Nat.card α :=
  Eq.symm <| Nat.card_congr <| Equiv.ofInjective f hf

namespace MonoidHom

@[to_additive]
lemma nat_card_range_of_injective
    {α β : Type*} [Group α] [Group β]
    {f : α →* β} (hf : Function.Injective f) :
    Nat.card (range f) = Nat.card α := by
  convert Set.nat_card_range_of_injective hf using 1

@[to_additive]
lemma ker_eq_top_iff {G : Type*} [Group G] {M : Type*} [MulOneClass M] (f : G →* M) :
    MonoidHom.ker f = ⊤ ↔ f = 1 := by
  constructor
  · intro h
    ext x
    rw [one_apply, ← MonoidHom.mem_ker]
    exact h ▸ Subgroup.mem_top x
  · exact fun h => h ▸ ker_one

end MonoidHom

section OfGenerator

variable {α β : Type*} [Group α] [Group β]

section Lemmas

@[to_additive]
theorem zpow_eq_self_iff_modEq {x : α} {n : ℤ} : x ^ n = x ↔ n ≡ 1 [ZMOD orderOf x] := by
  convert zpow_eq_zpow_iff_modEq .. using 2
  exact zpow_one x |>.symm

-- Also do `Nat` version
lemma Int.modEq_of_modEq_dvd {n m a b : ℤ} (h : m ∣ n) : a ≡ b [ZMOD n] → a ≡ b [ZMOD m] :=
  Int.modEq_iff_dvd.mpr ∘ Int.dvd_trans h ∘ Int.modEq_iff_dvd.mp

@[to_additive]
-- There are some `*.card_top`s in Mathlib.
lemma Subgroup.nat_card_top : Nat.card (⊤ : Subgroup α) = Nat.card α :=
  Nat.card_congr (Equiv.Set.univ α)

end Lemmas

variable {x : α} (hx : ∀ a : α, a ∈ Subgroup.zpowers x)
include hx

@[to_additive]
lemma MonoidHom.eq_of_apply_eq (f₁ f₂ : α →* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ := by
  ext y
  rw [← (hx y).choose_spec, map_zpow, map_zpow, h2]

@[to_additive]
lemma MulEquiv.eq_of_apply_eq (f₁ f₂ : α ≃* β) (h2 : f₁ x = f₂ x) : f₁ = f₂ :=
  MulEquiv.toMonoidHom_injective <| MonoidHom.eq_of_apply_eq hx _ _ h2

@[to_additive]
private lemma orderOf_eq_nat_card : orderOf x = Nat.card α :=
  Nat.card_zpowers x ▸ (Subgroup.eq_top_iff' _).mpr hx ▸ Subgroup.nat_card_top

variable {y : β} (hy : orderOf y ∣ Nat.card α)
include hy

@[to_additive AddMonoidHom.ofGeneratorAndImage]
private noncomputable def MonoidHom.ofGeneratorAndImage : α →* β where
  toFun a := y ^ (hx a).choose
  map_one' := by
    have hx' := (hx 1).choose_spec
    simp only [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_nat_card hx] at hx' ⊢
    exact Int.dvd_trans (Int.ofNat_dvd.mpr hy) hx'
  map_mul' a1 a2 := by
    have h := (hx (a1 * a2)).choose_spec
    nth_rewrite 3 [← (hx a1).choose_spec, ← (hx a2).choose_spec] at h
    rw [← zpow_add, zpow_eq_zpow_iff_modEq] at h ⊢
    exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)

@[to_additive]
lemma MonoidHom.exists_of_generator_and_image : ∃ f : α →* β, f x = y := by
  use MonoidHom.ofGeneratorAndImage hx hy
  change y ^ (hx x).choose = y
  have h := (hx x).choose_spec
  rw [zpow_eq_self_iff_modEq] at h ⊢
  exact Int.modEq_of_modEq_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_nat_card hx ▸ h)

end OfGenerator
