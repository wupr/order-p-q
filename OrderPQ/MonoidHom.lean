import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic

namespace MonoidHom

@[to_additive]
lemma ker_eq_top_iff {G : Type*} [Group G] {M : Type*} [MulOneClass M] (f : G →* M) :
    MonoidHom.ker f = ⊤ ↔ f = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ker_one⟩
  ext x
  rw [one_apply, ← MonoidHom.mem_ker]
  exact h ▸ Subgroup.mem_top x

end MonoidHom

variable {α β : Type*} [Group α] [Group β]

@[to_additive]
theorem zpow_eq_self_iff_modEq {x : α} {n : ℤ} : x ^ n = x ↔ n ≡ 1 [ZMOD orderOf x] := by
  nth_rw 2 [zpow_one x |>.symm]
  exact zpow_eq_zpow_iff_modEq ..

/-- There exists a group homomorphism `α →* β` that sends any generator `x` of `α` to
  any element `y` of `β`, provided the order of `y` divides the order of `α`. -/
@[to_additive "There exists an additive group homomorphism `α →+ β` that sends any generator `x`
  of `α` to any element `y` of `β`, provided the order of `y` divides the order of `α`."]
lemma MonoidHom.exists_unique_apply_generator_eq
    {x : α} (hx : ∀ a : α, a ∈ Subgroup.zpowers x) {y : β} (hy : orderOf y ∣ Nat.card α) :
    ∃! f : α →* β, f x = y := by
  have {m n : ℤ} (h : m ≡ n [ZMOD orderOf x]) :=
    Int.ModEq.of_dvd (Int.ofNat_dvd.mpr hy) (orderOf_eq_card_of_forall_mem_zpowers hx ▸ h)
  let f : α →* β := {
    toFun a := y ^ (hx a).choose
    map_one' := by
      have h := (hx 1).choose_spec
      simp_rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_card_of_forall_mem_zpowers hx] at h ⊢
      exact Int.dvd_trans (Int.ofNat_dvd.mpr hy) h
    map_mul' a1 a2 := by
      have h := (hx (a1 * a2)).choose_spec
      nth_rewrite 3 [← (hx a1).choose_spec, ← (hx a2).choose_spec] at h
      rw [← zpow_add, zpow_eq_zpow_iff_modEq] at h ⊢
      exact this h
  }
  have hf : f x = y
  · rw [coe_mk, OneHom.coe_mk]
    have h := (hx x).choose_spec
    rw [zpow_eq_self_iff_modEq] at h ⊢
    exact this h
  exact ⟨f, hf, fun f' hf' => MonoidHom.eq_iff_eq_on_generator hx f' f |>.mpr (hf ▸ hf')⟩
