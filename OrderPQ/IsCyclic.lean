import Mathlib.GroupTheory.SpecificGroups.Cyclic
import «OrderPQ».MonoidHom
import «OrderPQ».TorsionBy

namespace IsCyclic

section MulEquiv

variable {α β : Type*} [Group α] [Group β]

variable {x : α} (hx : ∀ a : α, a ∈ Subgroup.zpowers x)
variable {y : β} (hy : ∀ b : β, b ∈ Subgroup.zpowers y)
variable (h : Nat.card α = Nat.card β)

include hx in
@[to_additive]
private lemma monoidHom_comp_generator_generator
    {f : α →* β} (hf : f x  = y) {g : β →* α} (hg : g y = x) :
    MonoidHom.comp g f = MonoidHom.id α := by
  refine MonoidHom.eq_of_apply_eq hx _ _ (by simp [hf, hg])

include hx hy h in
@[to_additive]
lemma exists_mulEquiv_of_generators_and_card_eq : ∃ (f : α ≃* β), f x = y := by
  obtain ⟨f, hf⟩ := MonoidHom.exists_of_generator_and_image hx (h.symm ▸ orderOf_dvd_natCard y)
  obtain ⟨g, hg⟩ := MonoidHom.exists_of_generator_and_image hy (h ▸ orderOf_dvd_natCard x)
  use MonoidHom.toMulEquiv f g
    (monoidHom_comp_generator_generator hx hf hg) (monoidHom_comp_generator_generator hy hg hf)
  simp only [MonoidHom.toMulEquiv_apply, hf]

end MulEquiv

section Subgroup

variable {α : Type*} [Group α] [IsCyclic α]

@[to_additive]
lemma card_orderOf_dvd_eq [Fintype α] {d : ℕ} (hd : d ∣ Fintype.card α) :
    (Finset.univ.filter fun (a : α) => orderOf a ∣ d).card = d := by
  -- Just use `card_orderOf_eq_totient_aux₁` (private theorem in Mathlib)
  have (a : α) (ha : a ∈ Finset.univ.filter fun (a : α) => orderOf a ∣ d) : orderOf a ∈ d.divisors
  · refine Nat.mem_divisors.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mp ha |>.2
    · exact ne_zero_of_dvd_ne_zero Fintype.card_ne_zero hd
  rw [Finset.card_eq_sum_card_fiberwise this]
  convert Nat.sum_totient d using 1
  refine Finset.sum_congr rfl fun x hx => ?_
  replace hx := Nat.mem_divisors.mp hx |>.1
  rw [Finset.filter_filter]
  convert card_orderOf_eq_totient (Nat.dvd_trans hx hd) using 4
  exact and_iff_right_iff_imp.mpr fun h => h ▸ hx

-- lemma card_orderOf_dvd_eq' [Fintype α] {d : ℕ}:
--     (Finset.univ.filter fun (a : α) => orderOf a ∣ d).card = Nat.gcd n d := by
--   sorry

@[to_additive]
local instance : CommGroup α := IsCyclic.commGroup

@[to_additive]
lemma card_torsionBy' [Finite α] {d : ℕ} (hd : d ∣ Nat.card α) :
    Nat.card (Subgroup.torsionBy' α d) = d := by
  have: Fintype α := Fintype.ofFinite _
  have : (Subgroup.torsionBy' α d : Set α) = Finset.univ.filter (α := α) (fun a ↦ orderOf a ∣ d)
  · simp [orderOf_dvd_iff_pow_eq_one]
  simp_rw [← SetLike.coe_sort_coe, this]
  simp only [Nat.card_eq_fintype_card] at hd ⊢
  exact Finset.equivFin.proof_1 _ ▸ card_orderOf_dvd_eq hd

@[to_additive]
lemma subgroup_eq [Finite α] (s : Subgroup α) [Finite s] :
    s = Subgroup.torsionBy' α (Nat.card s) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (Nat.le_of_eq ?_)
  · exact fun a ha => orderOf_dvd_iff_pow_eq_one.mp <|
      Subgroup.orderOf_mk a ha ▸ orderOf_dvd_natCard ..
  · refine card_torsionBy' ?_
    exact Subgroup.card_subgroup_dvd_card s

@[to_additive]
lemma subgroup_eq_of_card_eq [Finite α] (s t : Subgroup α) [Finite s] [Finite t]
    (h : Nat.card s = Nat.card t) :
    s = t :=
  (subgroup_eq s).trans <| h ▸ (subgroup_eq t).symm

end Subgroup

section CoprimeOrders

variable {G : Type*} [Group G] [Finite G]

lemma isCyclic_prod_iff_coprime_card
    {G1 G2 : Type} [Group G1] [Finite G1] [Group G2] [Finite G2]
    [IsCyclic G1] [IsCyclic G2]:
    Nat.Coprime (Nat.card G1) (Nat.card G2) ↔ IsCyclic (G1 × G2) := by
  rw [isCyclic_iff_exists_orderOf_eq_natCard, Nat.card_prod, Prod.exists,
    Nat.coprime_iff_gcd_eq_one]
  refine ⟨fun h => ?_, fun ⟨a, b, h⟩ => ?_⟩
  · rw [← Nat.gcd_mul_lcm, h, one_mul]
    obtain ⟨x1, h1⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G1)
    obtain ⟨x2, h2⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G2)
    use x1, x2, h1 ▸ h2 ▸ Prod.orderOf_mk
  · have ha := orderOf_dvd_natCard a
    have hb := orderOf_dvd_natCard b
    have : (Nat.card G1 / orderOf a) * (Nat.card G2 / orderOf b) * Nat.gcd (orderOf a) (orderOf b)
      = 1
    · rw [Prod.orderOf_mk, Nat.lcm, ← Nat.mul_div_cancel' ha, ← Nat.mul_div_cancel' hb] at h
      replace h := Nat.eq_mul_of_div_eq_left
        (Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_right ..)) h
      rw [← Nat.mul_right_inj <| Nat.pos_iff_ne_zero.mp (orderOf_pos b),
        ← Nat.mul_right_inj <| Nat.pos_iff_ne_zero.mp (orderOf_pos a), mul_one, h]
      linarith
    have hgcd := Nat.eq_one_of_mul_eq_one_left this
    rw [mul_rotate] at this
    replace ha := Nat.eq_of_dvd_of_div_eq_one ha <| Nat.eq_one_of_mul_eq_one_left this
    rw [mul_rotate] at this
    replace hb := Nat.eq_of_dvd_of_div_eq_one hb <| Nat.eq_one_of_mul_eq_one_left this
    rwa [ha, hb] at hgcd

end CoprimeOrders

end IsCyclic

section CardEqPrime

-- also correct some `Finite.of...` names in Mathlib
theorem Finite.of_card_eq_neZero {n : ℕ} [NeZero n] {α : Type*} (h : Nat.card α = n) : Finite α :=
  Nat.finite_of_card_ne_zero (h ▸ NeZero.ne n)

theorem Nontrivial.of_card_eq_prime {p : ℕ} [hp : Fact p.Prime] {α : Type*} (h : Nat.card α = p) :
    Nontrivial α := by
  have : Finite α := Finite.of_card_eq_neZero h
  rw [← Finite.one_lt_card_iff_nontrivial, h]
  exact hp.elim.one_lt

-- deprecating `isCyclic_of_prime_card`
@[to_additive]
theorem IsCyclic.of_card_eq_prime {p : ℕ} [hp : Fact (Nat.Prime p)]
    {α : Type u} [Group α] (h : Nat.card α = p) :
    IsCyclic α := by
  have : Finite α := Finite.of_card_eq_neZero h
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  have : Nontrivial α := Nontrivial.of_card_eq_prime h
  obtain ⟨g, hg⟩ : ∃ g : α, g ≠ 1 := exists_ne 1
  use g
  have := orderOf_dvd_natCard g
  rw [h] at this ⊢
  symm
  refine (hp.elim.dvd_iff_eq ?_).mp this
  simp only [ne_eq, orderOf_eq_one_iff, hg, not_false_eq_true]

-- also modify `isCyclic_of_orderOf_eq_card`

-- deprecating `mulEquivOfPrimeCardEq`
open IsCyclic in
@[to_additive]
noncomputable def MulEquiv.ofPrimeCardEq {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H]
    (hG : Nat.card G = p) (hH : Nat.card H = p) : G ≃* H :=
  @mulEquivOfCyclicCardEq _ _ _ _ (of_card_eq_prime hG) (of_card_eq_prime hH) (hH ▸ hG)

end CardEqPrime
