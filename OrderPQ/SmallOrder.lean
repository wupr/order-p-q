import «OrderPQ».Main
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.KleinFour

-- lemma Std.not_commutative_iff {α : Sort u} (op : α → α → α) :
--     ¬Commutative op ↔ ∃ (x y : α), op x y ≠ op y x := by
--   simp_rw [← not_forall]
--   exact not_iff_not.mpr ⟨@Commutative.comm _ _, Commutative.mk⟩

lemma DihedralGroup.not_commutative_of_gt_two {n : ℕ} (h : n > 2) :
    ¬Std.Commutative fun (x y : DihedralGroup n) => x * y := by
  rintro ⟨h'⟩
  specialize h' (r 1) (sr 0)
  rw [r_mul_sr, zero_sub, sr_mul_r, zero_add, sr.injEq, neg_eq_iff_add_eq_zero, one_add_one_eq_two,
    ← ZMod.val_eq_zero, ← Nat.cast_two, ZMod.val_natCast, ← Nat.dvd_iff_mod_eq_zero] at h'
  exact Nat.not_le_of_gt h <| Nat.le_of_dvd Nat.zero_lt_two h'

lemma DihedralGroup.not_commutative_zero :
    ¬Std.Commutative fun (x y : DihedralGroup 0) => x * y := by
  rintro ⟨h'⟩
  specialize h' (r 1) (sr 0)
  simp at h'

lemma IsCyclic.commutative {G : Type*} [Group G] [IsCyclic G] :
    Std.Commutative (· * · : G → G → G) :=
  ⟨commGroup.mul_comm⟩

lemma DihedralGroup.not_isCyclic {n : ℕ} (h : n ≠ 1) :
    ¬IsCyclic (DihedralGroup n) := fun h' =>
  match n with
  | 0 => not_commutative_zero h'.commutative
  | 1 => h rfl
  | 2 => IsKleinFour.not_isCyclic h'
  | _ + 3 => not_commutative_of_gt_two (Nat.lt_of_sub_eq_succ rfl) h'.commutative

variable {G H : Type*} [Group G] [Group H]

section OrderSix

lemma nonempty_mulEquiv_of_card_eq_six (h1 : Nat.card G = 6) (h1' : ¬IsCyclic G)
    (h2 : Nat.card H = 6) (h2' : ¬IsCyclic H) :
    Nonempty (G ≃* H) :=
  nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic (p := 2) (q := 3) h1 h1' h2 h2'

lemma nonempty_mulEquiv_dihedralGroup_three (h1 : Nat.card G = 6) (h2 : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 3) :=
  nonempty_mulEquiv_of_card_eq_six h1 h2 DihedralGroup.nat_card <| DihedralGroup.not_isCyclic <|
    Nat.succ_succ_ne_one 1

end OrderSix

section OrderTen

instance Nat.fact_prime_five : Fact (Prime 5) := ⟨prime_five⟩

lemma nonempty_mulEquiv_of_card_eq_ten (h1 : Nat.card G = 10) (h1' : ¬IsCyclic G)
    (h2 : Nat.card H = 10) (h2' : ¬IsCyclic H) :
    Nonempty (G ≃* H) :=
  nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic (p := 2) (q := 5) h1 h1' h2 h2'

lemma nonempty_mulEquiv_dihedralGroup_five (h1 : Nat.card G = 10) (h2 : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 5) :=
  nonempty_mulEquiv_of_card_eq_ten h1 h2 DihedralGroup.nat_card <| DihedralGroup.not_isCyclic <|
    Nat.succ_succ_ne_one 3

end OrderTen

section OrderFourteen

theorem Nat.prime_seven : Prime 7 := by decide

instance Nat.fact_prime_seven : Fact (Prime 7) := ⟨prime_seven⟩

lemma nonempty_mulEquiv_of_card_eq_fourteen (h1 : Nat.card G = 14) (h1' : ¬IsCyclic G)
    (h2 : Nat.card H = 14) (h2' : ¬IsCyclic H) :
    Nonempty (G ≃* H) :=
  nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic (p := 2) (q := 7) h1 h1' h2 h2'

lemma nonempty_mulEquiv_dihedralGroup_seven (h1 : Nat.card G = 14) (h2 : ¬IsCyclic G) :
    Nonempty (G ≃* DihedralGroup 7) :=
  nonempty_mulEquiv_of_card_eq_fourteen h1 h2 DihedralGroup.nat_card <|
    DihedralGroup.not_isCyclic <| Nat.succ_succ_ne_one 5

end OrderFourteen

section OrderNine

lemma nonempty_mulEquiv_of_card_eq_nine (h1 : Nat.card G = 9) (h1' : ¬IsCyclic G)
    (h2 : Nat.card H = 9) (h2' : ¬IsCyclic H) :
    Nonempty (G ≃* H) :=
  nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic (p := 3) (q := 3) h1 h1' h2 h2'

lemma exponent_three_of_card_eq_nine_of_not_isCyclic (h1 : Nat.card G = 9) (h2 : ¬IsCyclic G) :
    Monoid.exponent G = 3 := by
  obtain ⟨f⟩ := nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic (p := 3) h1 h2
  rw [Monoid.exponent_eq_of_mulEquiv f, Monoid.exponent_prod, MulZMod.exponent]
  simp

end OrderNine

section OrderFifteen

lemma isCyclic_of_card_eq_fifteen (h : Nat.card G = 15) : IsCyclic G :=
  isCyclic_of_card_eq_prime_mul_prime' (p := 3) (q := 5) h (by decide)

end OrderFifteen
