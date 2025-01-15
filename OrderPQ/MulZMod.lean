import «OrderPQ».PrimeOrder

section MulZMod

-- How to tell to_additive how to convert this?
def MulZMod (n : ℕ) : Type := Multiplicative (ZMod n)

instance {n : ℕ} : DecidableEq (MulZMod n) := instDecidableEqMultiplicative

instance {n : ℕ} [NeZero n] : Fintype (MulZMod n) := Multiplicative.fintype

instance {n : ℕ} : Mul (MulZMod n) := Multiplicative.mul

instance {n : ℕ} : MulOneClass (MulZMod n) := Multiplicative.mulOneClass

instance {n : ℕ} : Group (MulZMod n) := Multiplicative.group

instance {n : ℕ} : IsCyclic (MulZMod n) := isCyclic_multiplicative

@[simp]
lemma MulZMod.card {n : ℕ} [NeZero n] : Fintype.card (MulZMod n) = n := by
  convert Fintype.card_multiplicative (ZMod n) using 1
  exact ZMod.card n |>.symm

lemma MulZMod.nat_card {n : ℕ} [NeZero n] : Nat.card (MulZMod n) = n := by simp

-- Why not `NeZero n`?
lemma ZMod.nat_card (n : ℕ) [Fintype (ZMod n)] : Nat.card (ZMod n) = n :=
  Fintype.card_eq_nat_card ▸ ZMod.card n

variable (p : ℕ) [hp : Fact p.Prime]

def mulEquivMulAutMulZMod : MulAut (MulZMod p) ≃* (ZMod p)ˣ :=
  AddEquiv.toMultiplicative.mulEquiv.symm.trans <| ZMod.addAutEquivUnits p

end MulZMod
