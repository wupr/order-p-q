import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Have
import Mathlib.Tactic.Group

@[simp]
lemma SemidirectProduct.card {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N) :
    Nat.card (N ⋊[φ] H) = Nat.card N * Nat.card H := by
  let ψ : N ⋊[φ] H ≃ N × H := {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  rw [Nat.card_eq_of_bijective ψ ψ.bijective, Nat.card_prod]

def SemidirectProduct.mulEquivProd
    {N H : Type*} [Group N] [Group H] :
    N ⋊[1] H ≃* N × H where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {N₁ N₂ H₁ H₂ : Type*} [Group N₁] [Group N₂] [Group H₁] [Group H₂]

def SemidirectProduct.congr
    {φ₁ : H₁ →* MulAut N₁} {φ₂ : H₂ →* MulAut N₂}
    (f₁ : N₁ ≃* N₂) (f₂ : H₁ ≃* H₂)
    (h : ∀ n₁ : N₁, ∀ h₁ : H₁, φ₂ (f₂ h₁) (f₁ n₁) = f₁ ((φ₁ h₁) n₁) ):
    N₁ ⋊[φ₁] H₁ ≃* N₂ ⋊[φ₂] H₂ where
  toFun x := ⟨f₁.toFun x.left, f₂.toFun x.right⟩
  invFun x := ⟨f₁.invFun x.left, f₂.invFun x.right⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by ext <;> simp [h]

@[simps]
def SemidirectProduct.monoidHomConjugate
    (φ₁ : H₁ →* MulAut N₁) (fn : N₁ ≃* N₂) (fh : H₁ ≃* H₂) :
    H₂ →* MulAut N₂ where
  toFun x :=
    {
      toFun := fn.toFun ∘ (φ₁.toFun (fh.invFun x)) ∘ fn.invFun
      invFun := fn.toFun ∘ (φ₁.toFun (fh.invFun x⁻¹)) ∘ fn.invFun
      left_inv := fun n => by simp
      right_inv := fun n => by simp
      map_mul' := by simp
    }
  map_mul' _ _ := by ext; simp
  map_one' := by simp; rfl

lemma SemidirectProduct.monoidHomConjugate_property
    (φ₁ : H₁ →* MulAut N₁) (f₁ : N₁ ≃* N₂) (f₂ : H₁ ≃* H₂) (n₁ : N₁) (h₁ : H₁) :
    ((SemidirectProduct.monoidHomConjugate φ₁ f₁ f₂) (f₂ h₁)) (f₁ n₁) = f₁ ((φ₁ h₁) n₁) := by
  simp

variable {G : Type*} [Group G]

lemma Subgroup.comm_of_normal_and_inf_eq_bot
    (N H : Subgroup G) (nN : Subgroup.Normal N) (nH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (n : N) (h : H) :
    (n : G) * (h : G) = (h : G) * (n : G) := by
  have : (n : G) * h * (n⁻¹ : G) * (h : G)⁻¹ ∈ N ⊓ H
  · refine mem_inf.mpr ⟨?_, ?_⟩
    · convert mul_mem (SetLike.coe_mem n) (nN.conj_mem _ (inv_mem (SetLike.coe_mem n)) h) using 1
      group
    · exact mul_mem (nH.conj_mem _ (SetLike.coe_mem _) _) (inv_mem (SetLike.coe_mem _))
  rwa [inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul] at this

noncomputable def mulEquivSemidirectProduct
    {N H : Subgroup G} (nN : Subgroup.Normal N) (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤)
    {φ : H →* MulAut N} (conj : φ = MulAut.conjNormal.restrict H):
    G ≃* N ⋊[φ] H := by
  let f : N ⋊[φ] H → G := fun x => x.1 * x.2
  have inj : f.Injective := by
    intro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    have h12 : (y1 : G)⁻¹ * x1 = y2 * (x2 : G)⁻¹
    · rwa [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
    have h1 : (y1 : G)⁻¹ * x1 ∈ N ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mul_mem (inv_mem <| SetLike.coe_mem y1) (SetLike.coe_mem x1)
      · exact h12 ▸ mul_mem (SetLike.coe_mem y2) (inv_mem <| SetLike.coe_mem x2)
    rw [inf_eq_bot, Subgroup.mem_bot] at h1
    have h2 : y2 * (x2 : G)⁻¹ = 1 := h12 ▸ h1
    rw_mod_cast [inv_mul_eq_one.mp h1, mul_inv_eq_one.mp h2]
  have surj : f.Surjective := by
    intro x
    obtain ⟨n, hN, h, hH, hyp⟩ : ∃ n ∈ N, ∃ h ∈ H, n * h = x
    · apply Set.mem_mul.mp
      rw [← Subgroup.normal_mul, sup_eq_top]
      exact Set.mem_univ x
    use ⟨⟨n, hN⟩,⟨h, hH⟩⟩
  refine MulEquiv.ofBijective (MulHom.mk f ?_) ⟨inj, surj⟩ |>.symm
  · intro _ _
    simp only [f, conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
      MonoidHom.restrict_apply, MulAut.conjNormal_apply]
    group

@[simps]
def Subgroup.subgroupOfMulEquiv {G : Type*} [Group G] (H K : Subgroup G) (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun x := ⟨x.1.1, mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, mem_subgroupOf.mpr <| SetLike.coe_mem ..⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[to_additive]
theorem Subgroup.subgroupOf_inf {H K L : Subgroup G} :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
  comap_inf H K L.subtype

noncomputable def mulEquivSemidirectProduct'
    {N H : Subgroup G} (nN : Subgroup.Normal N) (inf_eq_bot : N ⊓ H = ⊥)
    {φ : H →* MulAut N} (conj : φ = MulAut.conjNormal.restrict H):
    (N ⊔ H : Subgroup G) ≃* N ⋊[φ] H := by
  set NH : Subgroup G := N ⊔ H
  let φ' : (H.subgroupOf NH) →* MulAut (N.subgroupOf NH) := MulAut.conjNormal.restrict _
  let fn : N ≃* (N.subgroupOf NH) := N.subgroupOfMulEquiv NH le_sup_left |>.symm
  let fh : H ≃* (H.subgroupOf NH):= H.subgroupOfMulEquiv NH le_sup_right |>.symm
  let ψ := mulEquivSemidirectProduct (φ := φ') (by infer_instance) ?_ ?_ rfl
  refine ψ.trans <| MulEquiv.symm ?_
  · refine SemidirectProduct.congr fn fh fun n h => Subtype.eq <| Subtype.eq ?_
    rw [MonoidHom.restrict_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      InvMemClass.coe_inv, conj]
    repeat rw [Subgroup.subgroupOfMulEquiv_symm_apply_coe_coe]
    rw [MonoidHom.restrict_apply, MulAut.conjNormal_apply]
  · rw [Subgroup.subgroupOf_inf.symm, inf_eq_bot, Subgroup.bot_subgroupOf]
  · rw [Subgroup.sup_subgroupOf_eq] <;> simp [NH]

-- Can be generalised to subgroups of `G`.
noncomputable def mulEquivProd
    {N H : Subgroup G} (nN : Subgroup.Normal N) (nH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤) :
    G ≃* N × H := by
  refine MulEquiv.trans (mulEquivSemidirectProduct nN inf_eq_bot sup_eq_top rfl) ?_
  have : MulAut.conjNormal.restrict H = (1 : H →* MulAut N)
  · ext
    simp [← Subgroup.comm_of_normal_and_inf_eq_bot N H nN nH inf_eq_bot]
  exact this ▸ SemidirectProduct.mulEquivProd

-- noncomputable def mulEquivProd
--     {N H : Subgroup G} (nN : Subgroup.Normal N) (nH : Subgroup.Normal H) (int : N ⊓ H = ⊥) :
--     N ⊔ H ≃* N × H := sorry
