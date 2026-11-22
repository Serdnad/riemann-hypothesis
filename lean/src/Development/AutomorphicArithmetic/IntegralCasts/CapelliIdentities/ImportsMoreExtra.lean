import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

open Formalism.WeaklyAdmissibleFiltrations
open scoped TensorProduct

namespace UpperTheory.Reformulated.B.Qh15

section Character

variable {G A : Type} [inst : Group G] [inst_1 : CommRing A]

theorem aux1 {A : Type} [inst : CommRing A] : SMulCommClass A A A := inferInstance

theorem aux2 (κ : G →* Aˣ) :
    (κ 1 : A) • (LinearMap.id : A →ₗ[A] A) = 1 := by
  ext
  simp

theorem aux3 (κ : G →* Aˣ) (g h : G) :
    (κ (g * h) : A) • (LinearMap.id : A →ₗ[A] A) =
      ((κ g : A) • LinearMap.id) * ((κ h : A) • LinearMap.id) := by
  ext
  simp [mul_comm]

noncomputable def chRep (κ : G →* Aˣ) : Representation A G A where
  toFun g := (κ g : A) • LinearMap.id
  map_one' := aux2 κ
  map_mul' := aux3 κ

end Character

section Periods

variable {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp] [inst_2 : Field K₀] [inst_3 : Field K]
  [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K] [inst_6 : Algebra K₀ K] [inst_7 : IsScalarTower Qp K₀ K]
  {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR] [inst_10 : Algebra Qp B] [inst_11 : Algebra K₀ B]
  [inst_12 : IsScalarTower Qp K₀ B] [inst_13 : Algebra Qp BdR] [inst_14 : Algebra K₀ BdR] [inst_15 : Algebra K BdR]
  [inst_16 : IsScalarTower Qp K BdR] [inst_17 : IsScalarTower K₀ K BdR] [inst_18 : IsScalarTower Qp K₀ BdR]
  (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {E : Type} [inst_19 : Field E]
  [inst_20 : Algebra Qp E]

/-- Multiplication on the tensor product takes vectors twisted by two characters
to vectors twisted by their product. -/
theorem act_mul_chars (κ μ : G →* Eˣ) (g : G) (x y : E ⊗[Qp] B) :
    actVB PD (chRep κ) g x * actVB PD (chRep μ) g y = actVB PD (chRep (κ * μ)) g (x * y) := by
  have hact (χ : G →* Eˣ) (a : E) (b : B) :
      actVB PD (chRep χ) g (a ⊗ₜ[Qp] b) = ((χ g : E) * a) ⊗ₜ[Qp] PD.actB g b := rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mul]
  | add a b ha hb => simp only [map_add, add_mul, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | add c d hc hd => simp only [map_add, mul_add, hc, hd]
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, hact, map_mul, MonoidHom.mul_apply, Units.val_mul]
      congr 1
      ring

theorem act_mul (κ : G →* Eˣ) (g : G) (x y : E ⊗[Qp] B) :
    actVB PD (chRep κ) g x * actVB PD (chRep κ⁻¹) g y = actVB PD (chRep 1) g (x * y) := by
  simpa only [mul_inv_cancel] using act_mul_chars PD κ κ⁻¹ g x y

end Periods

end UpperTheory.Reformulated.B.Qh15
