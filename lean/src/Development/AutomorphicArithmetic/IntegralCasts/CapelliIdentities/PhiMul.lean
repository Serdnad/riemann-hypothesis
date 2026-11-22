import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

open Formalism.WeaklyAdmissibleFiltrations

theorem UpperTheory.Reformulated.B.Qf14.phi_mul : ∀ {G : Type} [inst : Group G] {Qp K₀ K : Type} [inst_1 : Field Qp]
  [inst_2 : Field K₀] [inst_3 : Field K] [inst_4 : Algebra Qp K₀] [inst_5 : Algebra Qp K] [inst_6 : Algebra K₀ K]
  [inst_7 : IsScalarTower Qp K₀ K] {B BdR : Type} [inst_8 : CommRing B] [inst_9 : CommRing BdR] [inst_10 : Algebra Qp B]
  [inst_11 : Algebra K₀ B] [inst_12 : IsScalarTower Qp K₀ B] [inst_13 : Algebra Qp BdR] [inst_14 : Algebra K₀ BdR]
  [inst_15 : Algebra K BdR] [inst_16 : IsScalarTower Qp K BdR] [inst_17 : IsScalarTower K₀ K BdR]
  [inst_18 : IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {E : Type} [inst_19 : Field E]
  [inst_20 : Algebra Qp E] (x y : TensorProduct Qp E B), (φVB PD (LL := E)) (x * y) = (φVB PD (LL := E)) x * (φVB PD (LL := E)) y := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD E _ _ x y
  have h : ∀ z : TensorProduct Qp E B,
      φVB PD (LL := E) (V := E) z
        = Algebra.TensorProduct.map (AlgHom.id E E) PD.φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact (h (x * y)).trans ((map_mul _ x y).trans (congrArg₂ (· * ·) (h x).symm (h y).symm))
