module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle017
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem det_one_add_eLast {k : Type} [Field k] {n : ℕ} (b : Fin (n + 1) → k) :
    (1 + vecMulVec (eLast k n) b).det = 1 + b (Fin.last n) := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    GlobalTheory.BZMir.eLast, dotProduct_single, mul_one]

theorem shearGL_mulVec_and_nabs_det : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (b : Fin (n + 1) → k), valuation k (b (Fin.last n)) < 1 → (∀ x : Fin (n + 1) → k, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x = x + (b ⬝ᵥ x) • eLast k n) ∧ nabs k (Matrix.GeneralLinearGroup.det (shearGL n b)) = 1 := by
  intro k _ _ _ _ n b hb
  have hv : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hb
  have hdet := GlobalTheory.CompanionTheory.MirPair.det_one_add_eLast b
  have hunit : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  have hcoe : ((GlobalTheory.CompanionTheory.MirPair.shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    simp only [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hunit, IsUnit.unit_spec]
  refine ⟨fun x => ?_, ?_⟩
  · rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcoe, hdet, hv]

end GlobalTheory.CompanionTheory.MirPair
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inv_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (m : ℕ) (g : GL (Fin m) k) (M : Set (Fin m → k))
    (F : (Fin m → k) → ℂ) :
    ∫ x in M, F (((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x) ∂(piHaar ν m) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
        ∫ y in {y | (g : Matrix (Fin m) (Fin m) k) *ᵥ y ∈ M}, F y ∂(piHaar ν m) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hinv : ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) * (g : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.inv_mul g
  have hinv' : (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.mul_inv g
  let e : (Fin m → k) ≃ᵐ (Fin m → k) :=
    { toFun := fun x => (g : Matrix (Fin m) (Fin m) k) *ᵥ x
      invFun := fun x => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x
      left_inv := fun x => by simp only [mulVec_mulVec, hinv, one_mulVec]
      right_inv := fun x => by simp only [mulVec_mulVec, hinv', one_mulVec]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have he : MeasurableEmbedding (Matrix.mulVec (g : Matrix (Fin m) (Fin m) k)) :=
    e.measurableEmbedding
  have hμ := GlobalTheory.UnipChange.smul_map_mulVec_pi ν (g : Matrix (Fin m) (Fin m) k)
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.val_det_apply g)
  unfold GlobalTheory.CompanionTheory.MirPair.piHaar GlobalTheory.SplitWeil.nabs
  conv_lhs => rw [← hμ]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul,
    he.restrict_map, he.integral_map]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mulVec_mulVec, hinv, one_mulVec]

end GlobalTheory.CompanionTheory.MirPair
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair.EvLin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem continuous_uM (n : ℕ) : Continuous (uM (k := k) n) :=
  (continuous_unipIn n).comp continuous_ofAdd

theorem uM_add (n : ℕ) (x y : Fin n → k) : uM n (x + y) = uM n x * uM n y := by
  simp only [uM, ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM (k := k) n 0 = 1 := by
  simp only [uM, ofAdd_zero, map_one]

theorem continuous_coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T)
    (v : V) (v' : V') : Continuous (coef T B v v') := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  refine ⟨(fun y => uM n (y - x)) ⁻¹' {g | T g v = v}, (hT v).preimage
    ((continuous_uM n).comp (continuous_id.sub continuous_const)), ?_, fun y hy => ?_⟩
  · simp [uM_zero]
  · have hy' : T (uM n (y - x)) v = v := hy
    have h : uM n y = uM n x * uM n (y - x) := by
      rw [← uM_add, add_sub_cancel]
    simp only [coef, h, map_mul, Module.End.mul_apply, hy']

theorem continuous_wt (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) : Continuous (wt ψ n) :=
  continuous_subtype_val.comp (hψ.comp (continuous_apply _).neg)

variable [MeasurableSpace k] [BorelSpace k]

theorem integrableOn_box (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) (v : V) (v' : V') (t : kˣ) :
    IntegrableOn (fun x => wt ψ n x * coef T B v v' x) (box (n + 1) t : Set (Fin (n + 1) → k))
      (piHaar ν (n + 1)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : IsFiniteMeasureOnCompacts (piHaar ν (n + 1)) := by
    unfold piHaar
    infer_instance
  exact ((continuous_wt ψ hψ n).mul (continuous_coef T B hT v v')).continuousOn.integrableOn_compact
    (isCompact_box _ t)

theorem coef_add_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v₁ v₂ : V) (v' : V')
    (x : Fin n → k) : coef T B (v₁ + v₂) v' x = coef T B v₁ v' x + coef T B v₂ v' x := by
  simp [coef]

theorem coef_smul_left (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B (z • v) v' x = z * coef T B v v' x := by
  simp [coef]

theorem coef_add_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v₁ v₂ : V')
    (x : Fin n → k) : coef T B v (v₁ + v₂) x = coef T B v v₁ x + coef T B v v₂ x := by
  simp [coef]

theorem coef_smul_right (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (z : ℂ) (v : V) (v' : V')
    (x : Fin n → k) : coef T B v (z • v') x = z * coef T B v v' x := by
  simp [coef]

theorem exists_common_threshold {P Q : kˣ → Prop}
    (hP : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t)
    (hQ : ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → Q t) :
    ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) → P t ∧ Q t := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
  · exact ⟨b, fun t ht => ⟨ha t (h.trans ht), hb t ht⟩⟩
  · exact ⟨a, fun t ht => ⟨ha t ht, hb t (h.trans ht)⟩⟩

theorem evVal_bilinear (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle)
    (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (hψ : Continuous ψ) (hT : IsSmooth T) :
    (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ →
      EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧
    (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ →
      EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧
    (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  refine ⟨fun v₁ v₂ v' A₁ A₂ h₁ h₂ => ?_, fun z v v' A h => ?_, fun v v₁ v₂ A₁ A₂ h₁ h₂ => ?_,
    fun z v v' A h => ?_⟩
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_left, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v₁ v' t) (integrableOn_box ν ψ T B hψ hT v₂ v' t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_left, mul_left_comm _ z]
    exact integral_const_mul z _
  · obtain ⟨t₀, ht₀⟩ := exists_common_threshold h₁ h₂
    refine ⟨t₀, fun t ht => ?_⟩
    obtain ⟨e₁, e₂⟩ := ht₀ t ht
    rw [← e₁, ← e₂]
    simp only [JJ, coef_add_right, mul_add]
    exact integral_add (integrableOn_box ν ψ T B hψ hT v v₁ t) (integrableOn_box ν ψ T B hψ hT v v₂ t)
  · obtain ⟨t₀, ht₀⟩ := h
    refine ⟨t₀, fun t ht => ?_⟩
    rw [← ht₀ t ht]
    simp only [JJ, coef_smul_right, mul_left_comm _ z]
    exact integral_const_mul z _

theorem evVal_additive_homogeneous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), Continuous ψ → IsSmooth T → (∀ (v₁ v₂ : V) (v' : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v₁ v' A₁ → EvVal ν ψ T B v₂ v' A₂ → EvVal ν ψ T B (v₁ + v₂) v' (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (z • v) v' (z * A)) ∧ (∀ (v : V) (v₁ v₂ : V') (A₁ A₂ : ℂ), EvVal ν ψ T B v v₁ A₁ → EvVal ν ψ T B v v₂ A₂ → EvVal ν ψ T B v (v₁ + v₂) (A₁ + A₂)) ∧ (∀ (z : ℂ) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B v (z • v') (z * A)) := by
  intro k _ _ _ _ _ _ ν _ ψ n V V' _ _ _ _ T B hψ hT
  exact evVal_bilinear ν ψ T B hψ hT

end GlobalTheory.CompanionTheory.MirPair.EvLin

end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inter_box_of_twists {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (ψ : AddChar k Circle) (c : kˣ) (hψ : Continuous ψ) (hc : HasConductor ψ c) (m : ℕ) (t : kˣ)
    (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ) (hM : IsCompact M) (hMm : MeasurableSet M)
    (hf : Continuous f)
    (h : ∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) :
    ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddHaarMeasure := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.MirPair.piHaar ν m) := by
    unfold GlobalTheory.CompanionTheory.MirPair.piHaar
    infer_instance
  haveI : (GlobalTheory.CompanionTheory.MirPair.piHaar ν m).IsAddRightInvariant := inferInstance
  set μ := GlobalTheory.CompanionTheory.MirPair.piHaar ν m with hμ
  have hbox : ∀ s : kˣ, GlobalTheory.SplitWeil.FourierPi.box (Fin m) s = (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m s : Set (Fin m → k)) := by
    intro s
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.coe_box]
    rfl
  set B' : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m (c * t⁻¹) : Set (Fin m → k)) with hB'
  set Bt : Set (Fin m → k) := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box m t : Set (Fin m → k)) with hBt
  have hB'c : IsCompact B' := GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m _
  have hB'm : MeasurableSet B' := hB'c.isClosed.measurableSet
  have hBtm : MeasurableSet Bt := (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box m t).isClosed.measurableSet
  have hpos : 0 < μ.real B' := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (μ.measure_pos_of_mem_nhds (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box_mem_nhds m _)).ne'
      hB'c.measure_lt_top.ne
  have hfour : ∀ x, ∫ b, B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ x) : Circle) : ℂ) ∂μ =
      Bt.indicator (fun _ => ((μ.real B' : ℝ) : ℂ)) x := by
    intro x
    have e := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi μ hc t x
    rw [hbox, hbox] at e
    exact e
  have hcc : Continuous (fun z : Circle => (z : ℂ)) := continuous_induced_dom
  have hdot : Continuous fun q : (Fin m → k) × (Fin m → k) => q.1 ⬝ᵥ q.2 :=
    GlobalTheory.SplitWeil.FourierPi.continuous_dot
  have hψc : Continuous fun q : (Fin m → k) × (Fin m → k) => ((ψ (-(q.1 ⬝ᵥ q.2)) : Circle) : ℂ) :=
    hcc.comp (hψ.comp hdot.neg)
  have hg1 : Integrable (B'.indicator fun _ => (1 : ℂ)) μ :=
    (integrable_indicator_iff hB'm).2 (continuousOn_const.integrableOn_compact' hB'c hB'm)
  have hg2 : Integrable (M.indicator f) μ :=
    (integrable_indicator_iff hMm).2 (hf.continuousOn.integrableOn_compact' hM hMm)
  have hint : Integrable (fun z : (Fin m → k) × (Fin m → k) => ((ψ (-(z.1 ⬝ᵥ z.2)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) z.1 * M.indicator f z.2)) (μ.prod μ) := by
    refine (hg1.mul_prod hg2).bdd_mul (c := 1) hψc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [Circle.norm_coe]
  have hswap : ∫ b, (∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ =
      ∫ x, (∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
        (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) ∂μ :=
    integral_integral_swap hint
  have hD : (fun b => ∫ x, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) = B'.indicator (fun _ => A) := by
    funext b
    by_cases hb : b ∈ B'
    · simp only [Set.indicator_of_mem hb, one_mul]
      have hx : (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * M.indicator f x) =
          M.indicator (fun x => ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x) := by
        funext x
        by_cases hxM : x ∈ M
        · simp only [Set.indicator_of_mem hxM]
        · simp only [Set.indicator_of_notMem hxM, mul_zero]
      rw [hx, integral_indicator hMm]
      exact h b hb
    · simp [Set.indicator_of_notMem hb]
  have hE : (fun x => ∫ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) *
      (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) ∂μ) =
      fun x => ((μ.real B' : ℝ) : ℂ) * (M ∩ Bt).indicator f x := by
    funext x
    have e : ∀ b, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (B'.indicator (fun _ => (1 : ℂ)) b * M.indicator f x) =
        B'.indicator (fun _ => (1 : ℂ)) b * ((ψ (b ⬝ᵥ -x) : Circle) : ℂ) * M.indicator f x := by
      intro b
      rw [dotProduct_neg]
      ring
    simp only [e]
    rw [integral_mul_const, hfour (-x)]
    have hneg : -x ∈ Bt ↔ x ∈ Bt := by
      simp only [hBt, SetLike.mem_coe, neg_mem_iff]
    by_cases hxB : x ∈ Bt
    · by_cases hxM : x ∈ M
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_mem hxM,
          Set.indicator_of_mem (Set.mem_inter hxM hxB)]
      · simp only [Set.indicator_of_mem (hneg.2 hxB), Set.indicator_of_notMem hxM,
          Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxM hx.1), mul_zero]
    · simp only [Set.indicator_of_notMem (fun hx : -x ∈ Bt => hxB (hneg.1 hx)),
        Set.indicator_of_notMem (fun hx : x ∈ M ∩ Bt => hxB hx.2), zero_mul, mul_zero]
  rw [hD, hE, integral_indicator_const _ hB'm, integral_const_mul,
    integral_indicator (hMm.inter hBtm), Complex.real_smul] at hswap
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hpos.ne') hswap).symm

end GlobalTheory.CompanionTheory.MirPair
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem dcos_compact_lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}
    (hL : LocSec Q P x) (hP : IsClosed (P : Set G)) (B₀ : Set G) (hB : IsCompact B₀) (hB₁ : B₀ ∈ 𝓝 (1 : G))
    (D : Set G) (hD : IsCompact D) (hDc : D ⊆ dcos Q P x) :
    ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  obtain ⟨O, hO, hsec⟩ := hL Set.univ Filter.univ_mem B₀ hB₁
  have hemb : Topology.IsClosedEmbedding (Subtype.val : P → G) := hP.isClosedEmbedding_subtypeVal
  have hC₁ : IsCompact ((Subtype.val : P → G) ⁻¹' B₀) := hemb.isCompact_preimage hB
  refine hD.induction_on
    (p := fun T => ∃ C : Set P, IsCompact C ∧ ∀ g ∈ T, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c)
    ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, hC, h⟩
    exact ⟨C, hC, fun g hg => h g (hST hg)⟩
  · rintro S T ⟨C, hC, h⟩ ⟨C', hC', h'⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    rintro g (hg | hg)
    · obtain ⟨q, hq, c, hc, e⟩ := h g hg
      exact ⟨q, hq, c, Or.inl hc, e⟩
    · obtain ⟨q, hq, c, hc, e⟩ := h' g hg
      exact ⟨q, hq, c, Or.inr hc, e⟩
  · intro g₀ hg₀
    obtain ⟨q₀, hq₀, p₀, hp₀, e₀⟩ := hDc hg₀
    have hcont : Continuous fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹ := by fun_prop
    have hval : (q₀ * x)⁻¹ * g₀ * p₀⁻¹ = 1 := by
      rw [e₀]; group
    have hU : (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O ∈ 𝓝 g₀ :=
      hcont.continuousAt.preimage_mem_nhds (by rw [hval]; exact hO)
    refine ⟨D ∩ (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O,
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
      (fun c : P => c * (⟨p₀, hp₀⟩ : P)) '' ((Subtype.val : P → G) ⁻¹' B₀),
      hC₁.image (by fun_prop), ?_⟩
    rintro g ⟨hgD, hgU⟩
    obtain ⟨q', hq', p', hp', e'⟩ := hDc hgD
    have hxu : x * ((q₀ * x)⁻¹ * g * p₀⁻¹) ∈ dcos Q P x := by
      refine ⟨q₀⁻¹ * q', Q.mul_mem (Q.inv_mem hq₀) hq', p' * p₀⁻¹, P.mul_mem hp' (P.inv_mem hp₀), ?_⟩
      rw [e']; group
    obtain ⟨s, hs, -, p₂, hp₂, hp₂B, e₂⟩ := hsec _ hgU hxu
    refine ⟨q₀ * s, Q.mul_mem hq₀ hs, ⟨p₂, hp₂⟩ * ⟨p₀, hp₀⟩, ⟨⟨p₂, hp₂⟩, hp₂B, rfl⟩, ?_⟩
    have e₃ : g = q₀ * (x * ((q₀ * x)⁻¹ * g * p₀⁻¹)) * p₀ := by group
    rw [e₃, e₂]
    simp [mul_assoc]

end GlobalTheory.CompanionTheory.BZRes
end
