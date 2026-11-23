module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle172
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteFock

variable {D : D7}

theorem compAt_mt_of_finite (θ : InfFam D) (τ : D.what₂.Tau) {S : HSp D} {k : GA D S} (hk : k ∈ GfC S) :
    compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
  have h1 : (Formalism.L2.Theta.mt S k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt S k) = ((Formalism.L2.Theta.mt S k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem dRho_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (c • f) = c • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [Pi.smul_apply, smul_eq_mul, ← deriv_const_mul_field]
  congr 1
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem pureTensorO_smul (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT) (c : ℂ)
    (f : WO S T → ℂ) (P) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, Module.End.one_apply]
  rw [dRho_smul, dRho_smul, smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem pureTensorO_one (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS sT BS BT)
    (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have e : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]
    rfl
  unfold pureTensorO pureTensorL
  rw [e, Module.Basis.constr_basis]
  simp [opPow]

theorem om_pureTensorO_of_finite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT f, (∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)) → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, ∀ c : ℂ, om (k, k') f = c • f → ∀ P, om (k, k') (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  intro D ψ θ S T χS χT om hθ hom sS sT BS BT f hf k hk k' hk' c hc P
  have hf0 : IsThetaFunO ψ S T f := by simpa only [pureTensorO_one] using hf 1
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k k'
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [compAt_mt_of_finite θ τ hk', Matrix.one_mul]) f hf0 P).2, hc, pureTensorO_smul]

end GlobalTheory.FiniteFock
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem translate_lift_linear_isometry : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∃ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y, ‖S y‖ = ‖y‖) ∧ ∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hMod i t g0 κ hκ
  have hex := fun y => GlobalTheory.translate_unitary_lifts R hlev hMod.HV hMod.cV i t g0 κ hκ y
  choose S hS hSn using hex
  have hinj : Function.Injective (R.HV i t).e := (hMod.HV i t).1
  refine ⟨{ toFun := S, map_add' := ?_, map_smul' := ?_ }, hSn, ?_⟩
  · intro y z
    apply hinj
    funext h
    simp only [map_add (f := _), Pi.add_apply, hS, smul_add]
  · intro a y
    apply hinj
    funext h
    simp only [map_smul, Pi.smul_apply, hS, RingHom.id_apply]
    exact smul_comm _ _ _
  · intro y h
    have hk : (R.cV i).ρ κ⁻¹ = 1 := (hMod.cV i).1 _ (inv_mem hκ.1)
    have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) =
        (finHom (Vc D i)).rangeRestrict h * (finHom (Vc D i)).rangeRestrict κ := map_mul _ _ _
    show (R.cV i).ρ h⁻¹ ((R.HV i t).e (S y) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)))
    have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
      rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
    refine (congrArg ((R.cV i).ρ h⁻¹) (hS y _)).trans ?_
    refine (LinearMap.map_smul _ _ _).trans (congrArg (fun w => (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) ?_)
    exact congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e y) hrr.symm)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → IsSelfDualC V Λ := by
  first | exact @GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame | exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame | (intros; apply GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (χS χT : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)), Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) χS χT ω → ∀ φ : WO (Vc D i) (Wc D i) → ℂ, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → ∀ (h : GA D (Vc D i)) (γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → ∀ g : GA D (Wc D i), Datum.thetaKO ω h (γ * g) φ = Datum.thetaKO ω h g φ := by
  first | exact @GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary | exact GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary | (intros; apply GlobalTheory.ThetaLeftW.thetaKernel_leftInvariant_rationalUnitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  first | exact @GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | exact GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay | (intros; apply GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRealise

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def toCx3One (R : RealDat3 D A3 Ks) (F : Face3 D A3) : CxData A3.fam3.amb3 where
  FC t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HX t).H
  jR t := Tw.semi _ R.toRealDat.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp3 p)
  EEl b := Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.toRealDat.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H
  θ' i t := Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp3 i p)
  dW b i := Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.toRealDat.WS F.lv2 b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.toRealDat.bC F.lv2 b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype)
  M b i := (R.FW i).Mcoord (F.lv2.lvl b).P (F.lv2.lvl b).ψ⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 b i)
  nP := RealDat.nP F.lv2
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam3
  err0 := R.err0

theorem toCx3_eq_one (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hph : ∀ i, R.phs i = 1) : R.toCx3 F = toCx3One R F := by
  unfold RealDat3.toCx3 toCx3One
  congr 1
  funext i t
  simp only [hph, one_smul]

end GlobalTheory.CharRealise
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.doublingIntegral_jointHarmonic_pos : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X := by
  first | exact @GlobalTheory.DoublingPos.doubling_pos | exact GlobalTheory.DoublingPos.doubling_pos | (intros; apply GlobalTheory.DoublingPos.doubling_pos <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.fockSpace_contains_discreteSeriesTensor : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X := by
  first | exact @GlobalTheory.FockTensor.fock_contains_tensor | exact GlobalTheory.FockTensor.fock_contains_tensor | (intros; apply GlobalTheory.FockTensor.fock_contains_tensor <;> assumption)
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KExpLine

section Abstract

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def zeroOn (S : Submodule ℂ (SchwartzMap Y ℂ)) (P : Finset Y) : Submodule ℂ S where
  carrier := {s | ∀ y ∈ P, (s : SchwartzMap Y ℂ) y = 0}
  add_mem' := by
    intro a b ha hb y hy
    simp [ha y hy, hb y hy]
  zero_mem' := by
    intro y _
    simp
  smul_mem' := by
    intro c a ha y hy
    simp [ha y hy]

theorem exists_finset_sep (S : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S] :
    ∃ P : Finset Y, ∀ s ∈ S, (∀ y ∈ P, s y = 0) → s = 0 := by
  classical
  obtain ⟨P, -, hmin⟩ := (measure fun P : Finset Y => Module.finrank ℂ (zeroOn S P)).wf.has_min Set.univ
    ⟨∅, trivial⟩
  refine ⟨P, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, s y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (SchwartzMap.ext h)
  have hlt : zeroOn S (insert y P) < zeroOn S P := by
    refine lt_of_le_of_ne (fun a ha z hz => ha z (Finset.mem_insert_of_mem hz)) fun heq => ?_
    have hmem : (⟨s, hs⟩ : S) ∈ zeroOn S P := h0
    rw [← heq] at hmem
    exact hy (hmem y (Finset.mem_insert_self y P))
  exact hmin (insert y P) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem sub_mem_of_hasDerivAt (S T : Submodule ℂ (SchwartzMap Y ℂ)) [FiniteDimensional ℂ S]
    (c d : ℝ → SchwartzMap Y ℂ) (hc : ∀ u, c u ∈ S) (hd : ∀ t, d t ∈ T)
    (hder : ∀ y t, HasDerivAt (fun u => c u y) (d t y) t) : c 1 - c 0 ∈ T := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_sep S
  let E : S →ₗ[ℂ] (P → ℂ) :=
    { toFun := fun s p => (s : SchwartzMap Y ℂ) p
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro a b; funext p; simp }
  have hE : LinearMap.ker E = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    exact Subtype.ext (hP s s.2 fun y hy => congrFun hs ⟨y, hy⟩)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective E hE
  let C : ℝ → (P → ℂ) := fun u p => c u p
  have hCd : ∀ t, HasDerivAt C (fun p => d t p) t := fun t => hasDerivAt_pi.2 fun p => hder p t
  have hLC : ∀ u, L (C u) = ⟨c u, hc u⟩ := fun u => LinearMap.congr_fun hL ⟨c u, hc u⟩
  let ev : SchwartzMap Y ℂ → Y → ℂ := fun g y => g y
  have hcomp : ∀ φ : (P → ℂ) →ₗ[ℂ] ℂ, ∀ t, HasDerivAt (fun u => φ (C u)) (φ (fun p => d t p)) t := fun φ t => by
    have h := (((LinearMap.toContinuousLinearMap φ).restrictScalars ℝ).hasFDerivAt (x := C t)).comp_hasDerivAt t (hCd t)
    simpa [Function.comp_def] using h

  have hdS : ∀ t, ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) = d t := by
    intro t
    ext y
    let evy : S →ₗ[ℂ] ℂ :=
      { toFun := fun s => (s : SchwartzMap Y ℂ) y
        map_add' := by intro a b; simp
        map_smul' := by intro a b; simp }
    have h1 := hcomp (evy ∘ₗ L) t
    have h2 : (fun u => (evy ∘ₗ L) (C u)) = fun u => c u y := by
      funext u
      simp only [LinearMap.comp_apply, hLC u]
      rfl
    rw [h2] at h1
    exact (hder y t).unique h1 |>.symm
  let T' : Submodule ℂ S := T.comap S.subtype
  have hdT : ∀ t, L (fun p => d t p) ∈ T' := fun t => by
    show ((L (fun p => d t p) : S) : SchwartzMap Y ℂ) ∈ T
    rw [hdS t]
    exact hd t
  have key : (⟨c 1, hc 1⟩ : S) - ⟨c 0, hc 0⟩ ∈ T' := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    let ψ : (P → ℂ) →ₗ[ℂ] ℂ := φ ∘ₗ T'.mkQ ∘ₗ L
    have hg : ∀ t, HasDerivAt (fun u => ψ (C u)) 0 t := by
      intro t
      have := hcomp ψ t
      have h0 : ψ (fun p => d t p) = 0 := by
        show φ (T'.mkQ (L (fun p => d t p))) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T').2 (hdT t), map_zero]
      rwa [h0] at this
    have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
    have e1 : ∀ u, ψ (C u) = φ (Submodule.Quotient.mk ⟨c u, hc u⟩) := fun u => by
      show φ (T'.mkQ (L (C u))) = _
      rw [hLC u]
      rfl
    rw [e1, e1] at hconst
    rw [Submodule.Quotient.mk_sub, map_sub, hconst, sub_self]
  exact key

end Abstract

end GlobalTheory.KExpLine

namespace GlobalTheory.KExpLine

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

end GlobalTheory.KExpLine
end
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.unfolding_zero_mean_normalized_subgroup : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ K F : H → ℂ, Measurable K → Measurable F → (∀ n ∈ N, ∀ h, K (n * h) = K h) → (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ h, ∫ n in 𝓝, F ((n : H) * h) ∂κ = 0) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → IntegrableOn (fun h => K h * F h) 𝓕 ν → ∫ h in 𝓕, K h * F h ∂ν = 0 := by
  first | exact @GlobalTheory.UnfoldNormal.unfold_zero_mean | exact GlobalTheory.UnfoldNormal.unfold_zero_mean | (intros; apply GlobalTheory.UnfoldNormal.unfold_zero_mean <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweGlobal

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c φ =>
      refine ⟨1, fun _ => c • x, fun _ => φ, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
      obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
      refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
      rw [TensorProduct.tmul_add, e₁, e₂, Fin.sum_univ_add]
      simp
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
    obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [e₁, e₂, Fin.sum_univ_add]
    simp

end GlobalTheory.HoweGlobal

end
end
