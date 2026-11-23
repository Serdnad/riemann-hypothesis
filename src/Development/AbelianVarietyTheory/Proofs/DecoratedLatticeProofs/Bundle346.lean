module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelCreationWeilActionMovedFrames
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle330
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle853
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle324
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocScalar

theorem place_ι_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have hx : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]
  have := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι] at this
  rw [this, ← mul_assoc, hx]

theorem place_ι_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have := p.ι_π 1
  rwa [map_one, mul_one] at this

theorem place_π_e {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  rw [← place_ι_one, p.π_ι]

theorem exists_isLoc_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z) (c : kˣ) (zk : GL Z k), (zk : Matrix Z Z k) = (c : k) • (1 : Matrix Z Z k) → ∃ z : GA D V, p.IsLoc F z zk := by
  intro D k _ _ _ _ p V Z _ _ F c zk hzk
  have he := p.split
  obtain ⟨g, h1, h2, h3⟩ := GlobalTheory.SplitOnto.exists_unitary (c := cA D) GlobalTheory.SplitOnto.cA_cA (GlobalTheory.SplitOnto.gram_mul_inv V)
    (GlobalTheory.SplitOnto.gram_conj V) he.1 he.2.1 (p.ι (c : k) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (p.ι ((c⁻¹ : kˣ) : k) • 1) (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul (p.ι _), ← place_ι_mul, Units.inv_mul, place_ι_one, smul_smul, he.1])
  let z : GA D V := ⟨g, h1⟩
  refine ⟨z, fun i j => congrFun (congrFun h2 i) j, ?_⟩
  rw [hzk, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, F.βγ]
  ext i j
  have := congrFun (congrFun h3 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  change p.π (g.1 i j) = _
  rw [← one_mul (p.π (g.1 i j)), ← place_π_e p, ← map_mul, this, map_mul, place_π_e, one_mul]
  by_cases hij : i = j
  · subst hij; simp [p.π_ι]
  · simp [hij]

end GlobalTheory.LocScalar
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def conjH (gk : GL Y' k) (hk : GL Y k) : Matrix Y Y' k ≃ₜ Matrix Y Y' k where
  toFun x := (hk⁻¹).val * x * gk.val
  invFun x := hk.val * x * (gk⁻¹).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def twist (c : ℂ) (gk : GL Y' k) (hk : GL Y k) : SB (Matrix Y Y' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => c * Φ.1 ((hk⁻¹).val * x * gk.val),
    (SB _).smul_mem c (show Φ.1 ∘ conjH gk hk ∈ SB _ from ⟨Φ.2.1.comp_continuous (conjH gk hk).continuous,
      Φ.2.2.comp_homeomorph (conjH gk hk)⟩)⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' a Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (c : ℂ) (gk : GL Y' k) (hk : GL Y k) (Φ : SB (Matrix Y Y' k)) (x) :
    (twist c gk hk Φ).1 x = c * Φ.1 ((hk⁻¹).val * x * gk.val) := rfl

variable {D : D7} (p : Place D k)

theorem mt_inv_mul' {S : HSp D} (g : GA D S) : mt S g⁻¹ * mt S g = 1 := by
  rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
  simp [Formalism.L2.Theta.mt]

theorem actO_up {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {g : GA D S} {gk : GL Y' k}
    {h : GA D T} {hk : GL Y k} (hg : p.IsLoc FS g gk) (hh : p.IsLoc FT h hk) (x : Matrix Y Y' k) :
    actO S T g h (p.up FS FT x) = p.up FS FT (hk.val * x * (gk⁻¹).val) := by
  have h1 : IsHalf p.e (actO S T g h (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO g h (Witness.up_half p FS FT x)
  rw [← Witness.up_down p FS FT h1]
  congr 1
  set M := (mt S g⁻¹).map p.π with hMdef
  have hM : M * (FS.β * gk.val * FS.γ) = 1 := by
    rw [← hg.2, hMdef, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : FS.γ * (M * FS.β) * gk.val = 1 := by
    have : FS.γ * (M * (FS.β * gk.val * FS.γ)) * FS.β = 1 := by rw [hM, Matrix.mul_one, FS.γβ]
    rw [← this]
    simp only [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hN : FS.γ * (M * FS.β) = (gk⁻¹).val := by
    calc FS.γ * (M * FS.β) = FS.γ * (M * FS.β) * gk.val * (gk⁻¹).val := by
          rw [Matrix.mul_assoc (FS.γ * (M * FS.β)), Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e1, Matrix.one_mul]
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hh.2, hu, ← hMdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, hN]

end GlobalTheory.LocTwist

namespace GlobalTheory.LocTwist

theorem conj_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → ∃ T₂ : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ), p.IsModel ψ FS FT T₂ ∧ ∀ Φ Φ' : SB (Matrix Y Y' k), Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → T₂ Φ = ω (g⁻¹, h⁻¹) (Tm Φ') := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT Y Y' _ _ _ _ FS FT Tm hm g gk h hk hg hh
  set c : ℂ := (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) *
    ((μS⁻¹ (Matrix.GeneralLinearGroup.det gk) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det hk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) : ℝ) : ℂ)) with hc
  let L := LocTwist.twist c gk hk
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (g⁻¹, h⁻¹)
  have hA := LocTwist.actO_up p FS FT hg hh
  have hback : ∀ z, actO S T g⁻¹ h⁻¹ (p.up FS FT (hk.val * z * (gk⁻¹).val)) = p.up FS FT z := fun z => by
    rw [← hA, GlobalTheory.SplitHecke.actO_inv_actO]
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun x Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + hk.val * x * (gk⁻¹).val) := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      congr 2
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc ((hk⁻¹).val) hk.val, Units.inv_mul, Matrix.one_mul]
    have h2 := hm.trans _ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hback]
  · set y' := actO S T g h y
    have hy' : IsHalf (cA D p.e) y' := GlobalTheory.SplitHecke.isHalf_actO g h hy
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y') * (L Φ).1 t := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      have hu : p.up FS FT ((hk⁻¹).val * t * gk.val) = actO S T g⁻¹ h⁻¹ (p.up FS FT t) := by
        rw [← hback ((hk⁻¹).val * t * gk.val)]
        congr 2
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hs : symplO S T (p.up FS FT ((hk⁻¹).val * t * gk.val)) y = symplO S T (p.up FS FT t) y' := by
        rw [hu, ← GlobalTheory.SplitHecke.symplO_actO S T g⁻¹ h⁻¹ (p.up FS FT t) y', GlobalTheory.SplitHecke.actO_inv_actO]
      rw [hs]; ring
    have h2 := hm.modul y' hy' (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), GlobalTheory.SplitHecke.actO_inv_actO]
  · have : Φ' = L Φ := by
      apply Subtype.ext; funext t
      rw [e]
      simp only [L, LocTwist.twist_apply, Pi.smul_apply, smul_eq_mul, om, hc]
      ring
    rw [this]; rfl

end GlobalTheory.LocTwist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

theorem _root_.GlobalTheory.T.isLocalModel_creation_weilAction_moved_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T), GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β → GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β → ∀ sS sT BS BT P T₁, p.IsModel ψ FS FT T₁ → ∃ T₂, p.IsModel ψ GS GT T₂ ∧ ∀ Φ, T₂ Φ = ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := by
  first | exact @GlobalTheory.LocModMove.isModel_move | exact GlobalTheory.LocModMove.isModel_move | (intros; apply GlobalTheory.LocModMove.isModel_move <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.schrodinger_dualHalf_derivative_linear_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  first | exact @GlobalTheory.StdUnn.sch_dRho_dualHalf | exact GlobalTheory.StdUnn.sch_dRho_dualHalf | (intros; apply GlobalTheory.StdUnn.sch_dRho_dualHalf <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.WeilCoefScalar

theorem integrableOn_mul_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {ν : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕) :
    IntegrableOn (fun w => f w * conj (g w)) 𝓕 ν := by
  refine GlobalTheory.MixModel.covolOne_integrableOn hν _
    (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_
  rintro _ ⟨γ, rfl⟩ a
  have e1 := hf.quasi γ a
  have e2 := hg.quasi γ a
  have hn : ∀ x, conj (ψ x) * ψ x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]; norm_num
  change f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)
  rw [e1, e2, map_mul]
  linear_combination (f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)

end GlobalTheory.WeilCoefScalar

namespace GlobalTheory.WeilCoefScalar

theorem wcoef_pure_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by

  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν
  have hc : (R.cV i).Is := hC.models.cV i
  have hW := hC.thP.ωP i t
  have hio := (hC.thP.ioP i t).1
  let J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))
  have hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x := fun x => rfl
  have hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x) := fun x => hC.thP.pt_theta i t _
  have hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν := fun x y =>
    integrableOn_mul_conj hW.std (hth y) (hth x) hν
  let B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν)
      (fun x x' y => by
        simp only [map_add (f := _), Pi.add_apply, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
      (fun x y y' => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint x y) (hint x y'))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
  have hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν := fun x y => rfl
  have hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x) := fun u hu x => by
    rw [← hJ, ← hJ]; exact hio u hu _ x
  have hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y := by
    intro u hu x y
    rw [hB, hB, ← hom u hu x, ← hom u hu y]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1))
      (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv
  refine ⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩
  · rw [hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]
  · rw [hJ] at hw
    have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν
    apply h1
    have h2 := hz w w
    rw [hz0, zero_mul, hB] at h2
    rw [GlobalTheory.RawLift.thetaIP, ← h2]
    congr 1; funext x
    rw [Complex.star_def, mul_comm]

end GlobalTheory.WeilCoefScalar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitVacAnnih

open GlobalTheory.FinPl.FrameLat

theorem trace_rankOne {k m n Y Y' : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [Fintype Y] [Fintype Y']
    (A G : Matrix m m k) (hAG : G * A = 1) (N : Matrix m n k) (B : Matrix n n k) (βT : Matrix n Y k) (βS : Matrix m Y' k)
    (γS : Matrix Y' m k) (hS : βS * γS = 1) (c : Y → k) (x : m → k) :
    Matrix.trace (A * N * B * (βT * vecMulVec c ((x ᵥ* G) ᵥ* βS) * γS)) = x ⬝ᵥ (N * B) *ᵥ (βT *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hS,
    Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc A, ← Matrix.mul_assoc G, hAG, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_of_char {ψk : AddChar k Circle} (h : HasConductor ψk 1) {b : k} (hb : ∀ a ∈ 𝒪[k], ψk (a * b) = 1) :
    b ∈ 𝒪[k] := by
  by_cases h0 : b = 0
  · rw [h0]; exact zero_mem _
  have h1 := (h b).1 fun t ht => by
    have := hb (t / b) (by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ ht zero_le)
    rwa [div_mul_cancel₀ _ h0] at this
  rw [Valuation.mem_integer_iff]
  simpa using h1

theorem annihilator_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ y : WO S T, IsHalf (cA D q.e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → y ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT ψ ψk _ hχ hc y hy hann
  have hce : cA D q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
    rw [← sec_one q]
    exact ⟨csec_mem_idAt 1, (cA_int_iff _).2 (sec_mem_intAt q 1 (one_mem _)).2⟩
  have hcs : ∀ a : AE D, cA D (q.sec (q.pr (cA D a))) = cA D q.e * a := fun a => by
    rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
  have hgram : ∀ (V : HSp D) i j, q.pr (cA D (incA D (V.gram i j))) = (V.gram.map (q.pr.comp (incA D))) j i :=
    fun V i j => by rw [cA_incA, GlobalTheory.LatVac.gram_star]; rfl
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hU.2 T LT]
  refine ⟨fun i j => ?_, fun x hx => ?_⟩
  · rw [← hy i j]
    exact Ideal.mul_mem_right _ _ hce.1
  set N : Matrix (Fin S.rank) (Fin T.rank) k := Matrix.of fun b c => q.pr (cA D (y c b)) with hN
  set x' : Fin S.rank → k := fun j => q.pr (cA D (x j)) with hx'
  have hyN : y = N.transpose.map fun a => cA D ((ofSplit q).ι a) := by
    ext i j
    exact ((hcs _).trans (hy i j)).symm
  have hx1 : (fun j => cA D (q.sec (x' j))) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    have := smul_mem hS hx hce
    convert this using 1
    funext j
    exact hcs _
  have hyx : (y : Matrix _ _ (AE D)) *ᵥ x = fun i => cA D (q.sec ((x' ᵥ* N) i)) := by
    funext i
    have : (x' ᵥ* N) i = q.pr (cA D (((y : Matrix _ _ (AE D)) *ᵥ x) i)) := by

      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, RingHom.map_mul, hN, hx', Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hcs]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hy i j]
  show (y : Matrix _ _ (AE D)) *ᵥ x ∈ _
  rw [hyx, csec_mem_iff hT]
  intro u hu
  have huc : FT.β *ᵥ (FT.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, FT.βγ, Matrix.one_mulVec]
  have hcint : ∀ i, (FT.γ *ᵥ u) i ∈ 𝒪[k] := (hFT _).2 (by rw [huc]; exact hu)
  set f := q.pr.comp (incA D) with hf
  have hrow : ∀ s, ((x' ᵥ* S.gram.map f) ᵥ* FS.β) s ∈ 𝒪[k] := fun s => by
    have h1 := (csec_mem_iff hS x').1 hx1 _ ((hFS (Pi.single s 1)).1 fun i => by
      by_cases h : i = s
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
    convert h1 using 1
    simp only [hgram, Matrix.mulVec_single_one, Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.col, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine int_of_char hc fun a ha => ?_
  have h2 := hann (vecMulVec (a • (FT.γ *ᵥ u)) ((x' ᵥ* S.gram.map f) ᵥ* FS.β)) fun r s =>
    mul_mem (mul_mem ha (hcint r)) (hrow s)
  have hA : S.gram.map f * (S.gram⁻¹).map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero f) (map_one f)]
  rw [GlobalTheory.LocSympl.psi_sympl_up _ FS FT ψ ψk hχ, hyN, GlobalTheory.LocSympl.pi_hO_up] at h2
  have h3 := trace_rankOne _ _ hA N (T.gram.map f) FT.β FS.β FS.γ FS.βγ (a • (FT.γ *ᵥ u)) x'
  rw [Matrix.mulVec_smul, huc, Matrix.mulVec_smul, dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h3
  have h4 : ∑ i, ∑ j, u i * q.pr (cA D (incA D (T.gram i j))) * (x' ᵥ* N) j = (x' ᵥ* N) ⬝ᵥ T.gram.map f *ᵥ u := by
    rw [Finset.sum_comm]
    simp only [hgram, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h4, ← smul_eq_mul, ← h3]
  exact Circle.ext h2

end GlobalTheory.SplitVacAnnih

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩


end GlobalTheory.SeeSaw.LocPlInhab
end
end
