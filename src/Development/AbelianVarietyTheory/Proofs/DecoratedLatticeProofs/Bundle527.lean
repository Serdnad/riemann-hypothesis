module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause lagr evZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.SwSecMem

variable {D : D7} (A B : HSp D) (omh : WRep (dblSp A) B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def intSub : Submodule ℂ (WO (dblSp A) B → ℂ) where
  carrier := {f | ∀ g : GA D (dblSp A), IntegrableOn (fun w => omh (g, 1) f (lagr A B w)) 𝓕 ν}
  zero_mem' g := by
    simp only [map_zero, Pi.zero_apply]
    exact integrableOn_zero
  add_mem' {f f'} hf hf' g := by
    simp only [map_add (f := _), Pi.add_apply]
    exact Integrable.add (hf g) (hf' g)
  smul_mem' c f hf g := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact Integrable.const_mul (hf g) c

def swLin : intSub A B omh ν 𝓕 →ₗ[ℂ] (GA D (dblSp A) → ℂ) where
  toFun f := swSec A B omh ν 𝓕 f
  map_add' f f' := by
    funext g
    simp only [swSec, evZero, Submodule.coe_add, map_add (f := _), Pi.add_apply]
    exact integral_add (f.2 g) (f'.2 g)
  map_smul' c f := by
    funext g
    simp only [swSec, evZero, Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem swSec_mul (φ : WO (dblSp A) B → ℂ) (g k : GA D (dblSp A)) :
    swSec A B omh ν 𝓕 φ (g * k) = swSec A B omh ν 𝓕 (omh (k, 1) φ) g := by
  have : ((g * k, 1) : GA D (dblSp A) × GA D B) = (g, 1) * (k, 1) := by simp
  simp only [swSec]
  rw [this, map_mul, Module.End.mul_apply]

theorem swSec_mem_degPS : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  intro hW D ψ A B χB omh hω ν 𝓕 hν φ hφ a hK
  have hint : ∀ f, IsThetaFunO ψ (dblSp A) B f → f ∈ intSub A B omh ν 𝓕 := fun f hf g =>
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν _ (hω.om_pres (g, 1) f hf)).1
  refine (mem_degPS A a).2 ⟨GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh hω ν 𝓕 hν φ hφ,
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν φ hφ).2, ?_⟩
  let S := Submodule.span ℂ {f : WO (dblSp A) B → ℂ | ∃ k ∈ Khat A a, f = omh (k, 1) φ}
  haveI : FiniteDimensional ℂ S := hK
  have hS : S ≤ intSub A B omh ν 𝓕 := Submodule.span_le.2 (by
    rintro _ ⟨k, -, rfl⟩
    exact hint _ (hω.om_pres _ _ hφ))
  refine isKFinite_iff.2 ⟨LinearMap.range ((swLin A B omh ν 𝓕).comp (Submodule.inclusion hS)), inferInstance,
    fun k hk => ⟨⟨omh (k, 1) φ, Submodule.subset_span ⟨k, hk, rfl⟩⟩, funext fun g => ?_⟩⟩
  exact (swSec_mul A B omh ν 𝓕 φ g k).symm

end GlobalTheory.SwSecMem

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.EvalAtZero

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem det_UX {ρ : ℕ} (γ : UX D ρ) : Matrix.GeneralLinearGroup.det γ.1 = 1 := by
  have hu : γ.1 ∈ UX D ρ := γ.2
  rw [mem_UX] at hu
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hT : (γ.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)).BlockTriangular id := fun i j hij => (hu i j).1 hij
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

end GlobalTheory.EvalAtZero

namespace GlobalTheory.EvalAtZero

theorem halfMod_UX {D : D7} {ρ : ℕ} (n : ℕ) (γ : UX D ρ) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n γ.1 = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_UX, map_one, NNReal.coe_one, Real.one_rpow]

end GlobalTheory.EvalAtZero


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_rad : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d).2.1 n).1 hn
  set k := J.d.nB b * J.d.nC c * J.d.emb0 h' with hk
  have hks : k ∈ stabX J.d := mul_mem (radX_le_stabX J.d hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d h')
  have hkx : mt J.W k⁻¹ ⬝ J.d.jX = J.d.jX := inv_mem hks

  have e1 : (embA B.d B.o h₀, k) = (embA B.d B.o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1) =
      om' (B.o.emb (h₀, 1), 1) (om' (1, k) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1))) := by
    have hc := (FS _ hk1).core (B.o.emb (h₀, 1)) (xZero J.d ⬝ u.1.1)
    have ht := (FS _ hΨ).target k (xZero J.d ⬝ u.1.1)
    change B.d.mixS _ _ _ _ _ _ = _ at hc
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, hc, ht, ← Matrix.mul_assoc,
      xZero, hkx]
    rfl
  set G := B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ B.V₀ J.W G := MV _

  have e2 : ((1 : GA D B.V₀), k) = (1, J.d.nB b) * ((1, J.d.nC c) * (1, J.d.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, J.d.emb0 h') G hGt
  have h2 := hom'.om_pres (1, J.d.nC c) _ h3
  have hy : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.V₀ J.W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC J.d B.V₀ y₀ b 0, J.d.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = J.d.qT B.V₀ c y₀ :=
    (GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant D ψ J.W J.W₀ B.V₀ ρ J.d y₀ (fun v hv => yZero_mul B.V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (B.o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, J.d.nB b) (om' (1, J.d.nC c) (om' (1, J.d.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [s1, t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (B.o.emb (h₀, 1), 1) (jacT ψ J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]
  rfl


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_levi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u γ
  have e0 : (mt J.W (J.d.levi γ.1)⁻¹ ⬝ (xZero J.d ⬝ u.1.1) : Mx D J.W.rank ρ) = xZero J.d ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d) J.W ψ s.vS.μ s.vS.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [(FS _ hΨ).target, e0, (FT _ (MV _)).levi, yZero_mul B.V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  rfl

theorem GlobalTheory.Unf.evalAt_xZero_yZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
  fun D ψ ρ B J s om' hom' Ψ hΨ => ⟨GlobalTheory.Unf.evalAt_xZero_yZero_rad D ψ ρ B J s om' hom' Ψ hΨ,
    GlobalTheory.Unf.evalAt_xZero_yZero_levi D ψ ρ B J s om' hom' Ψ hΨ⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing MeasureTheory

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.VLast.Transport

section RankZero

variable {D : D7} {S S₀ : HSp D} (d : HypDec S S₀ 0)

theorem rz_gA : gA S = adj d.p0 ⬝ (gA S₀ ⬝ d.p0) := by
  rw [d.gA_eq, Subsingleton.elim d.pX 0, Subsingleton.elim d.pY 0]
  simp

theorem rz_j0p0 : d.j0 ⬝ d.p0 = 1 := by
  have := d.sum_eq_one
  rwa [Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0, Matrix.zero_mul, Matrix.zero_mul, zero_add, add_zero] at this

theorem unitaryMatrix_rankZeroWittEmbedding_eq (g : GA D S₀) : mt S (d.emb0 g) = d.j0 ⬝ mt S₀ g ⬝ d.p0 := by
  rw [d.unitaryMatrix_wittCoreEmbedding, Subsingleton.elim d.jX 0, Subsingleton.elim d.jY 0]
  simp

theorem rz_unit (g : GA D S) : adj (d.p0 ⬝ mt S g ⬝ d.j0) ⬝ (gA S₀ ⬝ (d.p0 ⬝ mt S g ⬝ d.j0)) = gA S₀ := by
  have key : ∀ X : Mx D S.rank S₀.rank, adj d.p0 ⬝ (gA S₀ ⬝ (d.p0 ⬝ X)) = gA S ⬝ X := fun X => by
    rw [rz_gA d, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [adj_mul, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [key, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
  exact d.gram_00

def rzInv (g : GA D S) : GA D S₀ := ofMat S₀ (d.p0 ⬝ mt S g ⬝ d.j0) (rz_unit d g)

theorem mt_rzInv (g : GA D S) : mt S₀ (rzInv d g) = d.p0 ⬝ mt S g ⬝ d.j0 := mt_ofMat _ _ _

def rzEquiv : GA D S₀ ≃* GA D S where
  toFun := d.emb0
  invFun := rzInv d
  left_inv g := mt_injective S₀ (by
    rw [mt_rzInv, unitaryMatrix_rankZeroWittEmbedding_eq]
    simp only [Matrix.mul_assoc, d.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul])
  right_inv g := mt_injective S (by
    rw [unitaryMatrix_rankZeroWittEmbedding_eq, mt_rzInv]
    simp only [Matrix.mul_assoc, rz_j0p0 d, Matrix.mul_one]
    rw [← Matrix.mul_assoc, rz_j0p0 d, Matrix.one_mul])
  map_mul' := map_mul d.emb0

theorem rzInv_continuous : Continuous (rzInv d) :=
  continuous_of_mt S₀ (by
    simp only [mt_rzInv]
    exact (continuous_const.matrix_mul (continuous_mt S)).matrix_mul continuous_const)

theorem rzInv_mem_GQ {g : GA D S} (hg : g ∈ GQ S) : rzInv d g ∈ GQ S₀ := by
  rw [mem_GQ_iff, mt_rzInv]
  exact ratMx_mul (ratMx_mul (rat_mem _) ((mem_GQ_iff S g).1 hg)) (rat_mem _)

end RankZero

theorem weilRep_rankZeroWittEmbedding_valueAtZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ f, IsThetaFunO ψ S T f → ∀ (g₀ : GA D S₀) (h : GA D T), om (d.emb0 g₀, h) f 0 = om₀ (g₀, h) (fun w => f (d.ext0 T w)) 0 := by
  intro D ψ S S₀ T d χS χT om om₀ hom hom₀ f hf g₀ h
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne (D := D) (m := T.rank) (n := 0)
  have hF := GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T 0 d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  have H1 := (hF (om (1, h) f) (hom.om_pres _ _ hf)).core g₀ 0
  have H2 := (hF f hf).target h 0
  have hS : ∀ F x, _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 F x =
      fun w => F (d.ext0 T w) := mixS_rankZero ψ S S₀ T d μ 𝓕 hμ
  simp only [hS] at H1 H2
  rw [H2] at H1
  have e1 : ((d.emb0 g₀, h) : GA D S × GA D T) = (d.emb0 g₀, 1) * (1, h) := by simp
  have e2 : ((g₀, h) : GA D S₀ × GA D T) = (g₀, 1) * (1, h) := by simp
  have := congrFun H1 0
  simp only [map_zero] at this
  rw [e1, e2, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  exact this

theorem om_flatBF_rankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D 0) (J : JacLev D 0) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (h₀ : GA D B.A) (g₀ : GA D J.W₀), s.om (embA B.d B.o h₀, J.d.emb0 g₀) Ψ 0 = s.om₀ (B.o.emb (h₀, 1), g₀) (flatBF s Ψ) 0 := by
  intro D ψ B J s Ψ hΨ h₀ g₀
  have hflat : ∀ X, flatBF s X = evalBF s X := by
    intro X; funext w
    obtain ⟨-, 𝓤, -, h1⟩ := s.vU.unit
    have : Subsingleton (UX D 0) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have hU : 𝓤 = Set.univ := by
      rcases Set.eq_empty_or_nonempty 𝓤 with he | ⟨x, hx⟩
      · rw [he, measure_empty] at h1; exact absurd h1 zero_ne_one
      · exact Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
    have huniv : s.vU.ν Set.univ = 1 := hU ▸ h1
    have : IsProbabilityMeasure s.vU.ν := ⟨huniv⟩
    have hc : ∀ u : UX D 0, flatFun ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (xZero J.d) (yZero B.V₀ 0 (vecB B.o B.ζ)) X w u = evalBF s X w := by
      intro u
      simp only [flatFun, evalBF, evalZero]
      rw [Subsingleton.elim (xZero J.d ⬝ u.1.1) (xZero J.d)]
      simp [psiUni, upSum, psiE]
    simp only [flatBF, flat, flatAt, hc, integral_const, probReal_univ, one_smul]
  have hd := GlobalTheory.T.weilDatum_descends_to_wittCore D
  have hm : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedModelFormulas D := ⟨GlobalTheory.T.mixedModelFormulasWittSource_proof D, GlobalTheory.T.mixedModelFormulas_wittTarget D⟩
  have hv := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D
  rw [hflat, GlobalTheory.Unf.EvalCont.om_evalBF s hd hm hv hΨ h₀ g₀]
  unfold evalBF evalZero evalAt
  have hT : ∀ F y, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕 F y =
      fun w => F (J.d.inc0 B.V₀ w) := mixT_rankZero ψ _ _ _ J.d s.vT.μ s.vT.𝓕 s.vT.covol
  have hS : ∀ F x, _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source B.d J.W ψ s.vS.μ s.vS.𝓕 F x =
      fun w => F (B.d.ext0 J.W w) := mixS_rankZero ψ _ _ _ B.d s.vS.μ s.vS.𝓕 s.vS.covol
  rw [hT, hS]
  simp only [map_zero]

end GlobalTheory.FinPl.VLast.Transport

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf



theorem integral_base_term_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 hlay hfin
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank vb vU
  haveI : IsFiniteMeasure (vb.μ.restrict vb.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vb.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hψ1 : ∀ x, star (ψ x) * ψ x = 1 := fun x => by
    rw [Complex.star_def, Complex.conj_mul', hω.std.1.2.1 x]; norm_num
  have hq0 : d.qS W 0 (rat x₀) = 0 := by
    simp [HypDec.qS, symplOH, symplO, hO]
  set F : flagN d × GA D W → ℂ := fun p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ with hFdef
  have hFm : Measurable F := by
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hint : Integrable F ((vN.ν.restrict 𝓐).prod (vW.μ.restrict 𝓑)) := by
    rw [Measure.prod_restrict]
    exact ⟨hFm.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hpm : Measurable (Function.uncurry fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) :=
    (d.continuous_nB.measurable.comp measurable_snd).mul
      ((d.continuous_levi.comp continuous_subtype_val).measurable.comp measurable_fst)
  have hfib : ∀ h, Integrable (fun n => F (n, h)) (vN.ν.restrict 𝓐) →
      ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
    intro h hih
    classical
    have hΨ := hω.om_pres (1, h) Φ hΦ
    set f : GA D V → ℂ := (flagN d : Set (GA D V)).piecewise
      (fun g => Th g * G h * term ψ d W vS (om (g, h) Φ) x₀) 0 with hfdef
    have hfm : Measurable f := by
      refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)).measurableSet
      refine ((continuousOn_iff_continuous_restrict.2 hTh.cont).mul continuousOn_const).mul ?_
      exact (((hTL Φ hΦ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).continuousOn
    have hfF : ∀ n : flagN d, f n.1 = F (n, h) := fun n => Set.piecewise_eq_of_mem _ _ _ n.2
    have hcen : ∀ (c : skewA D ρ) (n : GA D V), n ∈ flagN d →
        term ψ d W vS (om (d.nC c * n, h) Φ) x₀ = ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀ := by
      intro c n hn
      have hΨ' := hω.om_pres (n, h) Φ hΦ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      rw [t1]
      simp [term]
    have hfinv : ∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)),
        f (t n) = f n := by
      rintro t ⟨c, rfl⟩ n hn
      have hm : d.nC c * n ∈ (flagN d : Set (GA D V)) := mul_mem (d.nC_mem_NFlag c) hn
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, Set.piecewise_eq_of_mem _ _ _ hn, hTh.cen c n hn, hcen c n hn]
      calc star (ψ (d.qS W c (rat x₀))) * Th n * G h * (ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀)
          = (star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x₀))) * (Th n * G h * term ψ d W vS (om (n, h) Φ) x₀) := by
            ring
        _ = _ := by rw [hψ1, one_mul]
    have hcoord : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        f (d.nB b * d.levi u.1) = G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b := by
      intro u b
      have hm : d.nB b * d.levi u.1 ∈ (flagN d : Set (GA D V)) := mul_mem (d.nB_mem_NFlag b) (d.levi_mem_NFlag u.2)
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul, hq0, AddChar.map_zero_eq_one, one_mul] at t1
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, hsplit, t1, flFun]
      ring
    have hlay' : ∀ g : GA D V → ENNReal, Measurable g →
        (∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)), g (t n) = g n) →
        ∫⁻ x, g (Subtype.val x) ∂(vN.ν.restrict 𝓐) =
          ∫⁻ u, ∫⁻ y, g ((fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) u y) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν :=
      fun g hg hinv => hlay g hg fun c n hn => hinv _ ⟨c, rfl⟩ n hn
    have hih' : Integrable (fun x : flagN d => f x.1) (vN.ν.restrict 𝓐) := by
      refine hih.congr (ae_of_all _ fun n => (hfF n).symm)
    obtain ⟨-, heq⟩ := GlobalTheory.T.lowerIntegral_to_integral_coordinates (flagN d) (UX D ρ) (Mx D ρ V₀.rank) (GA D V) (vN.ν.restrict 𝓐) vU.ν
      (vb.μ.restrict vb.𝓕) Subtype.val (fun u b => d.nB b * d.levi u.1) (fun t => ∃ c, t = (d.nC c * ·))
      measurable_subtype_coe hpm (flagN d) hlay' f hfm hfinv hih'
    calc ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = ∫ x, f x.1 ∂(vN.ν.restrict 𝓐) :=
          integral_congr_ae (ae_of_all _ fun n => (hfF n).symm)
      _ = ∫ u, ∫ b, f (d.nB b * d.levi u.1) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := heq
      _ = ∫ u, ∫ b, G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          exact integral_congr_ae (ae_of_all _ fun b => hcoord u b)
      _ = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
          simp only [integral_const_mul]; rfl
  have hae := hint.prod_left_ae
  have hI := hint.integral_prod_right
  have hEq : (fun h => ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐)) =ᵐ[vW.μ.restrict 𝓑]
      fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := hae.mono fun h hh => hfib h hh
  refine ⟨hI.congr hEq, ?_⟩
  rw [← Measure.prod_restrict, integral_prod_symm F hint]
  exact integral_congr_ae hEq

end GlobalTheory.Unf

end
end
