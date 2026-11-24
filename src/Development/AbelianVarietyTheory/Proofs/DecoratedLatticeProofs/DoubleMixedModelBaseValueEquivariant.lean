module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittTargetStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariantStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedCoordinates

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.EvalAtZero

variable {D : D7}

alias heisO_smul := _root_.GlobalTheory.SplitScalar.heisO_smul

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
theorem GlobalTheory.Unf.evalAt_xZero_yZero_rad_of_decompositions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ)
    (V V₀ W W₀ A L : HSp D) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (s : Step ψ V V₀ W W₀ ρ ρ) (om' : Om V₀ W), IsWeilDatumO ψ V₀ W s.χV s.χW om' → ∀ (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (u : UX D ρ) h₀, ∀ n ∈ radX dW, ∀ h', evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA dV o h₀, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) = s.om₀ (o.emb (h₀, 1), 1) (opA ψ dW o ζ s.om₀ n h' (evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)))) := by
  intro D ψ ρ V V₀ W W₀ A L dV dW o ζ s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ dV s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ V₀ W W₀ ρ dW s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 V V₀ W ρ dV s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero V₀ ρ (vecB o ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D W W₀ ρ dW).2.1 n).1 hn
  set k := dW.nB b * dW.nC c * dW.emb0 h' with hk
  have hks : k ∈ stabX dW := mul_mem (radX_le_stabX dW hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic dW h')
  have hkx : mt W k⁻¹ ⬝ dW.jX = dW.jX := inv_mem hks

  have e1 : (embA dV o h₀, k) = (embA dV o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (embA dV o h₀, k) Ψ) (xZero dW ⬝ u.1.1) =
      om' (o.emb (h₀, 1), 1) (om' (1, k) (dV.mixS W ψ s.vS.μ s.vS.𝓕 Ψ (xZero dW ⬝ u.1.1))) := by
    have hc := (FS _ hk1).core (o.emb (h₀, 1)) (xZero dW ⬝ u.1.1)
    have ht := (FS _ hΨ).target k (xZero dW ⬝ u.1.1)
    change dV.mixS _ _ _ _ _ _ = _ at hc
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, hc, ht, ← Matrix.mul_assoc,
      xZero, hkx]
    rfl
  set G := dV.mixS W ψ s.vS.μ s.vS.𝓕 Ψ (xZero dW ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ V₀ W G := MV _

  have e2 : ((1 : GA D V₀), k) = (1, dW.nB b) * ((1, dW.nC c) * (1, dW.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, dW.emb0 h') G hGt
  have h2 := hom'.om_pres (1, dW.nC c) _ h3
  have hy : mt V₀ (o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT dW V₀ y₀ (dW.nB b * dW.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj V₀ W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC dW V₀ y₀ b 0, dW.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT dW V₀ y₀ (dW.nB b * dW.nC c) = dW.qT V₀ c y₀ :=
    (GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant D ψ W W₀ V₀ ρ dW y₀ (fun v hv => yZero_mul V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, dW.nB b) (om' (1, dW.nC c) (om' (1, dW.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  change (_root_.I195MixedCoordinates.target dW) V₀ ψ s.vT.μ s.vT.𝓕 (dV.mixS W ψ s.vS.μ s.vS.𝓕 (s.om (embA dV o h₀, k) Ψ) (xZero dW ⬝ u.1.1)) y₀ = _
  rw [s1, t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (o.emb (h₀, 1), 1) (jacT ψ dW V₀ y₀ (dW.nB b * dW.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]
  rfl

open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_rad : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  exact _root_.GlobalTheory.Unf.evalAt_xZero_yZero_rad_of_decompositions D ψ ρ B.V B.V₀ J.W J.W₀ B.A B.L B.d J.d B.o B.ζ s om' hom' Ψ hΨ

open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_levi_of_decompositions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ)
    (V V₀ W W₀ A L : HSp D) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (s : Step ψ V V₀ W W₀ ρ ρ) (om' : Om V₀ W), IsWeilDatumO ψ V₀ W s.χV s.χW om' → ∀ (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (u γ : UX D ρ), evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.levi γ.1) Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) = evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero dW ⬝ (γ⁻¹ * u).1.1) (yZero V₀ ρ (vecB o ζ)) := by
  intro D ψ ρ V V₀ W W₀ A L dV dW o ζ s om' hom' Ψ hΨ
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ V V₀ W ρ dV s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => GlobalTheory.T.mixedModelFormulas_wittTarget D ψ V₀ W W₀ ρ dW s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ s.weil.std).1 V V₀ W ρ dV s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero V₀ ρ (vecB o ζ) with hy₀
  intro u γ
  have e0 : (mt W (dW.levi γ.1)⁻¹ ⬝ (xZero dW ⬝ u.1.1) : Mx D W.rank ρ) = xZero dW ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  change (_root_.I195MixedCoordinates.target dW) V₀ ψ s.vT.μ s.vT.𝓕 ((_root_.I195MixedCoordinates.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (1, dW.levi γ.1) Ψ) (xZero dW ⬝ u.1.1)) y₀ = _
  rw [(FS _ hΨ).target, e0, (FT _ (MV _)).levi, yZero_mul V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  rfl

open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_levi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  exact _root_.GlobalTheory.Unf.evalAt_xZero_yZero_levi_of_decompositions D ψ ρ B.V B.V₀ J.W J.W₀ B.A B.L B.d J.d B.o B.ζ s om' hom' Ψ hΨ

theorem GlobalTheory.Unf.evalAt_xZero_yZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
  fun D ψ ρ B J s om' hom' Ψ hΨ => ⟨GlobalTheory.Unf.evalAt_xZero_yZero_rad D ψ ρ B J s om' hom' Ψ hΨ,
    GlobalTheory.Unf.evalAt_xZero_yZero_levi D ψ ρ B J s om' hom' Ψ hΨ⟩
