module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairing

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.FlatCommBF

variable {D : D7}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) (h : ν.IsHaarMeasure) : SFinite ν := by
  haveI := h
  infer_instance

theorem continuous_psiUni (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  apply _root_.GlobalTheory.FlatBase.continuous_psiUni <;> assumption

theorem jacT_integral (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) {U : Type} [MeasurableSpace U] (m : Measure U) (G : U → WO S T₀ → ℂ)
    (w : WO S T₀) : jacT ψ d S y n (fun w' => ∫ u, G u w' ∂m) w = ∫ u, jacT ψ d S y n (G u) w ∂m := by
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]

theorem jacT_smul (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) (c : ℂ) (f : WO S T₀ → ℂ) :
    jacT ψ d S y n (c • f) = c • jacT ψ d S y n f := by
  funext w
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  ring



theorem flat_om_of_decompositions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ)
    (V V₀ W W₀ A L : HSp D) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (s : Step ψ V V₀ W W₀ ρ ρ) (om' : Om V₀ W), IsWeilDatumO ψ V₀ W s.χV s.χW om' → ∀ (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ h₀, ∀ n ∈ radX dW, ∀ h', (flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) (s.om (embA dV o h₀, n * dW.emb0 h') Ψ) = s.om₀ (o.emb (h₀, 1), 1) (opA ψ dW o ζ s.om₀ n h' ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) Ψ)) := by
  intro D ψ ρ V V₀ W W₀ A L dV dW o ζ s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D W W₀ ρ dW
  have hlin : LinearIndependent D.host.E dW.e.transpose := hbase.1
  have hev := GlobalTheory.Unf.evalAt_xZero_yZero_rad_of_decompositions D ψ ρ V V₀ W W₀ A L dV dW o ζ s om' hom' Ψ hΨ
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1)
      (yZero V₀ ρ (vecB o ζ)) = s.om₀ (1, h') (evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero dW ⬝ u.1.1)
      (yZero V₀ ρ (vecB o ζ))) := by
    intro u
    have h := hev u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1)
      (yZero V₀ ρ (vecB o ζ)) = opA ψ dW o ζ s.om₀ n h' (evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ))) := by
    intro u
    have h := hev u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ V W Φ → ∀ u : UX D ρ, IsThetaFunO ψ V₀ W₀
      (evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ))) :=
    fun Φ hΦ u => hmix.2 V₀ W W₀ ρ dW s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 V V₀ W ρ dV s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ V W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ ρ dV dW s.vS s.vT s.vU dW.e hlin
    (yZero V₀ ρ (vecB o ζ))
  have thflat : ∀ p, IsThetaFunO ψ V₀ W₀ ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ V V₀ W W₀ ρ ρ dV dW s.vS s.vT s.χV s.χW s.om s.weil s.vU dW.e hlin
    Ψ hΨ {1, (1, dW.emb0 h'), (1, n * dW.emb0 h'), (embA dV o h₀, n * dW.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, dW.emb0 h'), (1, n * dW.emb0 h'), (embA dV o h₀, n * dW.emb0 h')} :
      Set (GA D V × GA D W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W₀ ρ ρ dV dW s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero dW ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO V₀ W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero dW ⬝ q.1.1.1) (yZero V₀ ρ (vecB o ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO V₀ W₀ => ((p, xZero dW ⬝ q.1.1.1, yZero V₀ ρ (vecB o ζ), q.2) :
        (GA D V × GA D W) × Mx D W.rank ρ × Mx D V₀.rank ρ × WO V₀ W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO V₀ W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ V₀ W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) = star (psiUni ψ u.1) • evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA dV o h₀, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA dV o h₀, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) (o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ dW o ζ s.om₀ n h' ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ dW V₀ (yZero V₀ ρ (vecB o ζ)) n (s.om₀ (1, h') ((flat ψ dV o ζ dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν) Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, dW.emb0 h') Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero dW ⬝ u.1.1) (yZero V₀ ρ (vecB o ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

theorem flatBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  exact flat_om_of_decompositions D ψ ρ B.V B.V₀ J.W J.W₀ B.A B.L B.d J.d B.o B.ζ s om' hom' Ψ hΨ

end GlobalTheory.Unf.FlatCommBF
