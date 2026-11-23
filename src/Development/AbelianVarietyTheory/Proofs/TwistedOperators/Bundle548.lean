module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle299
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompOfIsTraceClass
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle542
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle541
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle472
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixParseval


set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem parseval : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ₀ : Measure (WO V W)) (𝓕₀ : Set (WO V W)), IsCovolOne (ratL W V) μ₀ 𝓕₀ → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), IsCovolOne (ratL W V') μ' 𝓕' → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → Continuous (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∧ Integrable (fun u : Mx D W.rank r => ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') μ ∧ ∫ w in 𝓕₀, f₁ w * starRingEnd ℂ (f₂ w) ∂μ₀ = ∫ u : Mx D W.rank r, (∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f₂) x) ∂μ') ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μ₀ 𝓕₀ hμ₀ μ' 𝓕' hμ' f₁ f₂ hf₁ hf₂
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, hμ'.2.2]; exact ENNReal.one_lt_top⟩
  let R : (WO V W → ℂ) → WO V' W → Mx D W.rank r → ℂ := fun f x u =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x
  let h : WO V' W → Mx D W.rank r → ℂ := fun x u => R f₁ x u * starRingEnd ℂ (R f₂ x u)
  obtain ⟨hc₁, M₁, hM₁⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₁ hf₁
  obtain ⟨hc₂, M₂, hM₂⟩ := GlobalTheory.T.restrictedHeisenbergTheta_continuous_bounded D V V' W r C C' B ψ hψ μ 𝓨 hμ f₂ hf₂
  have hhc : Continuous (Function.uncurry h) := hc₁.mul (Complex.continuous_conj.comp hc₂)
  have hhb : ∀ x u, ‖h x u‖ ≤ M₁ * M₂ := fun x u => by
    show ‖R f₁ x u * starRingEnd ℂ (R f₂ x u)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM₁ x u) (hM₂ x u) (norm_nonneg _) ((norm_nonneg _).trans (hM₁ x u))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf₂
  have hYr : μ.real 𝓨 = 1 := by simp [Measure.real, hμ.2.2]
  have hsq : ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ Cf : ℝ, (∀ w, ‖f w‖ ≤ Cf) → ∀ x u,
      Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 ≤ Cf ^ 2 := by
    intro f hf Cf hCf x u
    obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f f hf hf x u
    have e : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        ‖R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u))‖ = ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      fun ξ => by rw [norm_mul, Complex.norm_conj, sq]
    have hsum : Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖R f x (ξ.map (incA D) + u)‖ ^ 2) :=
      hs1.congr e
    refine ⟨hsum, ?_⟩
    have e2 : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
        R f x (ξ.map (incA D) + u) * starRingEnd ℂ (R f x (ξ.map (incA D) + u)) =
          ((‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hI := hs2.tsum_eq
    have hI' : ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ) =
        ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y +
          GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ := by
      rw [Complex.ofReal_tsum, ← hI]
      exact tsum_congr fun ξ => (e2 ξ).symm
    have hnn : 0 ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 :=
      tsum_nonneg fun _ => by positivity
    have hb : ∀ w, ‖f w * starRingEnd ℂ (f w)‖ ≤ Cf ^ 2 := fun w => by
      rw [norm_mul, Complex.norm_conj, ← sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCf w) 2
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2
        = ‖((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f x (ξ.map (incA D) + u)‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ Cf ^ 2 * (μ.restrict 𝓨).real Set.univ := by
          rw [hI']
          exact norm_integral_le_of_norm_le_const (.of_forall fun y => hb _)
      _ = Cf ^ 2 := by simp [Measure.real, Measure.restrict_apply_univ, hμ.2.2]
  have hb : ∀ x u, Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧
      ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by
    intro x u
    obtain ⟨s1, t1⟩ := hsq f₁ hf₁ C₁ hC₁ x u
    obtain ⟨s2, t2⟩ := hsq f₂ hf₂ C₂ hC₂ x u
    have hle : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤
        (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := fun ξ => by
      show ‖R f₁ x (ξ.map (incA D) + u) * starRingEnd ℂ (R f₂ x (ξ.map (incA D) + u))‖ ≤ _
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖R f₁ x (ξ.map (incA D) + u)‖ - ‖R f₂ x (ξ.map (incA D) + u)‖)]
    have hs' := (s1.add s2).div_const 2
    refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs', ?_⟩
    calc ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖h x (ξ.map (incA D) + u)‖
        ≤ ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
            (‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2 + ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs').tsum_le_tsum hle hs'
      _ = ((∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₁ x (ξ.map (incA D) + u)‖ ^ 2) +
            ∑' ξ : Matrix (Fin W.rank) (Fin r) D.host.E, ‖R f₂ x (ξ.map (incA D) + u)‖ ^ 2) / 2 := by
          rw [tsum_div_const, s1.tsum_add s2]
      _ ≤ (C₁ ^ 2 + C₂ ^ 2) / 2 := by linarith
  obtain ⟨hint, hEq⟩ := GlobalTheory.T.integral_parametric_unfold_rationalTranslates D W.rank r (WO V' W) (μ'.restrict 𝓕') μ 𝓨 hμ h hhc _ hb
  have a1 : ∀ x, Continuous (h x) := fun x => hhc.uncurry_left x
  have a2 : ∀ u, Continuous (fun x => h x u) := fun u => hhc.uncurry_right u
  have a3 : ∀ u, AEStronglyMeasurable (fun x => h x u) (μ'.restrict 𝓕') := fun u => (a2 u).aestronglyMeasurable
  haveI : FirstCountableTopology (Mx D W.rank r) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hG : Continuous (fun u => ∫ x, h x u ∂(μ'.restrict 𝓕')) :=
    continuous_of_dominated (bound := fun _ => M₁ * M₂) a3
      (fun u => .of_forall fun x => hhb x u) (integrable_const _) (.of_forall a1)
  refine ⟨hG, hint, ?_⟩
  show _ = ∫ u, (∫ x, h x u ∂(μ'.restrict 𝓕')) ∂μ
  rw [hEq]
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated D V V' W r C B hs C' h1 h2 h3 μ 𝓨 hμ
    μ₀ 𝓕₀ hμ₀.1 hμ₀.2.1 μ' 𝓕' hμ'.1 hμ'.2.1
  have hκ1 : κ = 1 := by
    have e := hκ (fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ (fun _ _ _ => rfl)
    simp only [setIntegral_const, Measure.real, hμ₀.2.2, hμ.2.2, hμ'.2.2, ENNReal.toReal_one, one_smul] at e
    rw [Complex.real_smul, mul_one] at e
    exact_mod_cast e.symm
  let H : WO V W → ℂ := fun w => f₁ w * starRingEnd ℂ (f₂ w)
  have hHc : Continuous H := hf₁.cont.mul (Complex.continuous_conj.comp hf₂.cont)
  have hHb : ∃ b : ℝ, ∀ w, ‖H w‖ ≤ b := ⟨C₁ * C₂, fun w => by
    show ‖f₁ w * starRingEnd ℂ (f₂ w)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ w) (hC₂ w) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ w))⟩
  have hHp : ∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w := by
    rintro γ ⟨g, rfl⟩ w
    show f₁ (ratW W V g + w) * starRingEnd ℂ (f₂ (ratW W V g + w)) = f₁ w * starRingEnd ℂ (f₂ w)
    rw [hf₁.quasi g w, hf₂.quasi g w, map_mul]
    have hu : ∀ a, ψ a * starRingEnd ℂ (ψ a) = 1 := fun a => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1]; norm_num
    calc ψ (-symplOH V W (ratW W V g) w) * f₁ w * (starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w)) * starRingEnd ℂ (f₂ w))
        = (ψ (-symplOH V W (ratW W V g) w) * starRingEnd ℂ (ψ (-symplOH V W (ratW W V g) w))) *
            (f₁ w * starRingEnd ℂ (f₂ w)) := by ring
      _ = _ := by rw [hu, one_mul]
  show ∫ w in 𝓕₀, H w ∂μ₀ = _
  rw [hκ H hHc hHb hHp, hκ1, one_smul]
  refine integral_congr_ae (.of_forall fun t => ?_)
  have hInt : Integrable (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := by
    obtain ⟨b, hb'⟩ := hHb
    have hcont : Continuous (Function.uncurry fun y x => H (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' t +
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x)) :=
      hHc.comp ((continuous_const.add ((continuous_fst).matrix_mul continuous_const)).add
        ((continuous_snd).matrix_mul continuous_const))
    exact Integrable.of_bound hcont.aestronglyMeasurable b (.of_forall fun p => hb' _)
  show ∫ y, ∫ x, H _ ∂(μ'.restrict 𝓕') ∂(μ.restrict 𝓨) = _
  haveI : SFinite (μ'.restrict 𝓕') := instSFiniteOfSigmaFinite
  haveI : SFinite (μ.restrict 𝓨) := instSFiniteOfSigmaFinite
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (.of_forall fun x => ?_)
  have hp := (GlobalTheory.T.parseval_mixedModel_isotropic_thetaProduct D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ f₁ f₂ hf₁ hf₂ x t).2
  refine Eq.trans ?_ hp.tsum_eq.symm
  refine integral_congr_ae (.of_forall fun y => ?_)
  show H _ = H _
  congr 1
  abel

end GlobalTheory.MixParseval

end
end

section

noncomputable section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.CuspidalOpAssembly

section Compress

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem trace_comp_comp_of_comp_eq_id (S : K →L[ℂ] H) (P : H →L[ℂ] K) (hPS : ∀ y, P (S y) = y)
    {T : K →L[ℂ] K} (hT : IsTraceClass T) : trace (S ∘L T ∘L P) = trace T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := hT
  have e : S ∘L (∑ i, B i ∘L C i) ∘L P = ∑ i, (S ∘L B i) ∘L (C i ∘L P) := by
    ext x; simp
  have t : ∀ i, trace ((S ∘L B i) ∘L (C i ∘L P)) = trace (B i ∘L C i) := fun i => by
    rw [trace_comp_comm ((hB i).comp_left S) ((hC i).comp_right P), trace_comp_comm (hB i) (hC i)]
    congr 1
    ext x; simp [hPS]
  have h1 : HasSum (fun j => ⟪stdBasis (H := H) j, (S ∘L (∑ i, B i ∘L C i) ∘L P) (stdBasis (H := H) j)⟫_ℂ)
      (∑ i, trace (B i ∘L C i)) := by
    rw [e]
    simpa only [ContinuousLinearMap.sum_apply, inner_sum, t] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) =>
        hasSum_trace_comp (stdBasis (H := H)) ((hB i).comp_left S) ((hC i).comp_right P)
  have h2 : HasSum (fun j => ⟪stdBasis (H := K) j, (∑ i, B i ∘L C i) (stdBasis (H := K) j)⟫_ℂ) (∑ i, trace (B i ∘L C i)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_trace_comp (stdBasis (H := K)) (hB i) (hC i)
  exact h1.tsum_eq.trans h2.tsum_eq.symm

end Compress

theorem cuspidalOperators : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CuspidalOperators V μ := by
  intro hCT D V μ _ _ f hf h1 h2
  have c := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have m1 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ f := GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero D V μ f hf h1
  have m2 : GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ (starFn f) :=
    GlobalTheory.T.unitaryAutomorphicConvolution_mem_cuspidal_of_radical_zero D V μ (starFn f) (GlobalTheory.Orb.starFn_mem_ccAd hf) h2
  have hd := GlobalTheory.CuspSpectrum.traceIsDiagonal (μ := μ) hCT hf m2
  have hk := fun (F : DividedPowerChartLift V μ) (x : GA D V) =>
    GlobalTheory.AutomorphicL2KernelIntegral.convR_eq_integral_kernelQ (GA D V) (GQ V) μ f c.1 c.2 F x
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.hasSum_cuspidalMultiplicity_trace hCT D V μ f hf
  have etr : trace (RopG V μ f) = trace (RcuspOp V μ f) := by
    rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    exact trace_comp_comp_of_comp_eq_id _ _
      (fun y => Submodule.orthogonalProjection_mem_subspace_eq_self y) (hCT D V μ f hf)
  refine ⟨m1, fun F hF => ?_, hd.1, fun F p => ?_, fun F => ?_, hd.2.1, hd.2.2, fun c' => ?_, t1, t2, etr ▸ t3⟩
  · rw [GlobalTheory.TraceDiagonal.RopG_eq_comp c.1 c.2 m2]
    simp [Submodule.orthogonalProjection_eq_zero_iff.2 hF]
  · induction p using Quotient.inductionOn with
    | h x => exact (hk F x).1
  · refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(AutomorphicL2Pointwise.lift_Rop_eq_convR (GA D V) (GQ V) μ f
      (c.1.integrable_of_hasCompactSupport c.2) F).2] with x hx
    exact hx.trans (hk F x).2
  · exact GlobalTheory.CuspSpectrum.multIn_L2cusp_lt (GlobalTheory.Published.cuspDiscreteDecomposition_of_traceClass hCT D V μ) c'.rep.isIrr

end GlobalTheory.CuspidalOpAssembly

end
end

section

set_option autoImplicit false

namespace GlobalTheory.HeckePointLaw

theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  heckePointLaws_of_transport GlobalTheory.T.heckeIsogeny_thetaGenerator_transport

end GlobalTheory.HeckePointLaw
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option autoImplicit false

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj

theorem smul_sum_sub_mem_span {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (cf : Fin n → ℂ) (bv : Fin n → V)
    (s : ℂ) (i : Fin n) (h1 : cf i = 1) (h0 : ∀ j, i < j → cf j = 0) :
    s • ∑ j, cf j • bv j - s • bv i ∈ Submodule.span ℂ (bv '' {j | j < i}) := by
  classical
  have e1 : s • ∑ j, cf j • bv j - s • bv i = ∑ j, (s * (cf j - if j = i then 1 else 0)) • bv j := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp
  rw [e1]
  refine Submodule.sum_mem _ fun j _ => ?_
  rcases lt_trichotomy j i with hj | rfl | hj
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · simp [h1]
  · simp [h0 j hj, hj.ne']

theorem exists_lift_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {σ' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di i) ty P) (hP' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod (F.Di j) ty P')
    {p : ℕ} (hp : p.Prime)
    {y y₁ y₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy₁ : y₁ = F.u j P') (hy₂ : y₂ = F.u j P')
    (C C' : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G))
    (ψ' : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₂)
    (ψp' : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₂ ⟶ Xo.univ.t.G))
    (hC : ∀ a ∈ C, a ^ p ^ 2 = 1) (hC' : ∀ a ∈ C', a ^ p ^ 2 = 1)
    (hI : Formalism.L2.Pj.IsHkIsog p y y₁ C ψ ψp) (hI' : Formalism.L2.Pj.IsHkIsog p y y₂ C' ψ' ψp') :
    ∃ (gam gam' : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (h h' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      (∀ a b, (F.Di j).EF (gam' a) (gam' b) = (p : ℤ) ^ 2 * (F.Di i).EF a b) ∧ (∀ a, P' (gam' a) = h' (P a)) ∧
      (∀ (w : Fin g → ℂ) (v : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => (F.ex j P' z).left) (h' w) (v ≫ ψ' ≫ pullback.fst _ _)) ∧
      (h = h' → C = C') := by
  subst hy hy₁ hy₂
  obtain ⟨gam, h, h1, h2, -, h4⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp hP hP' hp hC hI
  obtain ⟨gam', h', h1', h2', -, h4'⟩ :=
    GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog _ H Dw l Xo σ' g ty F i j P P' p C' ψ' ψp' hP hP' hp hC' hI'
  refine ⟨gam, gam', h, h', h1, h2, h1', h2', fun w v hvs hd => ?_, fun hh => ?_⟩
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    refine ⟨?_, ?_⟩
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left :=
        fun z => by
          rw [← Category.assoc, hI.2.2.1, h4]
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1
    · have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ' ≫ pullback.fst _ _)
      have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ' ≫ pullback.fst _ _ = (F.ex j P' (h' z)).left :=
        fun z => by
          rw [← Category.assoc, hI'.2.2.1, h4']
          exact pullback.lift_fst _ _ _
      simp only [e1] at d1
      exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h'.toLinearMap w _).1 d1
  · rw [← hI.2.2.2.2.2.1, ← hI'.2.2.2.2.2.1]
    congr 1
    refine MonoidHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := F.ex_onto i P hP x
    rw [← h4, ← h4', hh]

end GlobalTheory.HeckeInj

namespace GlobalTheory.HeckeInj

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeEx MonoidalCategory CartesianMonoidalCategory MonObj



theorem eq_of_hkRelFr_frBor : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hU P p i hHP k x C C' z z' w t t' hz hz' ht ht' hB hB'
  obtain ⟨-, -, hall, -, -, g, e, F, ik, φ, -, hpt⟩ := hU
  obtain ⟨Pm, -, per, hPx, hv, -⟩ := hpt k x
  obtain ⟨k'', x'', t'', hB''⟩ := hall w
  obtain ⟨Pm'', -, per'', hPx'', hv'', -⟩ := hpt k'' x''
  obtain ⟨ψ, ψp, hI, hL, -⟩ := hz
  obtain ⟨ψ', ψp', hI', hL', -⟩ := hz'
  have hpp : p.Prime := hHP.2.2.2.1
  have hwx : w.x = F.u (ik k'') Pm'' := hB''.1.trans hPx''
  obtain ⟨gam, gam', h, h', hiso, hh, hiso', hh', hder, hker⟩ :=
    exists_lift_pair F (ik k) (ik k'') Pm Pm'' per per'' hpp hPx (hB.1.trans hwx) (hB'.1.trans hwx) C.1 C'.1
      ψ ψp ψ' ψp' (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C.2 ha)
      (fun a ha => GlobalTheory.HkPts.pow_eq_one hHP.2.2.2.2 C'.2 ha) hI hI'
  choose c'' hc''1 hc''2 hc''3 using hB''.2.1
  let bv : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ) := fun τ j =>
    ∑ i, Formalism.L2.Pj.toC (c'' τ j i) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ)
  have hdw : ∀ τ j, IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (bv τ j) (w.u τ j) := fun τ j =>
    (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ ((U.un k'' x'').u τ) _ (hv'' τ) (c'' τ j)
      (w.u τ j)).1 (hPx'' ▸ hc''3 τ j)
  have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm'' per''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
    have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
      apply RingHom.ext
      intro a
      ext <;> simp [epsMul]
    rw [e0]
    first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
  letI : Field (Formalism.L2.Pj.CAt σ) := inferInstanceAs (Field ℂ)
  have col : ∀ (zz : Formalism.L2.Pj.FrPt Xo c (Formalism.L2.Pj.CAt σ)) (tt : Formalism.L2.Pj.Ix Dw → (Formalism.L2.Pj.CAt σ)ˣ)
      (ψ0 : pullback Xo.univ.t.G.hom (U.un k x).x ⟶ pullback Xo.univ.t.G.hom zz.x)
      (h0 : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ τ j, Formalism.L2.Pj.IsLieImageH p ψ0 ((U.un k x).u τ j) (zz.u τ j)) →
      (∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (U.un k x).x),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex (ik k'') Pm'' z).left) (h0 w) (v ≫ ψ0 ≫ pullback.fst _ _)) →
      (∀ j, j ≠ none → tt j = 1) → Formalism.L2.Pj.FrBor tt w zz →
      ∀ τ m, h0 (Pi.single (e.symm ⟨τ, m⟩) 1) - (p : ℂ) • bv τ m ∈
        Submodule.span ℂ (bv τ '' {j | j < m}) := by
    intro zz tt ψ0 h0 hL0 hder0 ht0 hB0 τ m
    choose cf hcf1 hcf2 hcf3 using hB0.2.1
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL0 τ m
    have d2 := hder0 (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hv τ m; rw [← hw1] at q; exact q)
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm'' per'' _ (w.u τ) _ (hdw τ) (cf τ m)
      (zz.u τ m)).1 (hwx ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e3 : spMap (epsMul (p : ℂ)) ≫ zz.u τ m = wv ≫ ψ0 ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3]
    refine smul_sum_sub_mem_span (fun j => Formalism.L2.Pj.toC (cf τ m j)) (bv τ) _ m ?_ fun j hj => ?_
    · show Formalism.L2.Pj.toC (cf τ m m) = 1
      rw [hcf1 τ m, ht0 _ (by simp)]
      rfl
    · show Formalism.L2.Pj.toC (cf τ m j) = 0
      rw [hcf2 τ m j hj]
      rfl
  obtain ⟨Hm, -, hpos, hHm⟩ := per''.2.2.2.2
  have hform : ∀ x y, hermForm Hm (h x) (h y) = hermForm Hm (h' x) (h' y) :=
    GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family Pm per.2.2.2.1 Hm h.toLinearMap h'.toLinearMap fun a b => by
      simp only [LinearEquiv.coe_coe]
      rw [← hh, ← hh, ← hh', ← hh', hHm, hHm, hiso, hiso']
  have hhh := GlobalTheory.T.eq_of_flag_of_hermForm_preserving e Hm hpos h h' hform bv (p : ℂ) hp0
    (col z t ψ h hL (fun w v a b => (hder w v a b).1) ht hB)
    (col z' t' ψ' h' hL' (fun w v a b => (hder w v a b).2) ht' hB')
  exact Subtype.ext (hker hhh)

end GlobalTheory.HeckeInj
end
end
