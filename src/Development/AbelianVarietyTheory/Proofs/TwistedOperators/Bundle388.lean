module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

variable {D : D7}

theorem xLast_lin {T T₀ A L : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (o : OrthDec T₀ A L) {ζ : Fin L.rank → D.host.E}
    (hζ : IsLineVec L ζ) : ∃ x : Matrix (Fin T.rank) (Fin (σ + 1)) D.host.E,
      LinearIndependent D.host.E x.transpose ∧ xLast d (vecB o ζ) = rat x := by
  set z : Fin T.rank → D.host.E := d.i₀ *ᵥ (o.iB *ᵥ ζ) with hz
  set x : Matrix (Fin T.rank) (Fin (σ + 1)) D.host.E :=
    Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (d.e k) (z k) with hxdef
  refine ⟨x, ?_, ?_⟩
  · refine (show LinearIndependent D.host.E x.col from ?_)
    rw [← Matrix.mulVec_injective_iff]
    intro v w hvw
    have key : ∀ u : Fin (σ + 1) → D.host.E, x *ᵥ u = d.e *ᵥ (fun j => u j.castSucc) + u (Fin.last σ) • z := by
      intro u; ext k
      simp only [x, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    set u := v - w with hu
    have h0 : x *ᵥ u = 0 := by rw [hu, Matrix.mulVec_sub, hvw, sub_self]
    have hi : d.e'ᴴ * T.gram * d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have hZ : (d.e'ᴴ * T.gram) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_mulVec, hi, Matrix.zero_mulVec]
    have h1 : (fun j : Fin σ => u j.castSucc) = 0 := by
      have := congrArg (fun y => (d.e'ᴴ * T.gram) *ᵥ y) ((key u).symm.trans h0)
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hZ, smul_zero, add_zero, Matrix.mulVec_mulVec, d.e'e,
        Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    have hzne : z ≠ 0 := by
      intro hz0
      apply hζ.2
      have e1 : L.gram *ᵥ ζ = (o.iBᴴ * d.i₀ᴴ * T.gram) *ᵥ z := by
        rw [hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← o.isoB, ← d.iso]
        simp only [Matrix.mul_assoc]
      rw [e1, hz0, Matrix.mulVec_zero, dotProduct_zero]
    have h2 : u (Fin.last σ) = 0 := by
      have := (key u).symm.trans h0
      rw [h1, Matrix.mulVec_zero, zero_add] at this
      exact (smul_eq_zero.1 this).resolve_right hzne
    have hu0 : u = 0 := by
      funext i
      refine Fin.lastCases h2 (fun j => congrFun h1 j) i
    exact sub_eq_zero.1 hu0
  · ext k i
    refine Fin.lastCases ?_ (fun j => ?_) i

    · simp only [xLast, x, z, vecB, HypDec.j0, rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.of_apply, Fin.snoc_last, Matrix.map_apply]
    · simp [xLast, x, HypDec.jX, rat]

end GlobalTheory.JacMean
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.RealDecay

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplOH_swap (S T : HSp D) (u v : WO S T) : symplOH S T v u = -symplOH S T u v := by
  obtain ⟨l1, l2, l3, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := l3 (u + v)
  rw [l1, l2, l2, l3, l3, zero_add, add_zero] at h
  linear_combination h

theorem symplO_zero_left (S T : HSp D) (w : WO S T) : symplO S T 0 w = 0 := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplOH_zero_left, add_zero]

theorem heisO_comm (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (u w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = ψ (symplO S T u w) • heisO ψ S T w (heisO ψ S T u f) := by
  have hc := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).1
  obtain ⟨-, -, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  rw [hc, hc, smul_smul, ← AddChar.map_add_eq_mul, add_comm w u, symplOH_swap S T u w, ← l4]
  congr 2
  ring

theorem dRho_heisO (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T)
    (hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w f₀) =
      deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 • heisO ψ S T w f₀ +
        heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) := by
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).2.2.1 w f₀ h₀
  funext x
  have h1 : HasDerivAt (fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x)
      (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) x) 0 :=
    (DS.1 f₀ h₀ (x + w)).const_mul (ψ (symplOH S T x w))
  have h2 := hd.hasDerivAt.mul h1
  have e : ((fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) *
      fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x) =
      fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T w f₀) x := by
    funext t
    rw [Pi.mul_apply, heisO_comm hψ S T (lineAt θ τ z t) w]
    rfl
  rw [e] at h2
  rw [(DS.1 _ hw x).unique h2]
  simp only [map_zero, symplO_zero_left, AddChar.map_zero_eq_one, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.OrientedHeis.heisO_zero]

theorem step_bound (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) {μ : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T) :
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤
      ‖thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀)‖ +
        ‖thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀))‖ := by
  set ℓ := deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 with hℓ
  by_cases hl : ℓ = 0
  · rw [hl, norm_zero, zero_mul]
    positivity
  have hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 := by
    by_contra hn
    exact hl (deriv_zero_of_not_differentiableAt hn)
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have HU := GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := HU.2.2.1 w f₀ h₀
  have hw' : IsThetaFunO ψ S T (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) :=
    HU.2.2.1 w _ (DS.2.1 f₀ h₀)
  have key := DS.2.2 μ 𝓕 hμ h𝓕 f _ h hw
  rw [dRho_heisO hψ hθ S T τ z h₀ w hd] at key
  have i1 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw
  have i2 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw'
  have e : GlobalTheory.Ker.ipO μ 𝓕 f (ℓ • heisO ψ S T w f₀ + heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) =
      conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) +
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    simp only [GlobalTheory.Ker.ipO, thPair, Complex.star_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, mul_add]
    rw [integral_add _ i2, ← integral_const_mul]
    · congr 1
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      ring
    · exact (i1.const_mul (conj ℓ)).congr (.of_forall fun x => by dsimp only; ring)
  change thPair μ 𝓕 _ _ = _ at key
  rw [e] at key
  have e2 : conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) =
      -thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀) -
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    rw [key]; ring
  calc ‖ℓ‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ = ‖conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀)‖ := by
        rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
        rw [e2]
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_neg]

theorem coeff_bounded (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (h1 : μ 𝓕 < ⊤) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h₀ : IsThetaFunO ψ S T f₀) :
    ∃ C : ℝ, ∀ w : WO S T, ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  obtain ⟨a, ha⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f h).2.1
  obtain ⟨b, hb⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f₀ h₀).2.1
  refine ⟨a * b * μ.real 𝓕, fun w => norm_setIntegral_le_of_norm_le_const h1 fun x _ => ?_⟩
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha x) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha x))

theorem realDecay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ →
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  intro D ψ hψ θ hθ S T μ 𝓕 hc f f₀ h h₀ τ z k
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  induction k generalizing f f₀ with
  | zero =>
    obtain ⟨C, hC⟩ := coeff_bounded hψ S T (μ := μ) (𝓕 := 𝓕) (by rw [h1]; exact ENNReal.one_lt_top) h h₀
    exact ⟨C, fun w => by rw [pow_zero, one_mul]; exact hC w⟩
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := ih _ f₀ (DS.2.1 f h) h₀
    obtain ⟨C₂, hC₂⟩ := ih f _ h (DS.2.1 f₀ h₀)
    refine ⟨C₁ + C₂, fun w => ?_⟩
    have hs := step_bound hψ hθ S T hμ h𝓕 τ z h h₀ w
    calc _ = ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k *
          (‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_add _ _ _
      _ ≤ C₁ + C₂ := add_le_add (hC₁ w) (hC₂ w)

end GlobalTheory.RealDecay

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.LevelSupBound

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm GlobalTheory.SupremumSobolevWords GlobalTheory.HeisTaylor
open scoped NNReal Topology

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem word_theta_level (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (h0 : u.map (infPart D) = 0) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
      heisO ψ S T u f = f → IsThetaFunO ψ S T (wordAct (heisDer ψ θ) l f) ∧
        heisO ψ S T u (wordAct (heisDer ψ θ) l f) = wordAct (heisDer ψ θ) l f := by
  intro l
  induction l with
  | nil => exact fun hf hu => ⟨hf, hu⟩
  | cons a l ih =>
    intro f hf hu
    obtain ⟨h1, h2⟩ := ih hf hu
    have e : wordAct (heisDer ψ θ) (a :: l) f = dv θ σ S T (letter a) (wordAct (heisDer ψ θ) l f) := by
      rw [dv_letter hc hψ]
      rfl
    rw [e]
    exact ⟨theta_dv hc hψ _ h1, dv_level hc hψ _ h0 h2⟩

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (p : ℕ) (f : WO S T → ℂ),
      sobO ψ θ μ 𝓕 p (wordAct (heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (p + l.length) f := by
  intro l
  induction l with
  | nil => intro p f; simp [wordAct]
  | cons a l ih =>
    intro p f
    refine (sobO_heisDer_le p a).trans ?_
    refine (ih (p + 1) f).trans_eq ?_
    congr 1
    simp only [List.length_cons]
    omega

theorem nsmul_fin {u : WO S T} (hinf : u.map (infPart D) = 0) (n : ℕ) : (n • u).map (infPart D) = 0 := by
  ext i j
  have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
  exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))

theorem pointwise (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T))
    (hK₀ : IsCompact K₀) :
    ∃ C : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ y : WO S T,
        ‖f y‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ Module.finrank ℝ (RW T S)) *
          sobO ψ θ μ 𝓕 (Module.finrank ℝ (RW T S)) f := by
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  set N := Module.finrank ℝ (RW T S) with hN
  let b : Module.Basis (Fin N) ℝ (RW T S) := Module.finBasis ℝ (RW T S)
  obtain ⟨c, hcube⟩ := cube_dilate_bound_at hψ hc b h0 hK₀
  let card : ℝ≥0 := Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
  let Q : ℝ≥0 := 1 + card * ‖fun i => b i‖₊
  refine ⟨NNReal.sqrt (4 ^ N * c) * Q ^ N, fun μ 𝓕 hm n hn f hf hl y => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, sobO ψ θ μ 𝓕 N f = s :=
    ⟨_, (ENNReal.coe_toNNReal (sobO_ne_top hψ hθ hm.1 hm.2.1 hf N)).symm⟩
  let ρ : ℝ≥0 := (n : ℝ≥0) * ‖fun i => b i‖₊
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ (ρ : ℝ)) ∧ F = (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • n • b i)) A (c * ((1 + card * ρ) ^ N * s : ℝ≥0) ^ 2) y
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ f ⟨[], le_rfl, by simp, rfl⟩
  · have hQ : 1 + card * ρ ≤ Q * n := by
      have h1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn
      calc 1 + card * ρ ≤ n + card * ρ := add_le_add h1 le_rfl
        _ = Q * n := by simp only [Q, ρ]; ring
    have key' : (‖f y‖₊ : ℝ≥0) ^ 2 ≤ 4 ^ N * (c * ((1 + card * ρ) ^ N * s) ^ 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      simpa using key
    have hb : (‖f y‖₊ : ℝ≥0) ≤ NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s := by
      rw [← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero]
      refine key'.trans ?_
      have e : (NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s) ^ 2 = 4 ^ N * (c * ((Q * n) ^ N * s) ^ 2) := by
        rw [mul_assoc, mul_assoc, mul_pow (NNReal.sqrt _), NNReal.sq_sqrt]
        ring_nf
      rw [e]
      gcongr
    rw [hs, enorm_eq_nnnorm]
    have e2 : ENNReal.ofReal (((NNReal.sqrt (4 ^ N * c) * Q ^ N : ℝ≥0) : ℝ) * (n : ℝ) ^ N) =
        ((NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [e2, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hb
  · rintro p _ ⟨l, h1, h2, rfl⟩
    refine ⟨(wd l).2.cont, fun i => ⟨_, ⟨l ++ [n • b i], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (n • b i) (wd l).2⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        refine norm_nsmul_le.trans ?_
        simp only [ρ, NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => b i) i) (Nat.cast_nonneg n)
    · simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    refine (hcube μ 𝓕 hm n hn _ (wd l).2 (fun u hu hinf => ?_) y).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2) c.coe_nonneg)
    · exact words_level hc hψ (nsmul_fin hinf n) l ⟨f, hf⟩ (hl u hu hinf)
    · refine ENNReal.toReal_le_coe_of_le_coe ((l2O_foldl_dvL_le_pow_mul_sobO hc hψ N l (by simpa using h1) h2 _).trans ?_)
      rw [hs, ← ENNReal.coe_pow, ← ENNReal.coe_mul]

theorem supN_word_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  intro D ψ hψ θ hθ V X K₀ h0 hK₀ μ 𝓕 hm
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨C, hC⟩ := pointwise (S := V) (T := X) hψ hθ h0 hK₀
  refine ⟨Module.finrank ℝ (RW X V), Module.finrank ℝ (RW X V), C, C.2, fun n hn f hf hl l => iSup_le fun y => ?_⟩
  have hw := fun u hu hinf => word_theta_level hc hψ (nsmul_fin (S := V) (T := X) hinf n) l hf (hl u hu hinf)
  have ht : IsThetaFunO ψ V X (wordAct (heisDer ψ θ) l f) :=
    (hw 0 (mem_of_mem_nhds h0) (Matrix.map_zero _ (map_zero _))).1
  refine (hC μ 𝓕 hm n hn _ ht (fun u hu hinf => (hw u hu hinf).2) y).trans ?_
  exact mul_le_mul' le_rfl (sobO_word_le μ 𝓕 l _ f)

end GlobalTheory.LevelSupBound
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothTranslate


open Classical in
theorem mult_equiv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => funext x; simp [rTr]
  | add T T' _ _ h h' =>
    funext x
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem translate : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  intro D V S θ M J χ T hT g
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V),
      T (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
        GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
        else v τ) x = T v (x * P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun v x => by simp⟩
    | insert a s ha ih =>
      obtain ⟨P, hP, hPe⟩ := ih
      refine ⟨atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) * P, mul_mem (Formalism.IndefR.TopMult.atTau_mem_GinfC θ a _) hP,
        fun v x => ?_⟩
      have hupd : (fun τ => if τ ∈ insert a s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) = Function.update (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) a ⟨M.rep a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) (v a),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ (v a).2⟩ := by
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd, mult_equiv θ M J χ T hT a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ _ (by simp [ha])]
      show T _ (x * atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a))) = _
      rw [hPe, mul_assoc]
  obtain ⟨P, hP, hPe⟩ := key Finset.univ
  exact ⟨P, hP, fun v x => by simpa using hPe v x⟩

end GlobalTheory.SmoothTranslate
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

theorem _root_.GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  first | exact @GlobalTheory.LevelSupBound.supN_word_le | exact GlobalTheory.LevelSupBound.supN_word_le | (intros; apply GlobalTheory.LevelSupBound.supN_word_le <;> assumption)

end
end
