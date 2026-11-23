module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle083
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle052
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle426
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle014
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Kdil

end
end

section

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (actZ)
open Matrix

variable {n : ℕ}

theorem up_decomp_pf (p : GR n) (hp : (mR p).toBlocks₂₁ = 0) :
    ∃ (nb ma : GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ mR nb = nU b ∧ mR ma = mLoc a ∧
      p = nb * ma ∧ actZ p (Complex.I • 1) = b + Complex.I • (a * aᴴ) :=
  GlobalTheory.T.parabolic_decomposition_upper_half_space n p hp

theorem fam_deriv_pf (m : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => fam m X z v) 0 = fP ((dil (2 * Real.pi) X ^ r) 1) v :=
  (GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero m n X v).2 r

theorem fam_int_hol_pf (m : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K)
    (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * fam m X z v) (Metric.ball 0 ρ) ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * fam m X z v) 0 =
        ∫ v, K v * iteratedDeriv r (fun z => fam m X z v) 0 :=
  GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential m n X K hK hK1

theorem iteratedDeriv_eq_of_real_pf {f g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ)) (hfg : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 :=
  GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment f g ρ hρ hf hg hfg r

theorem dcell_pf (y : GR n) (hy : ((mR y).toBlocks₂₂).det ≠ 0) :
    ∃ (p nbb : GR n) (c : Matrix (Fin n) (Fin n) ℂ), (mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ mR nbb = nbLoc c ∧ y = p * nbb :=
  GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization n y hy

theorem hol_int_pf {m : ℕ} (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ))
    (hc : ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ))
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * sq v))
    (K : (Fin m → Fin n → ℂ) → ℂ) (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧
        Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧
        ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * sq v) :=
  GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound m n Φ ρ C δ hρ hδ hd hc hb K hK hK1

theorem ft_uniq_pf {m : ℕ} (s : ℂ) (hs : s ≠ 0) (g : (Fin m → Fin n → ℂ) → ℂ) (hg : Continuous g) (hgi : Integrable g)
    (h0 : ∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) : g = 0 :=
  GlobalTheory.T.fourier_injective_matrix_space m n s hs g hg hgi h0

theorem up_decomp_closed : type_of% @up_decomp_pf := @up_decomp_pf

theorem fam_deriv_closed : type_of% @fam_deriv_pf := @fam_deriv_pf

theorem fam_int_hol_closed : type_of% @fam_int_hol_pf := @fam_int_hol_pf

theorem iteratedDeriv_eq_of_real_closed : type_of% @iteratedDeriv_eq_of_real_pf := @iteratedDeriv_eq_of_real_pf

theorem dcell_closed : type_of% @dcell_pf := @dcell_pf

theorem hol_int_closed : type_of% @hol_int_pf := @hol_int_pf

theorem ft_uniq_closed : type_of% @ft_uniq_pf := @ft_uniq_pf

end PositivityTheory.SiegelWeilFormula.Kdil

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem om_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : SD σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := by
  exact d.ok.dbl.weil.2.1.toIsSplitting.pres x Φ hΦ

theorem S_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : SD σ) (h : UA σ d.A.J) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.S h Φ ∈ d.sch := by
  exact d.ok.dbl.lin.toIsSplitting.pres h Φ hΦ

theorem thetaPt_of (hT : TAll) : ThetaPt := by
  intro F E _ _ _ _ _ σ d Φ hΦ x h
  obtain ⟨-, hPar, -, hTh, -⟩ := hT
  have hΦ' : d.om x (d.S h Φ) ∈ d.sch := om_mem d x (S_mem d h hΦ)
  rw [← ((hTh F E σ d _ hΦ').1).tsum_eq, (hTh F E σ d Φ hΦ).2 x h]
  refine tsum_congr fun X => ?_
  exact (hPar F E σ d _ (om_mem d x hΦ)).2.2 h _

end PositivityTheory.SiegelWeilFormula.Kdil

end
end
