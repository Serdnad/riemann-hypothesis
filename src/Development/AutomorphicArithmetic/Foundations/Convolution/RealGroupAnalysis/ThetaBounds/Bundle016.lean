module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle014
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle015
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle007
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieL O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y hY Φ hΦ
  funext g
  have hE := (exPar E Y)
  have h0 : ex Y 0 = 1 := by
    refine Units.ext ?_
    show NormedSpace.exp ((0 : ℝ) • Matrix.of Y) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ g (ex Y) Y h0 hE.2.2.1
  have h2 := derL F E D O W M π f hf φ hφ Y hY g
  rw [hΦ] at h1
  rw [GlobalTheory.CuspRep.lie_apply, hΦ]
  exact h1.unique h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem norm_det_kinf {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : Kinf E 2)
    (w : InfinitePlace E) : ‖(Unitary.toUnits k).val.det w‖ = 1 := by
  have h : star k.1 * k.1 = 1 := by simp
  have hd : star (k.1.det) * k.1.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at this
  have hw : star (k.1.det w) * k.1.det w = 1 := congrFun hd w
  have hn : ‖k.1.det w‖ * ‖k.1.det w‖ = 1 := by
    have := congrArg norm hw
    rwa [norm_mul, norm_star, norm_one] at this
  have h0 : 0 ≤ ‖k.1.det w‖ := norm_nonneg _
  change ‖k.1.det w‖ = 1
  nlinarith

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

theorem UpperTheory.ConvolutionTheory.R2.Ff.kFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), KFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ Φ hΦ
  have hl := lin F E D W M π
  obtain ⟨U, hUF, hfd, hU⟩ := (fockSt F E D W).cpt φ hφ
  have key : ∀ k : Kinf E 2, (cptRep E 2 k Φ).1 = lift W M f.1 (W.L (infGL E 2 (Unitary.toUnits k)) φ) := by
    intro k
    funext h
    have h1 : nu F (infGL E 2 (Unitary.toUnits k)) = 1 :=
      oneOf F E D (Unitary.toUnits k) (norm_det_kinf k)
    have h2 := transl F E D W M f.1 φ h (infGL E 2 (Unitary.toUnits k))
    rw [h1, dM_one'] at h2
    simp only [mul_one] at h2
    change Φ.1 (h * infGL E 2 (Unitary.toUnits k)) = _
    rw [hΦ]
    exact h2
  refine ⟨fun k => Submodule.subset_span ⟨f, hf, _, hUF (hU k), key k⟩, ?_⟩
  haveI := hfd
  let T : U →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ) :=
    { toFun := fun u => lift W M f.1 u.1
      map_add' := fun u u' => hl.1 f hf u.1 (hUF u.2) u'.1 (hUF u'.2)
      map_smul' := fun c u => hl.2.1 f.1 c u.1 }
  have hle : (Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype ≤ LinearMap.range T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨⟨_, hU k⟩, (key k).symm⟩
  haveI : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E 2 k Φ)).map (Sm E 2).subtype) :=
    Submodule.finiteDimensional_of_le hle
  exact (Submodule.equivMapOfInjective (Sm E 2).subtype (Submodule.injective_subtype _) _).symm.finiteDimensional
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.mov :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Mov W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G c Y hP hG hD
  obtain ⟨hinf, hPc⟩ := UpperTheory.ConvolutionTheory.R2.Ff.parCont F
  obtain ⟨hc0, hcc, hPn⟩ := hPc c Y hP
  have hGc : Continuous G := continuous_adelicSL2_of_continuous_entries fun i j => by
    have e : (fun t => G t i j) = fun t => (TR.infGL F 2 (c t)).val i j := by
      funext t
      rw [← hG t]
      rfl
    rw [e]
    have hv : Continuous fun t => (TR.infGL F 2 (c t)).val :=
      Units.continuous_val.comp (hinf.comp hcc)
    exact hv.matrix_elem i j
  have hG0 : G 0 = 1 := gl_injective (by rw [hG, hc0, map_one, gl_one])
  have hL : LRat f.1 := (π.cusp f hf).1.left
  have hinv : ∀ t, (gl (G t))⁻¹ = TR.infGL F 2 (c (-t)) := fun t => by
    have h1 : c (-t) = (c t)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hP.1, neg_add_cancel, hc0])
    rw [hG, h1, map_inv]
  funext h
  have d1 := UpperTheory.ConvolutionTheory.R2.Ff.derOm F E D W M π f hf φ hφ φ' hφ' G hGc hG0 hD h
  have d2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ (fun t => c (-t)) (-Y) hPn h
  have e : (fun t => lift W M (fun x => f.1 (x * TR.infGL F 2 (c (-t)))) φ h) =
      fun t => lift W M f.1 (W.Om (G t) φ) h := by
    funext t
    rw [UpperTheory.ConvolutionTheory.R2.Ff.movG F E D W M f.1 hL φ (G t) h, hinv]
  rw [e] at d2
  have hu := d1.unique d2
  have hl : (TR.lie F 2 (-Y) f).1 = (-1 : ℂ) • (TR.lie F 2 Y f).1 := by
    rw [map_neg]
    funext x
    simp
  have h4 := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2 (TR.lie F 2 Y f).1 (-1) φ
  rw [hu, hl, h4]
  simp
end
