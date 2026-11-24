module

public import Development.WeilBound.CoreStatements.TorusUniformisation.SiegelCompactSupport.ExistsRouteDatumTranslationCombinationGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SvN

open Matrix
open scoped PositivityTheory.Member.ZakTransform
open PositivityTheory.Member.ZakTransform (schr_tens lift lift_tens lift_schr lift_adm lift_lift lift_one lift_mem psv psv_apply evP offP
  offP_eq evalEmbedding_smul evalPoints_add Indep indep_pure ep ep_mul ep_ep ev_ep at_iff schr_zero schr_mem_SB cont_at spM spM_fst spM_snd
  spM_off mat_ext coB ev_symp map_smul_piW map_cA_piW incM_piW ev_dot stdF stdF_mem sub sub_mem hasSig_det schur
  exists_bump rest_zero tens_at pure_update pure_mem good_std Good)
open PositivityTheory.Member.ZakTransform.Z (psi_re re trace_emb)
open GlobalTheory.EmbChart (atPlace evFin_atPlace)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE cA incM UA Spc Model Rep mat UAt At Rest Acts tens piW)

theorem isCharAF_of_isStd {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ := by
  apply _root_.PositivityTheory.ThKEst.W.isCharAF <;> assumption

section Inverse

end Inverse

section Local

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ}

variable {I : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
  {J : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}

end Local

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem indep_of {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (h : ∀ x z, At (evFin F v) z → r (x + z) = r x) : Indep v r := fun x t =>
  h x _ ((at_iff _).2 (funext fun i => by
    show ep v * atPlace v (t i) = _
    rw [ep_mul, evFin_atPlace]))

end Split

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Main

end GlobalTheory.CompanionTheory.Ar.SvN
