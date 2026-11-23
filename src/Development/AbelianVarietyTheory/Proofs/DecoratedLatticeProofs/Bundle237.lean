module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle183
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle204
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotVal

theorem val_quot_ne_one : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ,
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  intro D c hc i j hi hij hj p hp w hw hS h1
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hoff : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hS
  refine GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity D (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹)
    (GlobalTheory.Chain.isHeckeChar_div (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj))
    (fun τ => ⟨_, ?_, GlobalTheory.Chain.hasInfExp_div (hc.exp ⟨i', by omega⟩ τ) (hc.exp ⟨j', by omega⟩ τ)⟩) p hp w hw
    ((hc.unr ⟨i', by omega⟩ w hoff).mul (hc.unr ⟨j', by omega⟩ w hoff).inv) ?_
  · have := QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
      Fin.mk_lt_mk.2 (by omega))
    intro h0
    linarith
  · rw [h1]
    exact IsOfFinOrder.one

end GlobalTheory.ChainOnto.QuotVal

end
end

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.RealParamSize

variable {D : D7} {m n : ℕ}

theorem compAt_add (θ : InfFam D) (τ : D.what₂.Tau) (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.add_apply]
  rw [map_add, map_add]

theorem compAt_neg (θ : InfFam D) (τ : D.what₂.Tau) (x : Mx D m n) :
    compAt θ τ (-x) = -compAt θ τ x := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.neg_apply]
  rw [(infPart D).map_neg, (θ τ).map_neg]

def realVec {k : ℕ} (θ : InfFam D) (L : (Fin k → ℝ) →+ Mx D m n) :
    (Fin k → ℝ) →+ (D.what₂.Tau → Fin m → Fin n → ℂ) where
  toFun t := fun τ i j => compAt θ τ (L t) i j
  map_zero' := by ext τ i j; simp [compAt]
  map_add' a b := by ext τ i j; simp [compAt_add]

theorem norm_compAt_le (θ : InfFam D) (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

theorem norm_vec_le (θ : InfFam D) (x : Mx D m n) :
    ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ ≤ GlobalTheory.Unf.realSize θ x :=
  (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun i =>
      (pi_norm_le_iff_of_nonneg (GlobalTheory.Unf.realSize_nonneg θ x)).2 fun j => norm_compAt_le θ x τ i j

theorem realSize_le (θ : InfFam D) (x : Mx D m n) :
    GlobalTheory.Unf.realSize θ x ≤ (Fintype.card D.what₂.Tau * (m * n) : ℝ) *
      ‖(fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ)‖ := by
  set v : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ x i j with hv
  unfold GlobalTheory.Unf.realSize
  calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖ ≤ ∑ τ : D.what₂.Tau, ∑ i : Fin m, ∑ j : Fin n, ‖v‖ :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (v τ i) j).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
    _ = _ := by simp [Finset.sum_const]; ring

theorem realSize_add_le (θ : InfFam D) (x y : Mx D m n) :
    GlobalTheory.Unf.realSize θ (x + y) ≤ GlobalTheory.Unf.realSize θ x + GlobalTheory.Unf.realSize θ y := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_add, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem realSize_neg (θ : InfFam D) (x : Mx D m n) : GlobalTheory.Unf.realSize θ (-x) = GlobalTheory.Unf.realSize θ x := by
  unfold GlobalTheory.Unf.realSize
  simp only [compAt_neg, Matrix.neg_apply, norm_neg]

theorem continuous_realVec {θ : InfFam D} (hθ : IsInfFam θ) {k : ℕ} {L : (Fin k → ℝ) →+ Mx D m n}
    (hL : Continuous L) : Continuous (realVec θ L) :=
  continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp ((continuous_apply i).comp hL))

end GlobalTheory.RealParamSize


open GlobalTheory.RealParamSize in
theorem GlobalTheory.Unf.realParam_size_bounds : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  intro D θ hθ m n k L hL
  have hc := continuous_realVec hθ hL.1
  set A := (realVec θ L).toRealLinearMap hc with hA
  have hAt : ∀ t, A t = realVec θ L t := fun t => rfl
  have hvec : ∀ t, realVec θ L t = (fun τ i j => compAt θ τ (L t) i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    fun t => rfl
  refine ⟨⟨(Fintype.card D.what₂.Tau * (m * n) : ℝ) * ‖A‖, fun t => ?_⟩, fun hinj => ?_⟩
  · refine (realSize_le θ (L t)).trans ?_
    rw [mul_assoc _ ‖A‖, ← hvec, ← hAt]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm t) (by positivity)
  · obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    have hker : (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro t ht
      have h0 : realVec θ L t = 0 := by rw [← hAt]; exact ht
      have hLt : L t = 0 := by
        ext i j
        refine hσ.ext _ ?_ fun τ => ?_
        · have h := congrFun (congrFun (hL.2 t) i) j
          simpa only [Matrix.map_apply, Matrix.zero_apply] using h
        · have h := congrFun (congrFun (congrFun h0 τ) i) j
          exact h
      exact hinj (hLt.trans L.map_zero.symm)
    obtain ⟨K, -, hK⟩ := (A : (Fin k → ℝ) →ₗ[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ)).exists_antilipschitzWith hker
    refine ⟨K, fun x t => ?_⟩
    have h1 : ‖t‖ ≤ K * ‖A t‖ := by
      have := hK.le_mul_dist t 0
      simpa [dist_eq_norm] using this
    have h2 : ‖A t‖ ≤ GlobalTheory.Unf.realSize θ (L t) := by rw [hAt, hvec]; exact norm_vec_le θ (L t)
    have h3 : GlobalTheory.Unf.realSize θ (L t) ≤ GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x := by
      have := realSize_add_le θ (x + L t) (-x)
      rwa [realSize_neg, add_neg_cancel_comm] at this
    calc ‖t‖ ≤ K * ‖A t‖ := h1
      _ ≤ K * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) K.coe_nonneg

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chainPar_of_nodeGap' : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ k, ChainPar D k := by
  first | exact @GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap | exact GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap | (intros; apply GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
private theorem bijective_quot_mk_map_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (κ : G₁ ≃* G₂)
    (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂) (hP : ∀ g, g ∈ P₁ ↔ κ g ∈ P₂)
    (hΓ : ∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) :
    Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂)
        (⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) := by
  have hout : ∀ q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁),
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) = q := by
    intro q
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
    exact Quotient.out_eq q
  constructor
  · intro q q' h
    simp only at h
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hp' : κ.symm ((p : Γ₂) : G₂) * (Quotient.out q : Γ₁) = (Quotient.out q' : Γ₁) := by
      apply κ.injective
      have := congrArg Subtype.val hp
      simpa using this
    have hmemΓ : κ.symm ((p : Γ₂) : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using ((p : Γ₂)).2
    have hmemP : (⟨κ.symm ((p : Γ₂) : G₂), hmemΓ⟩ : Γ₁) ∈ P₁.subgroupOf Γ₁ := by
      rw [Subgroup.mem_subgroupOf, hP]
      simpa using Subgroup.mem_subgroupOf.1 p.2
    rw [← hout q, ← hout q']
    refine _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩
    ext
    simpa using hp'
  · intro q₂
    obtain ⟨y, rfl⟩ : ∃ y : Γ₂, _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₂.subgroupOf Γ₂) y = q₂ := by
      refine ⟨Quotient.out q₂, ?_⟩
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q₂
    have hx : κ.symm (y : G₂) ∈ Γ₁ := by
      rw [hΓ]; simpa using y.2
    refine ⟨_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩, ?_⟩
    obtain ⟨p, hp⟩ := _root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1
      (hout (_root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) ⟨_, hx⟩)).symm
    simp only
    rw [← hp]
    have hmemΓ : κ ((p : Γ₁) : G₁) ∈ Γ₂ := (hΓ _).1 (p : Γ₁).2
    have hmemP : (⟨κ ((p : Γ₁) : G₁), hmemΓ⟩ : Γ₂) ∈ P₂.subgroupOf Γ₂ := by
      rw [Subgroup.mem_subgroupOf]
      exact (hP _).1 (Subgroup.mem_subgroupOf.1 p.2)
    refine (_root_.GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨_, hmemP⟩, ?_⟩).symm
    ext
    simp


open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff in
open MeasureTheory IsDedekindDomain NumberField in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.StdUnn.cosetSum_along_mulEquiv : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (κ : G₁ ≃* G₂) (P₁ Γ₁ : Subgroup G₁) (P₂ Γ₂ : Subgroup G₂), (∀ g, g ∈ P₁ ↔ κ g ∈ P₂) → (∀ g, g ∈ Γ₁ ↔ κ g ∈ Γ₂) → ∀ (Φ₂ : G₂ → ℂ) (x : G₁) (c : ℂ) (Φ₁ : G₁ → ℂ), (∀ g, Φ₁ g = c * Φ₂ (κ (g * x))) → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₂ ⊓ Γ₂) Φ₂ → _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ ∧ ∀ g, (_root_.GlobalTheory.Eis.CosetConv P₂ Γ₂ Φ₂ (κ (g * x)) → _root_.GlobalTheory.Eis.CosetConv P₁ Γ₁ Φ₁ g) ∧ _root_.GlobalTheory.Eis.cosetSum P₁ Γ₁ Φ₁ g = c * _root_.GlobalTheory.Eis.cosetSum P₂ Γ₂ Φ₂ (κ (g * x)) := by
  intro G₁ G₂ _ _ κ P₁ Γ₁ P₂ Γ₂ hP hΓ Φ₂ x c Φ₁ hΦ hinv₂
  have hinv₁ : _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv (P₁ ⊓ Γ₁) Φ₁ := by
    unfold _root_.GlobalTheory.AutomorphicL2Unitary.LeftInv at hinv₂ ⊢
    intro γ hγ g
    have hγ₂ : κ γ ∈ P₂ ⊓ Γ₂ :=
      Subgroup.mem_inf.2 ⟨(hP γ).1 (Subgroup.mem_inf.1 hγ).1, (hΓ γ).1 (Subgroup.mem_inf.1 hγ).2⟩
    rw [hΦ, hΦ, mul_assoc, map_mul, hinv₂ _ hγ₂]
  have hbij := bijective_quot_mk_map_out κ P₁ Γ₁ P₂ Γ₂ hP hΓ
  have hbij₁ : Function.Bijective fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
      _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q) := by
    have : (fun q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁) =>
        _root_.GlobalTheory.AutomorphicL2Unitary.mk (P₁.subgroupOf Γ₁) (Quotient.out q)) = id := by
      funext q
      unfold _root_.GlobalTheory.AutomorphicL2Unitary.mk
      exact Quotient.out_eq q
    rw [this]
    exact Function.bijective_id
  have hterm : ∀ (g : G₁) (q : _root_.GlobalTheory.AutomorphicL2Unitary.Quot (P₁.subgroupOf Γ₁)),
      Φ₁ (((Quotient.out q : Γ₁) : G₁) * g) =
        c * Φ₂ (((⟨κ (Quotient.out q : Γ₁), (hΓ _).1 (Quotient.out q : Γ₁).2⟩ : Γ₂) : G₂) *
          κ (g * x)) := by
    intro g q
    rw [hΦ, mul_assoc, map_mul]
  refine ⟨hinv₁, fun g => ⟨fun hconv => ?_, ?_⟩⟩
  · rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₁ hbij₁]
    rw [_root_.GlobalTheory.Eis.cosetConv_iff hinv₂ hbij] at hconv
    simp_rw [hterm g, norm_mul]
    exact hconv.mul_left _
  · rw [_root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₁ hbij₁,
      _root_.GlobalTheory.Eis.cosetSum_eq_tsum hinv₂ hbij]
    simp_rw [hterm g]
    exact tsum_mul_left

end GlobalTheory.StdUnn
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.Dom

theorem exists_integrable_bound_dblIntegrandQ : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q := by
  intro D V μ m hm f₁ f₂ hf₁ hf₂ C' c hC' C N
  have hC'1 : 1 ≤ C' := by
    have h := hC' 1 1
    have e : io V ((1 : GA D V), (1 : GA D V)) = 1 := map_one (io V)
    simp only [e, GlobalTheory.Grow.height_one, mul_one, one_pow] at h
    exact h
  set K : ℝ := max C 0 * (C' * 4 ^ c) ^ N with hK
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ hf₁ (c * N)
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ hf₂ (c * N)
  refine ⟨fun q => K * ((GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * ‖f₁ q.1.out‖) *
      (GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N) * ‖f₂ q.2.out‖)), (i₁.mul_prod i₂).const_mul K, ?_⟩
  intro E hE hEb q
  obtain ⟨γ₁, hγ₁, h₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, h₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) *
      GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
    rw [hinv]
    refine (hEb _).trans ?_
    have hh := hC' (γ₁ * q.1.out) (γ₂ * q.2.out)
    have hprod : GlobalTheory.Grow.height V (γ₁ * q.1.out) * GlobalTheory.Grow.height V (γ₂ * q.2.out) ≤
        4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
      have := mul_le_mul h₁ h₂ (by linarith) (by linarith)
      linarith
    have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
        C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c := by
      refine hh.trans ?_
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hprod c) (by linarith)
    have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
    calc C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N
        ≤ max C 0 * (C' * 4 ^ c * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) ^ c) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N) (le_max_right _ _)
      _ = K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) := by
          rw [hK, pow_mul, pow_mul]; ring
  have hμ : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, norm_mul, hμ, mul_one, Complex.norm_conj]
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg (by linarith) (by positivity)) N)
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ (c * N) * GlobalTheory.Grow.quotHeight V q.2.out ^ (c * N)) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

end GlobalTheory.Core.Rk.Dom
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

theorem _root_.GlobalTheory.T.wittHyperbolic_isotropic_columns_at_real_place : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  first | exact @GlobalTheory.IsoColReal.isotropic_at_real | exact GlobalTheory.IsoColReal.isotropic_at_real | (intros; apply GlobalTheory.IsoColReal.isotropic_at_real <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem realIdem_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem realIdem_gen (σ : E →ₐ[F] E) : ∃ e : AF F ⊗[F] E, e * e = e ∧ sigR (AF F) σ e = e ∧
    (∀ v, compFin F E v e = 0) ∧ (∀ w, compInf F E w e = 1) ∧
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom e = 0 ∧
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom e = 1 := by
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have h0 : sndA F (pairA F 1 0) = 0 := rfl
  have h1 : fstA F (pairA F 1 0) = 1 := rfl
  refine ⟨pairA F 1 0 ⊗ₜ[F] (1 : E), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  · exact realIdem_map F E (AlgHom.id F (AF F)) σ _
  · intro v
    refine (realIdem_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, h0, map_zero, TensorProduct.zero_tmul]
  · intro w
    refine (realIdem_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, h1, map_one, Algebra.TensorProduct.one_def]
  · rw [realIdem_map, h0, TensorProduct.zero_tmul]
  · rw [realIdem_map, h1, Algebra.TensorProduct.one_def]

end

theorem realIdem_exists : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 :=
  fun D => realIdem_gen D.host.F D.host.E _

end GlobalTheory.StdUnn
end
