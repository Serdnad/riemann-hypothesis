module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle031
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ChartIntSumOffHyperplane.proof (hFB : FibreBound.Statement)
    (hCN : ChartChangeSheetNull.Statement) : ChartIntSumOffHyperplane.Statement := by
  intro n d J A u m f F φ hJ hdim hA hu hf hint

  have hnull := hCN n d J J A A u u Set.univ Set.univ id id hJ hdim hJ hdim hu hu hA hA isOpen_univ
    isOpen_univ (Set.subset_univ _) (Set.subset_univ _) differentiableOn_id differentiableOn_id
    (fun x hx => hx) (fun x hx => hx) (fun x _ => rfl) (fun x _ => rfl)
  have hae : ∀ᵐ y ∂(volume : Measure (Fin d → ℂ)),
      chartDens J A f φ y = ∑ b, chartDens J A (F b) φ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    have hfin : (fibre J A y).Finite := (hFB n d J A hJ hdim hA y).2.1
    simp only [chartDens, sheetSum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · have hux : linEval u x ≠ 0 := by
        by_contra h0
        exact hy ⟨x, ⟨hx.1, hs, fun h => h.1 h0⟩, hx.2⟩
      rw [hf x hx.1 hux, Finset.sum_mul]
    · simp
  calc chartInt J A f φ = ∫ y, ∑ b, chartDens J A (F b) φ y := integral_congr_ae hae
    _ = ∑ b, chartInt J A (F b) φ := integral_finsetSum _ fun b _ => hint b

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem BranchIntDecompose.proof (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hGen : ComplexSets.GenericProjectionFinite.Statement) (hSum : ChartIntSumOffHyperplane.Statement)
    (hBr : BranchChartInt.Statement) : BranchIntDecompose.Statement := by
  intro n d J u q m γ ord hJ hdim hu hcov hdisj _
  obtain ⟨N₀, hN₀, hcovN⟩ := hcov
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu ⟨N₀, hN₀, hcovN⟩ hdisj b 0
      (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _
      (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨N₀ ∩ ⋂ b, Metric.ball q (e b),
    inter_mem hN₀ (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)),
    fun f ψ hf _ hfN hψ => ?_⟩
  have hex : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A :=
    (hGen n (d + 1) J hJ hdim).2.1
  have hAf : IsFiniteProjection J hex.choose := hex.choose_spec
  have hvar : varInt J (d + 1) f ψ = chartInt J hex.choose f ψ := by
    rw [varInt, dite_eq_left hex]
  have hbr : ∀ b, Integrable (chartDens J hex.choose ((γ b).image.indicator f) ψ) ∧
      chartInt J hex.choose ((γ b).image.indicator f) ψ =
        ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
          (Metric.ball 0 (γ b).radius) := by
    intro b
    refine hBr n (d + 1) J hex.choose q (γ b) f ψ hJ hdim hAf hf.continuous hψ
      ⟨Metric.closedBall 0 ((γ b).radius / 2), isCompact_closedBall _ _,
        Metric.closedBall_subset_ball (half_lt_self (γ b).radius_pos), fun t ht htK => ?_⟩
    by_contra hne
    have hx := hfN (subset_tsupport f hne)
    exact htK (Metric.ball_subset_closedBall (hpe b t ht (Set.mem_iInter.1 hx.2 b)))
  have hpt : ∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, (γ b).image.indicator f x := by
    intro x hxZ hux
    by_cases hfx : f x = 0
    · rw [hfx]
      exact (Finset.sum_eq_zero fun b _ => by by_cases hb : x ∈ (γ b).image <;> simp [hb, hfx]).symm
    · have hxN := hfN (subset_tsupport f hfx)
      obtain ⟨b₀, hb₀⟩ := Set.mem_iUnion.1 (hcovN ⟨hxZ, hxN.1⟩)
      rw [Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun hxb => hux (hdisj b b₀ hb ⟨hxb, hb₀⟩)) _)
        (fun h => absurd (Finset.mem_univ b₀) h), Set.indicator_of_mem hb₀]
  rw [hvar, hSum n (d + 1) J hex.choose u m f (fun b => (γ b).image.indicator f) ψ hJ hdim hAf hu hpt
    (fun b => (hbr b).1)]
  exact Finset.sum_congr rfl fun b _ => (hbr b).2

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem BranchProperAtPoint.proof (hrim : BranchAwayFromRim.Statement) :
    BranchProperAtPoint.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b s hs hsx P hP
  obtain ⟨ε₀, hε₀, ρ, hρ, hrimb⟩ := hrim n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨P', hP'P, hP'o, hsP'⟩ := mem_nhds_iff.mp hP
  set K : Set (Fin k → ℂ) := Metric.closedBall 0 ρ \ P' with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 ρ).diff hP'o
  have hKD : K ⊆ Metric.ball 0 (γ b).radius := fun τ hτ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hτ.1) hρ)
  have hcont : ContinuousOn (γ b).toFun K := (γ b).differentiableOn.continuousOn.mono hKD
  have hxK : x ∉ (γ b).toFun '' K := by
    rintro ⟨τ, hτK, hτx⟩
    have hτs : τ = s := (γ b).injOn (hKD hτK) hs (hτx.trans hsx.symm)
    exact hτK.2 (hτs ▸ hsP')
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (hKc.image_of_continuousOn hcont).isClosed.isOpen_compl x hxK
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun τ hτ hfτ => ?_⟩
  have h1 : ‖τ‖ ≤ ρ := hrimb τ hτ (Metric.ball_subset_ball (min_le_left _ _) hfτ)
  by_contra hτP
  have hτK : τ ∈ K := ⟨mem_closedBall_zero_iff.mpr h1, fun h => hτP (hP'P h)⟩
  exact hball (Metric.ball_subset_ball (min_le_right _ _) hfτ) ⟨τ, hτK, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ParamOffRegularZero.proof : ParamOffRegularZero.Statement := by
  intro n d W A σ r N hσ hZN f φ hfN
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set C : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} with hC
  set R : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  have hgd : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, DifferentiableAt ℂ g w := by
    intro w hw
    have hσw : DifferentiableAt ℂ σ w := (hσ w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiableAt.comp w hσw
  have hnull : volume (g '' C) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun w => (fderiv ℂ g w).restrictScalars ℝ) ?_ ?_
    · intro w hw
      exact ((hgd w hw.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro w hw
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, hw.2.2, Algebra.norm_complex_apply, map_zero]
  have hz : ∀ y ∉ g '' C, chartDens W A ((σ '' R)ᶜ.indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    classical
    rw [finsum_eq_if]
    split_ifs with hx hs
    · by_cases hxR : x ∈ σ '' R
      · simp [hxR]
      by_cases hf : f x = 0
      · simp [hxR, hf]
      exfalso
      have hxN : x ∈ N := hfN (subset_tsupport f (Function.mem_support.mpr hf))
      obtain ⟨w, hw, rfl⟩ := hZN ⟨hx.1, hxN⟩
      have hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0 := by
        by_contra hne
        exact hxR ⟨w, ⟨hw, hxN, hne⟩, rfl⟩
      exact hy ⟨w, ⟨hw, hxN, hdet⟩, hx.2⟩
    · rfl
    · rfl
  unfold chartInt
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra h
  exact hy (by simpa using hz y h)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorGeneralPointBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by
  rw [ringKrullDim_quotient] at h₁ h₂ ⊢
  rw [Order.krullDim_lt_coe_iff] at h₁ h₂ ⊢
  intro l
  have hhead : l.head.1 ∈ PrimeSpectrum.zeroLocus (I₁ : Set R) ∪ PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_inf]
    exact l.head.2
  have hup : ∀ (I : Ideal R), l.head.1 ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      ∀ i, (l i).1 ∈ PrimeSpectrum.zeroLocus (I : Set R) := fun I hI i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2
      (((PrimeSpectrum.mem_zeroLocus _ _).1 hI).trans (show l.head.1.asIdeal ≤ (l i).1.asIdeal from l.head_le i))
  rcases hhead with h | h
  · exact h₁ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₁ h i⟩, step := fun i => l.step i }
  · exact h₂ { length := l.length, toFun := fun i => ⟨(l i).1, hup I₂ h i⟩, step := fun i => l.step i }

theorem proof (hOne : DivisorOneComponent.Statement) (hBr : DivisorBranches.Statement) :
    DivisorGeneralPointBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hOne n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hBr n d J u hJ hdim hu
  refine ⟨I₁ ⊓ I₂, le_inf hle₁ hle₂, quotient_inf_dim_lt hdim₁ hdim₂, ?_⟩
  intro q hqJ hqu hqI
  have hq₁ : q ∉ zeroSet I₁ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).1
  have hq₂ : q ∉ zeroSet I₂ := fun h => hqI fun f hf => h f (Ideal.mem_inf.1 hf).2
  obtain ⟨W, hW, hqW, huniq, hnear⟩ := hI₁ q hqJ hqu hq₁
  obtain ⟨m, γ, ord, π, hcov, ⟨N, hN, hsl⟩, hpair, hord, hbij⟩ := hI₂ q hqJ hqu hq₂
  refine ⟨W, hW, hqW, huniq, hnear, m, γ, ord, π, hcov, ⟨N, hN, fun b x hx => ?_⟩, hpair, hord, hbij⟩
  have hKW : J ⊔ Ideal.span {linForm u} ≤ W := hW.1.2
  refine hsl x ⟨fun f hf => hx.1 f (hKW (Ideal.mem_sup_left hf)), hx.2⟩ ?_ b
  have hx0 := hx.1 _ (hKW (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using hx0

end DivisorGeneralPointBranches

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def PosPartLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ),
    Measurable f → (∀ k, SmoothNear (zeroSet J) (φ k)) →
    (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧
        ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
            ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem CutOffLimit.proof (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by
  intro n d J A P hJ hdim hA hP
  obtain ⟨χ, hχs, hχI, hχU, hχ1, hχE, hχM⟩ := hC n d J A P hJ hdim hA hP
  refine ⟨χ, hχs, hχU, fun F G φ hF hG hφ hc => ?_⟩
  have hcont : ∀ f, SmoothNear (zeroSet J) f → ContinuousOn f (zeroSet J) := by
    rintro f ⟨U, -, hU, hf⟩
    exact hf.continuousOn.mono hU
  have hcons : ∀ f, SmoothNear (zeroSet J) f → ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro f hf i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hφ i
  have hmeas : ∀ k, Measurable (χ k) := fun k => (hχs k).continuous.measurable
  refine ⟨hD n (d + 1) J A P χ F (vecCons G φ) hJ hdim hA hP hmeas hχI hχ1 (hcont F hF) (hcons G hG)
    (hM n (d + 1) J A F (vecCons G φ) hJ hdim hA (hcont F hF) (hcons G hG) (Or.inl hc)), ?_⟩
  have h1 := hD n (d + 1) J A P χ G (vecCons F φ) hJ hdim hA hP hmeas hχI hχ1 (hcont G hG) (hcons F hF)
    (hM n (d + 1) J A G (vecCons F φ) hJ hdim hA (hcont G hG) (hcons F hF) (Or.inr ⟨0, by simpa using hc⟩))
  obtain ⟨R, C, hRC⟩ := hB n d J A F G φ hJ hdim hA hF hG hφ hc
  have h0 : Tendsto (fun k => C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (χ k) φ) y) + Real.sqrt (energyInt J A (Metric.closedBall 0 R) (χ k)))) atTop (𝓝 0) := by
    simpa using ((hχM R φ hφ).add (hχE R).sqrt).const_mul C
  refine h1.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
  rw [Real.dist_eq, abs_sub_comm]
  exact hRC (χ k) (hχs k)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamChartInt.proof (hCA : ChartIntCountAdd.Statement) (hPI : ParamPieceInt.Statement)
    (hCN : ParamCritNull.Statement) (hOR : ParamOffRegularZero.Statement)
    (hRP : RegularInjectivePieces.Statement) (hDI : ParamDensIntegrable.Statement) :
    ParamChartInt.Statement := by
  intro n d W A σ r r' N hW hdim hA hσ hinj hN hrr hprop hcov f φ hf hfc hfN hφ
  classical
  set F : (Fin d → ℂ) → ℝ := fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w with hF
  have hf0 : ∀ x, x ∉ N → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfN h)
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hmv : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
    have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
    convert h using 1
    ext x i
    rfl
  have hgd : DifferentiableOn ℂ g Ω := hmv.comp_differentiableOn (hσ.mono Set.inter_subset_left)
  set Reg : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hReg
  obtain ⟨P, hPm, hPd, hPU, hPinj⟩ := hRP d Ω g hΩo hgd
  have hPReg : ⋃ i, P i = Reg := by
    rw [hPU]; ext w
    simp only [hΩ, Reg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  have hPsub : ∀ i, P i ⊆ Reg := fun i => hPReg ▸ Set.subset_iUnion P i
  have hRegB : Reg ⊆ Metric.ball 0 r := fun w hw => hw.1
  have hPB : ∀ i, P i ⊆ Metric.ball 0 r := fun i => (hPsub i).trans hRegB
  have hσP : ∀ i, MeasurableSet (σ '' P i) := fun i =>
    (hPm i).image_of_continuousOn_injOn (hσ.continuousOn.mono (hPB i)) (hinj.mono (hPB i))
  have hσReg : σ '' Reg = ⋃ i, σ '' P i := by rw [← hPReg, Set.image_iUnion]

  let E : ℕ → Set (Fin n → ℂ) := fun i => Nat.casesOn i (σ '' Reg)ᶜ fun j => σ '' P j
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    cases i with
    | zero => show MeasurableSet (σ '' Reg)ᶜ; rw [hσReg]; exact (MeasurableSet.iUnion hσP).compl
    | succ j => exact hσP j
  have hdisjP : ∀ i j, i ≠ j → Disjoint (σ '' P i) (σ '' P j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba := hinj (hPB j hb) (hPB i ha) hab
    subst hba
    exact Set.disjoint_left.1 (hPd hij) ha hb
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => exact Set.disjoint_compl_left_iff_subset.2 (Set.image_mono (hPsub j))
    | succ i =>
      cases j with
      | zero => exact Set.disjoint_compl_right_iff_subset.2 (Set.image_mono (hPsub i))
      | succ j => exact hdisjP i j fun h => hij (by rw [h])
  have hEU : ⋃ i, E i = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ σ '' Reg
    · rw [hσReg, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      exact Set.mem_iUnion.2 ⟨j + 1, hj⟩
    · exact Set.mem_iUnion.2 ⟨0, hx⟩

  have hsum := hCA n d W A f φ E hW hdim hA hf.continuous hfc hφ hEm hEd
  rw [hEU, Set.indicator_univ] at hsum
  have h0 : chartInt W A ((E 0).indicator f) φ = 0 := hOR n d W A σ r N hσ hcov f φ hfN
  have hi : ∀ j, chartInt W A ((E (j + 1)).indicator f) φ = ∫ w in P j, F w := fun j =>
    hPI n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ (P j) hφ (hPm j) (hPB j)
      (fun w hw => ⟨(hPsub j hw).2.1, (hPsub j hw).2.2⟩) (hPinj j)
  have hL : HasSum (fun j => ∫ w in P j, F w) (chartInt W A f φ) := by
    have h1 := (hasSum_nat_add_iff' 1).2 hsum
    rw [Finset.sum_range_one, h0, sub_zero] at h1
    have h2 : (fun j => chartInt W A ((E (j + 1)).indicator f) φ) = fun j => ∫ w in P j, F w :=
      funext hi
    rwa [h2] at h1

  have hint : IntegrableOn F (Metric.ball 0 r) :=
    hDI n d W σ r r' N hσ hrr hprop f φ hf.continuous hfN hφ
  have hR : HasSum (fun j => ∫ w in P j, F w) (∫ w in Reg, F w) := by
    have h1 := hasSum_integral_iUnion hPm hPd (by rw [hPReg]; exact hint.mono_set hRegB)
    rwa [hPReg] at h1
  have hnull := hCN n d W A σ r N hW hdim hA hσ hinj hN fun w hw hwN => (hprop w hw hwN).1
  have hB : ∫ w in Metric.ball 0 r, F w = ∫ w in Reg, F w := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hRegB ?_
    have hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℂ)), w ∉ {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧
        σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hae] with w hw hwd
    obtain ⟨hwB, hwR⟩ := hwd
    by_cases hwN : σ w ∈ N
    · exfalso
      by_cases hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0
      · exact hw ⟨hwB, hwN, hdet⟩
      · exact hwR ⟨hwB, hwN, hdet⟩
    · show f (σ w) * _ = 0
      rw [hf0 _ hwN, zero_mul]
  rw [hB]
  exact hL.unique hR

end

end GroundTheory.Heights₂.Heights
end
