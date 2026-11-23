module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtChartUnit.proof : ClosedPtChartUnit.Statement := by
  classical
  intro S _ K _ ι _ P hP I hI hX f a hf hfP
  have : P.IsPrime := hP.1.1

  have hTP : KH.cellMon S I ≤ P.primeCompl :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, i, hi, rfl⟩; exact hX k i hi)
  have hPh : NumbersDVR.IsMultiHomogIdeal P := (NumbersDVR.Objects.isMultiHomogIdeal_iff P).mpr hP.1.2.1

  obtain ⟨t, htT, htJ⟩ : ∃ t ∈ KH.cellMon S I, t ∈ P ⊔ Ideal.span {f} := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hJp, hdisj⟩ := Ideal.exists_le_prime_disjoint (P ⊔ Ideal.span {f}) (KH.cellMon S I)
      (Set.disjoint_left.mpr fun x hxJ hxT => hno x hxT hxJ)
    obtain ⟨W, hW, hWh, hWp, hWJ, hWf⟩ := NumbersDVR.exists_multiHomog_core hp
    have hPW : P ≤ W := hWJ P hPh (le_sup_left.trans hJp)
    have hfW : f ∈ W :=
      hWf f a ((NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf)
        (hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    have hrel : IsRelevant W := by
      intro k
      obtain ⟨i, hi⟩ := hI k
      refine ⟨i, fun hXW => Set.disjoint_left.mp hdisj (hWp hXW) ?_⟩
      exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
    have hWP : W = P := hP.2 W ⟨hW, (NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp hWh, hrel⟩ hPW
    exact hfP (hWP ▸ hfW)

  obtain ⟨e, hte'⟩ : ∃ e, NumbersDVR.IsMultiHomog t e := by
    clear htJ
    induction htT using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, i, -, rfl⟩ := hx
      exact ⟨_, isWeightedHomogeneous_X S (NumbersDVR.blockWeight ι) ⟨k, i⟩⟩
    | one => exact ⟨0, isWeightedHomogeneous_one S (NumbersDVR.blockWeight ι)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      exact ⟨c + d, IsWeightedHomogeneous.mul hc hd⟩
  have hf' : NumbersDVR.IsMultiHomog f a := (NumbersDVR.Objects.isMultiHomog_iff f a).mpr hf
  obtain ⟨p, hpP, r, hr, hpr⟩ := Submodule.mem_sup.mp htJ
  obtain ⟨g₀, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have hcomp : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p +
        weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e (g₀ * f) := by
    rw [← hpr, map_add (f := _)]
  have htself : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e t = t := by
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hte'), if_pos rfl]
  rw [htself] at hcomp
  have hpe : weightedHomogeneousComponent (NumbersDVR.blockWeight ι) e p ∈ P := hPh p hpP e
  by_cases hae : a ≤ e
  · refine ⟨t, htT, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (e - a) g₀, e - a, ?_, ?_, ?_⟩
    · rw [add_tsub_cancel_of_le hae]
      exact (NumbersDVR.Objects.isMultiHomog_iff t e).mp hte'
    · exact (NumbersDVR.Objects.isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · rw [NumbersDVR.component_mul_form_of_le hf' hae] at hcomp
      rw [hcomp, add_sub_cancel_right]
      exact hpe
  · rw [NumbersDVR.component_mul_form_of_not_le hf' hae, add_zero] at hcomp
    exact absurd (hcomp ▸ hpe) (hTP htT)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameGraphDeg.proof
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPt : ProjFrameFibrePt.Statement) (hDeg : ProjFrameFibreDeg.Statement) : ProjFrameGraphDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF
  have : (coordIdeal ℤ x).IsPrime := hP.2.1.1
  have := ProjFrameGraph.graphIdeal_isPrime (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
    (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
  let G := Inter.genFibreOf (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
    (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e)))
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr)
  have hch := ProjFrameGraph.isChart_fibreChart G (e 0).2 (ProjFrameGraph.frame_ne_zero hF 0)
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ (hPt D Ω κ x e hP hF G) hch, hDeg D Ω κ x e hP hF G _ hch]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ReductionToProjective

theorem powLog_shift_le (D : ℕ) {n j : ℕ} (hj : j ≤ n) :
    ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1) ≤
      2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
  have h1 := powLog_mono D (show n + j ≤ 2 * n by omega)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog : Real.log (((2 * n : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [h2]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hp : ((2 * n : ℕ) : ℝ) ^ D = 2 ^ D * (n : ℝ) ^ D := by push_cast; rw [mul_pow]
  calc ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)
      ≤ ((2 * n : ℕ) : ℝ) ^ D * Real.log (((2 * n : ℕ) : ℝ) + 1) := h1
    _ ≤ ((2 * n : ℕ) : ℝ) ^ D * (2 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by rw [hp]; ring

theorem sub_chiP_isBigO (D k : ℕ) (δ C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, k + 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => chi n - δ * chiP D n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  refine IsBigO.of_bound (δ * (k * (|C'| * 2 ^ (D + 1))) + |C|) ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hP0 : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := powLog_nonneg D n
  have hCP : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hP0
  have hCP' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le C) hP0
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)

  have hup : chiP D (n + k) - chiP D n ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    refine (chiP_add_sub_le D C' hC' k n (by omega)).trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          exact powLog_shift_le D (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  have hdn : chiP D n - chiP D (n - k) ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    have h := chiP_add_sub_le D C' hC' k (n - k) (by omega)
    rw [Nat.sub_add_cancel (by omega : k ≤ n)] at h
    refine h.trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n - k + j : ℕ) : ℝ) ^ D * Real.log (((n - k + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          have hj' := Finset.mem_range.1 hj
          refine (powLog_mono D (show n - k + j ≤ n by omega)).trans ?_
          exact le_mul_of_one_le_left hP0 h2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo' := hlo n hn
  have hhi' := hhi n hn
  have hu := mul_le_mul_of_nonneg_left hup hδ
  have hd := mul_le_mul_of_nonneg_left hdn hδ
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hP0, abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem defect_pullFS (hPB : ProjectionBounds.Statement) (hTop : TopPullFS.Statement) {D : ℕ} {Ω : Type}
    [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (I : AllFam) (hI : I.IsFamily) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) (hFS : IsPullFS d.x e d.m) :
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨k, E, C, -, -, -, -, -, -, -, hs⟩ := hPB D Ω κ d e hfr hFS
  have ht := hTop D Ω κ I d.x d.m e hI d.arith d.smooth hfr hFS
  refine (sub_chiP_isBigO D k (projDeg d.x e) C (Nat.cast_nonneg _) (resChi d) (fun n hn => (hs n hn).1)
    (fun n hn => (hs n hn).2)).congr_left fun n => ?_
  simp only [hsDefect, ht]
  ring

theorem isLittleO_pow_pw (D : ℕ) : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D :=
  (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop

theorem proof (hPB : ProjectionBounds.Statement) (hCL : ChangeOfLattice.Statement)
    (hTop : TopPullFS.Statement) (hDeg : ProjDegGenDeg.Statement) (hInv : GenDegMatAct.Statement)
    (hFC : FrameChange.Statement) (hMF : MetricToFS.Statement) : ReductionToProjective.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨fun e hfr hFS => defect_pullFS hPB hTop I hI d e hfr hFS, ?_⟩
  obtain ⟨B, d', e, hB, hx', hm', hfr', hidx⟩ := hFC D Ω κ d
  obtain ⟨d₀, hx₀, hFS₀, hmet⟩ := hMF D Ω κ I d' e hI hfr'
  have hfr₀ : IsProjFrame d₀.x e := hx₀ ▸ hfr'
  have hFS₀' : IsPullFS d₀.x e d₀.m := hx₀ ▸ hFS₀
  have h1 := (defect_pullFS hPB hTop I hI d₀ e hfr₀ hFS₀').trans_isLittleO (isLittleO_pow_mul_log D)
  rw [hx₀] at h1
  have h2 := (hCL D Ω κ I d.x B d.m d'.m hI d.arith d.indep hB d.smooth hm').trans_isLittleO
    (isLittleO_pow_pw D)
  rw [← hx'] at h2
  have hg : (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) = (projDeg d'.x e : ℝ) := by
    have hd := hDeg D Ω κ d'.x e d'.arith hfr'
    have hi := hInv D Ω κ d.x B hB
    rw [← hx', hd] at hi
    rw [← hi]
    push_cast
    rfl
  rw [hg]
  refine ((h1.sub hmet).sub (hidx.add h2)).congr_left fun n => ?_
  simp only [hsDefect]
  ring

end ReductionToProjective

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField Filter Topology

theorem isOpen_multiconePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem leviForm_eq_of_eventuallyEq_add_const {κ : Type*} [Fintype κ] (φ ψ : (κ → ℂ) → ℝ) (c : ℝ)
    (z w : κ → ℂ) (h : ψ =ᶠ[𝓝 z] fun x => φ x + c) : leviForm ψ z w = leviForm φ z w := by
  have h1 : fderiv ℝ ψ =ᶠ[𝓝 z] fderiv ℝ φ := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h1.fderiv_eq]

theorem TwistMetric.proof (hEW : EmbeddingWeight.Statement)
    (hTI : TwistIntersectionAnyDegree.Statement) : TwistMetric.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A P0 II u hD hII hY hbir _ hsemi hconj hlies hu hsum
  refine ⟨((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a, fun δ hδ => ?_⟩
  obtain ⟨B, hBa, hBs, hBc, hBloc⟩ := hEW K ι Ω F y (fun sg => Real.exp (u sg + δ))
    (fun _ => Real.exp_pos _) (fun sg => by simp only [hu]) hlies
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (F →+* ℂ) :=
      Fintype.card_pos_iff.mpr ⟨(IsAlgClosed.lift (R := ℚ) (S := F) (M := ℂ)).toRingHom⟩
    exact_mod_cast this.ne'
  refine ⟨A.tensor B, ?_, ?_, ?_, fun z hz sg hsg => ?_, ?_⟩
  · change A.a + B.a = A.a
    rw [hBa, add_zero]
  · unfold IsSemipositiveRel
    refine ⟨ContDiffOn.mul hsemi.1 hBs, fun z hz w hw => ?_⟩
    obtain ⟨sg, hsg, -⟩ := hlies z hz
    have hzA : ∀ᶠ x in 𝓝 z, A.h x ≠ 0 := by
      filter_upwards [isOpen_multiconePts.mem_nhds hz.1] with x hx using (A.pos x hx).ne'
    have heq : (fun x => Real.log ((A.tensor B).h x)) =ᶠ[𝓝 z]
        fun x => Real.log (A.h x) + Real.log (Real.exp (u sg + δ)) := by
      filter_upwards [hzA, hBloc z hz sg hsg] with x hx hB
      change Real.log (A.h x * B.h x) = _
      rw [hB, Real.log_mul hx (Real.exp_pos _).ne']
    rw [leviForm_eq_of_eventuallyEq_add_const _ _ _ z w heq]
    exact hsemi.2 z hz w hw
  · intro z
    change A.h _ * B.h _ = A.h z * B.h z
    rw [hconj z, hBc z]
  · change A.h z * B.h z = _
    rw [(hBloc z hz sg hsg).self_of_nhds, mul_comm]
  · rw [hTI K ι Ω F y D A B II (fun sg => Real.exp (u sg + δ)) hD hII hY hbir hsemi.1 hBa hBs
      (fun _ => Real.exp_pos _) hlies hBloc]
    have hs : (∑ sg, Real.log ((fun sg => Real.exp (u sg + δ)) sg)) / Fintype.card (F →+* ℂ) = δ := by
      simp only [Real.log_exp, Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, zero_add]
      field_simp
    rw [hs]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem TwoBlockPieceCycle.proof (hA : TwoBlockPieceIndex.Statement) (hF : TwoBlockModuleFinite.Statement)
    (hH : ModulePieceHilbert.Statement) (hC : TwoBlockModuleCycle.Statement) : TwoBlockPieceCycle.Statement := by
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl
  obtain ⟨hm₁, hm₂, hle, ⟨N, hN, hNJ⟩, hdim⟩ := hF D Ω κ x B c l hX hx hB hsp hl
  obtain ⟨a₀, C, h⟩ := hH (Fin 2) (FinTwoTypeFamily κ) _ _ N D hm₁ hm₂ hle hN hNJ hdim (fun _ => 1)
  refine ⟨a₀, C, fun a b ha hb => ?_⟩
  have h1 := h ![a, b] (fun k => by fin_cases k <;> simpa)
  have e1 : (![a, b] + fun _ => 1 : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun (_ : Fin D) (k : Fin 2) => ((![a, b] k : ℕ) : ℤ)) = fun _ => ![(a : ℤ), (b : ℤ)] := by
    funext _ k
    fin_cases k <;> rfl
  have e3 : ((∑ k, ![a, b] k : ℕ) : ℝ) = (a + b : ℝ) := by
    simp [Fin.sum_univ_two]
  rw [e1, e2, hC D Ω κ x B c l hX hx hB hsp hl, e3] at h1
  rw [hA D Ω κ x B c l hX hx hB hsp hl a b]
  exact h1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

theorem charZero_of_isHorizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast, ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn,
      map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem ArithmeticVolumeBig.proof (hB : G6.StatementB) (hZ : ArithmeticVolumeDegreeZero.Statement) : ArithmeticVolumeBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  by_cases hbig : 0 < genDeg (mCoordIdeal y) D A.a
  · have : CharZero Ω := charZero_of_isHorizontal y har.2.2.1
    exact hB K ι Ω y D A P0 II hD hII har hb ⟨hP0, hs, hc, hnef, hbig⟩
  · exact hZ K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc (not_lt.mp hbig)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

set_option linter.unusedSectionVars false

section Coordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_smul_one (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y a τ = chartLatQ y ((τ : ℤ) • a) 1 := by
  ext s
  show (∀ c : ∀ k, ι k, _ → _) ↔ (∀ c : ∀ k, ι k, _ → _)
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]

end Coordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def BlockRealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    (fun n => blockChi d n - blockCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y a n)) = Module.finrank ℚ (chartLatQ y a n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
