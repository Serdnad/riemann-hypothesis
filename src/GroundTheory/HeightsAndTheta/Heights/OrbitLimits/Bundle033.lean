module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle081
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle037
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle010
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem genFibreExists : GenFibreExistsStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' _ hP'
  exact Inter.GenericPointExists.proof K ι K' ι' v P' hP'.2.1.1

theorem existsUniqueAll : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)], ExistsUniqueStatement F ι := by
  intro F _ K _ ι _
  exact ExistsUnique.full F ι

theorem ChangeOfModel.of_found (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hIso : HilbertSamuel.IsomInvariance.Statement) (hGI : HilbertSamuel.GraphIsometric.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
  HilbertSamuel.ChangeOfModel.proof hAI3 hGr genFibreExists existsUniqueAll hIso hGI

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem Contract.pulledBackForms_topDensity_vanish : pointForm_holds.Statement :=
  pointForm_holds.proof (pointFormRank_holds.proof RatioAlgDep.proof) pointFormEuler_holds.proof

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_finset_sum {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type*} (S : Finset T) (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ (fun z => ∑ t ∈ S, u t z) y w = ∑ t ∈ S, sheetDensity Q Ψ φ (u t) y w := by
  unfold sheetDensity
  split_ifs <;> simp [Finset.sum_mul]

theorem integrable_fibreSum_degZero (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsDegZeroSmooth u) :
    Integrable (fun y => ∑ᶠ w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y, sheetDensity Q Ψ (pot L) u y w) := by
  have hsm : IsSmoothHerm (HermLine.ofWeight u hu.2) :=
    Real.contDiff_exp.comp_contDiffOn hu.1.neg
  have h := hInt K ι Q e Ψ L (HermLine.ofWeight u hu.2) 1 hQ hΨ hL hsm
    (Inter.isSectionOn_one hQ rfl)
  have hlog : logNorm (HermLine.ofWeight u hu.2) 1 = u := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_inv, Real.log_exp]
  rwa [hlog] at h

theorem ptsIntegral_finset_sum (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {T : Type*}
    (S : Finset T) {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t)) :
    ptsIntegral Q (pot L) (fun z => ∑ t ∈ S, u t z) = ∑ t ∈ S, ptsIntegral Q (pot L) (u t) := by
  classical
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  · simp only [ptsIntegral, dif_pos hΨ, ptsIntegralAt]
    rw [← integral_finsetSum S fun t _ =>
      integrable_fibreSum_degZero hInt hQ hΨ.choose_spec hL (hu t)]
    congr 1
    funext y
    have hfin := fibreFinite K ι Q e hΨ.choose hQ hΨ.choose_spec y
    simp only [sheetDensity_finset_sum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
  · simp [ptsIntegral, dif_neg hΨ]

theorem LelongSectionLimit.proof (hInt : PtsIntegrableStatement) (hChart : LelongChartLimit.Statement) :
    LelongSectionLimit.Statement := by
  classical
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hne : ∀ k, Nonempty (ι k) := fun k => ⟨(hP.2.1.2.2 k).choose⟩
  obtain ⟨δ, hδ, ρ, hρ, hsum, hsupp⟩ := SegrePartition.proof K ι hne
  have hv := isDegZeroSmooth_log hB hBa
  have hg : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρ i).mul hv
  have hvsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) :=
    funext fun z => by rw [← Finset.sum_mul, hsum, one_mul]

  have hlim := tendsto_finsetSum (Finset.univ : Finset ((k : K) → ι k)) fun i _ =>
    hChart K ι P n L A s _ i δ hP hL hA hs (hg i) hδ fun z hz => by simp [hsupp i z hz]

  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  have hsplit : ∀ f : Ideal (MRing ι) → ℝ,
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), f W = ∑ W ∈ hfin.toFinset, f W :=
    fun f => finsum_mem_eq_finite_toFinset_sum f hfin
  have hW : ∀ W ∈ hfin.toFinset, ptsIntegral W (pot L) (fun z => Real.log (B.h z)) =
      ∑ i, ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z)) := by
    intro W hW
    rw [Set.Finite.mem_toFinset] at hW
    have hWar : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
    rw [hvsum]
    exact ptsIntegral_finset_sum hInt hWar hL Finset.univ hg
  have hrhs : (∑ i, ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => ρ i z * Real.log (B.h z))) =
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    simp only [hsplit]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun W hW' => ?_
    rw [hW W hW', Finset.mul_sum]
  rw [hrhs] at hlim

  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  set M := (regLine A s ε ha hsa).tensor A
  have hM : IsSmoothHerm M := (isSmoothHerm_regLine hA hε ha hsa).mul hA
  have hcongr : ∀ g : ((Σ k, ι k) → ℂ) → ℝ,
      ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    intro g
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) :=
    fun j => Fin.cases hM (fun i => hL i) j
  simp only [hcongr]
  rw [hvsum]
  exact (ptsIntegral_finset_sum hInt hP hML Finset.univ hg).symm

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre mcPts
  isOpen_blockNonzero)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartComponents mem_segreChartComponents chartLift
  contDiff_chartLift chartLift_blockNonzero segre_chartLift chart_coord_eq_one)

theorem LelongChartLimit.proof (hInt : SegreChartIntegral.Statement) (hDim : SegreChartDim.Statement)
    (hNot : ChartSectionNotMem.Statement) (hLel : LelongPolyLimit.Statement)
    (hDiv : ChartDivisorCompare.Statement) : LelongChartLimit.Statement := by
  classical
  intro K _ _ ι _ P n L A s g i δ hP hL hA hs hg hδ hsupp
  obtain ⟨a, ha, hsa, -⟩ := id hs
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let G := fun x => χ x * g (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  let kk := fun x => A.h (lam x)
  let F := fun (ε : ℝ) x => Real.log (‖eval x (chartSection σ i s)‖ ^ 2 + ε * kk x ^ 2) / 2
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i
  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'
  have hxΩ : ∀ x ∈ segreChartSet P σ i, x ∈ Ω := by
    rintro _ ⟨z, -, hzi, rfl⟩
    exact chartLift_blockNonzero σ i (by simp [σ, hzi])

  have key : ∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [G, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [G, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)

  have hlim := tendsto_finsetSum (segreChartComponents P σ i) fun J hJs =>
    hLel _ n J (chartSection σ i s) G kk Φ (mem_segreChartComponents.1 hJs).1.1
      (hDim K ι P (n + 1) _ σ i hP J hJs) (hNot K ι P (n + 1) _ σ i A s hP hs J hJs)
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm g hg.1)⟩ χ.hasCompactSupport.mul_right
      (fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩) ⟨Ω, hΩ, hJ J hJs, hsm _ hA⟩
      fun x hx => A.pos _ (hJ J hJs hx)
  rw [hDiv K ι P n _ σ i L A s g δ G Φ hP hL hs hg hδ hsupp
    fun x hx => ⟨key x hx, fun j => EventuallyEq.rfl⟩] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)

  set M := (regLine A s ε ha hsa).tensor A
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) :=
    fun j => Fin.cases ((isSmoothHerm_regLine hA hε ha hsa).mul hA) (fun i => hL i) j
  have hcongr : ptsIntegral P
      (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
        (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  beta_reduce
  rw [hcongr]
  refine (hInt K ι P n _ σ i (Fin.cons M L) g δ G (Matrix.vecCons (F ε) Φ) hP hML hg hδ (Or.inl hsupp)
    fun x hx => ⟨key x hx, fun j => ?_⟩).symm
  refine Fin.cases ?_ (fun j => EventuallyEq.rfl) j
  filter_upwards [hΩ.mem_nhds (hxΩ x hx)] with y hy
  simp only [Matrix.cons_val_zero, Function.comp_apply, Inter.PtsAddFirst.pot_cons, Fin.cons_zero, F, kk,
    eval_chartSection]
  exact (log_regLine_tensor A s hε ha hsa (lam y) hy).symm

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensIntegrable.proof (hMass : PtsSemiPosMassFinite.Statement) : PtsPosDensIntegrable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg
  classical
  obtain ⟨M, hMb⟩ := PtsPosDens.exists_bound hg
  choose T hTs hTp hLTp using fun j => Inter.SemiPosTwist.proof Inter.TorusInvLevi.proof K ι (L j) (hL j)
  set N : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => ((L j).tensor (T j)).tensor (T j) with hNdef
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)
  have hNs : ∀ j, IsSmoothHerm (N j) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hLT j) (hTs j)
  have hNp : ∀ j, Inter.IsSemiPosHerm (N j) := fun j =>
    PtsPosDens.isSemiPosHerm_tensor (hLT j) (hTs j) (hLTp j) (hTp j)
  have hfinM := hMass K ι P e Ψ N hP hΨ hNs hNp
  have hfib := fibreFinite K ι P e Ψ hP hΨ
  set C : ℝ := max M 0 * 3 ^ e with hCdef
  have hC : 0 ≤ C := by positivity

  have key : ∀ y w, max (sheetDensity P Ψ (pot L) g y w) 0 ≤
      C * max (sheetDensity P Ψ (pot N) (fun _ => 1) y w) 0 := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      have hS := hγ.choose_spec
      have hab : |maDensity (fun j y' => pot L j (hγ.choose y')) y| ≤
          3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp hS
      have hmc : hγ.choose y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hgb : |g (hγ.choose y)| ≤ max M 0 := (hMb _ hmc.1).trans (le_max_left _ _)
      have hn : 0 ≤ maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hab) (by positivity)
      calc max (g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y) 0
          ≤ |g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ = |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y| := abs_mul _ _
        _ ≤ max M 0 * (3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y) :=
            mul_le_mul hgb hab (abs_nonneg _) (le_max_right _ _)
        _ = C * max (1 * maDensity (fun j y' => pot N j (hγ.choose y')) y) 0 := by
            rw [one_mul, max_eq_left hn, hCdef]
            ring
    · rw [dite_eq_right hγ, dite_eq_right hγ, max_self, mul_zero]

  have hpt : ∀ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) ≤
      ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ptsPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfib y), finsum_mem_eq_finite_toFinset_sum _ (hfib y),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => key y w
  have hnn : ∀ y, 0 ≤ ptsPosDens P Ψ (pot L) g y := fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
  refine ⟨PtsPosDens.aestronglyMeasurable hP hΨ hL hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  calc ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y)
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinM

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]


omit [Fintype σ] in
theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange


end GroundTheory.Heights₂.Heights.Targets
end
end
