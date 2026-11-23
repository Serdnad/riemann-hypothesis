module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.LocalRingCardinality.Bundle006
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

theorem finrank_host (D : D7) : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  push_cast
  ring

theorem discr_rpow (D : D7) :
    |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f) = D.host.rdE ^ 2 := by
  have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  unfold Host.rdE
  rw [finrank_host, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  field_simp

theorem two_le_dimY (D : D7) {j : ℕ} (hj : j < D.R.m) (h1 : 1 ≤ j) : 2 ≤ WeightFamilies.dimY D j := by
  have hf : 8 ≤ D.R.f := D.eight_le_f
  have hk := D.R.m_add_three_le_k
  have hp : 1 ≤ (D.R.sigW j).1 := by unfold Ranks.sigW; simp only; omega
  have hq : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpq : 1 ≤ (D.R.sigW j).1 * (D.R.sigW j).2 := Nat.mul_pos hp hq
  unfold WeightFamilies.dimY
  calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hf (by omega)

theorem core (r f m ρ rd PP c T g DF q : ℝ) (hg : g = 1250 * r) (hr : 0 ≤ r) (hrT : r ≤ T) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ m) (hrd : 2 * f * m ≤ rd) (hPP : 0 < PP) (hq : 0 < q)
    (hc : c = rd ^ 7 * PP * DF ^ 2 / q) (hql : (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 ≤ q) (hgP : g * f * m ^ 3 ≤ PP ^ 2) :
    r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) ≤ 2 * T := by
  have h2f : 2 * f ≤ rd := by nlinarith
  have hrd1 : 1 ≤ rd := by linarith
  have hT : 0 ≤ T := hr.trans hrT
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcP : c * (PP ^ 2 * rd ^ 21) ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one hq]
    calc _ = (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := hql
  have e : r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) =
      r + T * (c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9))) := by
    rw [hg]; field_simp; ring
  have a1 : g * f * ρ ^ 3 ≤ PP ^ 2 := by
    refine le_trans ?_ hgP
    have : 0 ≤ g * f := by rw [hg]; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρ 3) this
  have a2 : 2 * f * rd ^ 9 ≤ rd ^ 21 := by
    calc 2 * f * rd ^ 9 ≤ rd * rd ^ 9 := mul_le_mul_of_nonneg_right h2f (by positivity)
      _ = rd ^ 10 := by ring
      _ ≤ rd ^ 21 := pow_le_pow_right₀ hrd1 (by norm_num)
  have a3 : (g * f * ρ ^ 3) * (2 * f * rd ^ 9) ≤ PP ^ 2 * rd ^ 21 :=
    mul_le_mul a1 a2 (by positivity) (by positivity)
  have a4 : c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9)) ≤ 1 := (mul_le_mul_of_nonneg_left a3 hc0).trans hcP
  rw [e]
  have := mul_le_mul_of_nonneg_left a4 hT
  linarith

theorem numbers : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → j < D.R.m → 1 ≤ j → 1 ≤ WeightAlgebra.DF wL → 0 < WeightAlgebra.cc D large₂ C2 A2 CR wL ∧ (Tn : ℝ) * WeightAlgebra.cc D large₂ C2 A2 CR wL * g0 D ≤ 1 ∧ 1 ≤ WeightFamilies.RRv D K.CRm ∧ (D.R.r : ℝ) * (1 + WeightFamilies.c1 D K.CRm Tn (WeightAlgebra.cc D large₂ C2 A2 CR wL) j / (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) ≤ 2 * Tn ∧ addL wF wL Tn = ka ∧ 2 ≤ WeightFamilies.dimY D j ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn := by
  intro D B P j X K Ch Ah Cq Aq large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hH ht hPg hj h1 hDF
  obtain ⟨hA, hS, h3, -, -⟩ := hH
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hL, hF, -, -, -, -, hrT, -, -, h11, -, hd⟩ := hS
  have hgP := g0fm3_le_of_dom hPg ht hd
  obtain ⟨e1, e2, e3⟩ := tie_eqs ht
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hK : K.CRm = 7 := ht.2.2.2.2.2.2.1
  have hrd16 := sixteen_le_rdE_of_parA hA
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hRR : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
    unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hC : 1000 ≤ C2 := ht.1 ▸ hd.1
  have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have := WeightFamilies.one_le_zBase large₂
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hql, -, -, hTc, -, -⟩ := h3
  rw [Real.rpow_zero, one_mul, hCR, hRR] at hql
  rw [e1, e2, e3] at hTc
  have hDF' : (1 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrd0 : 0 < D.host.rdE := by linarith
  have hq : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by positivity) hql
  have hc : WeightAlgebra.cc D large₂ C2 A2 CR wL = D.host.rdE ^ 7 * WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 / (qq D : ℝ) := by
    unfold WeightAlgebra.cc; rw [hCR, hRR]
  refine ⟨by rw [hc]; positivity, hTc, ?_, ?_, ?_, two_le_dimY D hj h1, h11⟩
  · rw [hK, hRR]; exact one_le_pow₀ (by linarith)
  · rw [discr_rpow]
    unfold WeightFamilies.c1 WeightFamilies.dP
    rw [hK, hRR]
    push_cast
    have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    refine core _ _ (D.R.m : ℝ) _ _ _ _ _ (g0 D : ℝ) _ _ ?_ (Nat.cast_nonneg _) ?_ (by linarith) (by linarith)
      (Nat.cast_nonneg _) ?_ hrd hPP hq hc hql hgP
    · unfold g0; push_cast; norm_num
    · exact_mod_cast (by omega : D.R.r ≤ Tn)
    · have : WeightFamilies.rho D j ≤ D.R.m := by unfold WeightFamilies.rho Ranks.sigW; simp only; omega
      exact_mod_cast this
  · obtain ⟨f1, f2, f3⟩ := hF
    have l1 := hL.1
    obtain ⟨aP, aM, p1, p2, n, p3⟩ := ka
    unfold addL wadd wsmul
    simp only [WeightFamilies.Wt.mk.injEq]
    simp only at hn f2 f3
    refine ⟨?_, ?_, ?_⟩
    · funext τ i
      have := f2 τ i
      zify; linarith
    · funext τ i
      have := f3 τ i
      zify; linarith
    · rw [f1, l1, hn, hnV]

end GlobalTheory.ExtraWeight
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory

theorem shareRho_and_shareRhoT_of_shareRhoR :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
      (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) (Gc : ℝ), ShareRhoR G S T d → G.TiedZ S T Gc →
      (∀ la, InContainZ G la S T) →
      ShareRho (D := D) (j := j) T G.rz d ∧ ShareRhoT (D := D) (j := j) T G.rz G.rq d := by
  intro D B P j X ka wL wF G S T d Gc hR hT hZ
  obtain ⟨la0⟩ := Formalism.MainNotions.Gaps.EtaleWeightGaps.exists_prime B.KO
  have hr : Module.finrank (Kp X la0 G.N) ↥(Submodule.span (Kp X la0 G.N) (zAll G la0 S T)) = G.rz :=
    rz_eq_finrank G S T Gc la0 hT (hZ la0)
  have h := hR la0
  rw [hr] at h
  refine ⟨h, ?_⟩
  unfold ShareRhoT
  have h0 : (0 : ℝ) ≤ (G.rq : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviFibre

theorem contDiffAt_two_of_eventually {n : ℕ} {f : V n → ℂ} {z0 : V n}
    (h : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ f z) : ContDiffAt ℂ 2 f z0 := by
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 h
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffAt_complex hUo
    (fun z hz => (hU z hz).differentiableWithinAt) hz 2

theorem sum_wd_mul {n : ℕ} {f : V n → ℂ} {z0 : V n} (h : DifferentiableAt ℂ f z0)
    (ξ : Fin n → ℂ) : ∑ j, wd n j f z0 * ξ j = fderiv ℂ f z0 (WithLp.toLp 2 ξ) := by
  have hξ : (WithLp.toLp 2 ξ : V n) = ∑ j, ξ j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (WithLp.toLp 2 ξ)]
    simp [bas]

  rw [hξ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wd_of_differentiableAt h, map_smul, smul_eq_mul, mul_comm]

theorem fderiv_eq_of_quot {n : ℕ} {f g : V n → ℂ} {z0 v : V n} (hf : DifferentiableAt ℂ f z0)
    (hg : DifferentiableAt ℂ g z0) (h0 : g z0 ≠ 0)
    (h : fderiv ℂ (fun z => f z / g z) z0 v = 0) :
    fderiv ℂ f z0 v = (fderiv ℂ g z0 v / g z0) * f z0 := by
  have hq : DifferentiableAt ℂ (fun z => f z / g z) z0 := by
    simp only [div_eq_mul_inv]
    exact hf.mul (hg.inv h0)
  have hev : f =ᶠ[𝓝 z0] fun z => (f z / g z) * g z := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with z hz
    field_simp
  rw [hev.fderiv_eq, fderiv_fun_mul hq hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h]
  field_simp
  ring

theorem levi_log_sum_eq_zero {n m : ℕ} (z0 : V n) (ξ : Fin n → ℂ) (s : Fin m → V n → ℂ)
    (k0 : Fin m) (hs : ∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) (h0 : s k0 z0 ≠ 0)
    (hq : ∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) :
    leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ = 0 := by
  have hne : (fun i => s i z0) ≠ 0 := fun h => h0 (congrFun h k0)
  have key := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n m s z0 ξ
    (fun k => contDiffAt_two_of_eventually (hs k)) hne
  have hJ : ReciprocityTheory.L2DbarEstimates.H.wJac n m s z0 *ᵥ ξ =
      (fderiv ℂ (s k0) z0 (WithLp.toLp 2 ξ) / s k0 z0) • (fun i => s i z0) := by
    funext i
    have := sum_wd_mul (hs i).self_of_nhds ξ
    rw [fderiv_eq_of_quot (hs i).self_of_nhds (hs k0).self_of_nhds h0 (hq i)] at this
    simpa [ReciprocityTheory.L2DbarEstimates.H.wJac, Matrix.mulVec, dotProduct] using this
  have hP : ReciprocityTheory.L2DbarEstimates.projPerp (fun i => s i z0) *ᵥ (fun i => s i z0) = 0 :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self _ hne
  rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at key
  simp only [ReciprocityTheory.L2DbarEstimates.sqNorm, Complex.normSq_eq_norm_sq] at key
  rw [key]
  simp

theorem main : ∀ (n : ℕ) (z0 : V n) (ξ : Fin n → ℂ), (∀ (m : ℕ) (s : Fin m → V n → ℂ) (k0 : Fin m), (∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) → s k0 z0 ≠ 0 → (∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) → (leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ).re = 0) ∧ ∀ g : V n → ℝ, ContDiffAt ℝ 2 g z0 → IsLocalMax g z0 → (leviV n (fun z => ((g z : ℝ) : ℂ)) z0 ξ).re ≤ 0 := by
  intro n z0 ξ
  refine ⟨fun m s k0 hs h0 hq => ?_, fun g hg hmax => ?_⟩
  · rw [levi_log_sum_eq_zero z0 ξ s k0 hs h0 hq, Complex.zero_re]
  · exact ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hg hmax ξ

end GlobalTheory.LeviFibre
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FreeDivMetric

open GlobalTheory.Up GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}


open Classical in
noncomputable def Wfree (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ)

theorem Wfree_of_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X G x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wfree
  rw [if_pos hx]

theorem Wfree_of_notMem {x : Frame X.Ψ r} (hx : x ∉ X.dom) : Wfree Xa Fl G n x = 0 := by
  unfold Wfree
  rw [if_neg hx]

private lemma sum_norm_sq_pos_of_exists_ne_zero {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun i _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hk) 2⟩

theorem Wfree_eq_exp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-(phla X G x +
      (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)))) := by
  have hA : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero (Xa.w_nz x hx)
  have hB : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_norm_sq_pos_of_exists_ne_zero hs
  have key : Real.exp (-(phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))) =
      Real.exp (-phla X G x) * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
        (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hA.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_rpow_of_pos hA, ENNReal.ofReal_rpow_of_pos hB]

theorem Wfree_eq_pnorm {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Wfree Xa Fl G n x = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have hc : 0 < Real.exp (-phla X Xa.L x) := Real.exp_pos _
  have hw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Xa.w k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have hs : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = Real.exp (-phla X Xa.L x) * ∑ k, ‖Fl.s k x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.Up.pnorm_sq_eq_exp hx _ _
  have key : Real.exp (-phla X G x) = Real.exp (-phla X (G + n • Xa.L) x) *
      Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ)) * Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2)) := by
    rw [GlobalTheory.Up.phla_add_nsmul hx, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [Wfree_of_mem Xa Fl G n hx, hw, hs, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos hc, ENNReal.ofReal_rpow_of_pos hc, key,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hc.le _)),
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

private lemma isBddSec_of_mem_SSgt {la : Wt X.Ψ r} {c : ℝ} {P : Frame X.Ψ r → ℂ} (h : P ∈ X.SSgt la c) :
    X.IsBddSec la P := h.1.1

theorem measurable_Wfree : Measurable (Wfree Xa Fl G n) := by
  have hw : ∀ k, ContinuousOn (Xa.w k) X.dom := fun k => (isBddSec_of_mem_SSgt (Xa.w_van k)).1.1.continuousOn
  have hs : ∀ k, ContinuousOn (Fl.s k) X.dom := fun k => (isBddSec_of_mem_SSgt (Fl.s_van k)).1.1.continuousOn
  have ha : ContinuousOn (fun x => Real.exp (-phla X G x)) X.dom :=
    Real.continuous_exp.comp_continuousOn (IW.phla_contOn X G).neg
  have hA : ContinuousOn (fun x => ∑ k, ‖Xa.w k x‖ ^ 2) X.dom :=
    continuousOn_finsetSum _ fun k _ => ((hw k).norm).pow 2
  have hB : ContinuousOn (fun x => ∑ k, ‖Fl.s k x‖ ^ 2) X.dom :=
    continuousOn_finsetSum _ fun k _ => ((hs k).norm).pow 2
  have e : Wfree Xa Fl G n = fun x =>
      X.dom.indicator (fun x => ENNReal.ofReal (Real.exp (-phla X G x))) x *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2)) x ^ (-(1 / 2 : ℝ)) *
        X.dom.indicator (fun x => ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2)) x ^ (-((n : ℝ) - 1 / 2)) := by
    funext x
    by_cases hx : x ∈ X.dom
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact Wfree_of_mem Xa Fl G n hx
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul]
      exact Wfree_of_notMem Xa Fl G n hx
  rw [e]
  exact ((GlobalTheory.Up.DivMetricPf.measurable_cut ha).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hA).pow_const _)).mul
    ((GlobalTheory.Up.DivMetricPf.measurable_cut hB).pow_const _)

theorem Wfree_rmul (hN : NfacRmulStatement (E := E)) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    Wfree Xa Fl G n (rmul x b) =
      Wfree Xa Fl G n x / ENNReal.ofReal (‖bchar (G + n • Xa.L) b‖ ^ 2) := by
  have hxb : rmul x b ∈ X.dom := OntoS.dom_rmul X hx hb
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (rmul x b) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hx hb
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (rmul x b) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_rmul hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hx hb
  have h1 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hxb (G + n • Xa.L)
  have h2 := GlobalTheory.Up.DivMetricPf.exp_neg_phla hx (G + n • Xa.L)
  have h3 := hN r X (G + n • Xa.L) x hx b hb
  have hn0 : X.nfac (G + n • Xa.L) (rmul x b) ≠ 0 := by
    intro h
    have hp := Real.exp_pos (-phla X (G + n • Xa.L) (rmul x b))
    rw [h1, h] at hp
    norm_num at hp
  have hc : ‖bchar (G + n • Xa.L) b‖ ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at h3
    exact hn0 h3
  have hc2 : 0 < ‖bchar (G + n • Xa.L) b‖ ^ 2 := by positivity
  have hph : Real.exp (-phla X (G + n • Xa.L) (rmul x b)) =
      Real.exp (-phla X (G + n • Xa.L) x) / ‖bchar (G + n • Xa.L) b‖ ^ 2 := by
    rw [h1, h2, h3]
    field_simp
  rw [Wfree_eq_pnorm Xa Fl G n hxb, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs]
  rw [hph, ENNReal.ofReal_div_of_pos hc2]
  simp only [div_eq_mul_inv]
  ring

theorem Wfree_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wfree Xa Fl G n (lact γ x) = Wfree Xa Fl G n x := by
  have hxg : lact γ x ∈ X.dom := OntoS.dom_lact X hγ hx
  have hw : ∀ k, X.pnorm Xa.L (Xa.w k) (lact γ x) = X.pnorm Xa.L (Xa.w k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Xa.w_van k)).1 hγ hx
  have hs : ∀ k, X.pnorm Xa.L (Fl.s k) (lact γ x) = X.pnorm Xa.L (Fl.s k) x := fun k =>
    GlobalTheory.Up.DivMetricPf.pnorm_lact hN (isBddSec_of_mem_SSgt (Fl.s_van k)).1 hγ hx
  have hph : Real.exp (-phla X (G + n • Xa.L) (lact γ x)) = Real.exp (-phla X (G + n • Xa.L) x) := by
    rw [GlobalTheory.Up.DivMetricPf.exp_neg_phla hxg, GlobalTheory.Up.DivMetricPf.exp_neg_phla hx, hN r X _ γ hγ x hx]
  rw [Wfree_eq_pnorm Xa Fl G n hxg, Wfree_eq_pnorm Xa Fl G n hx]
  simp only [hw, hs, hph]

theorem Wfree_lower (hn : 1 ≤ n) : WLower X (G + n • Xa.L) (Wfree Xa Fl G n) := by
  obtain ⟨C, hC, hCw⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Xa.w_van k)
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.Up.DivMetricPf.exists_sum_le fun k => isBddSec_of_mem_SSgt (Fl.s_van k)
  have ht : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)),
    mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _), fun x hx => ?_⟩
  have e1 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hC (hCw x hx) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have e2 := GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le hD (hDs x hx) ht
  rw [Wfree_eq_pnorm Xa Fl G n hx]
  calc ENNReal.ofReal (C ^ (-(1 / 2 : ℝ)) * D ^ (-((n : ℝ) - 1 / 2)) * Real.exp (-phla X (G + n • Xa.L) x))
      = ENNReal.ofReal (Real.exp (-phla X (G + n • Xa.L) x)) * ENNReal.ofReal (C ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (D ^ (-((n : ℝ) - 1 / 2))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hC.le _))]
        congr 1
        ring
    _ ≤ _ := by gcongr

theorem freeDivMetric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  intro E _ _ _ r X Xa Fl G n hn
  have hR := GlobalTheory.NormFactor.nfacRmul_holds (E := E)
  have hL := GlobalTheory.NormFactor.nfacLact_holds (E := E)
  exact ⟨⟨measurable_Wfree Xa Fl G n, fun x hx b hb => Wfree_rmul Xa Fl G n hR hx hb,
    fun γ hγ x hx => Wfree_lact Xa Fl G n hL hγ hx⟩, Wfree_lower Xa Fl G n hn,
    fun x hx hs => Wfree_eq_exp Xa Fl G n hx hs⟩

end GlobalTheory.FreeDivMetric
end
