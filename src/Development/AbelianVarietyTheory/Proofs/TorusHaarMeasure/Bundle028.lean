module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChangeDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetMulStrictLowerEqOne
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableAtAdjugate
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralImageLeConst
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle021
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeadMCoeffEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ContDiff ENNReal

namespace GlobalTheory.SkodaIter

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def integrand (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G : V n → ℂ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  exact (hf.mono (HE.target_sub he)).congr (HE.comp_symm_eqOn f he)

theorem normSq_continuousOn {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (fun z => ∑ k, ‖s k z‖ ^ 2) U := by
  exact continuousOn_finsetSum _ (fun k _ => ((hs k).continuousOn.norm).pow 2)

theorem normSq_pos {s : Fin n → V n → ℂ} {z : V n} {k : Fin n} (h : s k z ≠ 0) :
    0 < ∑ k, ‖s k z‖ ^ 2 := by
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2)
    (Finset.single_le_sum (f := fun j => ‖s j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))

theorem extend (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    {ph : V n → ℝ} (hph : ContinuousOn ph U) {t : ℝ} (ht : 0 ≤ t) {G : V n → ℂ}
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ s k0 y ≠ 0})
    (hI : ∫⁻ z in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G z < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ s k0 y ≠ 0} ∧
      ∫⁻ z in U, integrand s ph t G' z < ⊤ := by
  have hM : IsOpen {y | y ∈ U ∧ s k0 y ≠ 0} := HE.isOpen_punct hU (hs k0)
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    have hKU : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hbU : ball p (ε / 2) ⊆ U := ball_subset_closedBall.trans hKU
    have hK : IsCompact (closedBall p (ε / 2)) := isCompact_closedBall p _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((normSq_continuousOn hs).mono hKU)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hph.mono hKU)
    refine ⟨ε / 2, half_pos hε, hbU, ?_⟩
    have hAM : ball p (ε / 2) \ {y | s k0 y = 0} ⊆ {y | y ∈ U ∧ s k0 y ≠ 0} :=
      fun y hy => ⟨hbU hy.1, hy.2⟩
    have hAeq : ball p (ε / 2) \ {y | s k0 y = 0} = ball p (ε / 2) ∩ {y | y ∈ U ∧ s k0 y ≠ 0} := by
      ext y
      exact ⟨fun h => ⟨h.1, hbU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hAm : MeasurableSet (ball p (ε / 2) \ {y | s k0 y = 0}) := by
      rw [hAeq]; exact (isOpen_ball.inter hM).measurableSet
    have hpt : ∀ y ∈ ball p (ε / 2) \ {y | s k0 y = 0},
        ENNReal.ofReal (‖G y‖ ^ 2) ≤ ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y := by
      intro y hy
      have hyK : y ∈ closedBall p (ε / 2) := ball_subset_closedBall hy.1
      have hpos : 0 < ∑ k, ‖s k y‖ ^ 2 := normSq_pos (k := k0) hy.2
      have hfB : ∑ k, ‖s k y‖ ^ 2 ≤ B := (Real.le_norm_self _).trans (hB y hyK)
      have hB0 : 0 < B := hpos.trans_le hfB
      have hphC : ph y ≤ C := (Real.le_norm_self _).trans (hC y hyK)
      have h1 : 1 ≤ (∑ k, ‖s k y‖ ^ 2) ^ (-t) * B ^ t := by
        rw [Real.rpow_neg hpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hpos t)]
        exact Real.rpow_le_rpow hpos.le hfB ht
      have h2 : 1 ≤ Real.exp C * Real.exp (-ph y) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h3 := mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
      simp only [integrand]
      rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hB0 t) (Real.exp_pos C)).le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖G y‖)]
    calc ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0},
            ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hAm hpt)
      _ = ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, integrand s ph t G y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G y :=
          mul_le_mul (le_refl _) (lintegral_mono_set hAM) zero_le zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
  obtain ⟨G', hG'd, hG'eq⟩ := HE.ext_glue hU (s k0) G (hs k0) hgn hG hloc
  refine ⟨G', hG'd, hG'eq, ?_⟩
  have hnull : volume {y | y ∈ U ∧ s k0 y = 0} = 0 := HE.zeros_null hU (hs k0) hgn
  have hae : (U : Set (V n)) =ᵐ[volume] {y | y ∈ U ∧ s k0 y ≠ 0} := by
    have e1 : volume (U \ {y | y ∈ U ∧ s k0 y ≠ 0}) = 0 :=
      measure_mono_null (fun y (hy : y ∈ U \ {y | y ∈ U ∧ s k0 y ≠ 0}) =>
        (⟨hy.1, Classical.byContradiction fun h => hy.2 ⟨hy.1, h⟩⟩ : y ∈ {y | y ∈ U ∧ s k0 y = 0})) hnull
    have e2 : volume ({y | y ∈ U ∧ s k0 y ≠ 0} \ U) = 0 :=
      measure_mono_null (fun y hy => (hy.2 hy.1.1).elim) measure_empty
    exact (ae_eq_set (μ := volume)).2 ⟨e1, e2⟩
  rw [Measure.restrict_congr_set hae]
  rw [lintegral_congr_ae (ae_restrict_of_forall_mem hM.measurableSet
    (fun y hy => show integrand s ph t G' y = integrand s ph t G y by simp only [integrand, hG'eq hy]))]
  exact hI

theorem step (hn : 2 ≤ n) (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (hS : ∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val)
    {ph : V n → ℝ} (hph : ContDiffOn ℝ ∞ ph U)
    (hl : ∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph w : ℝ) : ℂ)) z ξ).re)
    {t : ℝ} (ht : (n : ℝ) - 1 < t) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hI : ∫⁻ z in U, integrand s ph (t + 1) F z < ⊤) :
    ∃ h : Fin n → V n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U ∧
      ∫⁻ z in U, integrand s ph t (h i) z < ⊤) ∧ ∀ z ∈ U, F z = ∑ i, s i z * h i z := by
  obtain ⟨S, hSz⟩ := hS
  have hM : IsOpen {z | z ∈ U ∧ s k0 z ≠ 0} := HE.isOpen_punct hU (hs k0)
  have ht0 : 0 ≤ t := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (‖F x.1‖ ^ 2 * (∑ i, ‖s i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph x.1))
      ∂(vol n S.z) < ⊤ := by
    rw [hSz]
    refine (HE.lintegral_val hM (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖s i y‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph y)))).trans_lt ?_
    exact lt_of_le_of_lt (lintegral_mono_set (fun y hy => hy.1)) hI
  obtain ⟨hh, hhh, hdec, hbound⟩ := ReciprocityTheory.L2DbarEstimates.skoda n _ S n (fun i x => s i x.1) (fun x => ph x.1) t
    (fun x => F x.1) hn
    (fun i => by rw [hSz]; exact holo_val ((hs i).mono (fun y hy => hy.1)))
    (fun x => ⟨k0, x.2.2⟩)
    (by rw [hSz]; exact HE.smoothR_val (hph.mono (fun y hy => hy.1)))
    (by rw [hSz]; intro x ξ; rw [HE.levi_val hM ph x ξ]; exact hl x.1 x.2.1 ξ)
    ht
    (by rw [hSz]; exact holo_val (hF.mono (fun y hy => hy.1)))
    hint
  have hfin := lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
  rw [hSz] at hfin
  have hhv : ∀ i, Holo n (Subtype.val : {z // z ∈ {z | z ∈ U ∧ s k0 z ≠ 0}} → V n) (hh i) := by
    intro i; rw [← hSz]; exact hhh i
  have hGd : ∀ i, DifferentiableOn ℂ (HE.ext0 (hh i)) {z | z ∈ U ∧ s k0 z ≠ 0} :=
    fun i => HE.differentiableOn_extendByZero hM (hhv i)
  have hGi : ∀ i, ∫⁻ y in {z | z ∈ U ∧ s k0 z ≠ 0}, integrand s ph t (HE.ext0 (hh i)) y < ⊤ := by
    intro i
    refine ((HE.lintegral_val hM (fun y => integrand s ph t (HE.ext0 (hh i)) y)).symm.trans_le ?_).trans_lt hfin
    refine lintegral_mono (fun x => ?_)
    simp only [integrand, HE.extendByZeroOnSubset_apply_coe]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  choose H hHd hHeq hHint using fun i => extend hU k0 hs hgn hph.continuousOn ht0 (hGd i) (hGi i)
  refine ⟨H, fun i => ⟨hHd i, hHint i⟩, ?_⟩
  have hDc : ContinuousOn (fun z => F z - ∑ i, s i z * H i z) U :=
    hF.continuousOn.sub (continuousOn_finsetSum _ (fun i _ => (hs i).continuousOn.mul (hHd i).continuousOn))
  intro z hz
  by_contra hne
  have hW := hDc.isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨y, ⟨hyU, hyD⟩, hy0⟩ := hgn _ hW Set.inter_subset_left ⟨z, hz, by simpa [sub_eq_zero] using hne⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyD
  apply hyD
  have hd := hdec ⟨y, hyU, hy0⟩
  dsimp only at hd
  rw [sub_eq_zero, hd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hHeq i ⟨hyU, hy0⟩]
  exact (congrArg (fun w => s i y * w) (HE.extendByZeroOnSubset_apply_coe (hh i) ⟨y, hyU, hy0⟩)).symm

end

end GlobalTheory.SkodaIter
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeasureClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kapGG_holds : KapGGStatement (E := E) :=
  GlobalTheory.UnitriJac.kapGG_of_det GlobalTheory.det_conj_strictLower GlobalTheory.det_mul_strictLower_eq_one

theorem measInv_holds : MeasInvStatement (E := E) :=
  GlobalTheory.measInv_of_jacobian kapGG_holds GlobalTheory.NormFactor.nfac_transform

theorem frameMeas_holds : FrameMeasStatement (E := E) :=
  GlobalTheory.FrameMeas.frameMeas_of_local measInv_holds
    (GlobalTheory.frame_measure_local GlobalTheory.FrameSplit.frameSplit)

theorem extF_holds : ExtFStatement (E := E) :=
  extF_of lu_holds frameMeas_holds

theorem measure_statements :
    (KapGGStatement (E := E)) ∧ (MeasInvStatement (E := E)) ∧ (FrameMeasStatement (E := E)) ∧
      (ExtFStatement (E := E)) :=
  ⟨kapGG_holds, measInv_holds, frameMeas_holds, extF_holds⟩

end GlobalTheory.FrameMeasureClosed
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ManyForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_pow_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ}
    {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c) (hQ : X.IsBddSec L Q) (m : ℕ) :
    P * Q ^ m ∈ X.SSgt (G + m • L) c := by
  induction m with
  | zero => simpa using hP
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact (siegelSpaceAlgebra_holds r X _ L c).2.2.2 _ ih Q hQ

theorem mul_prod_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ} {ι : Type}
    {P : Frame X.Ψ r → ℂ} {s : ι → Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c)
    (hs : ∀ k, X.IsBddSec L (s k)) (α : ι → ℕ) (S : Finset ι) :
    P * ∏ k ∈ S, s k ^ α k ∈ X.SSgt (G + (∑ k ∈ S, α k) • L) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hP
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_comm (s a ^ α a), ← mul_assoc,
      add_comm (α a), add_nsmul, ← add_assoc]
    exact mul_pow_mem_SSgt X ih (hs a) _

theorem card_multiLt_succ (n T : ℕ) : (multiLt n (T + 1)).card = (T + n).choose n := by
  have h : multiLt n (T + 1) = Y.multiLe n T := by
    ext α
    rw [GlobalTheory.LeadIndep.mem_multiLt, Y.mem_multiLe_iff, Nat.lt_succ_iff]
  rw [h, Y.ind_count]

theorem exists_indep_forms : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T : ℕ) (c : ℝ), 0 ≤ c →
    (∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt G c, ∀ j, F (Fl.xs j) = v j) →
    ∃ f : Fin (Fl.δ * (T + nd X).choose (nd X)) → Frame X.Ψ r → ℂ,
      (∀ q, f q ∈ X.SSgt (G + T • Xa.L) c) ∧
      ∀ u : Fin (Fl.δ * (T + nd X).choose (nd X)) → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0 := by
  classical
  intro r X Xa Fl G T c _ hint
  choose F hF hFv using fun j : Fin Fl.δ => hint (Pi.single j 1)
  set M := multiLt (nd X) (T + 1) with hM
  set S : Finset (Fin Fl.δ) := Finset.univ with hS
  have hcard : (S ×ˢ M).card = Fl.δ * (T + nd X).choose (nd X) := by
    rw [Finset.card_product, hM, card_multiLt_succ, hS, Finset.card_univ, Fintype.card_fin]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let fP : Fin Fl.δ → (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α => F j * (∏ k, Fl.s k ^ α k) * Fl.w0 ^ (T - ∑ q, α q)
  refine ⟨fun q => fP (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · have hα : ∑ q', (e q).1.2 q' ≤ T :=
      Nat.lt_succ_iff.mp (GlobalTheory.LeadIndep.mem_multiLt.mp (Finset.mem_product.mp (e q).2).2)
    have h := mul_pow_mem_SSgt X
      (mul_prod_mem_SSgt X (hF (e q).1.1) (fun k => (Fl.s_van k).1.1) (e q).1.2 Finset.univ)
      Fl.weightForm_vanishes.1.1 (T - ∑ q', (e q).1.2 q')
    rwa [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hα] at h
  · let cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ S ×ˢ M then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ S ×ˢ M := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hcomb : ∀ x, leadM X Fl.s Fl.w0 F T (T + 1) cc x =
        ∑ q, a q * fP (e q).1.1 (e q).1.2 x := by
      intro x
      have h1 : leadM X Fl.s Fl.w0 F T (T + 1) cc x =
          ∑ p ∈ S ×ˢ M, cc p.2 p.1 * fP p.1 p.2 x := by
        rw [Finset.sum_product_right]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [fP, monoM, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
        ring
      rw [h1, ← Finset.sum_coe_sort (S ×ˢ M), ← e.sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have hind := GlobalTheory.LeadIndep.leadM_coeff_eq_zero r X Xa Fl G T (T + 1) Fl.δ F
      (fun k => (hF k).1.1.1)
      (fun u hu => by
        funext j
        have := hu j
        simpa [hFv, Pi.single_apply] using this) cc
      (fun j => by
        have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
          show cpt X (Fl.xs j) 0 ∈ X.dom
          rw [IW.cpt_zero]
          exact Fl.xs_mem j
        refine Asymptotics.IsBigO.of_bound 0 ?_
        filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with z hz
        rw [zero_mul, norm_le_zero_iff, hcomb]
        exact ha _ hz)
    funext q
    rw [← hc q]
    exact hind _ (Finset.mem_product.mp (e q).2).2 _

end GlobalTheory.ManyForms
end
