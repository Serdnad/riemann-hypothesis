module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapHolomorphicPullbackFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensity
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle102
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle078
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin

theorem hermitian_pair_one_coordinates (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] =
      G 0 0 + G 0 1 * b + (starRingEnd ℂ) a * G 1 0 + (starRingEnd ℂ) a * G 1 1 * b := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]
  ring

theorem gram_identity (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.IsHermitian) (a₀ a₁ : ℂ) :
    (herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 =
      G.det.re * ‖a₁ - a₀‖ ^ 2 := by
  have h10 : G 1 0 = (starRingEnd ℂ) (G 0 1) := (hG.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.apply 1 1)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, Matrix.det_fin_two,
    hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, hermitian_pair_one_coordinates, h10]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, h00, h11]
  ring

theorem hermitian_pair_one_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have hne : (![1, a] : Fin 2 → ℂ) ≠ 0 := fun h => by simpa using congrFun h 0
  have h := hG.dotProduct_mulVec_pos hne
  exact (Complex.lt_def.mp h).1

theorem det_re_pos (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.lt_def.mp hG.det_pos).1

theorem logSin_eq_log_add_xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) (hG : G.PosDef) (hne : a₀ ≠ a₁) :
    logSin G a₀ a₁ = Real.log ‖a₁ - a₀‖ + (1 / 2) * (xiPot G a₀ + xiPot G a₁) := by
  have hA := hermitian_pair_one_re_pos G hG a₀
  have hB := hermitian_pair_one_re_pos G hG a₁
  have hD := det_re_pos G hG
  have hn : 0 < ‖a₁ - a₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hid := gram_identity G hG.1 a₀ a₁
  unfold logSin xiPot
  set A := (herm2 G ![1, a₀] ![1, a₀]).re
  set B := (herm2 G ![1, a₁] ![1, a₁]).re
  set C := ‖herm2 G ![1, a₀] ![1, a₁]‖
  set D := G.det.re
  set n := ‖a₁ - a₀‖
  have harg : 1 - C ^ 2 / (A * B) = D * n ^ 2 / (A * B) := by
    rw [← hid]
    field_simp
  rw [harg, Real.log_div (by positivity) (by positivity), Real.log_mul hD.ne' (by positivity),
    Real.log_mul hA.ne' hB.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.LogSin
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_valAt_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  obtain ⟨h0, -, v0, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, v0⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨-, r, -, v⟩ := hst _ _ hfa ih1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨r, v.trans (by rw [ih2])⟩

theorem coE_regAt_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb F' F hz hF' hF hG' hG p q r
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M'.x zb hz
  have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
    (Cv.agree zb hz F' F hF' hF hG' hG p.1 a b).1
  have hmin := CovMap.LocImg.reg_minor hz hT
  have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
  have hzv := RegPhi.comp_mem_mcPts Cv.block Cv.φ hxv hz
  have hu (I : Finset (Fin N)) :
      RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I)) ∧
        valAt M'.x (Cv.φ (F.u q I)) zb = valAt M.x (F.u q I) (zb ∘ Cv.v) := by
    obtain ⟨d, g, h, hg, hh, hn, he⟩ := (hG.2.1 q I).1
    have hg' := RegPhi.isMultiHomog_rename_block Cv.block hg
    have hh' := RegPhi.isMultiHomog_rename_block Cv.block hh
    have hn' := RegPhi.rename_notMem Cv.block hn
    have hae (f : MRing (baseIdx ι M.blk)) :
        aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
      rw [aeval_rename, hxv, RegPhi.aeval_comp_ringHom]
    have he' : aeval M'.x (rename Cv.v g) = Cv.φ (F.u q I) * aeval M'.x (rename Cv.v h) := by
      rw [hae, hae, he, map_mul]
    refine ⟨⟨_, _, _, hg', hh', hn', he'⟩, ?_⟩
    let value := eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) /
      eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)
    have hv : IsValueAt M.x (F.u q I) (zb ∘ Cv.v) value :=
      ⟨d, g, h, hg, hh, ValRing.aeval_ne_zero_of_notMem hzv hh hn, he,
        ValRing.eval_ne_zero_of_notMem hh hn, rfl⟩
    have hv' : IsValueAt M'.x (Cv.φ (F.u q I)) zb value := by
      refine ⟨_, _, _, hg', hh', ValRing.aeval_ne_zero_of_notMem hz hh' hn', he',
        ValRing.eval_ne_zero_of_notMem hh' hn', ?_⟩
      rw [RegPhi.eval_rename_block, RegPhi.eval_rename_block]
    exact (valAt_eq hz hv').trans (valAt_eq hzv hv).symm
  have hu' := fun I' => (hG'.2.1 r I').2
  have hterm : ∀ I I', RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
      valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
        valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
    intro I I'
    obtain ⟨r1, -, v1, -⟩ := hst _ _ (hu I).1 (hmin I I').1
    obtain ⟨r2, -, v2, -⟩ := hst _ _ r1 (hu' I')
    refine ⟨r2, v2.trans ?_⟩
    rw [v1, (hu I).2, (hmin I I').2]
    rfl
  have hin := fun I => regAt_valAt_sum hz (Finset.univ.filter (IsStepRows N j p.2)) _
    fun I' _ => (hterm I I').1
  have hout := regAt_valAt_sum hz Finset.univ _ fun I _ => (hin I).1
  refine ⟨hout.1, ?_⟩
  refine hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)
  rw [(hin I).2]
  exact Finset.sum_congr rfl fun I' _ => (hterm I I').2

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_torus_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize.stepPh_le_log <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.isPshOn_stepPot <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical


theorem _root_.GlobalTheory.T.flag_gap_holomorphic_pullback_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (V : Set R.X) (c : ℝ), IsCompatChart R.A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry (fun x y => BM.s (pr x) (pr y)) → ‖fderiv ℝ (stepPh M BM p v R pr ∘ ψ.symm) (ψ x')‖ ≤ c * rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' ^ c * Real.exp (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc.stepPh_grad_local <;> assumption)
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem mul_elem_apply (A : Matrix (Fin N) (Fin N) ℂ) (ca cb r s : Fin N) (t : ℂ) :
    (A * (1 + Matrix.single cb ca t)) r s = A r s + if s = ca then A r cb * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  by_cases h : s = ca
  · subst h
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, h, Ne.symm h]

theorem elem_mul_elem {ca cb : Fin N} (hne : ca ≠ cb) (t u : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) * (1 + Matrix.single cb ca u) =
      1 + Matrix.single cb ca (t + u) := by
  ext r s
  rw [mul_elem_apply]
  by_cases h : s = ca
  · subst h
    by_cases hr : cb = r
    · subst hr
      simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne]
      try ring
    · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hne, Ne.symm hne, hr, Ne.symm hr]
  · simp [Matrix.add_apply, Matrix.single_apply, h, Ne.symm h]

theorem mul_elem_cancel {ca cb : Fin N} (hne : ca ≠ cb) (A : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) :
    A * (1 + Matrix.single cb ca t) * (1 + Matrix.single cb ca (-t)) = A := by
  rw [Matrix.mul_assoc, elem_mul_elem hne, add_neg_cancel, Matrix.single_zero, add_zero, Matrix.mul_one]

theorem isBlockDiag_elem {ca cb : Fin N} (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem isLowerUni_mul_elem {ca cb : Fin N} (hlt : ca < cb) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsLowerUni A)
    (t : ℂ) : IsLowerUni (A * (1 + Matrix.single cb ca t)) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [mul_elem_apply, hA.1]
    split_ifs with h
    · subst h
      rw [hA.2 r cb hlt, zero_mul, add_zero]
    · rw [add_zero]
  · rw [mul_elem_apply, hA.2 r s hrs]
    split_ifs with h
    · subst h
      rw [hA.2 r cb (hrs.trans hlt), zero_mul, add_zero]
    · rw [add_zero]

theorem isBlockDiag_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lc τ ca cb c τ') := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  unfold FC.Lc
  rw [dif_neg (fun h => hrs h.1.2), if_neg hne]

theorem isLowerUni_Lc (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) :
    IsLowerUni (FC.Lc τ ca cb c τ') := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_irrefl _ h.1.1), if_pos rfl]
  · unfold FC.Lc
    rw [dif_neg (fun h => lt_asymm hrs h.1.1), if_neg hrs.ne]

theorem Lc_apply_idx (τ : Ψ) (ca cb : Fin N) (c : FC.CIdx Ψ N j τ ca cb → ℂ) (q : FC.CIdx Ψ N j τ ca cb) :
    FC.Lc τ ca cb c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q := by
  unfold FC.Lc
  rw [dif_pos (⟨q.1.2, q.2⟩ : _ ∧ _)]

theorem Lc_self_apply (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (c : FC.CIdx Ψ N j τ ca cb → ℂ) :
    FC.Lc τ ca cb c τ cb ca = 0 := by
  unfold FC.Lc
  rw [dif_neg (fun h => h.2 rfl), if_neg (Ne.symm hne)]

theorem Lc_of_entries (τ : Ψ) {ca cb : Fin N} (hne : ca ≠ cb) (L : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) (h0 : L τ cb ca = 0) :
    FC.Lc τ ca cb (fun q : FC.CIdx Ψ N j τ ca cb => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) = L := by
  funext τ'
  ext r s
  unfold FC.Lc
  split_ifs with h hrs
  · rfl
  · subst hrs
    exact ((hL τ').2.1 r).symm
  · by_cases e : (τ', r, s) = (τ, cb, ca)
    · obtain ⟨rfl, rfl, rfl⟩ : τ' = τ ∧ r = cb ∧ s = ca := by simpa using e
      exact h0.symm
    · have hn : ¬ (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) := fun h' => h ⟨h', e⟩
      by_cases hsr : s < r
      · exact ((hL τ').1 r s fun hb => hn ⟨hsr, hb⟩).symm
      · exact ((hL τ').2.2 r s (lt_of_le_of_ne (not_lt.1 hsr) hrs)).symm

theorem Lc_analytic (τ : Ψ) (ca cb : Fin N) (τ' : Ψ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ := by
  unfold FC.Lc
  by_cases h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca)
  · simp only [dif_pos h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : FC.CIdx Ψ N j τ ca cb => ℂ)
      ⟨⟨(τ', r, s), h.1⟩, h.2⟩).analyticOnNhd _
  · simp only [dif_neg h]
    exact analyticOnNhd_const

theorem exists_Lca (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hL : ∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L := by
  have hne : ca ≠ cb := hlt.ne
  let a : ℂ := L τ cb ca
  let L' : Ψ → Matrix (Fin N) (Fin N) ℂ := Function.update L τ (L τ * (1 + Matrix.single cb ca (-a)))
  have hτ : L' τ = L τ * (1 + Matrix.single cb ca (-a)) := Function.update_self _ _ _
  have hL' : ∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [hτ]
      exact ⟨(hL _).1.mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (hL _).2 _⟩
    · have : L' τ' = L τ' := Function.update_of_ne e _ _
      rw [this]
      exact hL τ'
  have h0 : L' τ cb ca = 0 := by
    rw [hτ, mul_elem_apply, if_pos rfl, (hL τ).2.1 cb, one_mul]
    exact add_neg_cancel _
  refine ⟨fun q => L' q.1.1.1 q.1.1.2.1 q.1.1.2.2, a, ?_⟩
  have hback : L τ * (1 + Matrix.single cb ca (-a)) * (1 + Matrix.single cb ca a) = L τ := by
    have := mul_elem_cancel hne (L τ) (-a)
    rwa [neg_neg] at this
  unfold FC.Lca
  rw [Lc_of_entries τ hne L' hL' h0, hτ, hback]
  funext τ'
  by_cases e : τ' = τ
  · subst e
    exact Function.update_self _ _ _
  · rw [Function.update_of_ne e]
    exact Function.update_of_ne e _ _

theorem Lca_prop (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (hs : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j)
    (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) (τ' : Ψ) :
    IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ') := by
  unfold FC.Lca
  by_cases e : τ' = τ
  · subst e
    rw [Function.update_self]
    exact ⟨(isBlockDiag_Lc _ _ _ _ _).mul (isBlockDiag_elem hs _), isLowerUni_mul_elem hlt (isLowerUni_Lc _ _ _ _ _) _⟩
  · rw [Function.update_of_ne e]
    exact ⟨isBlockDiag_Lc _ _ _ _ _, isLowerUni_Lc _ _ _ _ _⟩

theorem Lca_injective (τ : Ψ) {ca cb : Fin N} (hlt : ca < cb) (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ)
    (h : FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a') : c = c' ∧ a = a' := by
  have hne : ca ≠ cb := hlt.ne
  have hτ : FC.Lc τ ca cb c τ * (1 + Matrix.single cb ca a) = FC.Lc τ ca cb c' τ * (1 + Matrix.single cb ca a') := by
    have := congrFun h τ
    unfold FC.Lca at this
    rwa [Function.update_self, Function.update_self] at this
  have entry : ∀ (d : FC.CIdx Ψ N j τ ca cb → ℂ) (t : ℂ),
      (FC.Lc τ ca cb d τ * (1 + Matrix.single cb ca t)) cb ca = t := fun d t => by
    rw [mul_elem_apply, if_pos rfl, Lc_self_apply τ hne, (isLowerUni_Lc τ ca cb d τ).1 cb, zero_add, one_mul]
  have ha : a = a' := by
    rw [← entry c a, hτ, entry]
  subst ha
  have hc : FC.Lc τ ca cb c = FC.Lc τ ca cb c' := by
    funext τ'
    by_cases e : τ' = τ
    · subst e
      rw [← mul_elem_cancel hne (FC.Lc τ' ca cb c τ') a, hτ, mul_elem_cancel hne]
    · have := congrFun h τ'
      unfold FC.Lca at this
      rwa [Function.update_of_ne e, Function.update_of_ne e] at this
  refine ⟨funext fun q => ?_, rfl⟩
  rw [← Lc_apply_idx τ ca cb c q, hc, Lc_apply_idx]

theorem lc_main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) τ', IsBlockDiag j (FC.Lc τ ca cb c τ') ∧ (FC.Lc τ ca cb c τ').det ≠ 0) ∧ (∀ τ' r s, AnalyticOnNhd ℂ (fun c : FC.CIdx Ψ N j τ ca cb → ℂ => FC.Lc τ ca cb c τ' r s) Set.univ) ∧ (∀ L : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), FC.Lca τ ca cb c a = L) ∧ (∀ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) τ', IsBlockDiag j (FC.Lca τ ca cb c a τ') ∧ IsLowerUni (FC.Lca τ ca cb c a τ')) ∧ ∀ (c c' : FC.CIdx Ψ N j τ ca cb → ℂ) (a a' : ℂ), FC.Lca τ ca cb c a = FC.Lca τ ca cb c' a' → c = c' ∧ a = a' := by
  intro Ψ _ _ N j τ ca cb hlt hs
  refine ⟨fun c τ' => ⟨isBlockDiag_Lc τ ca cb c τ', ?_⟩, fun τ' r s => Lc_analytic τ ca cb τ' r s,
    fun L hL => exists_Lca τ hlt hs L hL, fun c a τ' => Lca_prop τ hlt hs c a τ',
    fun c c' a a' h => Lca_injective τ hlt c c' a a' h⟩
  rw [(isLowerUni_Lc τ ca cb c τ').det]
  exact one_ne_zero

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_ne_zero_iff_of_sameOrbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (z z' : (Σ k, ι k) → ℂ) (p : Ψ × Fin N), SameOrbit z z' → (FC.plk M F b z p ≠ 0 ↔ FC.plk M F b z' p ≠ 0) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b z z' p h
  obtain ⟨c, hc, rfl⟩ := h
  unfold FC.plk
  cases hb : M.blk p with
  | none => simp
  | some k =>
    simp only [Option.elim, mul_left_comm _ (c k), ← Finset.mul_sum, ne_eq, mul_eq_zero, hc k, false_or]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)


theorem _root_.GlobalTheory.T.integrable_chartAbsDensity : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log <;> assumption)
end

section


theorem _root_.GlobalTheory.T.generic_degree_eq_geometric_degree : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system <;> assumption)
end
