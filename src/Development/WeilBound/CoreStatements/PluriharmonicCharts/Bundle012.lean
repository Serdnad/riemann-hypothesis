module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle032
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LeviDiagonalOfIsPeriodChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle100
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021

@[expose] public section

section

noncomputable section

namespace PositivityTheory.Xgp.plurisubharmonic_charts

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.continuousOn_of_holoOn <;> assumption

theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := by
  apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.holoOn_comp <;> assumption

theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.exists_log <;> assumption

end Holo

theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.detFac_ne_zero' <;> assumption

theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := PositivityTheory.Xgp.per_diag.levi_diagonal_of_isPeriodChart e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end PositivityTheory.Xgp.plurisubharmonic_charts
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_arith

open KaehlerDifferential

open Algebra in
theorem trdeg_int_eq_rat (L : Type) [Field L] [Algebra ℚ L] : Algebra.trdeg ℤ L = Algebra.trdeg ℚ L := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

end PositivityTheory.Xgp.c_bm_exists_arith

theorem PositivityTheory.Xgp.t_c_bm_exists_arith : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), 1 ≤ n → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩) → Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) := by
  intro X Ω _ _ ξ K _ J _ x n bd hn T hs
  classical

  obtain ⟨c, hc⟩ := T.cover ⟨genPt ξ, specializes_rfl⟩
  have hc0 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨m, f, a, hf, ha, hsum, hmain⟩ := hs c hc0
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  set R : Set Ω := Set.range fun p : Σ k, J k => x p / x ⟨p.1, c p.1⟩ with hR
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ R) with hS
  obtain ⟨hsm, z, n', -, hli, hspan, -⟩ := hmain l hl S rfl

  have hRS : R ⊆ S := fun r hr => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hr)
  have hmono : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ≤ S.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩ ∈ S
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => hRS ⟨⟨k, j k⟩, rfl⟩
  have hfr : IsFractionRing S Ω := by
    refine IsFractionRing.of_field S Ω fun a => ?_
    obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
    exact ⟨⟨g, hmono hg⟩, ⟨h, hmono hh⟩, e⟩
  have hfin : Module.finrank Ω (KaehlerDifferential ℚ Ω) = n :=
    GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis ℚ S ℚ Ω n z hli hspan

  have hK : Nonempty K := by
    by_contra hK
    rw [not_nonempty_iff] at hK
    have hall : ∀ a : Ω, a ∈ Set.range (algebraMap ℚ Ω) := by
      intro a
      obtain ⟨g, hg, h, hh, -, e⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin X Ω ξ _ _ c T hc.1 a
      have h1 : (Set.range fun j : (k : K) → J k => (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩) ⊆ {1} := by
        rintro _ ⟨j, rfl⟩
        simp
      have hbot : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
          (∏ k, x ⟨k, j k⟩) / ∏ k, x ⟨k, c k⟩), ∃ q : ℤ, b = q := by
        intro b hb
        have := Algebra.adjoin_mono h1 hb
        rw [Algebra.adjoin_singleton_one, Algebra.mem_bot] at this
        obtain ⟨q, rfl⟩ := this
        exact ⟨q, by simp⟩
      obtain ⟨q1, rfl⟩ := hbot g hg
      obtain ⟨q2, rfl⟩ := hbot h hh
      exact ⟨(q1 : ℚ) / q2, by rw [e]; simp⟩
    have hsub : Subsingleton (KaehlerDifferential ℚ Ω) := by
      have htop := KaehlerDifferential.span_range_derivation ℚ Ω
      refine subsingleton_of_forall_eq 0 fun w => ?_
      have hw : w ∈ (⊤ : Submodule Ω (KaehlerDifferential ℚ Ω)) := trivial
      rw [← htop] at hw
      have hle : Submodule.span Ω (Set.range (KaehlerDifferential.D ℚ Ω)) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        obtain ⟨q, rfl⟩ := hall b
        exact (KaehlerDifferential.D ℚ Ω).map_algebraMap q
      simpa using hle hw
    have := Module.finrank_zero_of_subsingleton (R := Ω) (M := KaehlerDifferential ℚ Ω)
    omega

  have : Algebra.EssFiniteType S Ω := .of_isLocalization Ω (nonZeroDivisors S)
  have : Algebra.EssFiniteType ℚ Ω := .comp ℚ S Ω
  have hfd : Module.Finite Ω (KaehlerDifferential ℚ Ω) := Module.finite_of_finrank_pos (by omega)
  have htr : Algebra.trdeg ℚ Ω = n := by
    rw [← GlobalTheory.rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank, hfin]
  have htr' : Algebra.trdeg ℤ Ω = n := (PositivityTheory.Xgp.c_bm_exists_arith.trdeg_int_eq_rat Ω).trans htr
  exact (GlobalTheory.T.birational_of_transcendence_degree X Ω ξ K J x n T htr').2
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_local

open GlobalTheory.CompanionTheory.Ar.HodgeMetric Filter Topology

theorem logR_le {n a : ℕ} {w₀ w : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} {m : Fin n → ℕ} (hm : ∀ i ∈ S, 1 ≤ m i) (hw : ‖w‖ ≤ 2) (hS : ∀ i ∈ S, w i ≠ 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a → π.symm i ∈ S ∧ w₀ (π.symm i) = 0) :
    (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0) ≤ rLoc S m w := by
  have hg : ∀ j ∈ S, 0 ≤ Real.log (4 / ‖w j‖ ^ 2) := by
    intro j hj
    apply Real.log_nonneg
    have h0 : 0 < ‖w j‖ := norm_pos_iff.2 (hS j hj)
    have h2 : ‖w j‖ ≤ 2 := (norm_le_pi_norm w j).trans hw
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hinv : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).2 hρ1
  have hterm : ∀ i : Fin n, (i : ℕ) < a →
      Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) ≤ Real.log (4 / ‖w (π.symm i)‖ ^ 2) := by
    intro i hi
    obtain ⟨hS', h0'⟩ := ha i hi
    have hpos : 0 < ‖w (π.symm i)‖ := norm_pos_iff.2 (hS _ hS')
    have hu : ‖uncentre w₀ ρ π w i‖ = ρ⁻¹ * ‖w (π.symm i)‖ := by
      simp [uncentre, h0', norm_mul, abs_of_pos hρ]
    have hx : ‖w (π.symm i)‖ ≤ ρ⁻¹ * ‖w (π.symm i)‖ := by nlinarith
    apply Real.log_le_log
    · rw [hu]
      positivity
    · rw [hu, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  unfold rLoc
  refine add_le_add le_rfl ?_
  calc (∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if (i : ℕ) < a then Real.log (4 / ‖w (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h
        · exact hterm i h
        · exact le_rfl
    _ = ∑ j : Fin n, if ((π j : Fin n) : ℕ) < a then Real.log (4 / ‖w j‖ ^ 2) else 0 := by
        rw [← Equiv.sum_comp π]
        simp
    _ = ∑ j ∈ Finset.univ.filter (fun j => ((π j : Fin n) : ℕ) < a), Real.log (4 / ‖w j‖ ^ 2) :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ j ∈ S, Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j hj _ => hg j hj)
        have := (ha (π j) (Finset.mem_filter.1 hj).2).1
        simpa using this
    _ ≤ ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact le_mul_of_one_le_left (hg j hj) (by exact_mod_cast hm j hj)

theorem exists_hasFDerivAt_uncentre {n : ℕ} (w₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ∃ A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ), ∀ w, HasFDerivAt (uncentre w₀ ρ π) A w := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => (ρ : ℂ)⁻¹ • ContinuousLinearMap.proj (R := ℂ) (π.symm i)
  refine ⟨L.restrictScalars ℝ, fun w => ?_⟩
  have hf : uncentre w₀ ρ π = fun t => L.restrictScalars ℝ t - L.restrictScalars ℝ w₀ := by
    funext t i
    simp [uncentre, L, mul_sub]
  rw [hf]
  exact (L.restrictScalars ℝ).hasFDerivAt.sub_const _

theorem posDef_of_inv {N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℂ} {c : ℝ} (hc : 0 < c)
    (h : (Γ⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) : Γ.PosDef := by
  have h1 : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast hc)
  have h2 := h1.add_posSemidef h
  rw [add_sub_cancel] at h2
  exact Matrix.posDef_inv_iff.1 h2

theorem psd_mono {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {r r' : ℝ} (hr : r ≤ r')
    (h : (((r : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef) :
    (((r' : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef := by
  have hI : ((((r' - r : ℝ)) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 hr)
  have h2 := h.add hI
  convert h2 using 1
  simp only [Complex.ofReal_sub, sub_smul]
  abel

end PositivityTheory.Xgp.c_bm_exists_local
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' x x' A A' h i j d hov hcov
  obtain ⟨hd, hf, -⟩ := hov
  have hgen : genPt A'.ξ₀ = genPt A.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt A'.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso A'.gen₀ A.gen₀ hgen
  have e1 : spMap A'.fn ≫ A'.ξ₀ = A'.ξ ≫ A'.f := A'.fn_over.symm
  have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
  have e3 : A'.ξ ≫ h = spMap i ≫ A.ξ := hd
  have e5 : spMap (A.fn.comp ψ.toRingHom) ≫ A'.ξ₀ = A.ξ ≫ A.f := by
    rw [FlagPull.spMap_comp, Category.assoc, hψ, e2]
  refine ⟨A.fn.comp ψ.toRingHom, ?_, e5.symm, ?_⟩
  · haveI := FlagPull.mono_of_isCptGen A'.gen₀
    have e4 : spMap (i.comp (A.fn.comp ψ.toRingHom)) = spMap A'.fn := by
      refine (cancel_mono A'.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, Category.assoc, e5, e1, hf, ← Category.assoc, ← e3, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  · letI := A.fn.toAlgebra
    letI := (A.fn.comp ψ.toRingHom).toAlgebra
    exact (Algebra.finrank_eq_of_equiv_equiv ψ (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)).trans hcov.2
end
