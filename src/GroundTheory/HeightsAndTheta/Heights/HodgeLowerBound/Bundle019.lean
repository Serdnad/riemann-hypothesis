module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle017
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpCuspIntegrable.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    IsSmoothHerm (X.NbarQ B p q t) →
      IsPtsIntegrable (mCoordIdeal D.y) (X.omN B p q t) (fun z => X.Cd.cuspWeight z / 2)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TpIntegrandLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ q → ∃ t₂ : ℝ, 0 < t₂ ∧ ∀ t : ℝ, 0 < t → t ≤ t₂ →
      ∃ (N : Set ((Σ k, ι k) → ℂ)) (C t'₀ : ℝ), 0 < t'₀ ∧ IsPtsNull (mCoordIdeal D.y) D.n N ∧
        (∀ t' : ℝ, 0 < t' → t' < t'₀ →
          (∀ z ∈ mcPts (mCoordIdeal D.y), |X.wSt B p q t t' z| ≤ C) ∧
          ContinuousOn (X.wSt B p q t t') (mcPts (mCoordIdeal D.y) \ N)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ N →
          Tendsto (fun t' => X.wSt B p q t t' z) (𝓝[>] 0)
            (𝓝 (cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_pi_of_eventually_differentiableAt {d m : ℕ} {f : (Fin d → ℂ) → Fin m → ℂ} {y : Fin d → ℂ}
    (h : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ f y') : AnalyticAt ℂ f y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 h
  refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun w => f w i) hUo (fun z hz => ?_) y hyU
  exact (differentiableAt_pi.mp (hU z hz) i).differentiableWithinAt

theorem RegChartData.contDiffAt_u {n : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas n X}
    (R : RegChartData A) (j : Fin R.N) {ξ : Fin n → ℂ} (hξ : ξ ∈ (R.chart j).target \ coordDiv (R.S j)) :
    ContDiffAt ℝ 2 (R.u j) ξ := by
  have hp : (R.chart j).symm ξ ∈ (R.chart j).source := (R.chart j).map_target hξ.1
  have hYo : R.Yo ∈ 𝓝 ((R.chart j).symm ξ) := by
    refine Filter.mem_of_superset (((R.chart j).isOpen_inter_preimage
      (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed (R.S j)).isOpen_compl).mem_nhds ⟨hp, ?_⟩)
      fun x hx => (R.mem_Yo j x hx.1).2 hx.2
    change (R.chart j) ((R.chart j).symm ξ) ∉ coordDiv (R.S j)
    rw [(R.chart j).right_inv hξ.1]
    exact hξ.2
  obtain ⟨i, hi⟩ := A.cover ((R.chart j).symm ξ)
  have hti : (A.chart i) ((R.chart j).symm ξ) ∈ (A.chart i).target := (A.chart i).map_source hi
  have h1 : ContDiffAt ℝ 2 (R.ph ∘ (A.chart i).symm) ((A.chart i) ((R.chart j).symm ξ)) := by
    refine ((R.ph_smooth i).contDiffAt (Filter.inter_mem ((A.chart i).open_target.mem_nhds hti) ?_)).of_le
      (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
    refine (A.chart i).continuousAt_symm hti |>.preimage_mem_nhds ?_
    rw [(A.chart i).left_inv hi]
    exact hYo
  have hτ : AnalyticAt ℂ ((A.chart i) ∘ (R.chart j).symm) ξ := ((R.compat j i).2) ξ ⟨hξ.1, hi⟩
  have h2 : ContDiffAt ℝ 2 (fun ξ' => R.ph ((R.chart j).symm ξ')) ξ := by
    refine (h1.comp ξ hτ.restrictScalars.contDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [(R.chart j).continuousAt_symm hξ.1 |>.preimage_mem_nhds
      ((A.chart i).open_source.mem_nhds hi)] with ξ' h
    simp only [Function.comp_apply, (A.chart i).left_inv h]
  have hq : ContDiffAt ℝ 2 (R.q j) ξ :=
    ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hξ.1)).of_le (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  exact hq.add h2

theorem LogLogRegularisationSetting.log_h_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {n : ℕ} {M : CxModel P n} {Xo : Set ((Σ k, ι k) → ℂ)} {A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (S : LogLogRegularisationSetting M Xo A)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) (hY : M.proj z ∈ S.R.Yo) :
    Real.log (A.h z) = S.R.ph (M.proj z) + Real.log (S.ref.h z) := by
  obtain ⟨z', ⟨hz'o, hz'⟩, hp⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, rfl⟩ := (M.fibre z' hz' _ hz).1 hp
  have hph := S.ph_eq z' ⟨hz'o, hz'⟩ (by rw [hp]; exact hY)
  have hA : A.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * A.h z' := A.smul c z' hc
  have hR : S.ref.h (torusSmul c z') = (∏ k, ‖c k‖ ^ A.a k) * S.ref.h z' := by
    rw [← S.ref_deg]; exact S.ref.smul c z' hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  rw [hA, hR, Real.log_mul hpos.ne' (A.pos z' hz'.1).ne', Real.log_mul hpos.ne' (S.ref.pos z' hz'.1).ne', ← hp,
    hph]
  ring

theorem MuSheetLeviNonneg.proof (hH : SheetChartHolo.Statement) (hR : RefAlongSheet.Statement) :
    MuSheetLeviNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q _
  filter_upwards [hH K ι (mCoordIdeal D.y) D.n X.M X.S.R Q] with y hy w γ hγ
  obtain ⟨j, hsrc, hYo, hev⟩ := hy w γ hγ
  have hγev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts (mCoordIdeal D.y) :=
    hγ.2.mono fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨G, hG, hGeq⟩ := hR K ι _ D.n X.M D.Xo (muLine X.H) X.S γ y j hγev hsrc hev
  set g : (Fin D.n → ℂ) → Fin D.n → ℂ := fun y'' => X.S.R.chart j (X.M.proj (γ y'')) with hgdef
  have hg : AnalyticAt ℂ g y := analyticAt_pi_of_eventually_differentiableAt (hev.mono fun _ h => h.2)
  have hgy : g y ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    ⟨(X.S.R.chart j).map_source hsrc, (X.S.R.mem_Yo j _ hsrc).1 hYo⟩
  have hUo : IsOpen ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    (X.S.R.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have hC2 : ContDiffOn ℝ 2 (X.S.R.u j) ((X.S.R.chart j).target \ coordDiv (X.S.R.S j)) :=
    fun ξ hξ => (RegChartData.contDiffAt_u X.S.R j hξ).contDiffWithinAt
  have hL := ((ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm _ _ _ hUo hC2).1 (X.S.R.u_psh j)).2
  have hgU : ∀ᶠ y' in 𝓝 y, g y' ∈ (X.S.R.chart j).target \ coordDiv (X.S.R.S j) :=
    hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgy)
  have heq : (fun y' => phMu X.H (γ y')) =ᶠ[𝓝 y] fun y' => (X.S.R.u j ∘ g) y' + 1 * (G y').re := by
    filter_upwards [hγev, hev, hgU, hGeq] with y' h1 h2 h3 h4
    have hY' : X.M.proj (γ y') ∈ X.S.R.Yo := (X.S.R.mem_Yo j _ h2.1).2 h3.2
    have hl := X.S.log_h_eq h1.2 hY'
    show Real.log ((muLine X.H).h (γ y')) =
      X.S.R.q j (g y') + X.S.R.ph ((X.S.R.chart j).symm (g y')) + 1 * (G y').re
    rw [hl, h4, hgdef]
    simp only [(X.S.R.chart j).left_inv h2.1]
    ring
  have hu2 : ContDiffAt ℝ 2 (X.S.R.u j) (g y) := RegChartData.contDiffAt_u X.S.R j hgy
  have hcomp : ContDiffAt ℝ 2 (X.S.R.u j ∘ g) y := hu2.comp y hg.restrictScalars.contDiffAt
  have hre : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  refine ⟨(hcomp.add (contDiffAt_const.mul hre)).congr_of_eventuallyEq heq, fun v => ?_⟩
  change 0 ≤ levi (fun y' => phMu X.H (γ y')) y v
  rw [ReciprocityTheory.AnForm.levi_congr heq, ReciprocityTheory.AnForm.levi_add_smul 1 hcomp hre,
    ReciprocityTheory.AnForm.levi_re_analytic hG, ReciprocityTheory.AnForm.levi_comp v hg hu2]
  simpa using hL _ hgy _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChart.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem GrassmannianHeightZTwo.proof (hZ2 : SuccessiveMinimaUpperBound) (hPush : FlagGrassPush.Statement)
    (hDeg : HilbertSamuel.FSGeomDegPos.Statement) : GrassmannianHeightZTwo.Statement := by
  intro II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have hmu : muPoly Ψ N j = 0 := by
      unfold muPoly
      exact Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim
    have hFA : FA Ψ N j cf = 0 := by
      unfold FA
      rw [hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [hFA, Fintype.card_eq_zero]
    simp [hFl]
  · set f := Fintype.card Ψ with hfdef
    have hf : 1 ≤ f := Fintype.card_pos
    have hP := hPush II Ψ N j cf hII hN hj1 hjN
    have hG := GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII
    have hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j)))
        (f * j * (N - j)) :=
      hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j))
        (GrassArithVar.full f j (N - j) hf)
    have hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ) := Rat.cast_pos.mpr hJ
    change -hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j))
        (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) =
      (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j))
        (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) at hP
    change -hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e
    have h1 := mul_le_mul_of_nonneg_left hG hJ'.le
    refine le_of_mul_le_mul_right ?_ hD
    rw [hP]
    calc _ ≤ _ := h1
      _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)
open scoped ContDiff

theorem continuousOn_levi_of_contDiffOn {n : ℕ} {f : (Fin n → ℂ) → ℝ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ 2 f W) :
    ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => levi f p.1 p.2) (W ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) W := hf.fderiv_of_isOpen hW (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) W := h1.continuousOn_fderiv_of_isOpen hW le_rfl
  have hH : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => fderiv ℝ (fderiv ℝ f) p.1) (W ×ˢ Set.univ) :=
    h2.comp continuousOn_fst fun p hp => hp.1
  have hI : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => Complex.I • p.2) (W ×ˢ Set.univ) :=
    continuousOn_snd.const_smul Complex.I
  unfold levi
  exact (((hH.clm_apply continuousOn_snd).clm_apply continuousOn_snd).add
    ((hH.clm_apply hI).clm_apply hI)).div_const 4

theorem APrimeChartLevi.proof (hL : APrimeChartLeviLocal.Statement) (hV : ChartVelLift.Statement) :
    APrimeChartLevi.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k
  set e := X.S.R.chart k with he
  have hloc : ∀ y : Fin D.n → ℂ, ∃ W : Set (Fin D.n → ℂ), ∃ f : (Fin D.n → ℂ) → ℝ,
      y ∈ e.target → IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ ∞ f W ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ e.source → e (X.M.proj z) ∈ W → ∀ w v,
          IsChartVel X.M e z w v →
            levi (fun y => Real.log (D.A'.h y)) z w = levi f (e (X.M.proj z)) v := by
    intro y
    by_cases hy : y ∈ e.target
    · obtain ⟨W, hW, hyW, f, hf, hrep⟩ := hL II Ψ K ι Ω E D O Lt X k y hy
      exact ⟨W, f, fun _ => ⟨hW, hyW, hf, hrep⟩⟩
    · exact ⟨∅, 0, fun h => absurd h hy⟩
  choose W f hWf using hloc
  have hagree : ∀ y₁ ∈ e.target, ∀ y ∈ e.target, y ∈ W y₁ → ∀ v, levi (f y₁) y v = levi (f y) y v := by
    intro y₁ hy₁ y hy hyW v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [levi]
    obtain ⟨z, hz, hpz, w, hw, -, -⟩ := hV II Ψ K ι Ω E D O Lt X k y hy v hv
    have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
    have hez : e (X.M.proj z) = y := by rw [hpz]; exact e.right_inv hy
    have h1 := (hWf y₁ hy₁).2.2.2 z hz hs (by rw [hez]; exact hyW) w v hw
    have h2 := (hWf y hy).2.2.2 z hz hs (by rw [hez]; exact (hWf y hy).2.1) w v hw
    rw [hez] at h1 h2
    rw [← h1, ← h2]
  refine ⟨fun y v => levi (f y) y v, ?_, ?_⟩
  · intro p hp
    obtain ⟨hW, hyW, hf, -⟩ := hWf p.1 hp.1
    have hN : W p.1 ∩ e.target ∈ 𝓝 p.1 := inter_mem (hW.mem_nhds hyW) (e.open_target.mem_nhds hp.1)
    have hc : ContinuousAt (fun q : (Fin D.n → ℂ) × (Fin D.n → ℂ) => levi (f p.1) q.1 q.2) p :=
      (continuousOn_levi_of_contDiffOn hW (hf.of_le (WithTop.coe_le_coe.2 le_top))).continuousAt
        (prod_mem_nhds (hW.mem_nhds hyW) univ_mem)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [prod_mem_nhds hN univ_mem] with q hq
    exact hagree p.1 hp.1 q.1 hq.1.2 hq.1.1 q.2
  · intro z hz hs w v hw
    have hy : e (X.M.proj z) ∈ e.target := e.map_source hs
    exact (hWf _ hy).2.2.2 z hz hs (hWf _ hy).2.1 w v hw

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

theorem levi_real_smul {κ : Type*} [Fintype κ] (φ : (κ → ℂ) → ℝ) (z w : κ → ℂ) (r : ℝ) :
    levi φ z (r • w) = r ^ 2 * levi φ z w := by
  unfold levi
  have h : Complex.I • (r • w) = r • (Complex.I • w) := smul_comm _ _ _
  rw [h]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem IsChartVel.real_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {d : ℕ} {M : CxModel P d} {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)} {z w : (Σ k, ι k) → ℂ}
    {v : Fin d → ℂ} (h : IsChartVel M e z w v) (r : ℝ) : IsChartVel M e z (r • w) (r • v) := by
  obtain ⟨γ, h0, hd, hev, hv⟩ := h
  have hm : HasDerivAt (fun s : ℂ => (r : ℂ) * s) (r : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)
  have ht : Tendsto (fun s : ℂ => (r : ℂ) * s) (𝓝 0) (𝓝 0) := by
    simpa using hm.continuousAt.tendsto
  have hsw : ∀ {κ : Type} (u : κ → ℂ), (r : ℂ) • u = r • u := fun u => by
    funext p
    simp [Complex.real_smul]
  refine ⟨fun s => γ ((r : ℂ) * s), by simpa using h0, ?_, ?_, ?_⟩
  · have hd' : HasDerivAt γ w ((r : ℂ) * 0) := by simpa using hd
    have h' := hd'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'
  · filter_upwards [ht.eventually hev] with s hs
    exact ⟨hs.1.comp s (differentiableAt_id.const_mul _), hs.2⟩
  · have hv' : HasDerivAt (fun s => e (M.proj (γ s))) v ((r : ℂ) * 0) := by simpa using hv
    have h' := hv'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'

theorem APrimeChartMargin.proof (hQ : APrimeChartLevi.Statement) (hL : ChartVelLift.Statement) :
    APrimeChartMargin.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  have hk : ∀ k : Fin X.S.R.N, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w := by
    intro k
    obtain ⟨Q, hcont, hrep⟩ := hQ II Ψ K ι Ω E D O Lt X k
    set e := X.S.R.chart k with he
    have hpos : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < Q y v := by
      intro y hy v hv
      obtain ⟨z, hz, hpz, w, hw, hcone, hnt⟩ := hL II Ψ K ι Ω E D O Lt X k y hy v hv
      have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
      have hr := hrep z hz hs w v hw
      rw [hpz, e.right_inv hy] at hr
      rw [← hr]
      exact D.A'_pos.2 z hz w hcone hnt
    set S := (e '' closure (X.S.R.mid k)) ×ˢ Metric.sphere (0 : Fin D.n → ℂ) 1 with hS
    have hcpt : IsCompact S :=
      (isClosed_closure.isCompact.image_of_continuousOn
        (e.continuousOn.mono (X.S.R.closure_mid k))).prod (isCompact_sphere 0 1)
    have hsub : S ⊆ e.target ×ˢ Set.univ := by
      rintro ⟨y, u⟩ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨e.map_source (X.S.R.closure_mid k hx), Set.mem_univ _⟩
    obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ Q p.1 p.2 := by
      rcases S.eq_empty_or_nonempty with hE | hne
      · exact ⟨1, one_pos, by simp [hE]⟩
      · obtain ⟨p, hp, hmin⟩ := hcpt.exists_isMinOn hne (hcont.mono hsub)
        refine ⟨Q p.1 p.2, hpos p.1 (hsub hp).1 p.2 ?_, fun q hq => hmin hq⟩
        intro h0
        have h2 := hp.2
        rw [h0, Metric.mem_sphere, dist_self] at h2
        exact zero_ne_one h2
    refine ⟨c, hc, fun z hz w hm v hv => ?_⟩
    have hs : X.M.proj z ∈ e.source := X.S.R.mid_subset_source k hm
    have hy : e (X.M.proj z) ∈ e '' closure (X.S.R.mid k) := ⟨_, subset_closure hm, rfl⟩
    have h1 := hrep z hz hs w v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · have h2 := hrep z hz hs _ _ (hv.real_smul 0)
      rw [levi_real_smul, smul_zero] at h2
      rw [h1, ← h2]
      simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h2 := hrep z hz hs _ _ (hv.real_smul ‖v‖⁻¹)
      rw [levi_real_smul] at h2
      have hu : (e (X.M.proj z), ‖v‖⁻¹ • v) ∈ S := by
        refine ⟨hy, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h3 := hcle _ hu
      rw [← h2] at h3
      calc c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * levi (fun y => Real.log (D.A'.h y)) z w) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = levi (fun y => Real.log (D.A'.h y)) z w := by
          field_simp
  choose ck hck hmk using hk
  have hne : (insert 1 (Finset.univ.image ck)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 (Finset.univ.image ck)).min' hne, ?_, ?_⟩
  · rcases Finset.mem_insert.1 (Finset.min'_mem _ hne) with h | h
    · rw [h]
      exact one_pos
    · obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
      rw [← hk]
      exact hck k
  · intro z hz w k hm v hv
    exact le_trans (mul_le_mul_of_nonneg_right (Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ k)))) (by positivity)) (hmk k z hz w hm v hv)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
