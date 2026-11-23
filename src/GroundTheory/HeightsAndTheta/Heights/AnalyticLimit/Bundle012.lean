module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

theorem LemmaETailMass.proof (hT : LemmaETrunc.Statement) (hC : LemmaETruncMass.Statement)
    (hB : LemmaETruncTail.Statement) : LemmaETailMass.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨K, hK0, hK⟩ := hB D A Om L s hL hs hd hle
  refine ⟨(C₁ + 2) ^ D * K, fun u hu R₀ hR₀ => ?_⟩
  have htr : ∀ R, Real.exp 1 ≤ R → ∀ i, ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (potForm Om.pot v) ∧
      (∀ x, -(C₁ * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧
      ∃ c : ℝ, ∀ x ∈ secOpen s, rSec L s x < R → v x = u i x + c := fun R hR i =>
    hT A Om (secOpen s) (rSec L s) C₁ (u i) (isOpen_secOpen hL hs) hd
      (fun x _ => exp_one_le_rSec hle x) hC₁ (hu i).smooth (hu i).nonneg (hu i).nonpos (hu i).le_u
      (hu i).smooth_or_pole R hR
  classical
  let ut : ℝ → Fin D → X → ℝ := fun R i =>
    if h : Real.exp 1 ≤ R then Classical.choose (htr R h i) else fun _ => 0
  have hut : ∀ R (h : Real.exp 1 ≤ R) i, ut R i = Classical.choose (htr R h i) := fun R h i => by
    simp only [ut, dif_pos h]
  obtain ⟨hint, hle₁⟩ := hC D A Om (secOpen s) (rSec L s) u ut (isOpen_secOpen hL hs)
    (continuousOn_rSec hL hs) (fun i => (hu i).smooth) (fun i => (hu i).nonneg)
    (fun R hR i => by
      rw [hut R hR i]
      obtain ⟨h1, h2, -, h4⟩ := Classical.choose_spec (htr R hR i)
      exact ⟨h1, h2, h4⟩) R₀ hR₀
  refine ⟨hint, hle₁.trans ?_⟩
  have hlog : 1 ≤ Real.log R₀ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hR₀
  have hM : 1 ≤ C₁ * Real.log R₀ + 2 := by nlinarith
  have hb := hK (C₁ * Real.log R₀ + 2) hM (ut R₀)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).1)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.1)
    (fun i x => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.2.1 x) R₀ hR₀
  refine hb.trans ?_
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hMle : C₁ * Real.log R₀ + 2 ≤ (C₁ + 2) * Real.log R₀ := by nlinarith
  have hpow : (C₁ * Real.log R₀ + 2) ^ D ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hMle D
  have hnum : (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by
    calc (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D * K :=
          mul_le_mul_of_nonneg_right hpow hK0
      _ = (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by ring
  exact div_le_div_of_nonneg_right hnum hR₀pos.le

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M

noncomputable section

structure EnergyStep.Data {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (n + 1) X)
    (Om : KaehlerForm A) where

  w : X → ℝ

  v : X → ℝ

  f : Fin n → X → ℝ

  M : ℝ
  w_smooth : A.Smooth w
  w_psh : IsPsh A (Om.pot + LocPot.ofFun w)
  v_smooth : A.Smooth v
  v_nonpos : ∀ x, v x ≤ 0
  le_v : ∀ x, -M ≤ v x
  f_smooth : ∀ i, A.Smooth (f i)
  f_psh : ∀ i, IsPsh A (Om.pot + LocPot.ofFun (f i))

def EnergyStep.Data.T {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas (n + 1) X}
    {Om : KaehlerForm A} (d : EnergyStep.Data A Om) : Fin n → LocPot X :=
  fun i => Om.pot + LocPot.ofFun (d.f i)

def EnergyStep.Statement : Prop :=
  ∀ {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (d : EnergyStep.Data A Om),
    mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -d.w x) ≤
      mInt A (Fin.cons Om.pot d.T) (fun x => -d.w x) + d.M * Om.vol

theorem KaehlerForm.isPsh {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    (Om : KaehlerForm A) : IsPsh A Om.pot := by
  intro x j y hy z
  by_cases hz : z = 0
  · subst hz
    simp [levi]
  · exact (Om.pos x j y hy z hz).le

theorem levi_add_const {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (c : ℝ) (y z : ι → ℂ) :
    levi (fun y' => g y' + c) y z = levi g y z := by
  have h : fderiv ℝ (fun y' => g y' + c) = fderiv ℝ g := funext fun y' => fderiv_add_const c
  unfold levi
  rw [h]

theorem isPsh_add_const {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {P : LocPot X} (hP : IsPsh A P) (c : ℝ) : IsPsh A (P + LocPot.ofFun fun _ => c) := by
  intro x j y hy z
  have h : (P + LocPot.ofFun fun _ => c).φ x ∘ (A.chart j).symm =
      fun y' => (P.φ x ∘ (A.chart j).symm) y' + c := rfl
  rw [h, levi_add_const]
  exact hP x j y ⟨hy.1, hy.2.1⟩ z

theorem mInt_neg {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas n X) (Φ : Fin n → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ)
    (hg : MIntegrable A Φ g) : mInt A Φ (fun x => -g x) = -mInt A Φ g := by
  have h := mIntLinear A Φ hΦ (-1) g (fun _ => 0) hg (mIntegrableCont A Φ hΦ _ continuous_const)
  simp only [neg_one_mul, add_zero, st_mInt_zero] at h
  exact h

theorem EnergyStep.proof : EnergyStep.Statement := by
  intro n X _ _ _ A Om d
  have hT : ∀ i, IsPotential A (d.T i) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (d.f_smooth i))
  have hcons : ∀ P, IsPotential A P → ∀ i, IsPotential A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · simpa using hT i
  have hw := isPotential_ofFun A _ d.w_smooth
  have hv := isPotential_ofFun A _ d.v_smooth
  have hOw := isPotentialAdd A _ _ Om.isPot hw
  have cw := st_smooth_continuous A d.w_smooth
  have cv := st_smooth_continuous A d.v_smooth
  have int : ∀ P, IsPotential A P → ∀ g : X → ℝ, Continuous g →
      MIntegrable A (Fin.cons P d.T) g := fun P hP g hg => mIntegrableCont A _ (hcons P hP) g hg

  have h1 := mIntAdd A Om.pot (LocPot.ofFun d.v) d.T Om.isPot hv hT (fun x => -d.w x)
    (int _ Om.isPot _ cw.neg) (int _ hv _ cw.neg)
  have h2 := mInt_neg A _ (hcons _ hv) d.w (int _ hv _ cw)
  have h3 := (byPartsSymm A d.v d.w d.v_smooth d.w_smooth d.T hT).symm
  have h4 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT d.v
    (int _ Om.isPot _ cv) (int _ hw _ cv)
  have hpsh : ∀ P, IsPsh A P → ∀ i, IsPsh A ((Fin.cons P d.T : Fin (n + 1) → LocPot X) i) := by
    intro P hP i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hP
    · exact d.f_psh i

  have h5 := mIntNonneg A _ (hcons _ Om.isPot) (hpsh _ Om.isPsh) (fun x => -d.v x)
    fun x => by have := d.v_nonpos x; linarith
  rw [mInt_neg A _ (hcons _ Om.isPot) d.v (int _ Om.isPot _ cv)] at h5

  have h6 := mIntLinear A _ (hcons _ hOw) d.M (fun _ => 1) d.v (int _ hOw _ continuous_const)
    (int _ hOw _ cv)
  beta_reduce at h6
  have h7 := mIntNonneg A _ (hcons _ hOw) (hpsh _ d.w_psh) (fun x => d.M * 1 + d.v x)
    fun x => by have := d.le_v x; linarith
  rw [h6] at h7

  have h8 := mIntAdd A Om.pot (LocPot.ofFun d.w) d.T Om.isPot hw hT (fun _ => 1)
    (int _ Om.isPot _ continuous_const) (int _ hw _ continuous_const)
  have h9 := stokes A d.w d.w_smooth d.T hT
  have h10 := massIndep A (fun _ => Om.pot) (Fin.cons (fun _ => 0) d.f) (fun _ => Om.isPot)
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using st_smooth_const A 0
      · simpa using d.f_smooth i)
  have h11 : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) =
      mInt A (fun i => Om.pot + LocPot.ofFun ((Fin.cons (fun _ => 0) d.f : Fin (n + 1) → X → ℝ) i))
        (fun _ => 1) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      show Om.pot.φ x y = Om.pot.φ x y + 0
      ring
    · rfl
  have hV : mInt A (Fin.cons Om.pot d.T) (fun _ => 1) = Om.vol := by
    rw [h11, h10]
    rfl
  rw [h8, h9, add_zero, hV] at h7
  rw [h1, h2, h3]
  linarith [h4, h5, h7]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm (levi levi_add_smul)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd maMeasureMono maMeasure_thm massIndep mIntegrableCont
  pot_contDiffAt_two)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_formNonneg {A : FinHolAtlas D X} {V : Set X} (hV : interior Vᶜ = ∅)
    {P : LocPot X} (hP : IsPotential A P) (hnn : FormNonneg A V P) : IsPsh A P := by
  intro x j y hy w
  by_contra hneg
  push Not at hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have h2 := pot_contDiffAt_two hP x j hy.1 hy.2
  have hc : ContinuousAt (fun z => levi (P.φ x ∘ (A.chart j).symm) z w) y := by
    have h0 := ((h2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt
    unfold levi
    exact (((h0.clm_apply continuousAt_const).clm_apply continuousAt_const).add
      ((h0.clm_apply continuousAt_const).clm_apply continuousAt_const)).div_const 4
  have hev : ∀ᶠ z in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) z w < 0 ∧
      z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    (hc.eventually (eventually_lt_nhds hneg)).and (hO.mem_nhds hy)
  obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 hev
  have himg : IsOpen ((A.chart j).symm '' N) :=
    (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2.1
  have hsub : (A.chart j).symm '' N ⊆ Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzV
    have h := hnn x j z ⟨(hNsub hz).2.1, hzV, (hNsub hz).2.2⟩ w
    linarith [(hNsub hz).1]
  have hmem : (A.chart j).symm y ∈ interior Vᶜ := interior_maximal hsub himg ⟨y, hyN, rfl⟩
  rw [hV] at hmem
  exact hmem

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
