module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle013
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle105
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle084
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle042
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateNorm

theorem inOK_neg {d : ℕ} {z : ℂ} (h : InOK d z) : InOK d (-z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨-u, -v, by push_cast; ring⟩

theorem thetaTranslateValueAtZero_neg (d : ℕ) (θ : ℂ → ℂ) (he : ∀ z, θ (-z) = θ z) (t z : ℂ) :
    U1 d (-t) θ z = U1 d t θ (-z) := by
  unfold U1 h1
  rw [← he (z + -t)]
  congr 2
  · ring
  · simp only [map_neg]; ring

theorem cmLatticeTranslationOperator_mul_neg_translate (d : ℕ) (θ : ℂ → ℂ) (t w : ℂ) :
    U1 d t θ w * U1 d (-t) θ (w + t) = θ w * θ (w + t) := by
  unfold U1 h1
  have h0 : w + t + -t = w := by ring
  rw [h0, mul_mul_mul_comm, ← Complex.exp_add]
  have : -(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * (w * conj t)) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (t * conj t)) +
      (-(Real.pi : ℂ) * (((2 / Real.sqrt d : ℝ) : ℂ) * ((w + t) * conj (-t))) -
      (Real.pi : ℂ) / 2 * (((2 / Real.sqrt d : ℝ) : ℂ) * (-t * conj (-t)))) = 0 := by
    simp only [map_neg]; ring
  rw [this, Complex.exp_zero]; ring

theorem differentiable_cmLatticeTranslationOperator_of_diff (d : ℕ) (θ : ℂ → ℂ) (hθ : Differentiable ℂ θ) (t : ℂ) : Differentiable ℂ (U1 d t θ) := by
  unfold U1 h1
  fun_prop

theorem ell_shift {L : PeriodPair} {φ : ℂ → ℂ} (h : Ell L φ) (a : ℂ) : Ell L (fun z => φ (z + a)) := by
  refine ⟨fun x => ?_, fun l hl z => ?_⟩
  · have h1 : MeromorphicAt φ ((fun z : ℂ => z + a) x) := h.1 _
    exact h1.comp_analyticAt (f := φ) (g := fun z : ℂ => z + a) (by fun_prop)
  · have := h.2 l hl (z + a)
    show φ (z + l + a) = φ (z + a)
    rw [← this]; congr 1; ring

theorem bd_one_of_inv {q : ℕ} [Fact q.Prime] (f g : ℂ_[q]⟦X⟧) (hf : Bdd f) (hg : Bdd g) (hfg : f * g = 1)
    (h : ∀ B, Bd B g → Bd B f) : Bd 1 f := by
  have h1 : Bd 1 (f * g) := by
    rw [hfg]
    intro n
    rw [coeff_one]
    split_ifs <;> simp
  have hm := (sup_norm_laws q).2.2.2.1 f g 1 hf hg h1
  intro i
  by_contra hi
  push_neg at hi
  have hp : 0 < ‖coeff i f‖ := lt_trans one_pos hi
  have hb : Bd (1 / ‖coeff i f‖) g := fun j => by
    rw [le_div_iff₀ hp, mul_comm]; exact hm i j
  have := h _ hb i
  rw [le_div_iff₀ hp] at this
  nlinarith

theorem bd_translate : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ t : ℂ, PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd 1 (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q _ M ω θ hd h16 hsp hOK hch hth t hpt hnt
  obtain ⟨s, hs, hsq, hst⟩ := id hpt
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨hdiff, h0, hev, -, hz⟩ := id hth
  have hθt : θ t ≠ 0 := fun h => hnt (hz t h)
  have hP := GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd h16 hsp hOK hch hth t s hs hsq hst
  have hN := GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd h16 hsp hOK hch hth (-t) s hs hsq
    (by have := inOK_neg hst; rwa [← mul_neg] at this)
  simp only at hP hN
  set φp : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφp
  set φm : ℂ → ℂ := fun z => U1 d (-t) θ ((s : ℂ) * z) / θ ((s : ℂ) * z) with hφm
  obtain ⟨-, hPa, -, hPs, hPb⟩ := hP
  obtain ⟨hNe, hNa, hNp, -, hNb⟩ := hN
  set t' : ℂ := t / s with ht'
  have hst' : (s : ℂ) * t' = t := by rw [ht']; field_simp
  set ψ : ℂ → ℂ := fun z => φm (z + t') with hψ
  have hψe : Ell M.L ψ := ell_shift hNe t'
  have hψan : ∀ p, AnalyticAt ℂ φm (p + t') → AnalyticAt ℂ ψ p := fun p hp =>
    AnalyticAt.comp (g := φm) (f := fun z : ℂ => z + t') hp (by fun_prop)
  have hψ0 : AnalyticAt ℂ ψ 0 := hψan 0 (hNp _ (by rwa [zero_add, hst']))
  have hψt : AnalyticAt ℂ ψ (-t') := hψan _ (by rwa [neg_add_cancel])
  have hψp : ∀ p, meromorphicOrderAt ψ p < 0 → ¬ M.Small p := by
    intro p hp
    apply hPs p t hpt hnt
    by_contra hne
    have : AnalyticAt ℂ ψ p := hψan p (hNp _ (by rwa [mul_add, hst']))
    exact absurd this.meromorphicOrderAt_nonneg (not_le.mpr hp)
  have hψb := GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ ψ hch hψe hψ0 hψp
  have hback : (fun z => ψ (z + -t')) = φm := by
    funext z; simp [hψ]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hat1 := TaylorRead.hat_laws q M.ι _ hℓ
  have hmul := MulSeries.mulS_laws q

  have hb1 : ∀ B, Bd B (hat M.ι (C ω * logS) ψ) → Bd B (hat M.ι (C ω * logS) φm) := by
    intro B hB
    by_cases hsm : M.Small (-t')
    · have hin : InOK d (-t') := (GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd h16 hsp hOK hch).2.2.1 (-t')
        ⟨s * s, Nat.mul_pos hs hs, Nat.Coprime.mul_left hsq hsq, by
          have : ((s * s : ℕ) : ℂ) * (-t') = -((s : ℂ) * t) := by
            rw [← hst']; push_cast; ring
          rw [this]; exact inOK_neg hst⟩ hsm
      have hl : t' ∈ M.L.lattice := (hOK t').2 (by simpa using inOK_neg hin)
      have : ψ = φm := funext fun z => hNe.2 t' hl z
      rwa [← this]
    · have := GlobalTheory.T.cpTransportedTaylorSeries_translate_norm_le q M _ ψ (-t') B hch hψe hψ0 hψt hψp hsm (by rwa [hback]) hB
      rwa [hback] at this

  have hmp : φm = fun z => φp ((-1 : ℂ) * z) := by
    funext z
    simp only [hφm, hφp]
    rw [thetaTranslateValueAtZero_neg d θ hev, ← hev ((s : ℂ) * z)]
    congr 2 <;> ring
  have hb2 : ∀ B, Bd B (hat M.ι (C ω * logS) φm) → Bd B (hat M.ι (C ω * logS) φp) := by
    intro B hB
    rw [hmp, (hat_multiplicative_chart q M.ι ω φp hPa).2.2.1 (-1) (-1) (by simp [zc])] at hB
    exact (hmul.2.2.2.1 (-1) _ B (by simp)).1 hB

  have hprod : hat M.ι (C ω * logS) φp * hat M.ι (C ω * logS) ψ = 1 := by
    rw [← (hat1.1 φp ψ hPa hψ0).2.1]
    have hc := hat1.2.1 1
    rw [map_one, map_one] at hc
    rw [← hc]
    apply (hat1.1 _ _ (hPa.mul hψ0) analyticAt_const).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have c1 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    have c2 : ContinuousAt (fun z : ℂ => θ ((s : ℂ) * z + t)) 0 :=
      (hdiff.continuous.comp (by fun_prop)).continuousAt
    filter_upwards [c1.eventually_ne (y := 0) (by simp [h0]), c2.eventually_ne (y := 0) (by simpa using hθt)]
      with z hz1 hz2
    simp only [hψ, hφm, hφp, Pi.mul_apply]
    rw [mul_add, hst', div_mul_div_comm, cmLatticeTranslationOperator_mul_neg_translate]
    exact div_self (mul_ne_zero hz1 hz2)
  have hP1 : Bd 1 (hat M.ι (C ω * logS) φp) :=
    bd_one_of_inv _ _ hPb hψb hprod fun B hB => hb2 B (hb1 B hB)

  have hθa : AnalyticAt ℂ θ 0 := hdiff.analyticAt 0
  have hUa : AnalyticAt ℂ (U1 d t θ) 0 := (differentiable_cmLatticeTranslationOperator_of_diff d θ hdiff t).analyticAt 0
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := hUa.div hθa (by simp [h0])
  have hf1 : Bd 1 (hat M.ι (C ω * logS) f) := by
    have e := (hat_multiplicative_chart q M.ι ω f hfa).2.2.1 (s : ℂ) (s : ℤ_[q]) (by simp [zc])
    have e' : φp = fun z => f ((s : ℂ) * z) := rfl
    rw [e', e] at hP1
    exact (hmul.2.2.2.1 (s : ℤ_[q]) _ 1 (PadicInt.norm_natCast_eq_one_iff.2 hsq.symm)).1 hP1
  have hθ1 := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h16 hsp hOK hch hth
  have hfin : hat M.ι (C ω * logS) (U1 d t θ) = hat M.ι (C ω * logS) f * hat M.ι (C ω * logS) θ := by
    rw [← (hat1.1 f θ hfa hθa).2.1]
    apply (hat1.1 _ _ hUa (hfa.mul hθa)).2.2.1
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [hdiff.continuous.continuousAt.eventually_ne (y := 0) (x := 0) (by simp [h0])] with z hz1
    simp only [hf, Pi.mul_apply]
    rw [div_mul_cancel₀ _ hz1]
  rw [hfin]
  simpa using ((sup_norm_laws q).1 _ _ 1 1 hf1 hθ1).2

end GlobalTheory.MomOne.TranslateNorm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.jets_on_copies_of_compatible_frames : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  first | exact @GlobalTheory.PowJets.jets_on_copies | exact GlobalTheory.PowJets.jets_on_copies | (intros; apply GlobalTheory.PowJets.jets_on_copies <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero => intro j _ w _; simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hk0 : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => by rw [pow_mul]; positivity
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ := fun v =>
      ((hκ.pow_const _).mul (hf v)).ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            have := mul_le_mul_of_nonneg_left (hx w) (hk0 x)
            simp only [Finset.mul_sum] at this
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ _ := this
          refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hk0 x) (hf0 _ x))]
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ (fun c _ => Finset.aemeasurable_fun_sum _ fun e _ => hm _)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [lintegral_finsetSum' _ (fun e _ => hm _)]
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) :=
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun e _ =>
            ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (∑ c, ∑ e, B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun c _ => Finset.sum_nonneg fun e _ => by positivity)]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => by positivity)]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (hs j w (by omega) hw) (pow_nonneg hB (2 * q))
          simp only [Finset.mul_sum] at this
          calc _ ≤ _ := this
            _ = _ := by ring

theorem ratio_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q hjq a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmass := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).1
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS
  have hDS := hFam ν hν
  obtain ⟨hBe, hdg, -⟩ := hSF ν hν
  obtain ⟨hae, -, hlen, hl⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν).1
  obtain ⟨⟨hbv, -⟩, hsh⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hShape := (hsh ν hν).2.1
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (v : (R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (fun c e v => E ν c e v)
    (Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)))
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (by positivity) ((hlen _).div (hlen _))
    (fun v => (((hl (l ν) hBe.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _)
    (fun v x => by positivity) ?_
    (fun i v hv c e => GlobalTheory.lev_E_add_two _ _ _ _ _ i v hMod.1 hMod.2.1 hv c e)
    (fun i v hi hv => ?_) (fun v => hmass v v.2) q j hjq w hw
  · filter_upwards [hae] with x hx v
    have h1 := mul_le_mul_of_nonneg_left
      (GlobalTheory.T.bessel_cayley_side_bound hK k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDS hG hBe.1 hQ (hE ν hν).1
        _ hx a v) hdg.le
    simp only [Finset.mul_sum] at h1
    calc _ = _ := by ring
      _ ≤ _ := h1
  · have h1 := GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k i bv b v hMod hShape hbv hi hv
    calc _ ≤ _ := h1
      _ = _ := by ring

end GlobalTheory.RatioMoment
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Moment

theorem n1_sub_single_one_le_add_one {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : (∑ i, ((Pi.single s (1 : ℤ) : Fin n → ℤ) i).natAbs) = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Int.natAbs_sub_le _ _

theorem moment_first_length : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ (q : ℕ) ν, n1 ν + q ≤ q0 → ∀ j : ℕ, j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q * ‖w‖ ^ 2) := by
  intro H k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE q
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hS.2.2.1.2.1
  have hC : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have h6 : 0 ≤ (6 * bv) ^ (2 * (2 * r + 2)) := by rw [pow_mul]; positivity
    positivity
  induction q with
  | zero =>
    intro ν hν j _ w _
    have := (GlobalTheory.T.bessel_functional_l2_bound_and_isometry H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν (by omega)).1 w w.2
    simpa using this
  | succ q ih =>
    intro ν hν j hj w hw
    have := GlobalTheory.T.family_setup_cayley_moment H k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν (by omega) j q _
      (by omega) (pow_nonneg hC q)
      (fun s y hy => ih (ν - Pi.single s 1) (by have := n1_sub_single_one_le_add_one ν s; omega) (j + 2) (by omega) y hy) w hw
    rw [pow_succ' _ q]
    exact this

end GlobalTheory.Moment
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSum

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2 MeasureTheory Filter
open scoped ComplexConjugate

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable [FiniteDimensional ℂ Wp]


open Finset MeasureTheory Filter in
open scoped ComplexConjugate in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
theorem _root_.GlobalTheory.BetaSum.beta_sesq (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ}
    (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {F F' G : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F) (hF' : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F')
    (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) (c : ℂ) :
    _root_.Formalism.FourierDecayAlt.B.beta D (F + c • F') G = _root_.Formalism.FourierDecayAlt.B.beta D F G + c * _root_.Formalism.FourierDecayAlt.B.beta D F' G ∧
      _root_.Formalism.FourierDecayAlt.B.beta D G (F + c • F') = _root_.Formalism.FourierDecayAlt.B.beta D G F + conj c * _root_.Formalism.FourierDecayAlt.B.beta D G F' :=
  _root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hF hF' hG c

end GlobalTheory.BetaSum

namespace GlobalTheory

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_eq_star_beta_swap (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (F G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) :
    _root_.Formalism.FourierDecayAlt.B.beta D F G = star (_root_.Formalism.FourierDecayAlt.B.beta D G F) := by
  unfold _root_.Formalism.FourierDecayAlt.B.beta _root_.Formalism.QuantumDeterminants.betaBig
  rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, ← integral_conj]
  congr 1
  ext p
  simp [inner_conj_symm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_congr_right_on_GV (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {F G G₂ : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (h : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, G g = G₂ g) : _root_.Formalism.FourierDecayAlt.B.beta D F G = _root_.Formalism.FourierDecayAlt.B.beta D F G₂ := by
  rw [beta_eq_star_beta_swap D F G, beta_eq_star_beta_swap D F G₂, _root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D h]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_left (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D (fun g ↦ ∑ i ∈ s, c i • Fi i g) G = ∑ i ∈ s, c i * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_zero
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA h0 h0 hG 1).1
    have e : ((fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) +
        (1 : ℂ) • (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp))) =
        (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := by
      funext g; simp
    rw [e, one_mul] at h
    simp only [Finset.sum_empty]
    have : _root_.Formalism.FourierDecayAlt.B.beta D (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) G = 0 := by
      linear_combination -h
    exact this
  | insert x s hx ih =>
    have hs : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun g ↦ ∑ i ∈ s, c i • Fi i g) :=
      _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum s (fun i g ↦ c i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (c i) (hFi i))
    have e : (fun g ↦ ∑ i ∈ insert x s, c i • Fi i g) =
        (fun g ↦ ∑ i ∈ s, c i • Fi i g) + c x • Fi x := by
      funext g; simp [Finset.sum_insert hx, add_comm]
    rw [e, (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hs (hFi x) hG (c x)).1, ih, Finset.sum_insert hx, add_comm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_right (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D G (fun g ↦ ∑ i ∈ s, c i • Fi i g) = ∑ i ∈ s, star (c i) * _root_.Formalism.FourierDecayAlt.B.beta D G (Fi i) := by
  rw [beta_eq_star_beta_swap, beta_sum_smul_left D hA s c Fi hFi hG, star_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [star_mul', beta_eq_star_beta_swap D G (Fi i)]


open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
theorem _root_.GlobalTheory.beta_finset_sum_smul_of_bessel : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (ι : Type) (S T : Finset ι) (a b : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (F F' : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → (∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F g = ∑ i ∈ S, a i • Fi i g) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F' g = ∑ i ∈ T, b i • Fi i g) → _root_.Formalism.FourierDecayAlt.B.beta D F F' = ∑ i ∈ S, ∑ j ∈ T, a i * star (b j) * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) (Fi j) := by
  intro _ k r Wp Wq _ _ _ _ _ _ D A ι S T a b Fi F F' hA hFi hF hF'
  rw [_root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D hF, beta_congr_right_on_GV D hF',
    beta_sum_smul_left D hA S a Fi hFi
      (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum T (fun i g ↦ b i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (b i) (hFi i)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [beta_sum_smul_right D hA T b Fi hFi (hFi i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end GlobalTheory
end
