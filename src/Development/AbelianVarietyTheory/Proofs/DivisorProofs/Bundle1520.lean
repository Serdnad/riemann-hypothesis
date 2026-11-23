module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle001
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035

@[expose] public section

section

open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

theorem summable_seminorm_term : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  intro E _ _ _ _ _ b c hb hc h t ht k n

  set δ : ℝ := min 1 (b / (6 * c)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ b / (6 * c) := min_le_right _ _
  set θ : ℝ := 1 + δ with hθ
  set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα
  have hθ1 : 1 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hθα : c * θ ^ 2 ≤ α * (b + c) := by
    have e1 : α * (b + c) = c + b / 2 := by rw [hα]; field_simp
    have e2 : δ * (6 * c) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hδ2
    rw [e1, hθ]; nlinarith

  choose K hK using fun m => GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded E c α hc hα1 k m
  set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => integral_nonneg fun a => by positivity
  set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB
  have hK0 : ∀ m, 0 ≤ K m := fun m => le_trans (by positivity) (hK m 0)
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)
  have hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B := by
    intro j
    refine SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_
    set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs
    have hs0 : 0 ≤ s := by positivity
    set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ :=
      ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf
    have hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y) := by
      funext y
      rw [ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) := by
      refine Complex.contDiff_exp.comp ?_
      refine ContDiff.neg ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y)) :=
      f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    have hL := norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)
    rw [hfun]
    have hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
      rw [hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤
        θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      set m := n - i
      have h1 := GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le E j f m y
      have h3 := GlobalTheory.T.gaussianConvolutionSeriesCoefficient_descFactorial_estimate E b c θ α hc hθ1 hα0 hθα h j m y
      have hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤
          θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m := by
        refine h1.trans (le_trans ?_ h3)
        have := mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))
        calc (j.descFactorial m : ℝ) * ‖f‖ * ‖y‖ ^ (j - m)
            ≤ (j.descFactorial m : ℝ) * (s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) * ‖y‖ ^ (j - m) := by
              gcongr
          _ = _ := by rw [hs]; ring
      have hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n := by
        have hinv : 0 < θ⁻¹ := inv_pos.2 hθpos
        have hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j :=
          pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)
        have e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m := by
          rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]
        rw [e]
        exact mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)
      have hGk := hK i y
      have hch : (0:ℝ) ≤ n.choose i := by positivity
      calc ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖)
          ≤ ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            (θ⁻¹ ^ j * θ ^ n * Real.exp (c * α * ‖y‖ ^ 2) * M m)) := by
            gcongr
            exact hPm.trans (by gcongr)
        _ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
              Real.exp (c * α * ‖y‖ ^ 2)))) := by ring
        _ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by
            gcongr
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) :=
            Finset.sum_le_sum hterm
      _ = θ⁻¹ ^ j * B := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B :=
    (summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B
  exact Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom

end GlobalTheory.ConvSeries
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaParseval

theorem exists_lintegral_sq_eq_mul_setLIntegral_theta : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ 𝓕 : Set ((κ → AF F) × (κ → AF F)),
      @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
      ∃ c : ENNReal, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
        ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2 ∂ν := by
  intro F _ _ ψ hψ κ _ μ hμ ν hν 𝓕 h𝓕
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F κ μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F κ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  refine ⟨(c₁ * μ 𝓕₁)⁻¹, fun Φ hΦ => ?_⟩
  have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F ψ hψ κ Φ hΦ
  have hG : @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) =>
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
  rw [hc _ hG (fun γ hγ w => by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F ψ hψ κ Φ γ hγ w])]
  simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F ψ hψ κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
  rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F κ μ hμ 𝓕₁ h𝓕₁ Φ hΦ, ← mul_assoc c₁, ← mul_assoc,
    ENNReal.inv_mul_cancel (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hctop htop), one_mul]

end GlobalTheory.ThetaParseval
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.SecWt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb Coeff Level)

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := fun τ τ' h => by
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conjEmb (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

theorem conj_cmHostRoot_ne_self : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro e
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 e
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end

theorem tauE_inj (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_inj {E : Type} [Field E] : Function.Injective (conjEmb (E := E)) := fun a b h => by
  ext x
  exact star_injective (RingHom.congr_fun h x)

theorem wtA_pos {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (tauE D s, n) = ext0 (w.aP s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl, if_neg (hne s s)]; rfl
  · intro t _ ht
    rw [if_neg (fun h => ht (tauE_inj D h).symm), if_neg (hne s t), add_zero]
  · simp

theorem wtA_neg {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (conjEmb (tauE D s), n) = ext0 (w.aM s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_neg (fun h => hne s s (Eq.symm h)), if_pos rfl, zero_add]
  · intro t _ ht
    rw [if_neg (fun h => hne t s (Eq.symm h)), if_neg (fun h => ht (tauE_inj D (conjEmb_inj h)).symm), add_zero]
  · simp

theorem aPl_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n < p) :
    (aPl D i p τ n : ℚ) =
      Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (p - 1 - n) n (by simp only [Ranks.r]; omega)
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) (n + (p - 1 - n)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have hc : ((p - 1 - n : ℕ) : ℚ) = (p : ℚ) - (n + 1) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hl, hc] at h3
  have g := (D.hc τ).gap_be i
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 =
      ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ z1 + z2 - (p - (n + 1)) - (s + 1) := by
    have : (0 : ℚ) ≤ ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aPl
  rw [if_pos hn, hz, Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem aMi_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p q c : ℕ) (hp : p = D.R.k + i) (hq : q = D.R.m - (i + 1))
    (hc : c < q) :
    (aMi D i p q τ (q - 1 - c) : ℚ) =
      -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) c p (by simp only [Ranks.r]; omega)
  have hm : (i : ℕ) + 1 < D.R.m := by omega
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) p = -(D.hc τ).b ⟨i + 1, hm⟩ := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  rw [hl] at h3
  have g := (D.hc τ).gap_eb i hm
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (p + c)
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) =
      ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ -(z2 + z1 + (c + 1) + s) := by
    have : (0 : ℚ) ≤ ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aMi
  rw [if_pos (by omega), show q - (q - 1 - c) = c + 1 by omega, show p + (c + 1) - 1 = p + c by omega, Nat.cast_succ, hz,
    Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem laU_eq_wtCol : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  intro D T _ κ hl ha hκ i σ hσ e he k ρ τ hτ c
  have hlab := (GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ).1 hσ
  have he' := he ρ
  generalize lab σ ρ = s at hlab he' ⊢
  have hrt : ∀ t, tauE D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hl.pins.1.2.2.2
  have hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t) := fun s t h => by
    have h1 := RingHom.congr_fun h (T.Q.H.rt : D.host.E)
    change _ = starRingEnd ℂ (tauE D t _) at h1
    rw [hrt, hrt] at h1
    exact conj_cmHostRoot_ne_self h1.symm
  have hrel : relab T.Q.c (res T σ) (tauE D s) = τ.1 := by
    rw [hτ, ← hlab]
    ext x
    show σ (algebraMap T.Q.c.F D.what₂.LL (embF T.Q.c (tauE D s) x)) = σ (labLL D s x)
    congr 1
    apply D.what₂.embLL.injective
    have h1 := RingHom.congr_fun (res_embLL T ha hl.pins.2.2.1) (embF T.Q.c (tauE D s) x)
    have h2 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau s).1 : D.host.E →+* D.host.E) x)
    exact h1.trans h2.symm
  have hi1 : Function.invFun (relab T.Q.c (res T σ)) τ.1 = tauE D s := by
    rw [← hrel]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hi2 : Function.invFun (relab T.Q.c (res T σ)) (conjEmb τ.1) = conjEmb (tauE D s) := by
    rw [← hrel, ← relab_conjEmb]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hp0 : ((T.U ((i : ℕ) + 1) (res T σ)).X k).p0 = (D.R.sigW ((i : ℕ) + 1)).2 :=
    ((hl.unf _ (inR i) _ hσ).2.1 k).1.trans (hl.pins.2.2.2 _ (inR i)).2.1
  have hs : (Wc D i).sig (tauE D s) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨hP, hM, hn⟩ := hκ i s
  rw [hs] at hP hM
  have hi := i.2
  have hc := c.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hq : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  have hr : D.R.r = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 := by
    rw [hp, hq]; simp only [Ranks.r]; omega
  obtain ⟨N, hN⟩ := (κ i).n_even
  have hN2 : (κ i).n / 2 = N := by omega
  have hNq : (N : ℚ) + N = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
    have : N + N = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
      rw [← hN, hn, ← hr]; rfl
    exact_mod_cast this
  unfold laU wtCol
  rw [hi1, hi2, hp0, hN2, wtA_pos hne, wtA_neg hne, ← sub_eq_iff_eq_add, eq_comm, Int.floor_eq_iff]
  by_cases h : (c : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2
  · have h1 : (D.R.sigW ((i : ℕ) + 1)).2 - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 := by omega
    have h2 := aMi_cast D i s _ _ c hp hq h
    rw [if_pos h, if_neg (not_le.2 h), ext0, dite_eq_left h1, hM]
    push_cast
    rw [h2, he']
    constructor <;> linarith
  · have h1 : (c : ℕ) - (D.R.sigW ((i : ℕ) + 1)).2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
    have h2 := aPl_cast D i s _ _ hp h1
    rw [if_neg h, if_pos (not_lt.1 h), ext0, dite_eq_left h1, hP]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [h2, he']
    constructor <;> linarith

end GlobalTheory.HolRead.SecWt
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem isIntegral_of_isIntB : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  intro v C _ _ _ κ b h1 hmul y hy
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) b with he
  have hsmul : ∀ (a : v.adicCompletionIntegers ℚ) (x : v.adicCompletion ℚ ⊗[ℚ] C),
      a • x = (a : v.adicCompletion ℚ) • x := fun a x => (algebraMap_smul (v.adicCompletion ℚ) a x).symm
  have hadd : ∀ x z, IsIntB v b x → IsIntB v b z → IsIntB v b (x + z) := fun x z hx hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hz i)
  let S : Subalgebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] C) :=
    { carrier := {x | IsIntB v b x}
      mul_mem' := fun {x z} hx hz => hmul x z hx hz
      one_mem' := h1
      add_mem' := fun {x z} hx hz => hadd x z hx hz
      zero_mem' := isIntB_zero v b
      algebraMap_mem' := fun a => by
        show IsIntB v b (algebraMap _ _ a)
        rw [Algebra.algebraMap_eq_smul_one, hsmul]
        intro i
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact mul_mem a.2 (h1 i) }
  have hS : Subalgebra.toSubmodule S = Submodule.span (v.adicCompletionIntegers ℚ)
      (Set.range fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
    apply le_antisymm
    · intro x hx
      rw [← e.sum_repr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ : ∃ c : v.adicCompletionIntegers ℚ, (c : v.adicCompletion ℚ) = e.repr x i :=
        ⟨⟨_, hx i⟩, rfl⟩
      rw [← hc, ← hsmul, he, Algebra.TensorProduct.basis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact isIntB_tmul_basis v b j
  refine IsIntegral.of_mem_of_fg S ?_ y hy
  rw [hS]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.AdicSpan
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem exists_int_smul_mem_adicCompletionIntegers_of_elt (v : HeightOneSpectrum ℤ) (a : v.adicCompletion ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : v.adicCompletion ℚ) * a ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨d, hd, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  rw [mul_comm]
  simpa using h

theorem exists_int_smul_isIntB : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M)
    (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] M), ∃ D : ℤ, D ≠ 0 ∧ IsIntB v b (D • y) := by
  intro M _ _ κ b v y
  choose d hd0 hd using exists_int_smul_mem_adicCompletionIntegers_of_elt v
  set c := (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y with hc
  refine ⟨∏ i ∈ c.support, d (c i), Finset.prod_ne_zero_iff.mpr fun i _ => hd0 _, fun i => ?_⟩
  rw [map_zsmul, ← hc, Finsupp.smul_apply, zsmul_eq_mul]
  by_cases hi : i ∈ c.support
  · rw [← Finset.prod_erase_mul _ _ hi, Int.cast_mul, mul_assoc]
    exact mul_mem (intCast_mem _ _) (hd _)
  · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
    exact zero_mem _

end GlobalTheory.AdicSpan
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits

theorem _root_.GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  first | exact @GlobalTheory.CurveClosure.exists_closure_arith_surface_rat | exact GlobalTheory.CurveClosure.exists_closure_arith_surface_rat | (intros; apply GlobalTheory.CurveClosure.exists_closure_arith_surface_rat <;> assumption)
end
