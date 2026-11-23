module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
import Aesop.Main
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle003
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
import GroundTheory.GlobalFields.TateThesis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle078
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle020
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

private theorem integral_indicator_mul_char_of_trivial {K : Type} [CommRing K] [MeasurableSpace K]
    (μ : Measure K) (p : K → ℂ) (S : AddSubgroup K) (hSm : MeasurableSet (S : Set K)) (y : K)
    (h : ∀ s ∈ S, p (s * y) = 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = ((μ (S : Set K)).toReal : ℂ) := by
  have hfun : (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) =
      (S : Set K).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ (S : Set K)
    · rw [Set.indicator_of_mem hx, one_mul, h x hx]
    · rw [Set.indicator_of_notMem hx, zero_mul]
  rw [hfun, integral_indicator_const _ hSm, measureReal_def, Complex.real_smul, mul_one]

private theorem integral_indicator_mul_char_eq_zero {K : Type} [CommRing K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) [μ.IsAddLeftInvariant] (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (S : AddSubgroup K) (y : K) (h : ∃ s ∈ S, p (s * y) ≠ 1) :
    ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
  obtain ⟨s, hs, hps⟩ := h
  have hI : ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      p (s * y) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ := by
    rw [← integral_const_mul, ← integral_add_left_eq_self
      (fun x => (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y)) s]
    congr 1
    funext x
    beta_reduce
    by_cases hx : x ∈ (S : Set K)
    · have hsx : s + x ∈ (S : Set K) := (S.add_mem_cancel_left hs).mpr hx
      rw [Set.indicator_of_mem hsx, Set.indicator_of_mem hx, add_mul, hadd]
      ring
    · have hsx : s + x ∉ (S : Set K) := fun h' => hx ((S.add_mem_cancel_left hs).mp h')
      rw [Set.indicator_of_notMem hsx, Set.indicator_of_notMem hx]
      ring
  have h1 : (1 - p (s * y)) * ∫ x, (S : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hps
  · exact h0

theorem ann_core {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] [MeasurableSpace K] [MeasurableAdd K]
    (μ : Measure K) (p : K → ℂ) (hadd : ∀ x y, p (x + y) = p x * p y)
    (hSD : SelfDual μ (fun s t => p (s * t)))
    (U A B : AddSubgroup K) (hUc : IsCompact (U : Set K)) (hUo : IsOpen (U : Set K))
    (hUm : MeasurableSet (U : Set K)) (hAm : MeasurableSet (A : Set K)) (hAf : μ (A : Set K) ≠ ⊤)
    (hA : ∀ y, y ∈ A ↔ ∀ s ∈ U, p (s * y) = 1)
    (hB : ∀ z, z ∈ B ↔ ∀ s ∈ A, p (s * z) = 1) :
    B = U ∧ (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by
  obtain ⟨hHaar, hinv⟩ := hSD
  have hp0 : p 0 = 1 := by simpa using (hA 0).mp A.zero_mem 0 U.zero_mem
  have hΦc : Continuous ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hUc.isClosed, hUo⟩ continuous_const
  have hΦs : HasCompactSupport ((U : Set K).indicator (fun _ => (1 : ℂ))) :=
    HasCompactSupport.intro hUc (fun x hx => Set.indicator_of_notMem hx _)
  have hFT : ∀ y, ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x * p (x * y) ∂μ =
      (A : Set K).indicator (fun _ => ((μ (U : Set K)).toReal : ℂ)) y := by
    intro y
    by_cases h : ∀ s ∈ U, p (s * y) = 1
    · rw [integral_indicator_mul_char_of_trivial μ p U hUm y h,
        Set.indicator_of_mem (show y ∈ (A : Set K) from (hA y).mpr h)]
    · push_neg at h
      rw [integral_indicator_mul_char_eq_zero μ p hadd U y h,
        Set.indicator_of_notMem (show y ∉ (A : Set K) from fun h' => by
          obtain ⟨s, hs, hps⟩ := h
          exact hps ((hA y).mp h' s hs))]
  have hint : Integrable (fun y => ∫ x, (U : Set K).indicator (fun _ => (1 : ℂ)) x *
      (fun s t => p (s * t)) x y ∂μ) μ := by
    simp only [hFT]
    exact (integrable_indicator_iff hAm).mpr (integrableOn_const hAf)
  have key : ∀ z, ((μ (U : Set K)).toReal : ℂ) *
      ∫ y, (A : Set K).indicator (fun _ => (1 : ℂ)) y * p (y * z) ∂μ =
      (U : Set K).indicator (fun _ => (1 : ℂ)) (-z) := by
    intro z
    rw [← integral_const_mul, ← hinv _ hΦc hΦs hint z]
    congr 1
    funext y
    beta_reduce
    rw [hFT y]
    by_cases hy : y ∈ (A : Set K)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have h0 := key 0
  have hc0 : ∀ s ∈ A, p (s * 0) = 1 := fun s _ => by rw [mul_zero, hp0]
  rw [integral_indicator_mul_char_of_trivial μ p A hAm 0 hc0, neg_zero,
    Set.indicator_of_mem (show (0 : K) ∈ (U : Set K) from U.zero_mem)] at h0
  have hprod : (μ (U : Set K)).toReal * (μ (A : Set K)).toReal = 1 := by exact_mod_cast h0
  refine ⟨?_, hprod⟩
  ext z
  rw [hB z]
  have hz := key z
  constructor
  · intro h
    rw [integral_indicator_mul_char_of_trivial μ p A hAm z h, h0] at hz
    by_contra hzU
    rw [Set.indicator_of_notMem (show -z ∉ (U : Set K) from fun h' => hzU (by simpa using U.neg_mem h'))] at hz
    exact one_ne_zero hz
  · intro hzU
    by_contra h
    push_neg at h
    rw [integral_indicator_mul_char_eq_zero μ p hadd A z h, mul_zero,
      Set.indicator_of_mem (show -z ∈ (U : Set K) from U.neg_mem hzU)] at hz
    exact zero_ne_one hz

theorem localDual : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (c : ℝ≥0), GlobalTheory.CompanionTheory.SW.IsStdV v lam → SelfDual (c • lam) (fun s t => psiV F ψ v (s * t)) → ∀ U : AddSubgroup (Fv F v), IsCompact (U : Set (Fv F v)) → IsOpen (U : Set (Fv F v)) → annV ψ v (annV ψ v U) = U ∧ IsCompact (annV ψ v U) ∧ IsOpen (annV ψ v U) ∧ (c : ℝ) ^ 2 * (lam U).toReal * (lam (annV ψ v U)).toReal = 1 := by
  intro F _ _ ψ hψ v lam c _ hSD U hUc hUo
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have h0 := psiV_zero ψ v
  have hinv := hSD.1
  have hcomp : IsCompact (annV ψ v U) := GlobalTheory.CompanionTheory.SW.PiV.ann_isCompact hc h0 hy U hUo
  have hnear : {x | ‖psiV F ψ v x - 1‖ < 1 / 2} ∈ nhds (0 : Fv F v) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds (by
      change ‖psiV F ψ v 0 - 1‖ < 1 / 2
      rw [h0]
      norm_num)
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_subset _ hnear
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.SW.PiV.exists_ball_of_isCompact _ hUc
  have htriv : ∀ x ∈ GlobalTheory.CompanionTheory.SW.PiV.ball v m, psiV F ψ v x = 1 := fun x hx =>
    char_eq_one_of_near (GlobalTheory.CompanionTheory.SW.PiV.ball v m) _ h0 ha (fun x hx => hm hx) hx
  have hsub : (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n) : Set (Fv F v)) ⊆ annV ψ v U := by
    intro t ht s hs
    refine htriv _ ?_
    rw [GlobalTheory.CompanionTheory.SW.PiV.mem_ball, map_mul]
    calc Valued.v s * Valued.v t ≤ WithZero.exp n * WithZero.exp (m - n) :=
          mul_le_mul' (hn hs) ht
      _ = WithZero.exp m := by rw [← WithZero.exp_add, add_sub_cancel]
  have hopen : IsOpen (annV ψ v U) :=
    AddSubgroup.isOpen_of_mem_nhds (annS ψ v U) (g := 0)
      (Filter.mem_of_superset ((GlobalTheory.CompanionTheory.SW.PiV.ball_isOpen (m - n)).mem_nhds
        (GlobalTheory.CompanionTheory.SW.PiV.ball v (m - n)).zero_mem) hsub)
  have hcore := ann_core (c • lam) (psiV F ψ v) ha hSD U (annS ψ v U) (annS ψ v (annV ψ v U))
    hUc hUo hUo.measurableSet hopen.measurableSet hcomp.measure_lt_top.ne
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨?_, hcomp, hopen, ?_⟩
  · rw [← coe_annS, hcore.1]
  · have h5 := hcore.2
    rw [coe_annS] at h5
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal] at h5
    rw [← h5]
    ring

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

section

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem hilbertClassFieldJ : GlobalTheory.Published.HilbertClassFieldJ :=
  GlobalTheory.Published.ComplexMultiplicationJSt.hilbertClassFieldJ GlobalTheory.CompanionTheory.Published.complexMultiplicationJ

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section


theorem _root_.GlobalTheory.T.complex_multiplication_jacquet_shalika : GlobalTheory.Published.ComplexMultiplicationJSt := by
  first | exact @GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | exact GlobalTheory.CompanionTheory.Published.complexMultiplicationJ | (intros; apply GlobalTheory.CompanionTheory.Published.complexMultiplicationJ <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim

theorem tendsto_fouInf_div_integral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∀ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets → ∀ t : Ainf F, Filter.Tendsto (fun k => fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) Filter.atTop (nhds 1) := by
  intro F _ _ ψ hψ laminf _ ρ hρ hsupp t
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hg_cont : Continuous fun x : Ainf F => psiInf F ψ (x * t) := by
    have h1 : Continuous fun x : Ainf F => pairA F (x * t) 0 :=
      (continuous_mul_const t).prodMk continuous_const
    exact hψ.1.comp h1
  have hg0 : psiInf F ψ (0 * t) = 1 := by
    have h0 : pairA F (0 * t) 0 = 0 := by
      rw [zero_mul]
      rfl
    show ψ (pairA F (0 * t) 0) = 1
    rw [h0, AddChar.map_zero_eq_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU : (fun x : Ainf F => psiInf F ψ (x * t)) ⁻¹' Metric.ball 1 (ε / 2) ∈ nhds (0 : Ainf F) := by
    apply hg_cont.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact Metric.ball_mem_nhds _ (half_pos hε)
  filter_upwards [Filter.tendsto_smallSets_iff.1 hsupp _ hU] with k hk
  obtain ⟨hc, hcs, hnn, hI⟩ := hρ k
  have hint : Integrable (ρ k) laminf := hc.integrable_of_hasCompactSupport hcs
  have hc1 : Continuous fun x => (ρ k x : ℂ) := Complex.continuous_ofReal.comp hc
  have hcs1 : HasCompactSupport fun x => (ρ k x : ℂ) := hcs.comp_left Complex.ofReal_zero
  have hi1 : Integrable (fun x => (ρ k x : ℂ)) laminf := hc1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable (fun x => (ρ k x : ℂ) * psiInf F ψ (x * t)) laminf :=
    (hc1.mul hg_cont).integrable_of_hasCompactSupport
      (hcs1.mul_right (f' := fun x => psiInf F ψ (x * t)))
  have key : fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)
      = ∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf := by
    unfold fouInf
    rw [← integral_complex_ofReal, ← integral_sub hi2 hi1]
    congr 1
    ext x
    ring
  have hIc : ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hI.ne'
  have hsplit : fouInf ψ laminf (ρ k) t / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) - 1
      = (fouInf ψ laminf (ρ k) t - ((∫ y, ρ k y ∂laminf : ℝ) : ℂ)) / ((∫ y, ρ k y ∂laminf : ℝ) : ℂ) := by
    rw [sub_div, div_self hIc]
  have hbound : ‖∫ x, (ρ k x : ℂ) * (psiInf F ψ (x * t) - 1) ∂laminf‖ ≤ ∫ x, ρ k x * (ε / 2) ∂laminf := by
    apply norm_integral_le_of_norm_le (hint.mul_const _)
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    by_cases hx : x ∈ tsupport (ρ k)
    · have h := hk hx
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_left h.le (hnn x)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [integral_mul_const] at hbound
  rw [dist_eq_norm, hsplit, key, norm_div, Complex.norm_real, Real.norm_of_nonneg hI.le, div_lt_iff₀ hI]
  nlinarith

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfLim
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integral_pure_indicator_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : AddSubgroup (Af F)), MeasurableSet (B : Set (Af F)) → lf (B : Set (Af F)) ≠ ⊤ → ∀ b : AF F, ∫ y, (g (fstA F y) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F y)) * ψ (y * b) ∂db = (∫ x, g x * psiInf F ψ (x * fstA F b) ∂laminf) * ((lf (B : Set (Af F))).toReal : ℂ) * (annF ψ (B : Set (Af F))).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
  intro F _ _ ψ _ db laminf lf hl hf e he hmp g B hB hfin b
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.1
  haveI : SecondCountableTopology (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.2.1
  haveI : SecondCountableTopology (Ainf F) := by
    haveI : SecondCountableTopology (Ainf F × Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1.2.1
    exact (Topology.IsEmbedding.of_comp (f := fun x : Ainf F => (x, (0 : Af F))) (g := Prod.fst)
      (by fun_prop) continuous_fst Topology.IsEmbedding.id).secondCountableTopology
  haveI : LocallyCompactSpace (Ainf F) := inferInstance
  haveI : IsLocallyFiniteMeasure laminf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : IsLocallyFiniteMeasure lf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SFinite laminf := inferInstance
  haveI : SFinite lf := inferInstance
  set χ : Af F → ℂ := fun u => psiF ψ (u * sndA F b) with hχ
  have hχadd : ∀ x y, χ (x + y) = χ x * χ y := fun x y => by
    simp only [hχ, add_mul, psiF_add]
  have hpt : ∀ p : Ainf F × Af F,
      (g (fstA F (e p)) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F (e p))) * ψ (e p * b) =
        (g p.1 * psiInf F ψ (p.1 * fstA F b)) * (B : Set (Af F)).indicator χ p.2 := by
    rintro ⟨x, u⟩
    have h1 : e (x, u) * b = pairA F (x * fstA F b) (u * sndA F b) := by
      rw [he]; rfl
    have h2 : fstA F (e (x, u)) = x := by rw [he]; rfl
    have h3 : sndA F (e (x, u)) = u := by rw [he]; rfl
    rw [h1, h2, h3, psi_pairA]
    by_cases hu : u ∈ (B : Set (Af F))
    · simp only [Set.indicator_of_mem hu, hχ]
      ring
    · simp only [Set.indicator_of_notMem hu]
      ring
  rw [← hmp.integral_comp e.measurableEmbedding]
  simp only [hpt]
  rw [integral_prod_mul (fun x => g x * psiInf F ψ (x * fstA F b))
    (fun u => (B : Set (Af F)).indicator χ u), mul_assoc]
  congr 1
  by_cases hb : sndA F b ∈ annF ψ (B : Set (Af F))
  · rw [integral_indicator_char_of_trivial lf B hB χ (fun x hx => hb x hx),
      Set.indicator_of_mem hb, mul_one]
  · obtain ⟨y, hy, hne⟩ : ∃ y ∈ (B : Set (Af F)), psiF ψ (y * sndA F b) ≠ 1 := by
      simpa [annF] using hb
    rw [integral_indicator_char_of_ne lf B χ hχadd hy hne, Set.indicator_of_notMem hb, mul_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx

theorem exists_bumps_inf : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  intro hreal F _ _ hF ψ hψ laminf hH
  haveI := hF
  classical
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) := (GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous
  have he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm := (GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := GlobalTheory.CompanionTheory.SW.SdPi.exists_form (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  obtain ⟨g, hg1, hg2, hg3⟩ := hreal (InfinitePlace F) a ha
  set e := GlobalTheory.CompanionTheory.SW.RealCoord.coord F with hedef
  set E := GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F with hEdef
  have hEe : ∀ y, E y = e y := fun _ => rfl
  haveI : (laminf.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map laminf e.toAddEquiv he he'
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, laminf.map e = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : laminf.map e = 0 := by simpa using hc
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := laminf.map e)).open_pos Set.univ isOpen_univ
      Set.univ_nonempty (by simp [h0])
  have hme : MeasurableEmbedding e := E.measurableEmbedding
  have hint : ∀ f : (InfinitePlace F → ℝ) → ℂ, ∫ y, f (e y) ∂laminf = (c : ℝ) • ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  have hintR : ∀ f : (InfinitePlace F → ℝ) → ℝ, ∫ y, f (e y) ∂laminf = (c : ℝ) * ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  refine ⟨fun k y => g k (e y), fun k => ⟨(hg1 k).1.comp he, (hg1 k).2.1.comp_homeomorph E, fun y => (hg1 k).2.2.1 _, ?_⟩, ?_, fun k => ?_⟩
  · rw [hintR]
    have : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc0
    exact mul_pos this (hg1 k).2.2.2
  · rw [Filter.tendsto_smallSets_iff]
    intro U hU
    have hV : E.symm ⁻¹' U ∈ nhds (0 : InfinitePlace F → ℝ) := by
      apply E.symm.continuous.continuousAt.preimage_mem_nhds
      have : E.symm 0 = 0 := e.symm.map_zero
      rwa [this]
    obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (ge_mem_nhds hε)] with k hk y hy
    have h1 : e y ∈ tsupport (g k) := tsupport_comp_subset_preimage (g k) he hy
    have h3 : e y ∈ E.symm ⁻¹' U := hεV (Metric.closedBall_subset_closedBall hk (hg2 k h1))
    have h5 : E.symm (e y) = y := E.symm_apply_apply y
    rw [Set.mem_preimage, h5] at h3
    exact h3
  · have hfou : ∀ t, fouInf ψ laminf (fun y => g k (e y)) t = (c : ℝ) • ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ)) := by
      intro t
      have h6 := hint (fun u => (g k u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * e t w) : ℝ) : ℂ)))
      rw [← h6, fouInf]
      simp only [hχ, map_mul, Pi.mul_apply]
    have hG : Integrable (fun t => ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))) laminf := by
      have h7 : Integrable (fun t : InfinitePlace F → ℝ => ∫ x, (g k x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) (laminf.map e) := by
        rw [hc]
        exact (hg3 k).smul_measure_nnreal
      exact hme.integrable_map_iff.1 h7
    rw [funext hfou]
    exact hG.smul (c : ℝ)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx
end
end
