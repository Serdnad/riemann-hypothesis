module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle013
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOpenChartDiagonalUnipotent
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Dens

def qMap {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x : InfinitePlace F → ι → ℝ) : InfinitePlace F → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))

def gW {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))

section
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_qMap (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Continuous (qMap B ρ) := by
  refine continuous_pi fun w => ?_
  exact continuous_const.mul (Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w)))

theorem continuous_gW (P : InfinitePlace F → Matrix ι ι ℝ) : Continuous (gW P) := by
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun w _ => ?_))
  exact Continuous.dotProduct (continuous_apply w)
    (Continuous.matrix_mulVec continuous_const (continuous_apply w))

theorem gauss_I (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun _ => Complex.I) x = (gW P x : ℂ) := by
  simp only [gauss, gW, Complex.I_re, Complex.I_im]
  push_cast
  congr 1
  simp [Finset.mul_sum]

theorem gauss_shift (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (t : InfinitePlace F → ℝ) (v : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v =
      (gW P v : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w, qMap B ρ v w * t w : ℝ) : ℂ)) := by
  simp only [gauss, gW, qMap]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, add_zero, zero_add, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring

theorem one_dim_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun t : ℝ => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  have h2 : ‖(t : ℂ) + Complex.I‖ ^ 2 = 1 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h1 : 1 ≤ ‖(t : ℂ) + Complex.I‖ := by
    have : (1 : ℝ) ^ 2 ≤ ‖(t : ℂ) + Complex.I‖ ^ 2 := by rw [h2]; nlinarith [sq_nonneg t]
    exact (pow_le_pow_iff_left₀ zero_le_one (norm_nonneg _) two_ne_zero).1 this
  rw [Real.norm_of_nonneg (by positivity), ← h2]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))

theorem prod_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun x : InfinitePlace F → ℝ => (∏ w, ‖(x w : ℂ) + Complex.I‖ ^ M)⁻¹) := by
  have := Integrable.fintype_prod (μ := fun _ => (volume : Measure ℝ))
    (f := fun (_ : InfinitePlace F) (t : ℝ) => (‖(t : ℂ) + Complex.I‖ ^ M)⁻¹)
    (fun _ => one_dim_integrable M hM)
  simpa [Finset.prod_inv_distrib, volume_pi] using this

theorem density_of_q : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∃ Di : (InfinitePlace F → ℝ) → ℝ, Continuous Di ∧ (∀ y, 0 ≤ Di y) ∧ (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Di y)) ∧ Integrable (fun x : InfinitePlace F → ℝ => cG B ρ P (fun w => (x w : ℂ) + Complex.I)) ∧ ∀ z : InfinitePlace F → ℝ, ∫ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) = ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di z : ℝ) : ℂ) := by
  intro F _ _ ι _ _ M B ρ P h hM
  classical
  have hdet : B.det ≠ 0 := h.2.2.2.1
  set S : ℝ := Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| with hS
  have hSpos : 0 < S := by
    refine Real.sqrt_pos.2 (abs_pos.2 ?_)
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hdet)
  have hSc : (S : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'

  have hgi : Integrable (gW P) := by
    have h0 := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P h (fun _ => Complex.I) (fun _ => by simp)).1
    have h1 := h0.re
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [gauss_I]
  have hgn : ∀ x, 0 ≤ gW P x := fun x => (Real.exp_pos _).le
  have hdm : Measurable fun x => ENNReal.ofReal (gW P x) :=
    ENNReal.measurable_ofReal.comp (continuous_gW P).measurable
  let ν : Measure (InfinitePlace F → ι → ℝ) := volume.withDensity fun x => ENNReal.ofReal (gW P x)
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hgi.2
  have hQ : Continuous (qMap B ρ) := continuous_qMap B ρ
  let m : Measure (InfinitePlace F → ℝ) := ν.map (qMap B ρ)
  haveI : IsFiniteMeasure m := Measure.isFiniteMeasure_map ν _

  have hχ : ∀ t : InfinitePlace F → ℝ,
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m =
        ∫ v, gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v := by
    intro t
    have hc : Continuous fun z : InfinitePlace F → ℝ =>
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) := by fun_prop
    rw [integral_map hQ.aemeasurable hc.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hdm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [ENNReal.toReal_ofReal (hgn v), Complex.real_smul]
    exact (gauss_shift B ρ P t v).symm
  have hcG : ∀ t : InfinitePlace F → ℝ, cG B ρ P (fun w => (t w : ℂ) + Complex.I) =
      (S : ℂ) * ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    intro t
    rw [hχ t]
    rfl

  have hcont : Continuous fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_) (fun t => ?_)
      (integrable_const _) (Filter.Eventually.of_forall fun z => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Filter.Eventually.of_forall fun z => ?_
      have : (2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ) =
          ((2 * Real.pi * ∑ w, z w * t w : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
  have hcGi : Integrable fun t : InfinitePlace F → ℝ =>
      cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
    have hcc : Continuous fun t : InfinitePlace F → ℝ =>
        cG B ρ P (fun w => (t w : ℂ) + Complex.I) := by
      simp only [hcG]
      exact continuous_const.mul hcont
    refine (prod_integrable (F := F) M hM).mono' hcc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have him : ∀ w, 0 < ((t w : ℂ) + Complex.I).im := fun w => by simp
    exact ((GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P h _ him).2.1).le
  have hχi : Integrable fun t : InfinitePlace F → ℝ =>
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * t w : ℝ) : ℂ)) ∂m := by
    refine (hcGi.const_mul ((S : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hcG]
    rw [inv_mul_cancel_left₀ hSc]
  obtain ⟨D, hDc, hD0, hDf, hDm⟩ := GlobalTheory.T.schur_function_compact_support_modulo_unipotent (InfinitePlace F) m inferInstance hχi
  refine ⟨D, hDc, hD0, fun U hU => ?_, hcGi, fun z => ?_⟩
  · rw [← hDm U hU, Measure.map_apply hQ.measurable hU, withDensity_apply _ (hQ.measurable hU)]
    rfl
  · have hmul : ∀ x : InfinitePlace F → ℝ, cG B ρ P (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) =
        (S : ℂ) * ((∫ u, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ w, u w * x w : ℝ) : ℂ)) ∂m) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ))) := by
      intro x
      rw [hcG x, mul_assoc]
    simp only [hmul]
    rw [integral_const_mul, ← hDf z, Complex.ofReal_mul]

end

end GlobalTheory.CompanionTheory.SW.Core.Dens
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_unitary_group_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ (pinf : HA (AF F) σ J →* HA (Ainf F) σ J) (p : ∀ v : HeightOneSpectrum (𝓞 F), HA (AF F) σ J →* HA (Fv F v) σ J), (∀ (n : ℕ) (h : HA (AF F) σ J) (X : (Fin n → Fin M → AF F ⊗[F] E)), projInf (actW (AF F) σ J h X) = actW (Ainf F) σ J (pinf h) (projInf X) ∧ ∀ v, projV v (projFin (actW (AF F) σ J h X)) = actW (Fv F v) σ J (p v h) (projV v (projFin X))) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (h : HA (AF F) σ J), ∀ᶠ v in Filter.cofinite, ∀ (n : ℕ) (X : (Fin n → Fin M → Fv F v ⊗[F] E)), actW (Fv F v) σ J (p v h) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ginf : HA (Ainf F) σ J) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J), ∃ h : HA (AF F) σ J, pinf h = ginf ∧ (∀ v ∈ S, p v h = g v) ∧ ∀ v, v ∉ S → p v h = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.HProj.components | exact GlobalTheory.CompanionTheory.SW.HProj.components | (intros; apply GlobalTheory.CompanionTheory.SW.HProj.components <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TupFubini

variable {T : Type} [MeasurableSpace T]

theorem measurable_cons_tail {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) :
    Measurable (fun Y : Fin n → A => (Fin.cons x Y : Fin (n + 1) → A)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using measurable_pi_apply j

theorem piFinSuccAbove_symm_apply {A : Type} [MeasurableSpace A] {n : ℕ} (x : A) (Y : Fin n → A) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).symm (x, Y) = Fin.cons x Y := by
  apply (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) 0).injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem lintegral_tuple_succ (m : Measure T) [SigmaFinite m] (n N : ℕ)
    (ψ : (Fin (n + 1) → Fin N → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ X, ψ X ∂(Measure.pi fun _ : Fin (n + 1) => Measure.pi fun _ : Fin N => m) =
      ∫⁻ y : Fin 1 → Fin N → T, ∫⁻ Y : Fin n → Fin N → T, ψ (Fin.cons (y 0) Y)
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin N => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin N => m) := by
  set P : Measure (Fin N → T) := Measure.pi fun _ : Fin N => m with hP
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0
  have h2 := measurePreserving_funUnique P (Fin 1)
  have hg : Measurable fun p : (Fin N → T) × (Fin n → Fin N → T) =>
      ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin N → T) 0).symm p) :=
    hψ.comp (MeasurableEquiv.measurable _)
  rw [← h1.symm.lintegral_comp hψ, lintegral_prod _ hg.aemeasurable,
    ← h2.lintegral_comp hg.lintegral_prod_right']
  refine lintegral_congr fun y => lintegral_congr fun Y => ?_
  rw [piFinSuccAbove_symm_apply]
  rfl

theorem lintegral_tuple_first_coord (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 1) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) =
      ∫⁻ c : Fin n → T, ∫⁻ X : Fin n → Fin M → T, ψ (fun a => Fin.cons (c a) (X a))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin n => m) := by
  let e₁ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => T) 0
  have h₁ : MeasurePreserving e₁ (Measure.pi fun _ : Fin (M + 1) => m)
      (m.prod (Measure.pi fun _ : Fin M => m)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => m) 0
  have h₂ := measurePreserving_pi (fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
    (fun _ : Fin n => m.prod (Measure.pi fun _ : Fin M => m)) (f := fun _ => e₁) (fun _ => h₁)
  have h₃ := measurePreserving_arrowProdEquivProdArrow T (Fin M → T) (Fin n) (fun _ => m)
    (fun _ => Measure.pi fun _ : Fin M => m)
  have h₄ := h₃.comp h₂
  let g : (Fin n → T) × (Fin n → Fin M → T) → Fin n → Fin (M + 1) → T :=
    fun p a => e₁.symm (p.1 a, p.2 a)
  have hg : Measurable g := by
    refine measurable_pi_iff.2 fun a => e₁.symm.measurable.comp ?_
    exact ((measurable_pi_apply a).comp measurable_fst).prodMk
      ((measurable_pi_apply a).comp measurable_snd)
  have hgi : ∀ Y, g ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
      fun Y a => e₁ (Y a)) Y) = Y := by
    intro Y
    funext a
    exact e₁.symm_apply_apply (Y a)
  have hψg : Measurable (ψ ∘ g) := hψ.comp hg
  calc ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m)
      = ∫⁻ Y, (ψ ∘ g) ((MeasurableEquiv.arrowProdEquivProdArrow T (Fin M → T) (Fin n) ∘
          fun Y a => e₁ (Y a)) Y) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) :=
        lintegral_congr fun Y => by simp only [Function.comp_apply (f := ψ), hgi]
    _ = _ := h₄.lintegral_comp hψg
    _ = _ := lintegral_prod _ hψg.aemeasurable
    _ = _ := by
      refine lintegral_congr fun c => lintegral_congr fun X => ?_
      simp only [Function.comp_apply, g]
      congr 1
      funext a
      exact piFinSuccAbove_symm_apply (c a) (X a)

end GlobalTheory.CompanionTheory.SW.TupFubini

namespace GlobalTheory.CompanionTheory.SW

theorem lintegral_tuple_moving_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ (n : ℕ) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ J), Measurable s → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ y, ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E, φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) ∂(coordW R b lam 1 (M + 1)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR d b lam hlam n s _ φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hact : ∀ h : HA R σ J, Measurable (actW R σ J h :
      (Fin n → Fin (M + 1) → R ⊗[F] E) → Fin n → Fin (M + 1) → R ⊗[F] E) := by
    intro h
    have := hBorel n (M + 1)
    have hc := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) J hJ R).2.2.2.2.2 n).1
    exact (hc.comp (Continuous.prodMk_right h)).measurable
  have key : ∀ y : Fin 1 → Fin (M + 1) → R ⊗[F] E,
      ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1)) =
      ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        φ (Fin.cons (y 0) (actW R σ J (s y) (fun a => Fin.cons (c a) (X a))))
        ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam) := by
    intro y
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 1) J hJ R hR n (coordW R b lam n (M + 1)) (hW n (M + 1)) (s y)
    have hf : Measurable fun Y : Fin n → Fin (M + 1) → R ⊗[F] E =>
        φ (Fin.cons (y 0) Y) := hφ.comp (TupFubini.measurable_cons_tail (y 0))
    calc ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y) ∂(coordW R b lam n (M + 1))
        = ∫⁻ Y, φ (Fin.cons (y 0) Y) ∂((coordW R b lam n (M + 1)).map (actW R σ J (s y))) := by
          rw [hinv]
      _ = ∫⁻ Y, φ (Fin.cons (y 0) (actW R σ J (s y) Y)) ∂(coordW R b lam n (M + 1)) :=
          lintegral_map hf (hact (s y))
      _ = _ := TupFubini.lintegral_tuple_first_coord (coordK R b lam) n M _ (hf.comp (hact (s y)))
  calc ∫⁻ X, φ X ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, ∫⁻ Y : Fin n → Fin (M + 1) → R ⊗[F] E, φ (Fin.cons (y 0) Y)
          ∂(coordW R b lam n (M + 1)) ∂(coordW R b lam 1 (M + 1)) :=
        TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 1) φ hφ
    _ = _ := lintegral_congr key

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.units_open_embedding_local_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding | exact GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding | (intros; apply GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramFib

theorem fibre_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ m', IsGramFib R σ J n μ ν m' → ∀ S, m S = m' S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm m' hm' S
  have hU := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have h1 : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have h2 : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [B, IsUnit]
    rw [h2]
    exact hU.isOpen_range.preimage h1
  have hUB : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' B := by
    ext X
    simp [B, hgf X]
  have hι : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m := by
    rw [← hUB]; exact hm
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' B) ν B m' := by
    rw [← hUB]; exact hm'
  by_cases hS : S ∈ B
  · exact (GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B B hBo hBo subset_rfl m' m h2 h1 S hS)
  · have a := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m h1).2.1 S hS
    have b := (GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic _ _ _ μ ν (gramR R σ J) g Subtype.val hι hgc hgf
      B hBo m' h2).2.1 S hS
    rw [a, b]

end GlobalTheory.CompanionTheory.SW.GramFib
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.hermitian_open_chart_diagonal_unipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, ∃ o : (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) → HermR R σ n, IsOpenEmbedding o ∧ ∀ d u, ∀ N : Matrix (Fin n) (Fin n) (R ⊗[F] E), (N = Matrix.of fun i j => if i = j then 1 else if h : i < j then u ⟨(i, j), h⟩ else 0) → (o (d, u) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) N * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * N := by
  first | exact @GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding | exact GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding | (intros; apply GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.gaussian_fourier_transform_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | exact GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gaussian_continuous_rapid_decay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay | exact GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay | (intros; apply GlobalTheory.CompanionTheory.SW.BB.gaussQ_continuous_rapidDecay <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_hermitian_diagonalization_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (S : HermR R σ n), IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (d : Fin n → Rˣ), IsUnit g.det ∧ (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * g := by
  first | exact @GlobalTheory.CompanionTheory.SW.hermR_unit_diagonalisable | exact GlobalTheory.CompanionTheory.SW.hermR_unit_diagonalisable | (intros; apply GlobalTheory.CompanionTheory.SW.hermR_unit_diagonalisable <;> assumption)
end
