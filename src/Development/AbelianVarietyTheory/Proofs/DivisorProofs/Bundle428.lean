module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle375
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle370
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

section

open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.RealWeil.SchrFamily

variable {l : Type} [Fintype l]

def pCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := pPart, map_add' := pPart_add, map_smul' := pPart_smul }

def qCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := qPart, map_add' := qPart_add, map_smul' := qPart_smul }

theorem rhoSch_eq (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by
  ext x
  rw [coe_rhoSch, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, rhoFun, phase_eq_eChar, sub_neg_eq_add]
  simp

theorem seminorm_rhoSch_sub_le (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ (Sch l)) (M₁ M₂ M₃ : ℕ), ∀ (w : l ⊕ l → ℝ) (g : Sch l),
      p (rhoSch w g - g) ≤ (‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2|) * (1 + ‖qPart w‖) ^ M₁ *
          (‖pPart w‖ * (1 + ‖pPart w‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart w‖ * (1 + ‖pPart w‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-pPart w) g with hT
  have hL : ‖innerSL ℝ (qPart w)‖ = ‖qPart w‖ := innerSL_apply_norm _ _
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2)) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  rw [rhoSch_eq]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [hL]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (pPart w) g
  gcongr
  linarith

theorem tendsto_rhoSch_zero (g : Sch l) : Tendsto (fun u => rhoSch u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (schwartzSeminormFamily ℂ _ ℂ i)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm i)
  have hpc : Tendsto (fun u : l ⊕ l → ℝ => pPart u) (𝓝 0) (𝓝 0) := by
    have := (pCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hqc : Tendsto (fun u : l ⊕ l → ℝ => qPart u) (𝓝 0) (𝓝 0) := by
    have := (qCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hpn : Tendsto (fun u : l ⊕ l → ℝ => ‖pPart u‖) (𝓝 0) (𝓝 0) := by simpa using hpc.norm
  have hqn : Tendsto (fun u : l ⊕ l → ℝ => ‖qPart u‖) (𝓝 0) (𝓝 0) := by simpa using hqc.norm
  have hk : Tendsto (fun u : l ⊕ l → ℝ => |⟪pPart u, qPart u⟫ / 2|) (𝓝 0) (𝓝 0) := by
    have := ((hpc.inner (𝕜 := ℝ) hqc).div_const 2).abs
    simpa using this
  have lim : Tendsto (fun u : l ⊕ l → ℝ => (‖qPart u‖ + |⟪pPart u, qPart u⟫ / 2|) * (1 + ‖qPart u‖) ^ M₁ *
          (‖pPart u‖ * (1 + ‖pPart u‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart u‖ * (1 + ‖pPart u‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hqn.add hk).mul ((hqn.const_add 1).pow M₁)).mul
      (((hpn.mul ((hpn.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((hpn.mul ((hpn.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (hb u g).trans_lt hu

theorem rhoSch_rhoSch (w₀ u : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w₀ (rhoSch u g) = Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) • rhoSch (w₀ + u) g := by
  ext x
  rw [coe_rhoSch, coe_rhoSch, rhoFun_rhoFun, SchwartzMap.smul_apply, coe_rhoSch]
  rfl

theorem continuous_rhoSch (g : Sch l) : Continuous fun w => rhoSch w g := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : (l ⊕ l → ℝ) → ℂ := fun u => Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) with hcdef
  have hs : Continuous fun u : l ⊕ l → ℝ => sympl w₀ u := by
    have e : (fun u : l ⊕ l → ℝ => sympl w₀ u) =
        fun u => ⟪pPart w₀, qCLM l u⟫ - ⟪qPart w₀, pCLM l u⟫ := rfl
    rw [e]
    exact (continuous_const.inner (qCLM l).continuous).sub (continuous_const.inner (pCLM l).continuous)
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • rhoSch w₀ (rhoSch u g)) (𝓝 0) (𝓝 ((c 0)⁻¹ • rhoSch w₀ g)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((rhoSch w₀).continuous.tendsto g).comp (tendsto_rhoSch_zero g))
  have hq0 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hp0 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hc0 : c 0 = 1 := by simp [hcdef, sympl, hq0, hp0]
  have e : ∀ u, (c u)⁻¹ • rhoSch w₀ (rhoSch u g) = rhoSch (w₀ + u) g := fun u => by
    rw [rhoSch_rhoSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp

theorem seminorm_rhoSch_le (g : Sch l) (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (rhoSch w g) ≤ C * (1 + ‖w‖) ^ N := by
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := EuclideanSpace ℝ l) (F := ℂ) with hpdef
  set c := ‖pCLM l‖ + ‖qCLM l‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := by positivity
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hpw : ‖pPart w‖ ≤ ‖pCLM l‖ * ‖w‖ := (pCLM l).le_opNorm w
  have hqw : ‖qPart w‖ ≤ ‖qCLM l‖ * ‖w‖ := (qCLM l).le_opNorm w
  have hpn := norm_nonneg (pCLM l)
  have hqn := norm_nonneg (qCLM l)
  have ha : 1 + ‖pPart w‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖qPart w‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖pPart w‖ ≤ X := by linarith
  have hb'' : ‖qPart w‖ ≤ X := by linarith
  have hk : ‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2| ≤ 2 * X ^ 2 := by
    have h1 : |⟪pPart w, qPart w⟫| ≤ ‖pPart w‖ * ‖qPart w‖ := abs_real_inner_le_norm _ _
    have h2 : ‖pPart w‖ * ‖qPart w‖ ≤ X * X := mul_le_mul ha' hb'' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := by
    simpa using map_add_le_add p (rhoSch w g - g) g
  calc p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring

theorem exists_continuous_schwartz_rhoFun : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n),
    Continuous G ∧ (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N :=
  fun _ f => ⟨fun w => rhoSch w f, continuous_rhoSch f, fun w => coe_rhoSch w f, seminorm_rhoSch_le f⟩

end GlobalTheory.RealWeil.SchrFamily
end
end

section

open NumberField IsDedekindDomain GlobalTheory.SUVol

theorem _root_.GlobalTheory.T.local_factor_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  first | exact @GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | exact GlobalTheory.SUVol.prod_le_locFactor_of_isPrime | (intros; apply GlobalTheory.SUVol.prod_le_locFactor_of_isPrime <;> assumption)
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.SUVol.DensChart

open scoped Pointwise

theorem mem_grpBall_iff_norm {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) {ε : ℝ}
    (hε : 0 < ε) (g : H) :
    g ∈ grpBall H ε ↔ ‖(fun τ i j => ((((g : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) i j) - (fun (_ : ι) i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j)‖ < ε := by
  rw [pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem tanBall_eq_ball {ι : Type} [Fintype ι] {r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tanBall ι r ε = Metric.ball 0 ε := by
  ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem density_at_one : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  intro ι _ r H _ μ W _ _ _ _ _ lam _ Q D h a ρ hD hQ0 hDi hon hh ha0 hat hρ hμ
  set f : W → (ι → Fin r → Fin r → ℂ) := fun w τ i j =>
    ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf
  set one : ι → Fin r → Fin r → ℂ := fun _ i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hone
  have hf0 : f 0 = one := by simp [hf, hone, hQ0]
  have hD' : HasStrictFDerivAt f D 0 := hD
  obtain ⟨K, -, hK⟩ := (D : W →ₗ[ℝ] (ι → Fin r → Fin r → ℂ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hDi)
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hnorm : ∀ w, ‖w‖ ≤ K' * ‖D w‖ := by
    intro w
    have h1 := hK.le_mul_dist w 0
    simp only [dist_zero_right, map_zero] at h1
    calc ‖w‖ ≤ K * ‖D w‖ := h1
      _ ≤ K' * ‖D w‖ := by gcongr; linarith
  have hcw : ∀ c : ℝ, 0 ≤ c → ∀ w, c / K' * ‖w‖ ≤ c * ‖D w‖ := by
    intro c hc w
    calc c / K' * ‖w‖ ≤ c / K' * (K' * ‖D w‖) := by gcongr; exact hnorm w
      _ = c * ‖D w‖ := by field_simp
  have approx : ∀ κ : ℝ, 0 < κ → ∃ δ > 0, ∀ w : W, ‖w‖ < δ → ‖f w - one - D w‖ ≤ κ * ‖w‖ := by
    intro κ hκ
    have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD'.hasFDerivAt).def hκ
    obtain ⟨δ, hδ, hh'⟩ := Metric.eventually_nhds_iff.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hh' (y := w) (by rwa [dist_zero_right])
    simpa [hf0] using this
  set V : ℝ → ℝ≥0∞ := fun ε => lam (D ⁻¹' Metric.ball 0 ε) with hVdef
  set S : ℝ → Set W := fun ε => D ⁻¹' Metric.ball 0 ε ∩ Metric.ball 0 ρ with hSdef
  set F : ℝ → ℝ≥0∞ := fun ε => μ (Q '' S ε) with hFdef
  have hV0 : ∀ ε : ℝ, 0 < ε → V ε ≠ 0 := fun ε hε =>
    (Metric.isOpen_ball.preimage D.continuous).measure_ne_zero lam ⟨0, by simp [hε]⟩
  have hVt : ∀ ε : ℝ, V ε ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := lam) (x := 0) (r := K' * ε)).ne
      (measure_mono fun w hw => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ ≤ K' * ε := by gcongr
  have hVhom : ∀ t ε : ℝ, 0 < t → 0 < ε → V (t * ε) = ENNReal.ofReal (t ^ Module.finrank ℝ W) * V ε := by
    intro t ε ht _
    have hs : D ⁻¹' Metric.ball 0 (t * ε) = t • (D ⁻¹' Metric.ball 0 ε) := by
      ext w
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
      simp only [Set.mem_preimage, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht]
      rw [inv_mul_lt_iff₀ ht]
    simp only [hVdef]
    rw [hs, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]
  have hSmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurableSet_ball.preimage D.measurable).inter measurableSet_ball
  have hSeq : ∀ ε : ℝ, ε < ρ / K' → S ε = D ⁻¹' Metric.ball 0 ε := by
    intro ε hε
    refine Set.inter_eq_left.2 fun w hw => ?_
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ < K' * (ρ / K') := by gcongr; linarith [norm_nonneg (D w)]
      _ = ρ := by field_simp
  have hFint : ∀ ε : ℝ, F ε = ∫⁻ w in S ε, h w ∂lam := fun ε =>
    hμ (S ε) (hSmeas ε) Set.inter_subset_right
  have hF : Tendsto (fun ε => F ε / V ε) (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨a', hb', ha'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (lt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : a' * V ε ≤ F ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc b < a' := hb'
        _ = a' * V ε / V ε := (ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)).symm
        _ ≤ F ε / V ε := ENNReal.div_le_div_right hle _
    · obtain ⟨a', ha', hb'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (gt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : F ε ≤ a' * V ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc F ε / V ε ≤ a' * V ε / V ε := ENNReal.div_le_div_right hle _
        _ = a' := ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)
        _ < b := hb'
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (t⁻¹ * ε) ≤ μ (grpBall H ε) ∧ μ (grpBall H ε) ≤ F (t * ε) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    obtain ⟨δ1, hδ1, H1⟩ := approx ((t - 1) / K') (div_pos (by linarith) hK'0)
    obtain ⟨δ2, hδ2, H2⟩ := approx ((1 - t⁻¹) / K') (div_pos (by linarith) hK'0)
    obtain ⟨ε0, hε0, hon0⟩ := hon (min ρ δ2) (lt_min hρ hδ2)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hε0 (lt_min (div_pos hδ1 hK'0) (div_pos hρ hK'0)))]
      with ε hε
    obtain ⟨hεp, hε1⟩ := hε
    simp only [lt_min_iff] at hε1
    obtain ⟨hεe, hεd, hερ⟩ := hε1
    constructor
    · refine measure_mono ?_
      rintro _ ⟨w, ⟨hw1, -⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff] at hw1
      rw [mem_grpBall_iff_norm H hεp]
      change ‖f w - one‖ < ε
      have hDw : ‖D w‖ < ε := by
        calc ‖D w‖ < t⁻¹ * ε := hw1
          _ < 1 * ε := by gcongr
          _ = ε := one_mul ε
      have hw : ‖w‖ < δ1 := by
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δ1 / K') := by gcongr; linarith
          _ = δ1 := by field_simp
      have e1 := H1 w hw
      have e2 := hcw (t - 1) (by linarith) w
      have e3 : ‖f w - one‖ ≤ ‖D w‖ + ‖f w - one - D w‖ := by
        calc ‖f w - one‖ = ‖D w + (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have e4 : t * ‖D w‖ < ε := by
        calc t * ‖D w‖ < t * (t⁻¹ * ε) := by gcongr
          _ = ε := by field_simp
      nlinarith
    · refine measure_mono fun g hg => ?_
      have hg0 : g ∈ grpBall H ε0 := fun τ i j => (hg τ i j).trans hεe
      obtain ⟨w, hw, rfl⟩ := hon0 g hg0
      rw [lt_min_iff] at hw
      rw [mem_grpBall_iff_norm H hεp] at hg
      change ‖f w - one‖ < ε at hg
      refine ⟨w, ⟨?_, mem_ball_zero_iff.2 hw.1⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have e1 := H2 w hw.2
      have e2 := hcw (1 - t⁻¹) (by linarith) w
      have e3 : ‖D w‖ ≤ ‖f w - one‖ + ‖f w - one - D w‖ := by
        calc ‖D w‖ = ‖(f w - one) - (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e4 : t⁻¹ * ‖D w‖ < ε := by linarith
      calc ‖D w‖ = t * (t⁻¹ * ‖D w‖) := by field_simp
        _ < t * ε := by gcongr
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze (F := F) (V := V)
    (A := fun ε => μ (grpBall H ε)) (n := Module.finrank ℝ W) hat hVhom hF hA
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  simp only [hVdef]
  rw [tanBall_eq_ball hε, Measure.map_apply D.measurable measurableSet_ball]

end GlobalTheory.SUVol.DensChart
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.schrodinger_product_euclidean_models_agree : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  first | exact @GlobalTheory.Proof.schrodinger_models_agree | exact GlobalTheory.Proof.schrodinger_models_agree | (intros; apply GlobalTheory.Proof.schrodinger_models_agree <;> assumption)
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.matrix_coeff_continuous_rapid_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_continuous_rapidDecay | exact GlobalTheory.matrixCoeff_continuous_rapidDecay | (intros; apply GlobalTheory.matrixCoeff_continuous_rapidDecay <;> assumption)
end

section


theorem _root_.GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (s : ℂ), ∃ (c : ℕ → A) (t : ℂ),
    c (m + 1) = 1 ∧ c m = ∑ i, E i i + t • (1 : A) ∧
      ∀ u : ℂ, Formalism.REAL.qdet E (u - s) = ∑ k ∈ Finset.range (m + 1 + 1), u ^ k • c k := by
  first | exact @GlobalTheory.CapelliNext.qdet_shift_next_coeff | exact GlobalTheory.CapelliNext.qdet_shift_next_coeff | (intros; apply GlobalTheory.CapelliNext.qdet_shift_next_coeff <;> assumption)
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.aeval_quantumDeterminant_intertwining : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  first | exact @GlobalTheory.capelli_intertw | exact GlobalTheory.capelli_intertw | (intros; apply GlobalTheory.capelli_intertw <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.RatFix

theorem ratfix_mul_eq (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E) (hBA : B₀ * A₀ = 1) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hG : ∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) :
    G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι
  have hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [hN]
  have hBN : B₀ * (1 - A₀ * B₀) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  ext i j
  have hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0 := by
    funext a
    have := congrFun (congrFun hBN a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have := congrFun (hG _ hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem ratfix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) :=
  fun F E _ _ _ R _ _ M A₀ B₀ hBA G hG => ratfix_mul_eq F E R M A₀ B₀ hBA G hG

end GlobalTheory.RatFix
end
