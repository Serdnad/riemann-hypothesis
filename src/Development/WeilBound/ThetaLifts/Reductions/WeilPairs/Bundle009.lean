module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ParsevalPolarization

open GlobalTheory.ThetaTransform

theorem polar_pt (z w : ℂ) : z * starRingEnd ℂ w =
    (((‖z + 1 * w‖ ^ 2 - ‖z + (-1) * w‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((‖z + Complex.I * w‖ ^ 2 - ‖z + (-Complex.I) * w‖ ^ 2 : ℝ) : ℂ)) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem polar {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (f₁ f₂ : X → ℂ) (g₁ g₂ : Y → ℂ) (c : ℝ)
    (hf : ∀ a : ℂ, Integrable (fun x => ‖f₁ x + a * f₂ x‖ ^ 2) μ)
    (hg : ∀ a : ℂ, Integrable (fun y => ‖g₁ y + a * g₂ y‖ ^ 2) ν)
    (h : ∀ a : ℂ, ∫ y, ‖g₁ y + a * g₂ y‖ ^ 2 ∂ν = c * ∫ x, ‖f₁ x + a * f₂ x‖ ^ 2 ∂μ) :
    ∫ y, g₁ y * starRingEnd ℂ (g₂ y) ∂ν = (c : ℂ) * ∫ x, f₁ x * starRingEnd ℂ (f₂ x) ∂μ := by
  have key : ∀ {Z : Type} [MeasurableSpace Z] (ρ : Measure Z) (k₁ k₂ : Z → ℂ),
      (∀ a : ℂ, Integrable (fun x => ‖k₁ x + a * k₂ x‖ ^ 2) ρ) →
      ∫ x, k₁ x * starRingEnd ℂ (k₂ x) ∂ρ =
        (((∫ x, ‖k₁ x + 1 * k₂ x‖ ^ 2 ∂ρ) - ∫ x, ‖k₁ x + (-1) * k₂ x‖ ^ 2 ∂ρ : ℝ) +
          Complex.I * (((∫ x, ‖k₁ x + Complex.I * k₂ x‖ ^ 2 ∂ρ) -
            ∫ x, ‖k₁ x + (-Complex.I) * k₂ x‖ ^ 2 ∂ρ : ℝ) : ℂ)) / 4 := by
    intro Z _ ρ k₁ k₂ hk
    simp_rw [polar_pt (k₁ _) (k₂ _)]
    rw [integral_div, integral_add, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (hk 1) (hk (-1)), integral_sub (hk Complex.I) (hk (-Complex.I))]
    · exact ((hk 1).sub (hk (-1))).ofReal
    · exact (((hk Complex.I).sub (hk (-Complex.I))).ofReal).const_mul _
  rw [key ν g₁ g₂ hg, key μ f₁ f₂ hf, h 1, h (-1), h Complex.I, h (-Complex.I)]
  push_cast
  ring

theorem thV_smul {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {N : ℕ}
    (a : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (a • Φ) = a • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext ξ; ring

theorem parseval_adelic_pair_fundamental : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E}, B.IsGood σ → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  letI mA : MeasurableSpace (Fin N → AF F) := borel _
  letI mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop

  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK, mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₁ hΦ₁) (GlobalTheory.SchwartzDecay.decay_smul a (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this

end PositivityTheory.ThKW.ParsevalPolarization

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

theorem circle_eq_one_of_pos {u : Circle} {t : ℝ} (ht : 0 < t) (h : (u : ℂ) = t) : u = 1 := by
  have h1 : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
  apply Circle.ext
  rw [h, h1, Circle.coe_one]
  simp

theorem mtF_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mtF σ J 1 = 1 := by
  unfold mtF; rw [map_one]; rfl

theorem suppAtF_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : AF F ⊗[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : SuppAtF σ e J 1 := by
  intro i j
  rw [mtF_one', sub_self, Matrix.zero_apply, mul_zero]

theorem isDetAtF_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : AF F ⊗[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : IsDetAtF σ e J 1 1 := by
  show ((1 : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = e * (mtF σ J 1).det + (1 - e)
  rw [mtF_one', Matrix.det_one, Units.val_one]; ring

theorem modu_pos {F : Type} [Field F] [NumberField F] (x : (AF F)ˣ) : 0 < ((adeleClass F).modu x : ℝ) := by
  have h : (adeleClass F).modu x * (adeleClass F).modu x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : (adeleClass F).modu x ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact lt_of_le_of_ne (NNReal.coe_nonneg _) (by exact_mod_cast h0.symm)

end GlobalTheory.SplitLagrF

open GlobalTheory.SplitLagrF in
theorem PositivityTheory.ThKW.lagrangian_integral_parseval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne e he t ht
  obtain ⟨h, hhC, hsupp, ⟨M, hM, hMy⟩, x, hx, hχx⟩ := exists_levi F E σ B hB nT JT hT e he t ht
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hcmp⟩ := exists_form F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨R, hR, hRk⟩ := hcmp M hM
  obtain ⟨r, hr, hsp⟩ := hωd.om_split e he 1 h (suppAtF_one σ e JS) hsupp 1 x (isDetAtF_one σ e JS) hx
  set m : ℝ := (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) with hm_def
  have hm : 0 < m := Real.rpow_pos_of_pos (modu_pos _) _
  have h1 := hsp ℓ hinv f hf
  have h2 : ℓ (ωd (1, h) f) = (R : ℂ) * ((α t : ℂ) * (m : ℂ)) * ℓ f := by
    refine hRk f (ωd (1, h) f) _ hf (hωd.om_pres _ f hf) (fun y _ => ?_)
    have hth : IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (aC F E nT * (M * y)) f) :=
      GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS (nT + nT) JS _ ξ₀ _ f hf
    have hh := hωd.om_heis 1 h (aC F E nT * (M * y)) f hf
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (aC F E nT * (M * y)) = aC F E nT * y := by
      unfold actOF
      rw [← hMy nS y, ← Matrix.mul_assoc, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, inv_one]
      simp only [mtF_one', Matrix.one_mul, Matrix.mul_one]
    unfold prof
    rw [← hact, ← hh]
    exact hlaw h t hhC _ hth
  have h3 : (R : ℂ) * ((α t : ℂ) * (m : ℂ)) = (r : ℂ) * (χS x : ℂ) := by
    have := h2.symm.trans h1
    simp only [splitFacOF, MonoidHom.one_apply, inv_one, one_mul] at this
    exact mul_right_cancel₀ hℓf this
  have hu : α t * (χS x)⁻¹ = 1 := by
    apply circle_eq_one_of_pos (t := r / (R * m)) (div_pos hr (mul_pos hR hm))
    have hx0 : ((χS x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [Circle.coe_mul, Circle.coe_inv]
    push_cast
    field_simp
    linear_combination h3
  rw [← hχx χS nS hωd.resS]
  exact mul_inv_eq_one.mp hu
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem psi_cancel [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (A C : AF F) (D : ℂ) :
    ψ (⅟2 * -A) * (ψ (C + ⅟2 * A) * D) = D * ψ C := by
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, show ⅟(2 : AF F) * -A + (C + ⅟2 * A) = C by ring]
  ring

theorem lam_formula {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y)
    (hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) := by
  classical
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  haveI hBor : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable E := GlobalTheory.ThetaParsevalInner.countable_numberField E
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : Countable (ratLF F E nS nT) := by
    refine Function.Surjective.countable
      (f := fun m : Fin nT → Fin nS → E => (⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of m),
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ratLF F E nS nT)) ?_
    rintro ⟨r, m, rfl⟩
    exact ⟨m, rfl⟩
  obtain ⟨Nn, hNn⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).2
    (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
  obtain ⟨h0, htop, -, -⟩ := hNn ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.mpr htop
  haveI := hν
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hstd.1
  refine ⟨((ν 𝓕).toReal : ℂ), ?_, fun Φ hΦ v => ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  set x : Fin N → AF F := α v with hx
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin N → F) → (Fin N → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin N → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : (Fin N → F) → WOF F E nS nT → ℂ, ch = fun ξ u => B.ψ (emb ξ ⬝ᵥ β u) := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have hch_norm : ∀ ξ u, ‖ch ξ u‖ = 1 := fun ξ u => by rw [hch]; exact hnorm _
  have hch_cont : ∀ ξ, Continuous (ch ξ) := fun ξ => by
    rw [hch]; exact hcont.comp (continuous_const.dotProduct hβc)

  have hint : ∀ u : WOF F E nS nT,
      heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)
        (dC (AF F ⊗[F] E) nT * u) = ∑' ξ, a ξ * ch ξ u := by
    intro u
    have h1 : e (dC (AF F ⊗[F] E) nT * u) = (0, β u) := by
      have := hCe u 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    have h2 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    simp only [heisOF, symplOHF, Function.comp_apply, he, h1, h2, hCe, GlobalTheory.ThetaOntoF.algebraMap_half]
    unfold thV GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    rw [← tsum_mul_left]
    congr 1
    funext ξ
    subst ha hch hemb
    simp only [symV, dotProduct_zero, zero_dotProduct, zero_sub]
    exact psi_cancel B.ψ _ _ _
  have hFint : ∀ ξ, Integrable (fun u => a ξ * ch ξ u) (ν.restrict 𝓕) := fun ξ =>
    (Integrable.of_bound (hch_cont _).aestronglyMeasurable 1 (ae_of_all _ fun u => (hch_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ, ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν = ‖a ξ‖ * ν.real 𝓕 := by
    intro ξ
    simp only [norm_mul, hch_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ => ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : Fin N → F, ∫ u in 𝓕, ch ζ u ∂ν = if ζ = 0 then (ν.real 𝓕 : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ u, ch 0 u = 1 := fun u => by simp [hch, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push Not at h; exact hζ (funext h)
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist ν (ratLF F E nS nT) h𝓕 (h := ch ζ) ?_
        (c := β.symm (Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0))) (a := B.ψ s0) ?_ hs0
      · intro r hr u
        obtain ⟨x₀, rfl⟩ := hr
        obtain ⟨η, hη⟩ := hr1 x₀
        have hr' : β ((incAF F E).toAddMonoidHom.mapMatrix x₀) = GlobalTheory.SWQ.rat η := hη
        simp only [hch, map_add (f := _), hr', dotProduct_add, AddChar.map_add_eq_mul]

        rw [show emb ζ ⬝ᵥ GlobalTheory.SWQ.rat η = algebraMap F (AF F) (ζ ⬝ᵥ η) by
        subst hemb; simp [dotProduct, map_sum, map_mul, GlobalTheory.SWQ.rat], htriv, one_mul]
      · intro u
        simp only [hch, map_add (f := _), LinearEquiv.apply_symm_apply, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [integral_const_mul, horth]
  rw [tsum_eq_single 0 (fun ξ hξ => by rw [if_neg hξ, mul_zero])]
  rw [if_pos rfl, ha, hemb]
  have hz : (fun i : Fin N => (0 : AF F)) + x = x := by funext i; simp
  simp only [Pi.zero_apply, map_zero]
  rw [hz, Measure.real]
  ring

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end
