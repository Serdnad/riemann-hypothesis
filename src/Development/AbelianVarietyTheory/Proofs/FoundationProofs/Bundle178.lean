module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open scoped TensorProduct

namespace GlobalTheory.TwistedSelmerCompare

theorem natCast_mem_maximalIdeal {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _
  have h2 := IsLocalRing.eq_maximalIdeal h
  have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h2, Ideal.mem_comap, map_natCast] at h3
  exact h3

theorem padicInt_hom_ext {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (f g : ℤ_[l] →+* O) : f = g := by
  ext z
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  have : f z - g z = (f c - g c) * (l : O) ^ n := by
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl n)

theorem crystallineCocycle_transport_conjugation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K₁ K₂ L₁ L₂ : FinExt l)
    (θ : ↥(GK K₂) →* ↥(GK K₁)) (hθ : Continuous θ) (σ : GQ l)
    (hσ : ∀ g : ↥(GK K₂), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹) {k : ℕ}
    (M₁ : ↥(GK K₁) →* Matrix (Fin k) (Fin k) ↥L₁.1) (M₂ : ↥(GK K₂) →* Matrix (Fin k) (Fin k) ↥L₂.1)
    (p : ↥L₁.1 →ₗ[ℚ_[l]] ↥L₂.1)
    (hp : ∀ g (v : Fin k → ↥L₁.1), (fun j => p ((M₁ (θ g)).mulVec v j)) = (M₂ g).mulVec fun j => p (v j))
    (c : ↥(GK K₁) → Fin k → ↥L₁.1) (hc : c ∈ finiteCocycles (P.PD K₁) (matRep M₁)) :
    (fun g j => p (c (θ g) j)) ∈ finiteCocycles (P.PD K₂) (matRep M₂) := by
  obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hc
  have := L₁.2
  have hpc : Continuous p := p.continuous_of_finiteDimensional
  let q : (Fin k → ↥L₁.1) →ₗ[ℚ_[l]] (Fin k → ↥L₂.1) := LinearMap.compLeft p (Fin k)
  have hq : ∀ g v, q (matRep M₁ (θ g) v) = matRep M₂ g (q v) := fun g v => hp g v
  let T := TensorProduct.map q (P.actQ σ).toLinearMap
  have hT : ∀ g y, T (actVB (P.PD K₁) (matRep M₁) (θ g) y) = actVB (P.PD K₂) (matRep M₂) g (T y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b =>
      change q (matRep M₁ (θ g) v) ⊗ₜ[ℚ_[l]] P.actQ σ ((P.PD K₁).actB (θ g) b) =
        matRep M₂ g (q v) ⊗ₜ[ℚ_[l]] (P.PD K₂).actB g (P.actQ σ b)
      rw [hq, P.PD_actB, P.PD_actB, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul]
      congr 3
      rw [hσ g]; group
  refine ⟨⟨continuous_pi fun j => hpc.comp ((continuous_apply j).comp (hc1.comp hθ)), fun g h => ?_⟩,
    T x, fun g => ?_⟩
  · change q (c (θ (g * h))) = q (c (θ g)) + matRep M₂ g (q (c (θ h)))
    rw [map_mul, hc2, map_add (f := _), hq]
  · rw [← hT, ← map_sub, ← hx]
    change q (c (θ g)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = q (c (θ g)) ⊗ₜ[ℚ_[l]] P.actQ σ 1
    rw [map_one]

section Coef

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem toLLK_bijective (B : LocBridge l E Ω Gw O) : Function.Bijective (Br.toLLK B) := by
  refine ⟨(Br.toLLK B).injective, fun x => ?_⟩
  have := B.LL.2
  have : Algebra.IsAlgebraic ℤ_[l] ↥B.LL.1 := IsFractionRing.comap_isAlgebraic_iff.2
    (inferInstance : Algebra.IsAlgebraic ℚ_[l] ↥B.LL.1)
  obtain ⟨d, hd, hx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
  obtain ⟨n, hn⟩ := B.eO.surjective ⟨d • x, hx⟩
  refine ⟨algebraMap O _ n / algebraMap O _ (algebraMap ℤ_[l] O d), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, hn, B.eO_alg, ← IsScalarTower.algebraMap_apply, div_eq_iff]
  · change d • x = _
    rw [Algebra.smul_def, mul_comm]
  · rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥B.LL.1]
    simpa using hd

theorem exists_coefMap (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (f : O₀ →+* O)
    (hf : Function.Injective f) (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ φ : ↥B₀.LL.1 →ₐ[ℚ_[l]] ↥B.LL.1,
      ∀ x : FractionRing O₀, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := by
  let e := RingEquiv.ofBijective _ (toLLK_bijective B₀)
  let φ : ↥B₀.LL.1 →+* ↥B.LL.1 := (Br.toLLK B).comp ((GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf).comp e.symm.toRingHom)
  have hφ : ∀ x, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := fun x =>
    congrArg (fun y => Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf y)) (e.symm_apply_apply x)
  have hc : φ.comp (algebraMap ℚ_[l] ↥B₀.LL.1) = algebraMap ℚ_[l] ↥B.LL.1 := by
    refine IsFractionRing.ringHom_ext (A := ℤ_[l]) fun z => ?_
    have h := hφ (algebraMap O₀ _ (algebraMap ℤ_[l] O₀ z))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, hz, Br.toLLK_alg, Br.toLLK_alg, B.eO_alg, B₀.eO_alg,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  exact ⟨{ φ with commutes' := fun q => DFunLike.congr_fun hc q }, hφ⟩

end Coef

end GlobalTheory.TwistedSelmerCompare

end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (GlobalTheory.T.unitStrip_integral_eq_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedThetaQProduct_modularS_transform : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → (∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) → cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  first | exact @GlobalTheory.Sieg.cth_modular_S | exact GlobalTheory.Sieg.cth_modular_S | (intros; apply GlobalTheory.Sieg.cth_modular_S <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem mem_Fix_iff {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) (x : L) : x ∈ Fix L N ↔ ∀ h : G, h ∈ N → h • x = x :=
  ⟨fun hx h hh => hx ⟨h, hh⟩, fun hx m => hx m.1 m.2⟩

noncomputable instance quotFixAction {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] :
    MulSemiringAction (G ⧸ U) (Fix L U) :=
  inferInstanceAs (MulSemiringAction (G ⧸ U) (FixedPoints.subring L U))

theorem quot_smul_coe {L : Type} [Field L] {G : Type} [Group G]
    [MulSemiringAction G L] (U : Subgroup G) [U.Normal] (g : G) (x : Fix L U) :
    (((g : G ⧸ U) • x : Fix L U) : L) = g • (x : L) := rfl

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem almostSep_of_normal_finiteIndex : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ),
    p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L],
    (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ U : Subgroup G, U.Normal → U.FiniteIndex →
    (∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x) → AlmostSep v U := by
  intro L _ v p hp hp0 hp1 G _ _ hv ζ hζ hζG hroot U hU hUfin hfaith
  refine GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers L v G hv U hU hUfin ?_
  intro σ hσ
  let L' := ↥(Fix L U)
  let v' : Valuation L' ℝ≥0 := v.comap (Fix L U).subtype
  have hv'x : ∀ x : L', v' x = v (x : L) := fun x => rfl
  haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : FaithfulSMul (G ⧸ U) L' := by
    refine ⟨fun {q₁ q₂} h => ?_⟩
    induction q₁ using QuotientGroup.induction_on with | H g₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H g₂ => ?_
    rw [QuotientGroup.eq]
    by_contra hne
    obtain ⟨x, hx, hmov⟩ := hfaith _ hne
    apply hmov
    have h1 := congrArg Subtype.val (h ⟨x, hx⟩)
    rw [quot_smul_coe, quot_smul_coe] at h1
    rw [mul_smul, ← h1, ← mul_smul, inv_mul_cancel, one_smul]
  have hpcast : ((p : L') : L) = (p : L) := map_natCast (Fix L U).subtype p
  have hζU : ζ ∈ Fix L U := (mem_Fix_iff U ζ).2 fun h _ => hζG h
  let ζ' : L' := ⟨ζ, hζU⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := (Fix L U).subtype) Subtype.val_injective).1 hζ
  have hmain := GlobalTheory.T.almostPurity_moves_integers_of_ne_one L' v' p hp (by rw [hv'x, hpcast]; exact hp0)
    (by rw [hv'x, hpcast]; exact hp1) (G ⧸ U)
    (by
      intro q x
      induction q using QuotientGroup.induction_on with | H g => ?_
      rw [hv'x, hv'x, quot_smul_coe, hv])
    ζ' hζ'
    (by
      intro q
      induction q using QuotientGroup.induction_on with | H g => ?_
      exact Subtype.ext (by rw [quot_smul_coe]; exact hζG g))
    (by
      obtain ⟨θ, hθ, hθu⟩ := hroot
      refine ⟨θ, hθ, fun u hu => ?_⟩
      have hu' : (u : L) ∈ Fix L (⊤ : Subgroup G) := by
        refine (mem_Fix_iff _ _).2 fun g _ => ?_
        have := congrArg Subtype.val (((mem_Fix_iff _ u).1 hu) (g : G ⧸ U) trivial)
        rwa [quot_smul_coe] at this
      obtain ⟨w, hw, hwu⟩ := hθu _ hu'
      have hwU : w ∈ Fix L U := (mem_Fix_iff U w).2 fun h _ => (mem_Fix_iff _ w).1 hw h trivial
      refine ⟨⟨w, hwU⟩, ?_, ?_⟩
      · refine (mem_Fix_iff _ _).2 fun q _ => ?_
        induction q using QuotientGroup.induction_on with | H g => ?_
        exact Subtype.ext (by rw [quot_smul_coe]; exact (mem_Fix_iff _ w).1 hw g trivial)
      · rw [hv'x, hv'x]
        exact hwu)
    (σ : G ⧸ U) (by rwa [Ne, QuotientGroup.eq_one_iff])
  intro r hr
  obtain ⟨x, -, hx1, hxr⟩ := hmain r hr
  refine ⟨(x : L), x.2, hx1, ?_⟩
  rw [hv'x, AddSubgroupClass.coe_sub, quot_smul_coe] at hxr
  exact hxr

end GlobalTheory.AlmostEt
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ)
    (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N →
    QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) →
    QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) →
    IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s g N w f f' h h' hg hN hA hC hf hf' r
  obtain ⟨a, ha, haE⟩ := hA
  obtain ⟨c, hc, hc'⟩ := hC
  have hac : a = c := HasQ.coeff_unique hN ha hc
  subst hac
  choose b hb using fun n => RingHom.mem_range.mp (haE n)
  have ha' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    have e : (fun n => ε (b n)) = a := funext hb
    rw [e]; exact ha
  have hc2 : HasQ N (fun τ => DD τ ^ w * f' τ) (fun n => ε (s (b n))) := by
    have e : (fun n => ε (s (b n))) = fun n => g (a n) := funext fun n => by rw [← hg, hb]
    rw [e]; exact hc'
  obtain ⟨H, hH, hHk, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN ha'
  obtain ⟨H', hH', hHk', hH0'⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ (fun n => s (b n)) hN hc2
  obtain ⟨hD, hDe, hD0, -, hDZ⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, -, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω s 1 (fun _ => 1) one_pos rfl (fun _ _ => (one_mul 1).symm)
  have hΦc : ∀ x r, (Φ x).coeff r = s (x.coeff r) := fun x r => by simpa using hΦ x r
  have hpow : ∀ (u : ℍ → ℂ) (k : HahnSeries ℚ Ω), IsExp ε u k → ∀ m : ℕ,
      IsExp ε (fun τ => DD τ ^ m * u τ) (hD ^ m * k) := by
    intro u k hu m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      have hm := (hops _ _ _ _ hDe ih).2.2
      have e1 : (fun τ => DD τ ^ (m + 1) * u τ) = DD * fun τ => DD τ ^ m * u τ := by
        funext τ; simp only [Pi.mul_apply, pow_succ]; ring
      have e2 : hD ^ (m + 1) * k = hD * (hD ^ m * k) := by ring
      rw [e1, e2]; exact hm
  have e1 : hD ^ w * h = H := huniq _ _ _ (hpow f h hf w) hH
  have e2 : hD ^ w * h' = H' := huniq _ _ _ (hpow f' h' hf' w) hH'
  have hΦD : Φ hD = hD := by
    ext r; rw [hΦc]; obtain ⟨n, hn⟩ := hDZ r; rw [hn, map_intCast]
  have hΦH : Φ H = H' := by
    ext r; rw [hΦc]
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr; rw [hHk, hHk']
    · push_neg at hr; rw [hH0 r hr, hH0' r hr, map_zero]
  have key : hD ^ w * Φ h = hD ^ w * h' := by
    rw [e2, ← hΦH, ← e1, map_mul, map_pow, hΦD]
  have hne : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hh := mul_left_cancel₀ hne key
  rw [← hh, hΦc]

end GlobalTheory.FN
end
