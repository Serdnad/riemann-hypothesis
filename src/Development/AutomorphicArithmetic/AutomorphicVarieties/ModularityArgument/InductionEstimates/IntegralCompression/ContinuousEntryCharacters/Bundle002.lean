module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.InstCompactUG
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.KTypeExist
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.PeterWeyl
import GroundTheory.AutomorphicForms.RealIwasawaIntegration
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Compactness.Paracompact
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.minSwap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ τ₁ τ₂ : Submodule ℂ (LL μ),
        τ₁.map (θ.U : LL μ →ₗ[ℂ] LL μ) = τ₂ → ∀ s u n q, CE.MinAt μ τ₁ (s, u) n q → CE.MinAt μ τ₂ (s + 1, u) n q := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ τ₁ τ₂ hτ s u n q hmin
  obtain ⟨hnorm, -, hint⟩ := UpperTheory.ConvolutionTheory.Dp.twUnitary E 2 μ θ
  have htw := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw F E σ D CF CE hC μ θ hθ
  let L : LL μ →ₗᵢ[ℂ] LL μ := ⟨(θ.U : LL μ →ₗ[ℂ] LL μ), hnorm⟩
  have hL : ∀ v, L v = θ.U v := fun _ => rfl
  have key : ∀ n' q' v, θ.U (CE.Pi μ (s, u) n' q' v) = CE.Pi μ (s + 1, u) n' q' (θ.U v) := by
    intro n' q' v
    unfold Co.Pi
    rw [← hL, ← L.integral_comp_comm]
    congr 1
    funext m
    rw [map_smul, hL, hint, htw]
  subst hτ
  obtain ⟨⟨v, hv, hne⟩, hz⟩ := hmin
  refine ⟨⟨θ.U v, Submodule.mem_map_of_mem hv, fun h => hne ?_⟩, ?_⟩
  · rw [← key] at h
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  · rintro n' q' hn _ ⟨w, hw, rfl⟩
    have := key n' q' w
    rw [hz n' q' hn w hw, map_zero] at this
    exact this.symm
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem pw2 {f : U2 → ℂ} (hf : Continuous f)
    (h : ∀ (n : ℕ) (q : ℤ) (l r : U2), ∫ m, conj (KT.psi n q n m) * f (l * m * r) ∂μK = 0) : f = 0 := by
  have key : (fun k => conj (f k)) = 0 := by
    refine PW.eq_zero_of_forall_integral_coeff (Complex.continuous_conj.comp hf) fun n q l₁ l₂ => ?_
    have h1 := h n q l₁⁻¹ l₂⁻¹
    rw [← integral_mul_left_K _ l₁, ← integral_mul_right_K _ l₂] at h1
    have h2 := congrArg conj h1
    rw [← integral_conj, map_zero] at h2
    have hne : ((l₁ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q * (l₂ : Matrix (Fin 2) (Fin 2) ℂ).det ^ q) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (det_ne_zero_of_U2 _)) (zpow_ne_zero _ (det_ne_zero_of_U2 _))
    apply mul_left_cancel₀ hne
    rw [mul_zero, ← integral_const_mul, ← h2]
    congr 1; funext k
    have e : l₁⁻¹ * (l₁ * (k * l₂)) * l₂⁻¹ = k := by group
    rw [e, map_mul, starRingEnd_self_apply, ← mul_assoc l₁, KT.psi_mul_mul]
    ring
  funext k
  simpa using congrFun key k

private theorem int2 {f : U2 × U2 → ℂ} (hf : Continuous f) : Integrable f (μK.prod μK) :=
  hf.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

private theorem tor2 (n₁ : ℕ) (q₁ : ℤ) (n₂ : ℕ) (q₂ : ℤ) (ν : Fin (2 + 2) → ℤ) (b : U4 → ℂ)
    (hb : ∀ θ h, b (dg θ * h) = chi ν θ * b h) (hν : ν ≠ wt n₁ q₁ n₂ q₂) (g : U4) :
    ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g) ∂(μK.prod μK) = 0 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, hdg, -, hchi, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  by_contra hI
  refine hν (hchi _ _ fun θ => ?_)
  apply mul_right_cancel₀ hI
  conv_rhs => rw [← integral_mul_left_eq_self _ ((tC (θ 0) (θ 1), tC (θ 2) (θ 3)) : U2 × U2)]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1; funext p
  have hθ : θ = ![θ 0, θ 1, θ 2, θ 3] := by
    funext i; fin_cases i <;> rfl
  have e : bd (tC (θ 0) (θ 1) * p.1) (tC (θ 2) (θ 3) * p.2) * g = dg θ * (bd p.1 p.2 * g) := by
    rw [← hmul, ← hdg, ← hθ, mul_assoc]
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [e, hb, KT.psi_tC_mul n₁ q₁ le_rfl, KT.psi_tC_mul n₂ q₂ le_rfl, map_mul, map_mul]
  have hc : chi (wt n₁ q₁ n₂ q₂) θ * (conj (Complex.exp (Complex.I * ((((n₁ : ℝ) + q₁) * θ 0 + ((n₁ : ℝ) - n₁ + q₁) * θ 1 : ℝ) : ℂ))) *
      conj (Complex.exp (Complex.I * ((((n₂ : ℝ) + q₂) * θ 2 + ((n₂ : ℝ) - n₂ + q₂) * θ 3 : ℝ) : ℂ)))) = 1 := by
    rw [chi, ← Complex.exp_conj, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    have hs : ∑ i, ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ) =
        ((n₁ : ℂ) + q₁) * θ 0 + q₁ * θ 1 + ((n₂ : ℂ) + q₂) * θ 2 + q₂ * θ 3 := by
      have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n₁ q₁ n₂ q₂ i : ℤ) : ℂ) * (θ i : ℂ))
      refine this.trans ?_
      simp [wt]
    rw [hs]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  linear_combination (-(chi ν θ * conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) * b (bd p.1 p.2 * g))) * hc

private theorem wt_eq {n : ℕ} {q : ℤ} {n' : ℕ} {q' : ℤ} {n₁ : ℕ} {q₁ : ℤ} {n₂ : ℕ} {q₂ : ℤ} (h₁ : Above n q n₁ q₁)
    (h₂ : Above n' q' n₂ q₂) (h : ∑ i, wt n₁ q₁ n₂ q₂ i ^ 2 ≤ ∑ i, wt n q n' q' i ^ 2) : wt n₁ q₁ n₂ q₂ = wt n q n' q' := by
  have hs : ∀ (a : ℕ) (b : ℤ) (c : ℕ) (d : ℤ), ∑ i, wt a b c d i ^ 2 = (a + b) ^ 2 + b ^ 2 + (c + d) ^ 2 + d ^ 2 := by
    intro a b c d
    refine (Fin.sum_univ_four (fun i : Fin 4 => wt a b c d i ^ 2)).trans ?_
    simp [wt]
  rw [hs, hs] at h
  obtain ⟨a1, a2⟩ := h₁
  obtain ⟨b1, b2⟩ := h₂
  have a1' : (n : ℤ) ≤ n₁ := by exact_mod_cast a1
  have b1' : (n' : ℤ) ≤ n₂ := by exact_mod_cast b1
  have hn : (0 : ℤ) ≤ n := by positivity
  have hn' : (0 : ℤ) ≤ n' := by positivity
  have e : ∀ a b : ℤ, 2 * ((a + b) ^ 2 + b ^ 2) = (a + 2 * b) ^ 2 + a ^ 2 := by intros; ring
  have e1 := e n₁ q₁
  have e2 := e n₂ q₂
  have e3 := e n q
  have e4 := e n' q'
  rw [a2] at e1
  rw [b2] at e2
  have s1 : (n : ℤ) ^ 2 ≤ (n₁ : ℤ) ^ 2 := by gcongr
  have s2 : (n' : ℤ) ^ 2 ≤ (n₂ : ℤ) ^ 2 := by gcongr
  have t1 : (n₁ : ℤ) = n := (pow_left_inj₀ (by omega) hn two_ne_zero).1 (by linarith)
  have t2 : (n₂ : ℤ) = n' := (pow_left_inj₀ (by omega) hn' two_ne_zero).1 (by linarith)
  have u1 : q₁ = q := by omega
  have u2 : q₂ = q' := by omega
  simp only [wt, t1, t2, u1, u2]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefInj :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ →
      LAbove (fun m => bd m 1) n q Φ → LAbove (fun m => bd 1 m) n' q' Φ → (∀ a b, Φ (bd a b) = 0) → Φ = 0 := by
  intro μ ψ n q n' q' hμ _ hψ Φ hΦ hfix hL hR h0
  obtain ⟨-, hmul, hone, -, hcont, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha0, hb0, hν0, htor, hgood, hgood'⟩ := hψ.exp
  haveI := hμ.prob
  haveI : μ.IsMulLeftInvariant := ⟨fun k => (hμ.left k).map_eq⟩
  have int4 : ∀ f : U4 → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  set c : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ with hcdef
  have hrep : ∀ g, Φ g = ∫ k, c * ψ (k⁻¹ * g) * Φ k ∂μ := by
    intro g
    rw [← integral_mul_left_eq_self _ g, ← hfix g]
    congr 1; funext k
    have e : (g * k)⁻¹ * g = k⁻¹ := by group
    rw [e, hψ.star, eOf]
  have hsum : ∀ h x, Φ (h * x) = ∑ j, (∫ k, c * a j (k⁻¹ * h) * Φ k ∂μ) * b j x := by
    intro h x
    rw [hrep]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum]
    · congr 1; funext k
      rw [← mul_assoc, hexp, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro j _
      have := (hc j).1
      exact int4 _ (by fun_prop)
  have hp := fun m r => KT.continuous_conj_psi m r m
  have hbd : ∀ l l' : U2, Continuous fun p : U2 × U2 => bd (l * p.1) (l' * p.2) := fun l l' =>
    hcont.comp (f := fun p : U2 × U2 => (l * p.1, l' * p.2)) (by fun_prop)
  have hint : ∀ n₁ q₁ n₂ q₂ l l' g, Integrable (fun p : U2 × U2 => conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g)) (μK.prod μK) := fun n₁ q₁ n₂ q₂ l l' g =>
    int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
      (hΦ.comp ((hbd l l').mul continuous_const)))
  have main : ∀ n₁ q₁ n₂ q₂ l l' g, ∫ p : U2 × U2, conj (KT.psi n₁ q₁ n₁ p.1) * conj (KT.psi n₂ q₂ n₂ p.2) *
      Φ (bd (l * p.1) (l' * p.2) * g) ∂(μK.prod μK) = 0 := by
    intro n₁ q₁ n₂ q₂ l l' g
    by_cases h₁ : Above n q n₁ q₁
    · by_cases h₂ : Above n' q' n₂ q₂
      · simp_rw [← hmul l l', mul_assoc (bd l l'), hsum (bd l l'), Finset.mul_sum]
        rw [integral_finsetSum]
        · refine Finset.sum_eq_zero fun j _ => ?_
          simp_rw [mul_left_comm _ (∫ k, c * a j (k⁻¹ * bd l l') * Φ k ∂μ)]
          rw [integral_const_mul]
          by_cases hj : j = j₀
          · rw [hj, ha0, ← hrep, h0, zero_mul]
          · rw [tor2 n₁ q₁ n₂ q₂ (ν j) (b j) (fun θ h => (htor j θ h).2.2), mul_zero]
            intro hν
            have h3 := hgood j
            simp only [hν] at h3
            exact hgood' j hj (hν.trans (wt_eq h₁ h₂ h3))
        · intro j _
          exact int2 ((((hp _ _).comp continuous_fst).mul ((hp _ _).comp continuous_snd)).mul
            (continuous_const.mul ((hc j).2.comp (hcont.mul continuous_const))))
      · rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' g)]
        refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
        have h3 := hR n₂ q₂ h₂ l' (bd (l * x) 1 * g)
        simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
        simp only [mul_assoc (conj (KT.psi n₁ q₁ n₁ x))]
        rw [integral_const_mul, h3, mul_zero]
    · rw [integral_prod_symm _ (hint n₁ q₁ n₂ q₂ l l' g)]
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
      have h3 := hL n₁ q₁ h₁ l (bd 1 (l' * x) * g)
      simp only [← mul_assoc, hmul, one_mul, mul_one] at h3
      simp only [mul_comm _ (conj (KT.psi n₂ q₂ n₂ x)), mul_assoc (conj (KT.psi n₂ q₂ n₂ x))]
      rw [integral_const_mul, h3, mul_zero]
  have step : ∀ n₂ q₂ l' g, (fun x => ∫ y, conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g) ∂μK) = 0 := by
    intro n₂ q₂ l' g
    refine pw2 ?_ fun n₁ q₁ l r => ?_
    · have h3 := continuous_parametric_integral_of_continuous (μ := μK)
        (f := fun x y : U2 => conj (KT.psi n₂ q₂ n₂ y) * Φ (bd x (l' * y) * g))
        (((hp _ _).comp continuous_snd).mul (hΦ.comp ((by simpa using hbd 1 l' : Continuous fun p : U2 × U2 => bd p.1 (l' * p.2)).mul
          continuous_const))) isCompact_univ
      simpa only [Measure.restrict_univ] using h3
    · have h3 := main n₁ q₁ n₂ q₂ l l' (bd r 1 * g)
      rw [integral_prod _ (hint n₁ q₁ n₂ q₂ l l' _)] at h3
      rw [← h3]
      congr 1; funext x
      rw [← integral_const_mul]
      congr 1; funext y
      simp only [← mul_assoc, hmul, mul_one]
  funext g
  have fin : (fun y => Φ (bd 1 y * g)) = 0 := by
    refine pw2 (hΦ.comp ((hcont.comp (f := fun y : U2 => ((1 : U2), y)) (by fun_prop)).mul continuous_const)) fun n₂ q₂ l r => ?_
    have h3 := congrFun (step n₂ q₂ l (bd 1 r * g)) 1
    simpa only [← mul_assoc, hmul, mul_one, Pi.zero_apply] using h3
  simpa [hone] using congrFun fin 1
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem sum_fin_four_expand {M : Type} [AddCommMonoid M] (f : Fin (2 + 2) → M) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private theorem eb_dg (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  u4.2.2.2.2.2.2.2.1 θ

private theorem eb_chi_single (j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) :
    chi (Pi.single j 1) θ = Complex.exp (Complex.I * θ j) := by
  unfold chi
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

private theorem eb_chi_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (-ν) θ = conj (chi ν θ) := by
  unfold chi
  rw [← Complex.exp_conj]
  congr 1

  simp [map_sum]

private theorem eb_right (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (h * dg θ) = chi (Pi.single j 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, mul_diagonal, mul_comm]

private theorem eb_left (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (dg θ * h) = chi (Pi.single i 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, diagonal_mul]

private theorem eb_mul (π : Equiv.Perm (Fin (2 + 2))) (i j : Fin (2 + 2)) (h k : U4) :
    en i j (h * k) = ∑ s, en i (π s) h * en (π s) j k := by
  unfold en
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  exact (Equiv.sum_comp π fun s => (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i s * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) s j).symm

private theorem eb_cont (i j : Fin (2 + 2)) : Continuous (en i j) :=
  (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_elem i j

private theorem eb_pair (j : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) : ∑ i, (Pi.single j 1 : Fin (2 + 2) → ℤ) i * f i = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem eb_pairπ (π : Equiv.Perm (Fin (2 + 2))) (s : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) :
    ∑ i, (Pi.single (π s) 1 : Fin (2 + 2) → ℤ) (π i) * f i = f s := by
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (π.injective.ne hb)]
  · simp

private theorem eb_top (z : Fin (2 + 2) → ℤ) (hz : Antitone z) (s t : Fin (2 + 2)) (hst : s ≠ t) : z s + z t ≤ z 0 + z 1 := by
  have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
  have h1 : ∀ u : Fin (2 + 2), u ≠ 0 → (1 : Fin (2 + 2)) ≤ u := by decide
  by_cases hs : s = 0
  · have ht : t ≠ 0 := fun h => hst (hs.trans h.symm)
    have := hz (h0 s)
    have := hz (h1 t ht)
    omega
  · have := hz (h0 t)
    have := hz (h1 s hs)
    omega

private theorem eb_one (π : Equiv.Perm (Fin (2 + 2))) : OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 0, fun s => en (π 0) (π s), fun s => en (π s) (π 0), fun s => Pi.single (π s) 1,
    fun s => ⟨eb_cont _ _, eb_cont _ _⟩, fun h k => eb_mul π _ _ h k, rfl, rfl, rfl,
    fun s θ h => ⟨eb_right _ _ _ _, eb_left _ _ _ _, eb_left _ _ _ _⟩, fun s w y hy => ?_, fun s hs => ?_⟩
  · rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · beta_reduce
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ)]
    revert s
    decide

private theorem eb_three (π : Equiv.Perm (Fin (2 + 2))) : OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 3, fun s k => conj (en (π 3) (π s) k), fun s k => conj (en (π s) (π 3) k),
    fun s => -Pi.single (π s) 1,
    fun s => ⟨Complex.continuous_conj.comp (eb_cont _ _), Complex.continuous_conj.comp (eb_cont _ _)⟩, fun h k => ?_, rfl, rfl, rfl,
    fun s θ h => ?_, fun s w y hy => ?_, fun s hs => ?_⟩

  · simp only [eb_mul π, map_sum, map_mul]
  · simp only [eb_right, eb_left, eb_chi_neg, map_mul, and_self]
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), u ≤ (3 : Fin (2 + 2)) := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 3 fun i => -(i : ℤ)]
    revert s
    decide

private def ebS : Fin 6 → Fin (2 + 2) := ![0, 0, 0, 1, 1, 2]

private def ebT : Fin 6 → Fin (2 + 2) := ![1, 2, 3, 2, 3, 3]

private theorem eb_two (π : Equiv.Perm (Fin (2 + 2))) :
    OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k)
      (Pi.single (π 0) 1 + Pi.single (π 1) 1) := by
  refine ⟨Fin 6, inferInstance, 0,
    fun p k => en (π 0) (π (ebS p)) k * en (π 1) (π (ebT p)) k - en (π 0) (π (ebT p)) k * en (π 1) (π (ebS p)) k,
    fun p k => en (π (ebS p)) (π 0) k * en (π (ebT p)) (π 1) k - en (π (ebS p)) (π 1) k * en (π (ebT p)) (π 0) k,
    fun p => Pi.single (π (ebS p)) 1 + Pi.single (π (ebT p)) 1,
    fun p => ⟨((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _)),
      ((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _))⟩, fun h k => ?_, rfl, rfl, rfl,
    fun p θ h => ?_, fun p w y hy => ?_, fun p hp => ?_⟩
  · simp only [eb_mul π, sum_fin_four_expand, Fin.sum_univ_six, ebS, ebT, Matrix.cons_val]
    ring
  · simp only [eb_right, eb_left, eb_chi_add]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pair (π (ebS p)) fun i => y (w i), eb_pair (π (ebT p)) fun i => y (w i), eb_pair, eb_pair]
    have hne : ∀ p, ebS p ≠ ebT p := by decide
    simpa using eb_top _ hy (π.symm (w (π (ebS p)))) (π.symm (w (π (ebT p))))
      (π.symm.injective.ne (w.injective.ne (π.injective.ne (hne p))))
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pairπ π (ebS p) fun i => -(i : ℤ), eb_pairπ π (ebT p) fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ),
      eb_pairπ π 1 fun i => -(i : ℤ)]
    revert p
    decide

private theorem eb_det_dg (δ : ℤ) (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ = chi (fun _ => δ) θ := by
  unfold chi
  rw [eb_dg, det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  ring

private theorem eb_four (π : Equiv.Perm (Fin (2 + 2))) (δ : ℤ) :
    OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  have hc : Continuous fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ :=
    (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_det.zpow₀ δ fun k =>
      Or.inl (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  have hm : ∀ h k : U4, ((h * k : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ =
      (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ := fun h k => by
    rw [Submonoid.coe_mul, det_mul, mul_zpow]
  refine ⟨Unit, inferInstance, (), fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ,
    fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ _ => δ, fun _ => ⟨hc, hc⟩, fun h k => ?_, rfl, rfl, rfl,
    fun _ θ h => ?_, fun _ w y _ => ?_, fun _ hs => absurd rfl hs⟩
  · simp only [hm, Finset.univ_unique, Finset.sum_singleton]
  · simp only [hm, eb_det_dg, and_self, and_true]
    exact mul_comm _ _
  · exact (Equiv.sum_comp w fun i => δ * y i).le

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expBasic :
    ∀ π : Equiv.Perm (Fin (2 + 2)), OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) ∧
      OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k) (Pi.single (π 0) 1 + Pi.single (π 1) 1) ∧
      OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) ∧ ∀ δ : ℤ, OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  intro π
  exact ⟨eb_one π, eb_two π, eb_three π, eb_four π⟩
end
