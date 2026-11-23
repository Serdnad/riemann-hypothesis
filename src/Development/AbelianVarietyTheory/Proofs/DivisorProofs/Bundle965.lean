module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle333
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle496
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle936
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle937
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle938
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.partialZetaDenominatorExponent_le_of_integral : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  first | exact @GlobalTheory.DenomBound.cE_le_of_inZl | exact GlobalTheory.DenomBound.cE_le_of_inZl | (intros; apply GlobalTheory.DenomBound.cE_le_of_inZl <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_eq_of_exists {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (h : ∃ γ, IsNorm s δ γ) (f : GL (Fin n) F → ℂ) :
    shLift s f δ = f h.choose := by
  unfold shLift
  rw [dite_eq_left h]

theorem exists_virt_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  intro F F' _ _ _ _ s hp hs ι θ hθ k
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hcard : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := by
    exact IsGalois.card_aut_eq_finrank F F'
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    haveI : Fact (Module.finrank F F').Prime := ⟨hp⟩
    rw [zpowers_eq_top_of_prime_card hcard hs]; intro t; trivial
  have hlift1 : ∀ (m : ℕ) (δ : GL (Fin m) F'), shLift s (fun _ : GL (Fin m) F => (1 : ℂ)) δ = 1 := by
    intro m δ
    exact shLift_eq_of_exists s δ (GlobalTheory.T.every_element_is_norm F F' s hgen m δ) _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hZ : ∀ a : Fin n, ∃ Z ∈ Virt ℂ ℂ (GHat F F' n),
      (∀ δ, Z (inl δ) = hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n δ) ∧
      ∀ δ, Z (inl δ * inr s) = hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ := by
    intro a
    obtain ⟨Xa, hXa, h1, h2⟩ := ih a a.2
    obtain ⟨Z, hZv, hZe⟩ := GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL F F' a (n - a) n (by omega) Xa hXa
    refine ⟨Z, hZv, fun δ => ?_, fun δ => ?_⟩
    · have e := hZe 1 δ
      simp only [map_one, mul_one] at e
      have e2 : (fun d => Xa (inl d)) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a :=
        funext h1
      rw [e2] at e
      exact e
    · rw [hZe s δ]
      have e2 : (fun d => Xa (inl d * inr s)) = shLift s (psiG (rootSum (pullθ ι θ) k) a) := funext h2
      rw [e2]
  choose Z hZv hZ1 hZ2 using hZ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s
    (by rw [hcard]; exact hp) hs (fun x => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F')))
    (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F' θ hθ n k)
  refine ⟨A - ∑ a : Fin n, Z a, sub_mem hA (sum_mem fun a _ => hZv a), fun g => ?_, fun δ => ?_⟩
  · simp only [Pi.sub_apply, Finset.sum_apply, hA1, hZ1]
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F' _ n g]
    rw [Fin.sum_univ_eq_sum_range (fun a => hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n g) n]
    congr 1
    unfold chG
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [galAct_apply, ← Matrix.charpoly_map]
    congr 2
  · simp only [Pi.sub_apply, Finset.sum_apply, hA2, hZ2]
    have hex := GlobalTheory.T.every_element_is_norm F F' s hgen n δ
    rw [shLift_eq_of_exists s δ hex, GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n, ← shLift_eq_of_exists s δ hex (chG _ n),
      GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm F F' s hgen ι θ k n δ]
    rw [Fin.sum_univ_eq_sum_range (fun a => hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ) n]
    congr 1
    · unfold chG nrm
      rw [hcard]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have han : n = a + (n - a) := by have := Finset.mem_range.1 ha; omega
      rw [← shLift_eq_of_exists s δ hex (hc a (n - a) (psiG (rootSum (pullθ ι θ) k) a) (fun _ => 1) n),
        GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen a (n - a) n han _ _
          ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 a (fun _ => 1) (fun _ => 1)).2.2 _).1 (fun _ _ => rfl)]
      congr 1
      funext x
      exact (hlift1 _ x).symm

end GlobalTheory.Shin
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.adelicMatrixFamilyDegree_le_rank_mul_line_bound : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  first | exact @GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | exact GlobalTheory.Nef.deg_le_rank_mul_of_linesLE | (intros; apply GlobalTheory.Nef.deg_le_rank_mul_of_linesLE <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem ofReal_sq_sub_mul_le (x y z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (‖x - y‖ ^ 2 * ρ) ≤
      2 * ENNReal.ofReal (‖z - x‖ ^ 2 * ρ) + 2 * ENNReal.ofReal (‖z - y‖ ^ 2 * ρ) := by
  have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
    calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; ring
      _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
      _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
  have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (z - x), norm_nonneg (z - y),
      sq_nonneg (‖z - x‖ - ‖z - y‖)]
  have h3 : ‖x - y‖ ^ 2 * ρ ≤ 2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ) := by
    have := mul_le_mul_of_nonneg_right h2 hρ
    linarith
  calc ENNReal.ofReal (‖x - y‖ ^ 2 * ρ)
      ≤ ENNReal.ofReal (2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem exists_isSec_of_rapid_cauchy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  intro n Y _ _ _ _ _ ι La _ A C la t K F ht hcurv hK hF hcau hn1
  obtain ⟨f, hfc, hfm, hfn⟩ := GlobalTheory.T.geometric_series_sections_l2_limit n Y ι La A la F K hK hF hcau

  have hWsub : ∀ a, ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
    fun a => ball_subset_closedBall.trans (C.sub a)

  have hH : ∀ m a, ∃ u : V n → ℂ, DifferentiableOn ℂ u (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤ ENNReal.ofReal t⁻¹ * n1 C la (F m) := by
    intro m a
    obtain ⟨u, hu, hle⟩ := GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t
      (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w)) (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) ht
      ((A.smooth_ph la (C.idx a)).mono (hWsub a)) (((hF m).1 (C.idx a)).mono (hWsub a))
      (by
        intro v hv ξ
        have := hcurv a v hv ξ
        simp only [WeightedAtlas.leviAt] at this
        rwa [(A.chart (C.idx a)).right_inv (hWsub a hv)] at this)
    refine ⟨u, hu, hle.trans ?_⟩
    gcongr
    unfold n1
    exact Finset.single_le_sum (f := fun a => ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      ((∑ j, ‖wdb n j (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) (fun _ _ => bot_le) (Finset.mem_univ a)
  choose u hu hule using hH

  have hD : ∀ m a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) -
      f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
      ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
    intro m a
    have e := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (F m - f) measurableSet_ball (hWsub a)
      (by
        intro y hy _
        simp only [Pi.sub_apply]
        rw [(hF m).2 _ _ _ (A.mem_pick y) hy, hfc _ _ _ (A.mem_pick y) hy]
        ring)
      (((((hF m).1 (C.idx a)).continuousOn.aemeasurable (A.chart (C.idx a)).open_target.measurableSet).sub
        (hfm (C.idx a))).mono_measure (Measure.restrict_mono (hWsub a) le_rfl))
    refine le_trans (le_of_eq e.symm) ?_
    exact (setLIntegral_le_lintegral _ _).trans (hfn m)
  have hT : Tendsto (fun m : ℕ => 2 * ENNReal.ofReal (4 * K / 4 ^ m) +
      2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (4 * K / 4 ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have h2 : Tendsto (fun m => ENNReal.ofReal t⁻¹ * n1 C la (F m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hn1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofNat_ne_top))

  have hG : ∀ a, ∃ g : V n → ℂ, DifferentiableOn ℂ g (ball (C.c a) (C.r a)) ∧
      g =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm := by
    intro a
    have hρ : ContinuousOn (fun v => Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        (ball (C.c a) (C.r a)) :=
      Real.continuous_exp.comp_continuousOn
        (((A.smooth_ph la (C.idx a)).continuousOn.mono (hWsub a)).neg)
    refine GlobalTheory.T.exists_differentiableOn_ae_eq_of_weighted_L2_limit n (ball (C.c a) (C.r a)) _ (fun m => u m a)
      (f (C.idx a) ∘ (A.chart (C.idx a)).symm) isOpen_ball hρ (fun v _ => Real.exp_pos _)
      (fun m => hu m a) ((hfm (C.idx a)).mono_measure (Measure.restrict_mono (hWsub a) le_rfl)) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) ?_
    intro m
    have hY : AEMeasurable (fun v => 2 * ENNReal.ofReal
        (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        (volume.restrict (ball (C.c a) (C.r a))) := by
      refine AEMeasurable.const_mul ?_ _
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ hρ
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.norm ?_
      exact ((((hF m).1 (C.idx a)).continuousOn.mono (hWsub a))).sub (hu m a).continuousOn
    calc ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖(f (C.idx a) ∘ (A.chart (C.idx a)).symm) v - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        ≤ ∫⁻ v in ball (C.c a) (C.r a), (2 * ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) +
          2 * ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
          lintegral_mono (fun v => ofReal_sq_sub_mul_le _ _ _ _ (Real.exp_pos _).le)
      _ = 2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) +
          2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
          rw [lintegral_add_right' _ hY, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal (4 * K / 4 ^ m) + 2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m)) := by
          gcongr
          · exact hD m a
          · exact hule m a
  choose g hg hgae using hG
  obtain ⟨G, hGs, hGae⟩ := GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover n Y ι La A C (A.kap + la) f g hfc hg hgae
  refine ⟨G, hGs, ?_⟩
  have e : n0 A la (F 0 - G) = n0 A la (F 0 - f) := by
    unfold n0
    apply lintegral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [WeightedAtlas.nsq, Pi.sub_apply, hy]
  rw [e]
  simpa using hfn 0

end GlobalTheory.OTY
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem hormander_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨K', hK'0, hK'⟩ := GlobalTheory.T.dbar_energy_glued_section_le n Y ι La A C
  refine ⟨max (C.m : ℝ) K', le_max_of_le_right hK'0, ?_⟩
  intro la t ht hcurv F0 hF0
  have hball : ∀ a : Fin C.m, ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - F v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal t⁻¹ * ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hsub : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    refine GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w))
      (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) ht ((A.smooth_ph la (C.idx a)).mono hsub)
      ((hF0.1 (C.idx a)).mono hsub) ?_
    intro v hv ξ
    have h := hcurv a v hv ξ
    unfold WeightedAtlas.leviAt at h
    rwa [(A.chart (C.idx a)).right_inv (hsub hv)] at h
  choose u hu hE using hball
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hE a)
  rw [← Finset.mul_sum] at hsum
  have hK : ENNReal.ofReal (max (C.m : ℝ) K' / t) =
      ENNReal.ofReal (max (C.m : ℝ) K') * ENNReal.ofReal t⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_max_of_le_right hK'0)]
  refine ⟨glue C la u, GlobalTheory.T.isSSec_glueSectionByPartition_of_holo n Y ι La A C la u hu, ?_, ?_⟩
  · have hm : (C.m : ℝ≥0∞) ≤ ENNReal.ofReal (max (C.m : ℝ) K') := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc n0 A la (F0 - glue C la u) ≤ _ := GlobalTheory.T.n0_sub_glue_le_card_mul_sum_lintegral n Y ι La A C la F0 u hF0 hu
      _ ≤ (C.m : ℝ≥0∞) * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr
      _ = _ := by rw [hK, mul_assoc]
  · calc n1 C la (glue C la u) ≤ _ := hK' la F0 u hF0 hu
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by
        gcongr; exact le_max_right _ _
      _ = _ := by rw [hK, mul_assoc]

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.RingCont.main
  | exact GlobalTheory.EtC.RingCont.main
  | (intros; apply GlobalTheory.EtC.RingCont.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M → ∃ τ : M.Sec, SameDiv σ τ := by
  first | exact @GlobalTheory.LogPair.exists_sameDiv_of_lbIso | exact GlobalTheory.LogPair.exists_sameDiv_of_lbIso | (intros; apply GlobalTheory.LogPair.exists_sameDiv_of_lbIso <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem isEtCoord_res : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (U W : X.Opens) (h : W ≤ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord f W (fun a => resG X h (t a)) := by
  intro R _ X f U W h d t hU hW ht
  have h1 : (resG X h).Etale := GlobalTheory.TopForm.etale_resG hU hW h
  have h2 : ((resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t)).Etale :=
    RingHom.Etale.stableUnderComposition _ _ ht h1
  have h3 : MvPolynomial.eval₂Hom (cstOn f W) (fun a => resG X h (t a)) =
      (resG X h).comp (MvPolynomial.eval₂Hom (cstOn f U) t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have hc : cstOn f W = (resG X h).comp (cstOn f U) := by
        unfold cstOn resG
        rw [← CommRingCat.hom_comp]
        have e := Scheme.Hom.appLE_map f (U := ⊤) (V := U) (by simp) (homOfLE h).op
        exact congrArg (fun g => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g).hom) e.symm
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hc]
    · intro i
      simp
  unfold IsEtCoord
  rw [h3]
  exact h2

end GlobalTheory.LogPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_pull_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R) (e : Y ⟶ X) [IsOpenImmersion e] (U : X.Opens) (W : Y.Opens) (h : W ≤ e ⁻¹ᵁ U) (d : ℕ) (t : Fin d → Γ(X, U)), IsAffineOpen U → IsAffineOpen W → IsEtCoord f U t → IsEtCoord (e ≫ f) W (fun a => (e.appLE U W h).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_openImmersion | exact GlobalTheory.LogPair.isEtCoord_openImmersion | (intros; apply GlobalTheory.LogPair.isEtCoord_openImmersion <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  intro A _ g L u hA U k h
  choose! W hWU hzW hreg using h
  let K : Type := {z // z ∈ pre u.ex U}
  let V : K → A.left.Opens := fun z => W z.1
  have hVU : ∀ i : K, V i ≤ U := fun i => hWU i.1 i.2
  have hb : ∀ i : K, ∃ b : Γ(A.left, V i), ∀ z ∈ pre u.ex (V i), k z = val u.ex (V i) b z := fun i => hreg i.1 i.2
  choose b hb using hb
  have hcov : U ≤ ⨆ i, V i := GlobalTheory.T.le_iSup_of_uniformisationParameters_cover A g L u hA U K V fun z hz => ⟨⟨z, hz⟩, hzW z hz⟩
  have hcompat : TopCat.Presheaf.IsCompatible A.left.sheaf.1 V b := by
    intro i j
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA (V i ⊓ V j) _ fun z hz => ?_
    have hz' := (GlobalTheory.top_le_preimage_inf (u.ex z).left (V i) (V j)).1 hz
    have e1 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLELeft (V i) (V j)).op (b i) hz
    have e2 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLERight (V i) (V j)).op (b j) hz
    refine (GlobalTheory.valAt'_sub (u.ex z).left (V i ⊓ V j) _ _).trans ?_
    rw [sub_eq_zero]
    exact e1.trans (((hb i z hz'.1).symm.trans (hb j z hz'.2)).trans e2.symm)
  obtain ⟨s, hs, -⟩ := A.left.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcov b hcompat
  refine ⟨s, fun z hz => ?_⟩
  have h1 := hb ⟨z, hz⟩ z (hzW z hz)
  have h2 := GlobalTheory.valAt'_map (u.ex z).left (homOfLE (hVU ⟨z, hz⟩)).op s (hzW z hz)
  rw [h1, ← hs ⟨z, hz⟩]
  exact h2

end GlobalTheory.CechPer
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

theorem _root_.GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s)) (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (exact GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_equiv_globalOneForms_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → Flat s' → Surjective s' → ∃ e : R' ⊗[R] GlobForm s ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | exact GlobalTheory.AbCoh.exists_equiv_globForm_baseChange | (intros; apply GlobalTheory.AbCoh.exists_equiv_globForm_baseChange <;> assumption)
end
