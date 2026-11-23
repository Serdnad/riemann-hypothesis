module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle100
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ComponentAttainedAtBaseFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Formalism.HermitianCurvature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle127
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle126
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle076
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle008
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finsetSum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]



theorem moment_step : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q MM hj hMM hind w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hNum, hFam, hG, hSide⟩ := id hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hνs : ∀ s, n1 (ν - Pi.single s 1) ≤ q0 := fun s => (lOneNorm_sub_single_one_le ν s).trans hν
  have hDS := hFam ν hν0
  have hDSs := fun s => hFam _ (hνs s)
  obtain ⟨hBe, hdg, -⟩ := hSide ν hν0
  have hBes := fun s => (hSide _ (hνs s)).1
  have hdgs := fun s => (hSide _ (hνs s)).2.1
  obtain ⟨hae, -, hmL, hml⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  by_cases hnz : NzOn (R ν) (l ν)
  swap
  · have : ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) *
        (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae (hae.mono fun x hx => ?_)
      have : l ν ((R ν).σ (Matrix.of x) w) = 0 := by
        by_contra hne
        exact hnz ⟨_, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hDS.2 w.2 hx, hne⟩
      simp [this]
    rw [this]
    exact bot_le
  obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH k r lam u b bv ga h q0 R hNum hFam ν).2 hν
  have hF := GlobalTheory.isFRep_dualM k r
  have hkap := fun s => GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν)
    (fun s => R (ν - Pi.single s 1)) io pr ep _ _ _ Wp z π u μW μN μG νq
    (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDSs hF hT hG
    (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).2) hBe hnz s
    (l (ν - Pi.single s 1)) (hBes s)
  choose κ hκ using fun s => (hkap s).1
  have hdual := fun s => (hkap s).2 (κ s) (hκ s)
  have hA : ∀ s, ‖(ep s : ℂ) * star (κ s)‖ ^ 2 * dg ν ≤
      (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * dg (ν - Pi.single s 1) := by
    intro s
    have h1 := GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s
      (κ s) (hκ s)
    rw [div_le_iff₀ (hdgs s)] at h1
    have h2 : ‖(ep s : ℂ) * star (κ s)‖ = ‖κ s‖ := by
      rcases hT.ep_sq s with h | h <;> simp [h]
    rwa [h2]
  obtain ⟨io', pr', hAlg, hpr⟩ := GlobalTheory.T.dual_tensor_cayley_weighted hK k r _ _ (R ν) hDS (fun s => R (ν - Pi.single s 1)) _ io pr ep Q
    (E ν) (fun s => E (ν - Pi.single s 1)) hDSs hT hQ (hE ν hν0).1 (fun s => (hE _ (hνs s)).1)
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν0).1
  have hMods : ∀ s, IsMod (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1))
      ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := fun s => by
    rw [← param_sub_single]
    exact GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ _ hNum.1 (hDSs s) Q _ hQ (hE _ (hνs s)).1
  have hShape := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.1
  have hlev := GlobalTheory.T.unitaryGl_projection_level_sum_sq_le _ _ _ (E ν) (fun s => (R (ν - Pi.single s 1)).smSub) (fun s => E (ν - Pi.single s 1))
    io' pr' _ k j bv w hMod hMods hAlg hShape hj hw
  have hexp : 2 * r + k + 1 + 1 - k = 2 * r + 2 := by omega
  rw [hexp] at hlev
  have hy : ∀ d s, ((pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub) : (R (ν - Pi.single s 1)).H) =
      ∑ c, pr s c (tm (R ν) (fun c => Q d c) w c) := by
    intro d s
    rw [hpr]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [Finset.sum_eq_single d]
    · simp [tm]
    · intro e _ he; simp [he]
    · simp
  have hA0 : 0 ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := mul_nonneg hG.2.1.le (by positivity)
  have key := lintegral_le_of_le_sum νq
    (fun x => lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2))
    (fun d s x => lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) *
      ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x)
        (pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub))‖ ^ 2))
    ((Fintype.card (Fin (2 * r + k + 1)) : ℝ) * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4))
    (fun d s => MM * ‖pr' s (Pi.single d w)‖ ^ 2) (by positivity)
    (fun d s x => mul_nonneg (by rw [pow_mul]; positivity) (mul_nonneg (hdgs s).le (by positivity)))
    (fun d s => ((hmL 0).pow_const _).mul
      ((((GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ _ Wp z π u μW μN μG νq (hDSs s) hG).2.2.2 _ (hBes s).1 _
        (pr' s (Pi.single d w)).2).norm.aemeasurable.pow_const _).const_mul _))
    (hae.mono fun x hx => by
      refine pointwise_le _ _ _ q
        (fun d => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (dualM (Matrix.of x) *ᵥ (fun c => Q d c))
          (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)))
        (fun s => (ep s : ℂ) * star (κ s)) _ _ _ hdg.le ?_ (fun d => ?_) hA
      · rw [GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal k r _ dualM _ Q 1 _ hF hQ.2 _ hx]
        exact (GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).2.1
      · simp only [hy]
        exact GlobalTheory.T.tensor_bessel_transfer hK k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1)) io pr _ _ _
          Wp _ (l ν) (fun s => l (ν - Pi.single s 1)) _ hDS hDSs hT.raw hBe.1.1 hBe.1.2.1 hdual _ w w.2 _ hx)
    (fun d s => by positivity)
    (fun d s => hind s _ (by rw [param_sub_single]; exact (hlev d).1 s))
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ d, ∑ s, MM * ‖pr' s (Pi.single d w)‖ ^ 2 ≤
      ∑ _d : Fin (2 * r + k + 1), MM * ((6 * bv) ^ (2 * (2 * r + 2)) * ‖w‖ ^ 2) := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hlev d).2 hMM
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.MomentStep
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private theorem exists_quotient_side_of_isType_lemma (k r : ℕ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (hk : 1 ≤ k)
    (z : Fin (2 * r + k + 1) → ℂ) (π : _root_.Formalism.FourierDecayAlt.B.Mat k r → W →L[ℂ] W) (u : ℕ → ℝ)
    (μW μN μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z)
    (hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW) (hN : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN)
    (hG : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.BranchingSupport.GG k r) μG) (hπ : _root_.Formalism.FourierDecayAlt.Q.IsType k r z π u) :
    ∃ ν, _root_.BranchingSupport.SideG k r z π u μW μN μG ν := by
  have hW' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.UWset k r z) μW :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).2 hW
  have hN' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.Formalism.QuantumDeterminants.Nset k r) μN :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1).2 hN
  have hG' : _root_.PI.BesselPeriodGGP.IsHaarOn (_root_.BranchingSupport.GG k r) μG :=
    ((_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1).2 hG
  obtain ⟨ν, hν⟩ :=
    _root_.GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW μN μG hz hT hW' hN' hG'
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.besType_hcParam k r W z π u hz hT hπ
  exact ⟨ν, hz, hT, ⟨u₀, hu₀⟩, hπ.2.2.2.2.2, hW', hN', hG', hν⟩


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.exists_sideG_both_of_isType : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type)
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq]
    (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z D.π u →
    _root_.Formalism.FourierDecayAlt.Q.IsType k r D.z' D.π' u' → ∃ νq νq',
      _root_.BranchingSupport.SideG k r D.z D.π u D.μW D.μN D.μG νq ∧
        _root_.BranchingSupport.SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D u u' hp hq
  obtain ⟨z, z', π, π', μG, μW, μN, μW', _, _, hk, hz, hz', hT, hT', _, _, _, _, _, _, hG, hW,
    hN, hW', _, _, _, _⟩ := D
  obtain ⟨ν, hν⟩ := exists_quotient_side_of_isType_lemma k r Wp hk z π u μW μN μG hz hT hW hN hG hp
  obtain ⟨ν', hν'⟩ :=
    exists_quotient_side_of_isType_lemma k r Wq hk z' π' u' μW' μN μG hz' hT' hW' hN hG hq
  exact ⟨ν, ν', hν, hν'⟩

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open scoped Matrix nonZeroDivisors
open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_marked_of_component : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  intro D V H Dw l Xo σ' g ty F hty r hr X k φ io hW hef hemb hform
  subst hr
  obtain ⟨hinj, hrange⟩ := hemb
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (gmW V rfl) (io x) (io y)) := by
    intro x y
    have h := trace_herm_gmW V rfl (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [hform, neg_neg, ← h]
    rfl
  obtain ⟨-, P, hP⟩ := (PeriodExists.typeFn_period_exist _ H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨f, h1, h2, h3, h4⟩ := familyUnif_lattice_genus _ H Dw l Xo σ' g ty F k P hP
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hW.2]
    exact neg_ne_zero.2 X.ξ0_ne
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    (-(-D.host.xi0)) hξ Dw.La (F.Di k).La (fun x y => Dw.EF x y) (fun x y => (F.Di k).EF x y) io hinj
    X.Λ φ hfg hsp X.Λ_fg X.Λ_span hEF
    (fun x y => by
      have := hef x y
      rw [hW.1, hW.2] at this
      exact this) f h1 h2 h3
  obtain ⟨u, hu, hug⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank X.Λ X.Λ_fg
    X.Λ_span).1
  refine ⟨u, ?_, fun a ha => ?_⟩
  · rw [(hlat u).1, hug]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    rw [AdLat.latOf, hg1]
    exact (hc v).symm
  · obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hgw⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    have hmem : ∀ z, z ∈ latGHat V u ↔ z ∈ AdLat.hat D.host.F (X.Λ : Set (Fin V.rank → D.host.E)) := by
      intro z
      rw [← SetLike.mem_coe, (hlat u).2, hug, hg1, SetLike.mem_coe]
    rw [hug]
    refine ⟨-(AdLat.fv D.host.F (φ e : Fin V.rank → D.host.E) + w),
      (hmem _).2 (neg_mem (add_mem ((hc _).2 (φ e).2) hw)), ?_⟩
    change AdLat.fv D.host.F (φ (F.t k a) : Fin V.rank → D.host.E) - gf.1 *ᵥ AdLat.fv D.host.F (io a) = _
    rw [hgw, he, map_add (f := _), map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, AdLat.cap_fv_add,
      AdLat.cap_fv_nsmul]
    exact comp_sub_eq _ _ _ _

end GlobalTheory.ShortMove
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.WigSh

def splitCasimirDual {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)) where
  toFun y := WithLp.toLp 2 (fun a => ∑ c, E a c (y c))
  map_add' x y := by
    ext a
    simp [Finset.sum_add_distrib]
  map_smul' t y := by
    ext a
    simp [Finset.smul_sum]

theorem splitCasimirDual_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (y : PiLp 2 (fun _ : Fin (n + 1) => V))
    (a : Fin (n + 1)) : splitCasimirDual E y a = ∑ c, E a c (y c) := rfl

theorem pieri_step_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ j, L j ≠ L l - 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l - 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wM L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hH hadj hEt hL
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_dualStandard V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  have h4 := GlobalTheory.T.reducedWignerCoefficient_lowering V n E Et (splitCasimirDual E) β L l hH hadj hEt
    (splitCasimirDual_apply E)
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.succ + 1) := by
    intro j
    have := hH.anti (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    constructor <;> simp only <;> omega
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hH).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hH.anti).2 hL
  have hz : (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := by
    have hm := (Module.End.eigenspace (splitCasimirDual E) (β + L l + (n : ℂ))).starProjection_apply_mem
      (PiLp.single 2 (Fin.last n) v)
    exact (Submodule.eq_bot_iff _).1 hbot _ hm
  rw [hz] at h5
  have h6 : ((wM L (fun j : Fin n => L j.succ + 1) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end
end

section

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory.WigSh

theorem exists_splitCasimir_std (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) :
    ∃ Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), ∀ y b, Om y b = ∑ c, E c b (y c) := by
  refine ⟨(WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun b => ∑ c, E c b ∘ₗ LinearMap.proj c) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (n + 1) → V)).toLinearMap, ?_⟩
  intro y b
  simp [LinearMap.sum_apply]

theorem pieri_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ j, L j ≠ L l + 1) → ∃ S : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), Stab Et S ∧ S ≠ ⊥ ∧ (∀ S' : Submodule ℂ (PiLp 2 (fun _ : Fin (n + 1) => V)), S' ≤ S → Stab Et S' → S' = ⊥ ∨ S' = S) ∧ S ≤ CapSp Et (shf β (Function.update L l (L l + 1))) ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → S.starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et β L l hyp hadj hEt hL
  obtain ⟨Om, hOm⟩ := exists_splitCasimir_std V n E
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.splitCasimir_eigenspace_irreducible_standard_alt V n E Et Om β L l hyp hadj hEt hOm
  have h4 := GlobalTheory.T.starProjection_splitCasimir_raising_last V n E Et Om β L l hyp hadj hEt hOm
  refine ⟨_, h1, ?_, h2, h3, h4⟩
  intro hbot
  have hbox : Box L (fun j : Fin n => L j.castSucc) := fun j =>
    ⟨hyp.anti (Fin.castSucc_lt_succ), le_rfl⟩
  have hne := (Formalism.FourierDecayAlt.P.branching_decomposition V n E β L hyp).1 _ hbox
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have h5 := h4 _ v hv
  have hw := (wigner_extreme_ne_zero n L l hyp.anti).1 hL
  have hmem := Submodule.starProjection_apply_mem (Module.End.eigenspace Om (β + L l + 0))
    (PiLp.single 2 (Fin.last n) v)
  have hz : (Module.End.eigenspace Om (β + L l + 0)).starProjection
      (PiLp.single 2 (Fin.last n) v) = 0 := (Submodule.eq_bot_iff _).1 hbot _ hmem
  rw [hz] at h5
  have h6 : ((wP L (fun j : Fin n => L j.castSucc) l : ℝ) : ℂ) • v = 0 := by
    rw [← h5]; rfl
  rcases smul_eq_zero.1 h6 with h | h
  · exact hw (by exact_mod_cast h)
  · exact hv0 h

end GlobalTheory.WigSh
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

theorem capelli_det_frame_indep : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B B' : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsFrameOf k r [z] B → IsFrameOf k r [z] B' → ∀ w : ℂ, qdet (EB π B) w = qdet (EB π B') w :=
  fun _ _ _ _ _ _ _ _ _ _ hz hT hπ hB hB' w => Formalism.FourierDecayAlt.P.QrCap.capChange hz hT hπ hB hB' w

end GlobalTheory
end
