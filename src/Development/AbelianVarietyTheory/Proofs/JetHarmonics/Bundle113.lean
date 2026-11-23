module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle073
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Function.L2Space
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem lastPos_L_of_setC {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {large₂ : SizeData₂ D} {X : WeightAlgebra.PJ D B P j}
    {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : WeightAlgebra.SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : wL.LastPos := by
  intro τ i hi1
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold WeightAlgebra.gapZ at h3
  rw [dite_eq_right hn] at h3
  have hTp : (0 : ℤ) < (WeightAlgebra.Tp D j T : ℤ) := by unfold WeightAlgebra.Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (WeightAlgebra.Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, _root_.one_mul]
    unfold WeightAlgebra.Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  rw [← h3] at h4
  exact_mod_cast h4

theorem rootDiscriminantDegreeRatio_le_rootDiscriminant_sq (D : D7) : rr0 D ≤ D.host.rdE ^ (2 : ℝ) := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := D.host.E)
  have e : D.host.rdE ^ (2 : ℝ) = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [e]
  unfold rr0
  exact div_le_self (by positivity) (by linarith)

theorem runNum_of_sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ), InR D j → ∀ (X : WeightAlgebra.PJ D B P j) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), WeightAlgebra.ParA large₂ H.CA → WeightAlgebra.SetC large₂ X H.CK H.C1 H.A1 ka wL wF Tn nP nW h0 → WeightAlgebra.H3 large₂ H C2 A2 CR 0 wL Tn → PageSupp D large₂ B C2 A2 nW S wL → 2 ≤ CR → RunNum D wL (WeightAlgebra.cc D large₂ C2 A2 CR wL) := by
  intro D large₂ B P j hj X H C2 A2 CR S ka wL wF Tn nP nW h0 hA hS h3 hP hCR
  have h1 := lastPos_L_of_setC hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hn, -, hL, -⟩ := hS
  have hw : wL.n = nW := hL.1
  obtain ⟨hP13, -, -, hr, hD⟩ := hP
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hf : 1 ≤ D.R.f := by
    have hmf : D.R.m ≤ D.R.f := D.R.m_le_f
    have hmpos := D.R.two_le_m
    omega
  have hm : 1 ≤ D.R.m := hj.1.trans hj.2
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hDR : (3 : ℝ) ≤ WeightAlgebra.DF wL := by exact_mod_cast hD
  have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * wL.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    rw [hw]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hP13
  have hq := modulus_pos_of_third_hypothesis h3
  have h31 := h3.1
  rw [Real.rpow_zero, _root_.one_mul] at h31
  have hs : (2 : ℝ) ≤ 2 * D.R.f * D.R.m := by nlinarith
  have hRR : D.host.rdE ^ (2 : ℝ) ≤ WeightFamilies.RRv D CR :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hCR
  have h4 : rr0 D ≤ WeightFamilies.RRv D CR := (rootDiscriminantDegreeRatio_le_rootDiscriminant_sq D).trans hRR
  have hqg : ∀ i, (WeightAlgebra.qq D : ℝ) ≤ D.host.g i := fun i => by
    have : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      exacts [min_le_left _ _, min_le_right _ _]
    exact_mod_cast this
  have r0 : 0 ≤ rr0 D := by unfold rr0; positivity
  generalize hsd : (2 * D.R.f * D.R.m : ℝ) = s at *
  have p0 : (1 : ℝ) ≤ s ^ 4 * wL.n + 2 * s ^ 3 := by
    have a : (0 : ℝ) ≤ s ^ 4 * wL.n := by positivity
    have b : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hR2 : s ^ 2 ≤ WeightFamilies.RRv D CR := by
    refine le_trans ?_ hRR
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith) hrd 2
  have hR1 : 1 ≤ WeightFamilies.RRv D CR := by nlinarith
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := p0.trans h5
  have hkey : s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ WeightAlgebra.qq D := by
    refine le_trans ?_ h31
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc s ^ 2 ≤ WeightFamilies.RRv D CR := hR2
      _ ≤ WeightFamilies.RRv D CR ^ 4 := le_self_pow₀ hR1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hP1)
  refine ⟨h1, ?_, fun i => ?_, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨?_, ?_⟩⟩
  · rw [hw]
    refine le_trans ?_ hn
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  · have a : 4 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have b : 4 * (WeightAlgebra.DF wL : ℝ) + 4 ≤ D.host.g i := by nlinarith [hqg i]
    exact_mod_cast b
  · rw [hsd]
    have a : Real.sqrt s ≤ s := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have b : (WeightAlgebra.DF wL : ℝ) * (2 * Real.sqrt s) ≤ (WeightAlgebra.DF wL : ℝ) * s * 2 := by nlinarith
    have c : (6 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) * s := by nlinarith
    have d := hqg i
    nlinarith
  · rw [hsd]
    have d := hqg i
    unfold WeightAlgebra.cc
    gcongr

end GlobalTheory.PtTie
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPairing

theorem integrable_inner_of_memLp {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫_ℂ) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem pairing : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π u μW μN μG νq om Bm BI β hR hRI hinj hT hS hB
    hiso hev I hI y hy a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmem : ∀ J, (∑ c, pr J c (tm R a w c)) ∈ (RI J).sm := by
    intro J
    refine (RI J).smSub.sum_mem (fun c _ => ?_)
    exact (hT.pr_sm J c).mem _ (R.smSub.smul_mem (a c) hw)
  have hae := (GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hR hS).1
  have hexp := GlobalTheory.T.tensor_bessel_transfer hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp om Bm BI β hR hRI hT hB.1 hB.2.1 hev a w hw
  have hpolI := GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI I) (RI I) Wp z π u μW μN μG νq (BI I) (hRI I) hS hI
  have h1 : ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y),
        Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq
      = ∫ x, ∑ J, β J * ⟪BI I ((RI I).σ (Matrix.of x) y),
        BI J ((RI J).σ (Matrix.of x) (∑ c, pr J c (tm R a w c)))⟫_ℂ ∂νq := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hexp _ hx, inner_sum]
    simp only [inner_smul_right]
  rw [h1, integral_finsetSum]
  · simp only [integral_const_mul]
    rw [Finset.sum_eq_single I]
    · rw [hpolI.2 _ (hmem I) y hy]
    · intro J _ hJ
      rcases hiso J with hJ' | hJ'
      · rw [GlobalTheory.T.isometric_bessel_compare hH k r ε (muI J) (muI I) (RI J) (RI I) Wp z π u μW μN μG νq (BI J) (BI I) (hRI J) (hRI I)
          (fun h => hJ (hinj h)) hS hJ' hI _ (hmem J) y hy, mul_zero]
      · rw [hJ', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ I) h
  · intro J _
    rcases hiso J with hJ' | hJ'
    · exact (integrable_inner_of_memLp (hpolI.1 y hy)
        ((GlobalTheory.T.isometric_bessel_memLp_and_integral_inner_eq hK k r ε (muI J) (RI J) Wp z π u μW μN μG νq (BI J) (hRI J) hS hJ').1 _ (hmem J))).const_mul _
    · simp only [hJ', zero_mul]
      exact integrable_zero _ _ _

end GlobalTheory.BesselPairing
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
open Formalism.REAL (qdet GlRel IsHW)

noncomputable section

namespace GlobalTheory.TensorDualStd

section General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k : ℕ}

def tensorOp (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 fun c => ∑ d, C c d • A (y d)
      map_add' := fun x y => by
        ext c
        simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by
        ext c
        simp [Finset.smul_sum, smul_smul, mul_comm] }

theorem tensorOp_apply (C : Matrix (Fin k) (Fin k) ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tensorOp C A y c = ∑ d, C c d • A (y d) := rfl

theorem tensorOp_one : tensorOp (1 : Matrix (Fin k) (Fin k) ℂ) (1 : V →L[ℂ] V) = 1 := by
  ext y c
  simp [tensorOp_apply, Matrix.one_apply]

theorem tensorOp_mul (C D : Matrix (Fin k) (Fin k) ℂ) (A B : V →L[ℂ] V) :
    tensorOp (C * D) (A.comp B) = (tensorOp C A).comp (tensorOp D B) := by
  ext y c

  simp only [tensorOp_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply, Finset.sum_smul, map_sum,
  map_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensorOp_norm {C : Matrix (Fin k) (Fin k) ℂ} (hC : ∀ d e, ∑ c, star (C c d) * C c e = if d = e then 1 else 0)
    {A : V →L[ℂ] V} (hA : ∀ v, ‖A v‖ = ‖v‖) (y : PiLp 2 (fun _ : Fin k => V)) : ‖tensorOp C A y‖ = ‖y‖ := by
  have h1 : inner ℂ (tensorOp C A y) (tensorOp C A y) = inner ℂ y y := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    calc ∑ c, inner ℂ (tensorOp C A y c) (tensorOp C A y c)
        = ∑ c, ∑ d, ∑ e, (star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [tensorOp_apply, sum_inner]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [inner_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [inner_smul_left, inner_smul_right, mul_assoc]
          rfl
      _ = ∑ d, ∑ e, (∑ c, star (C c d) * C c e) * inner ℂ (A (y d)) (A (y e)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ d, inner ℂ (y d) (y d) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          simp only [hC, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hA]
  rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]

theorem tensorOp_continuousOn {X : Type} [TopologicalSpace X] {s : Set X} {C : X → Matrix (Fin k) (Fin k) ℂ}
    {A : X → (V →L[ℂ] V)} (hC : ∀ c d, Continuous fun x => C x c d) (hA : ContinuousOn A s) :
    ContinuousOn (fun x => tensorOp (C x) (A x)) s := by
  rw [continuousOn_clm_apply]
  intro y
  have h : ContinuousOn (fun x => fun c => ∑ d, C x c d • A x (y d)) s := by
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    exact (hC c d).continuousOn.smul (hA.clm_apply continuousOn_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin k => V)).comp_continuousOn h

end General

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem herm_inv {h : Mx k r} (hh : h ∈ UWset k r z) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ v) (h *ᵥ w) = herm (Hpk k r) v w := by
  have e : hᴴ * Hpk k r * h = Hpk k r := hh.1
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]

theorem inWb_mulVec {h : Mx k r} (hh : h ∈ UWset k r z) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (h *ᵥ v) := by
  rw [Qx8.inWb_iff] at hv ⊢
  intro c
  have hc := hh.2.1 c
  constructor
  · rw [← Qx8.coord_e (h *ᵥ v) c, ← hc.2, herm_inv hh, Qx8.coord_e]
    exact (hv c).1
  · rw [← Qx8.coord_es (h *ᵥ v) c, ← hc.1, herm_inv hh, Qx8.coord_es]
    exact (hv c).2

theorem expand {B : Fin k → Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hB : IsFrameOf k r [z] B) {h : Mx k r} (hh : h ∈ UWset k r z) (d : Fin k) :
    h *ᵥ B d = ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) • B c := by
  refine HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB (inWb_mulVec hh (hB.1 d)) ?_
  have h1 := herm_inv hh (B d) z
  rw [hh.2.2] at h1
  rw [h1]
  exact hB.2.2 d z (by simp)

def dualMat (k r : ℕ) (B : Fin k → Fin (2 * r + k + 1) → ℂ) (h : Mx k r) : Matrix (Fin k) (Fin k) ℂ :=
  fun c d => star (herm (Hpk k r) (h *ᵥ B d) (B c))

end GlobalTheory.TensorDualStd


open GlobalTheory.TensorDualStd in
theorem GlobalTheory.tensor_dual_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hn hB
  refine ⟨fun h => tensorOp (dualMat k r B h) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, fun h _ y c => rfl⟩
  · have h1 : dualMat k r B 1 = 1 := by
      ext c d
      simp only [dualMat, Matrix.one_mulVec, hB.2.1, Matrix.one_apply]
      by_cases h : c = d
      · simp [h]
      · simp [h, Ne.symm h]
    simp only [h1, hπ.1.1]
    exact tensorOp_one
  · intro a ha b hb
    have h1 : dualMat k r B (a * b) = dualMat k r B a * dualMat k r B b := by
      ext c d
      simp only [dualMat, Matrix.mul_apply]
      rw [← Matrix.mulVec_mulVec]
      conv_lhs => rw [expand hz hT hB hb d, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
      rw [HermitianFormSums.herm_lsum, star_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [star_mul]
    simp only [h1, hπ.1.2 a ha b hb]
    exact tensorOp_mul _ _ _ _
  · refine tensorOp_continuousOn (fun c d => ?_) hπ.2
    unfold dualMat herm
    fun_prop
  · intro h hh v
    refine tensorOp_norm (fun d e => ?_) (hn h hh) v
    simp only [dualMat, star_star]
    rw [← HermitianFormSums.herm_comb hB, ← expand hz hT hB hh, ← expand hz hT hB hh, herm_inv hh, hB.2.1]

end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bigCellExpansion_of_besselFunction_zero : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ), 0 ≤ b → (AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] (TBB.bigPt P.r c))) → (∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → p.V f (TBB.bigPt P.r c) = 0) → Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁ := by
  intro P Wp Wq _ _ _ _ _ _ p f b C₃ a₁ hb hm hV
  have hV' : ∀ c : Fin (P.r + 1) → ℂ, p.V f (TBB.bigPt P.r c) = 0 := by
    intro c
    by_cases hc : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
    · exact hV c hc.1 hc.2
    · exact Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ hc
  refine ⟨ℤ, inferInstance, fun _ => f, 0, fun _ => 0, fun _ => 0, 0, (P.r + 1) * a₁, 0, rfl, le_rfl,
    fun _ _ => le_rfl, fun _ _ => le_rfl, rfl, rfl, ?_, le_rfl, ?_, fun _ => le_rfl, fun _ => hm⟩
  · intro μ _
    refine ⟨0, ?_, ?_, ?_⟩
    · funext c
      simp [hV' c]
    · simp
    · simp
  · rw [zero_pow (Nat.succ_ne_zero _)]
    exact Real.rpow_nonneg hb _

end GlobalTheory
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.FrameExpansion

open Matrix in
private lemma herm_mulVec_invariant {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w := by
  simp only [_root_.Formalism.QuantumDeterminants.herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hH]

open Matrix in
private lemma inWb_of_coords_eq_zero {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ a, v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0) (h2 : ∀ a, v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0) : _root_.Formalism.QuantumDeterminants.inWb k r v := by
  intro i hi
  rcases hi with hi | hi
  · have e : _root_.Formalism.QuantumDeterminants.eI k r ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← e]; exact h1 _
  · have e : _root_.Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i, by omega⟩ = i :=
      Fin.ext (show 2 * r + k - (2 * r + k - (i : ℕ)) = i by omega)
    rw [← e]; exact h2 _

open Matrix in
private lemma herm_bvec_esI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) = v (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_eI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0 :=
  hv _ (Or.inl (show (a : ℕ) < r from a.2))

open Matrix in
private lemma herm_bvec_eI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) = v (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_esI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0 :=
  hv _ (Or.inr (show r + k < 2 * r + k - (a : ℕ) by have := a.2; omega))


open Matrix in
theorem _root_.GlobalTheory.FrameExpansion.frame_expansion_uw_group :
    ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B → (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → w = ∑ c, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w (B c) • B c) ∧ ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → _root_.Formalism.QuantumDeterminants.inWb k r (h *ᵥ w) ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ w) z = 0) ∧ (∀ v w, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w) ∧ h⁻¹ ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 ∧ ∀ h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, h * h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  intro k r z B hz hT hB
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  refine ⟨fun w hw hwz => _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz, ?_⟩
  intro h hh
  have hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r := hh.1
  have hinv := herm_mulVec_invariant hH
  have hfz : h *ᵥ z = z := hh.2.2
  have hdet : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  refine ⟨fun w hw hwz => ⟨?_, ?_⟩, hinv, _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh, mul_nonsing_inv h hdet,
    nonsing_inv_mul h hdet, fun h' hh' => _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh hh'⟩
  · apply inWb_of_coords_eq_zero
    · intro a
      rw [← herm_bvec_esI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).2, hinv, herm_bvec_esI_jet_harmonics]
      exact coord_eI_eq_zero_of_inWb hw a
    · intro a
      rw [← herm_bvec_eI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).1, hinv, herm_bvec_eI_jet_harmonics]
      exact coord_esI_eq_zero_of_inWb hw a
  · rw [← hfz, hinv, hwz]

end GlobalTheory.FrameExpansion
end
