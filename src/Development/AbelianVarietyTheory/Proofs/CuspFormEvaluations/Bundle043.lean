module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle032
public import Formalism.LocalRingCardinality.Bundle006
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameReadingLeadingMinorProductExtremal
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbert
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetTypesOfBoundedBases
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunParametersAtRecord

theorem lower_real (R P d a r q : ℝ) (hR : 0 ≤ R) (hd : 1 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (h1 : 90 * (a + 1) ≤ P) (h2 : r ≤ P) (hq : R ^ 4 * P ^ 3 * d ^ 2 ≤ q) :
    R ^ 4 * (90 * (a + d)) * d * r ≤ q := by
  have hP : 1 ≤ P := by linarith
  have e1 : 90 * (a + d) ≤ P * d := by nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ d), mul_le_mul_of_nonneg_left hd ha]
  have e2 : r ≤ P ^ 2 := by nlinarith
  refine le_trans ?_ hq
  have hd0 : 0 ≤ d := by linarith
  have hP0 : 0 ≤ P := by linarith
  calc R ^ 4 * (90 * (a + d)) * d * r ≤ R ^ 4 * (P * d) * d * P ^ 2 := by gcongr
    _ = R ^ 4 * P ^ 3 * d ^ 2 := by ring

theorem run_at_record : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  intro D B P j X K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp ht hPg hSu
  obtain ⟨hA, hS, h3, -, -⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcol, -, hL, -, -, -, -, -, -, h40, -, -, -, hd⟩ := hS
  obtain ⟨hq1, -, -, -, -, hq6⟩ := h3
  rw [Real.rpow_zero, one_mul] at hq1
  obtain ⟨h13, -, hf2, hr8, hDF⟩ := hSu
  have hn : wL.n = nW := hL.1
  have hC1 : H.C1 = C2 := ht.1
  rw [hC1] at hd
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hA2 : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hf := hostSize_f D
  have hrd := hostSize_rd D
  have h16 := EtaleWeightGaps.sixteen_le_rdE_of_parA hA
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  have hf8 := D.eight_le_f
  have hm2 := D.R.two_le_m
  have hRR : WeightFamilies.RRv D CR = I2.RR (E := D.host.E) := by
    rw [hCR]
    unfold WeightFamilies.RRv I2.RR
    rw [hrd]
    exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hRR0 : 0 ≤ I2.RR (E := D.host.E) := by
    unfold I2.RR
    rw [hrd]
    positivity
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have h12 : WeightAlgebra.sizeConstantAtParamsWeight D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    refine le_trans hd.2.2.2.2.2.2.2.2.1 ?_
    unfold WeightFamilies.PPv
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hd.1])
    change zBase large₂ ^ 4 ≤ _
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by push_cast; linarith)
  have h90 : 90 * ((D.R.f : ℝ) * D.R.r + 1) ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h12
  have hf8' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have hr8' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast hr8
  have hDF' : (3 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrP : (D.R.r : ℝ) ≤ WeightFamilies.PPv D large₂ C2 A2 := by nlinarith
  have hq2 : (2 : ℝ) ≤ (qq D : ℝ) := by
    have : (0 : ℝ) ≤ ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) := by positivity
    linarith
  have hq2' : 2 ≤ qq D := by exact_mod_cast hq2
  have hg0 : 2 ≤ D.host.g 0 := le_trans hq2' (min_le_left _ _)
  have hg1 : 2 ≤ D.host.g 1 := le_trans hq2' (min_le_right _ _)
  have hqg : qq D ≤ D.host.g 0 * D.host.g 1 :=
    le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have hqg' : (qq D : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hqg
  have hds : (I2.dstar (E := D.host.E) D.R.m : ℝ) = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by
    unfold I2.dstar
    rw [hf]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, by omega⟩
  · have key := GlobalTheory.RunParametersOfLower.runOK_of_le D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) D.R.m (by omega)
      (by rw [hf]; nlinarith) (by omega) (by rw [hf]; exact_mod_cast hm4) (by rw [hf, hrd]; exact hf2)
      (by rw [hrd]; exact h16)
      (by
        rw [hf]
        rw [hRR] at hq1
        exact lower_real _ _ _ _ _ _ hRR0 (by linarith) (by positivity) (by positivity) h90 hrP (hq1.trans hqg'))
    rw [hf] at key
    exact key
  · unfold cc
    rw [hRR, hds, hn]
    have a1 : 16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h13
    have a0 : 0 ≤ 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 := by positivity
    have a2 : 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := by linarith
    have hP0 : 0 ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans a0 a2
    have a3 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      le_mul_of_one_le_right hP0 (one_le_pow₀ (by linarith))
    refine div_le_div₀ (by positivity) ?_ (by linarith) hqg'
    rw [mul_comm _ (I2.RR (E := D.host.E)), mul_assoc (I2.RR (E := D.host.E))]
    exact mul_le_mul_of_nonneg_left (a2.trans a3) hRR0
  · unfold p14
    rw [hds, hn]
    have g0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
    have g1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
    have g4 : (4 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith
    have b1 : Real.log Real.pi ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_le_four])
    have b0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := Real.log_nonneg (by linarith)
    have hW : (1 : ℝ) ≤ nW := by exact_mod_cast (by omega : 1 ≤ nW)
    have b2 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * nW :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hW
    have b3 := le_mul_of_one_le_left b0 b2
    have e1 : 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) = 4 * D.R.f * D.R.m := by ring
    have e2 : 2 * (D.R.f : ℝ) * (D.R.m : ℝ) / 2 = D.R.f * D.R.m := by ring
    rw [e1, e2]
    linarith

end GlobalTheory.RunParametersAtRecord
end

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

theorem _root_.GlobalTheory.T.frameReading_leadingMinorProduct_extremal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ ε : ℤˣ, cof Dw pl c.F n (pG (Dw := Dw) c a n) = ((ε : ℤ) : c.F) • (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) := by
  first | exact @GlobalTheory.FrameReadHw.cof_pG | exact GlobalTheory.FrameReadHw.cof_pG | (intros; apply GlobalTheory.FrameReadHw.cof_pG <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem complexConj_rt_eq_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  set u := φ (H.rt : E) with hu
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have him' : u.re * u.im = 0 := by linarith
  have hu0 : u.re = 0 := by
    rcases mul_eq_zero.1 him' with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg u.re]
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply Complex.ext
  all_goals simp
  all_goals (rw [← hu]; linarith)

theorem halfIntegralGenerator_trace_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  apply RingOfIntegers.coe_injective
  have h1 := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h1
  have h2 := congrArg (IsCMField.complexConj E) h1
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h2
  have hr : IsCMField.complexConj E (algebraMap (𝓞 E) E H.rt) = -(algebraMap (𝓞 E) E H.rt) :=
    complexConj_rt_eq_neg H
  have hb : algebraMap (𝓞 E) E (H.bar H.w0) = IsCMField.complexConj E (algebraMap (𝓞 E) E H.w0) :=
    H.bar_eq _
  rw [map_add (f := _), map_one]
  linear_combination (h1 + h2) / 2 + hb + hr / 2

theorem univ_finset_fin_two : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide

theorem chi_sum_two {M : Type} [AddCommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, f I = f ⟨∅⟩ + f ⟨{0}⟩ + f ⟨{1}⟩ + f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.sum_comp, univ_finset_fin_two,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, add_assoc]

theorem chi_prod_two {M : Type} [CommMonoid M] (f : ULift.{0} (Finset (Fin 2)) → M) :
    ∏ I, f I = f ⟨∅⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨{0, 1}⟩ := by
  rw [← (Equiv.ulift (α := Finset (Fin 2))).symm.prod_comp, univ_finset_fin_two,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp only [Equiv.ulift_symm_apply, _root_.mul_assoc]

theorem chi_eq_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 ∧ Φ.χ a = Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ a ha
  obtain ⟨⟨wP, hP⟩, hrd⟩ := GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ
  have hlat : ∀ b ∈ Φ.lat, tyAct ty H.w0 b ∈ Φ.lat := by
    intro b hb
    have := Xo.univ.t.act.hom H.w0
    rw [← Φ.e_ker, Φ.lin, (Φ.e_ker b).2 hb, MonObj.one_comp]
  have hw := hlat a ha
  have htr : ∀ w : Fin g → ℂ, tyAct ty H.w0 w + tyAct ty (H.bar H.w0) w = w := by
    intro w
    have h1 : (H.w0 : E) + ((H.bar H.w0 : 𝓞 E) : E) = 1 := by
      exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) (halfIntegralGenerator_trace_eq_one H)
    funext k
    simp only [tyAct, Pi.add_apply, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [← add_mul, ← map_add (f := _), h1, map_one, _root_.one_mul]
  let Λ : (Fin 1 ⊕ ULift.{0} (Finset (Fin 2))) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    Sum.elim (fun _ => LinearMap.id) (fun I => (psumL 2 g I).comp (LinearMap.pi ![LinearMap.id, tyAct ty H.w0]))
  have hΛ : ∀ k z, Λ k z = Sum.elim (fun _ => z) (fun I => psumL 2 g I ![z, tyAct ty H.w0 z]) k := by
    intro k z
    rcases k with k | I
    · rfl
    · simp only [Λ, Sum.elim_inr, LinearMap.comp_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
  have hT := GlobalTheory.T.abelianHolomorphicFrame_reading_const_of_forms_cancel _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr _ _ _ _ wP hP.1 g
    (fun z => (Φ.e z).left) Λ Φ.lat Φ.hol
    (fun z k => by rw [hΛ]; exact (hrd wP hP z).1 k) Φ.span
    (fun gm hgm => ⟨fun z => by simp only [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one], fun k => by
      rw [hΛ]
      rcases k with k | I
      · exact hgm
      · show psumL 2 g I ![gm, tyAct ty H.w0 gm] ∈ Φ.lat
        simp only [psumL, LinearMap.sum_apply, LinearMap.proj_apply]
        refine AddSubgroup.sum_mem _ fun i _ => ?_
        fin_cases i
        · exact hgm
        · exact hlat gm hgm⟩)
    (fun z w => by
      rw [Fintype.sum_sum_type, Fin.sum_univ_one, chi_sum_two]
      simp [Λ, psumL, cε]
      have hz := semichar_herm_add_left Φ.Hm z (tyAct ty H.w0 z) (w + tyAct ty H.w0 w)
      have hz1 := semichar_herm_add_right Φ.Hm z w (tyAct ty H.w0 w)
      have hz2 := semichar_herm_add_right Φ.Hm (tyAct ty H.w0 z) w (tyAct ty H.w0 w)
      have h0 := semichar_herm_zero_left Φ.Hm (0 : Fin g → ℂ)
      have hadj := Φ.adj H.w0 z w
      have hs := semichar_herm_add_right Φ.Hm z (tyAct ty H.w0 w) (tyAct ty (H.bar H.w0) w)
      rw [htr] at hs
      linear_combination (-1 : ℂ) * hz - hz1 - hz2 - h0 - hadj + hs)
  have hprod := hT.2 a ha
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, chi_prod_two] at hprod
  simp [Λ, psumL, cε] at hprod
  rw [Φ.toAnFr.χ_zero, Φ.toAnFr.χ_add ha hw] at hprod
  have ha0 := Φ.toAnFr.χ_ne_zero ha
  have hw0 := Φ.toAnFr.χ_ne_zero hw
  have hX := Complex.exp_ne_zero (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ))
  have key : Φ.χ a * (Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a (tyAct ty H.w0 a)).im : ℂ)))⁻¹ = 1 := by
    rw [← hprod]
    field_simp
    try ring
  have hχ := (mul_inv_eq_one₀ hX).1 key
  obtain ⟨k, hk⟩ := Φ.toAnFr.herm_im_int ha hw
  refine ⟨?_, hχ⟩
  rw [hχ, hk, ← Complex.exp_nat_mul]
  convert Complex.exp_int_mul_two_pi_mul_I k using 2
  push_cast
  ring

end GlobalTheory.AnVal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (k : ℤ) (n : ℕ) (U : ThetaGrp A L.L k (Over.mk x0)) (x δ : Fin g → ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Odd n → δ ∈ Φ.lat → (n : ℂ) • x = (2 : ℂ) • δ → SymLift A L.L k n (Φ.e x) U → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fock Φ.Hm k x θ) := by
  first | exact @GlobalTheory.AnVal.rd_fock_of_symLift | exact GlobalTheory.AnVal.rd_fock_of_symLift | (intros; apply GlobalTheory.AnVal.rd_fock_of_symLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_adjointness_series_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → (∀ a : 𝓞 E, star a = H.bar a) → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)]) (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m ((anFB ty).ad a) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y g Φ.jx m (0 : Fin 2)) (jpt y g Φ.jx m (1 : Fin 2))).left) (pe y g Φ.jx e m ![fun j => psIn g m ![0] ((anFB ty).A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])) (scaleGen _ _ (unitΓ u) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn g m ![1] ((anFB ty).A.act (H.bar a) j)])) := by
  first | exact @GlobalTheory.AnValAd.adjoint_series_trivial | exact GlobalTheory.AnValAd.adjoint_series_trivial | (intros; apply GlobalTheory.AnValAd.adjoint_series_trivial <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analyticFrame_first_partial_law_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph1 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (0 : Fin 3)) (lift (jpt y g Φ.jx m (1 : Fin 3)) (jpt y g Φ.jx m (2 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => psIn g m ![0, 1] ((anFB ty).G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  first | exact @GlobalTheory.AnValPh1.first_partial_law | exact GlobalTheory.AnValPh1.first_partial_law | (intros; apply GlobalTheory.AnValPh1.first_partial_law <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  first | exact @GlobalTheory.AnValEL.eL_appellHumbert | exact GlobalTheory.AnValEL.eL_appellHumbert | (intros; apply GlobalTheory.AnValEL.eL_appellHumbert <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMax

open GlobalTheory.NetMulti

theorem exists_net_all_components_max : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] [Nonempty Comp] (Xx : Comp → DataX E r) (la : ∀ k, Wt (Xx k).Ψ r) (M w L : ℝ), 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → (∀ k, (∑ τ, (Xx k).spread (la k) τ) ≤ w) → (∀ k, ∀ v ∈ (Xx k).L', herm (Xx k).Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ (Xx k).Γ, (Xx k).χ (la k) γ = 1 ∧ ∀ τ : (Xx k).Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = (Xx k).flowMat v τ ((M : ℂ) * τ.1 b)) → Real.log (fdeg E) ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log (dE E) ≤ 4 * fdeg E * L → (∀ k, Real.log (1 + ∑ τ, ∑ i, |(la k τ i : ℝ)|) ≤ 3 * L ∧ Real.log (Xx k).NA ≤ 30 * fdeg E * L ∧ Real.log (Xx k).NC ≤ 30 * fdeg E * L ∧ Real.log (Xx k).g ≤ 30 * fdeg E * L) → Real.log (Fintype.card Comp) ≤ 41 * (fdeg E * r * L) ^ 2 → ∃ NN : Finset (FPt (fun k => (Xx k).toData)), NN.Nonempty ∧ (∀ P ∈ holSub (fun k => (Xx k).toData) la, ∃ p ∈ NN, supN (fun k => (Xx k).toData) la P ≤ 4 * ((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * (fdeg E * r * L) ^ 3 := by
  classical
  intro E _ _ _ r Comp _ _ Xx la M w L hr hL hM hw hsp hT hfL hrL hML hwL hdL hk hC

  have hf1 : (1 : ℝ) ≤ fdeg E := by
    have h2 := GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg (E := E)
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : 1 ≤ fdeg E := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 ≤ (fdeg E : ℝ) * r * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL

  have hnet : ∀ k, ∃ N : Finset (Frame (Xx k).Ψ r), N.Nonempty ∧ (∀ y ∈ N, y ∈ (Xx k).dom) ∧
      (∀ Q ∈ (Xx k).SS (la k), ∀ x ∈ (Xx k).dom, ∃ y ∈ N,
        (Xx k).pnorm (la k) Q x ≤ 4 * (Xx k).pnorm (la k) Q y) ∧
      Real.log (16 * N.card) ≤ 1000 * ((fdeg E : ℝ) * r * L) ^ 3 := by
    intro k
    have hex := GlobalTheory.exists_finite_net (Xx k) (la k) M w (by linarith) (hsp k) hw (hT k)
    dsimp only at hex
    obtain ⟨N, hne, hdom, hmax, -, hsz⟩ := hex
    refine ⟨N, hne, hdom, hmax, ?_⟩
    obtain ⟨hs, hNA, hNC, hg⟩ := hk k
    have hk0 : Real.log (Xx k).k0 ≤ 4 * L := by
      have h1 : Real.log (Xx k).k0 ≤ Real.log 2 := Real.log_le_log (Xx k).minWeight_pos (Xx k).k0_le
      have h2 := Real.log_two_lt_d9
      norm_num at h2
      linarith
    have hcub := GlobalTheory.NetSize.net_size_cubic (fdeg E) r L M w (Xx k).k0 (dE E)
      (∑ τ, ∑ i, |(la k τ i : ℝ)|) (Xx k).NA (Xx k).NC (Xx k).g hf1 hr1 hL hM hw (Xx k).minWeight_pos
      (GlobalTheory.NetMulti.one_le_absDisc E) (by positivity) (by exact_mod_cast (Xx k).NA_pos)
      (by exact_mod_cast (Xx k).NC_pos) (by exact_mod_cast (Xx k).g_pos) hfL hrL hML hwL hk0 hdL
      hs hNA hNC hg
    have hcard : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.2 hne
    rw [Real.log_mul (by norm_num) hcard.ne']
    linarith
  choose N hNne hNdom hNmax hNsz using hnet

  let NN : Finset (FPt (fun k => (Xx k).toData)) :=
    Finset.univ.sigma fun k => (N k).subtype fun y => y ∈ ((Xx k).dom : Set (Frame (Xx k).Ψ r))
  have hmemNN : ∀ k y (hy : y ∈ (Xx k).dom), y ∈ N k →
      (⟨k, ⟨y, hy⟩⟩ : FPt (fun k => (Xx k).toData)) ∈ NN := by
    intro k y hy hyN
    simp only [NN, Finset.mem_sigma, Finset.mem_univ, Finset.mem_subtype, true_and]
    exact hyN
  have hNNne : NN.Nonempty := by
    obtain ⟨k⟩ := (inferInstance : Nonempty Comp)
    obtain ⟨y, hy⟩ := hNne k
    exact ⟨_, hmemNN k y (hNdom k y hy) hy⟩
  refine ⟨NN, hNNne, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨p, hpNN, hpmax⟩ := NN.exists_max_image
      (fun q => ((Xx q.1).toData).pnorm (la q.1) (P q.1) q.2) hNNne
    refine ⟨p, hpNN, ?_⟩
    have hSS := GlobalTheory.NetMulti.component_mem_SS (fun k => (Xx k).toData) la hP
    have hp0 : 0 ≤ ((Xx p.1).toData).pnorm (la p.1) (P p.1) p.2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)
    unfold supN
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    unfold supE
    refine iSup_le fun q => ?_
    obtain ⟨k, x, hx⟩ := q
    obtain ⟨y, hy, hxy⟩ := hNmax k (P k) (hSS k) x hx
    have hle := hpmax _ (hmemNN k y (hNdom k y hy) hy)
    apply ENNReal.ofReal_le_ofReal
    simp only at hle hxy ⊢
    linarith
  ·
    have h2 : ∀ k, 16 * ((N k).card : ℝ) ≤ Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      intro k
      have hc : (0 : ℝ) < (N k).card := by exact_mod_cast Finset.card_pos.2 (hNne k)
      exact (Real.log_le_iff_le_exp (by positivity)).1 (hNsz k)
    have h1 : (NN.card : ℝ) ≤ ∑ k : Comp, ((N k).card : ℝ) := by
      have : NN.card ≤ ∑ k : Comp, (N k).card := by
        simp only [NN, Finset.card_sigma]
        exact Finset.sum_le_sum fun k _ =>
          (Finset.card_subtype _ _).trans_le (Finset.card_filter_le _ _)
      exact_mod_cast this
    have hcardle : 16 * (NN.card : ℝ) ≤
        Fintype.card Comp * Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      calc 16 * (NN.card : ℝ) ≤ 16 * ∑ k : Comp, ((N k).card : ℝ) := by linarith
        _ = ∑ k : Comp, 16 * ((N k).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ ∑ _k : Comp, Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) :=
          Finset.sum_le_sum fun k _ => h2 k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hNNpos : 0 < 16 * (NN.card : ℝ) := by
      have : (0 : ℝ) < NN.card := by exact_mod_cast Finset.card_pos.2 hNNne
      positivity
    have hCpos : (0 : ℝ) < Fintype.card Comp := by exact_mod_cast Fintype.card_pos
    set A := (fdeg E : ℝ) * r * L with hAdef
    have hA23 : A ^ 2 ≤ A ^ 3 := by nlinarith [sq_nonneg A, mul_nonneg (sq_nonneg A) (sub_nonneg.2 hA)]
    calc Real.log (16 * NN.card) ≤ Real.log (Fintype.card Comp * Real.exp (1000 * A ^ 3)) :=
          Real.log_le_log hNNpos hcardle
      _ = Real.log (Fintype.card Comp) + 1000 * A ^ 3 := by
          rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 1041 * A ^ 3 := by linarith

end GlobalTheory.NetMax
end
