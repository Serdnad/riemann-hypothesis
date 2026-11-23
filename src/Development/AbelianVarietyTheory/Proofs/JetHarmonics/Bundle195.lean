module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle194
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle005
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem combBound_of_depth_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : WeightAlgebra.PJ D B P j}
    {ka wL wF : WeightFamilies.Wt D j} {S : WeightAlgebra.Scal B} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (G : GlobalFamilyData X ka wL wF) (c : ℝ) (hc0 : 0 ≤ c)
    (hH1 : ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la + c * X.phiC la y : ℝ) : EReal))
    (hEt : j < D.R.m → 0 < G.iet ∧
      ∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.CombBound G S c nus := by
  intro la y
  have hφ := Formalism.MainNotions.Gaps.T0.phiC_nonneg X la y
  have hd := hH1 la y
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · obtain ⟨hi, h⟩ := hEt hj
    have hi' : (0 : ℝ) < 2 * (G.iet : ℝ) := by positivity
    have h1 := h la y
    have h0 : (0 : ℝ) ≤ 2 * G.iet * X.phiC la y := mul_nonneg hi'.le hφ
    refine ⟨le_trans (by exact_mod_cast h0) h1, fun hfin => hd.trans ?_⟩
    rw [← EReal.coe_toReal hfin (X.vAt_ne_bot la y _), EReal.coe_le_coe_iff] at h1
    rw [EReal.coe_le_coe_iff]
    have h2 : X.phiC la y ≤ (X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) := by
      rw [le_div_iff₀ hi']; linarith
    have h4 : c * X.phiC la y ≤ c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) :=
      mul_le_mul_of_nonneg_left h2 hc0
    have h5 : c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal =
        c * ((X.vAt la y (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ))) := by ring
    rw [h5]
    linarith
  · have h0 : X.phiC la y = 0 := by
      unfold WeightAlgebra.PJ.phiC
      rw [if_neg (not_lt.2 hj)]
    rw [h0, mul_zero, add_zero] at hd
    exact hd

theorem combBound_alg : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (ka wF : WeightFamilies.Wt D j) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka w wF), S.sW = sWt (recB h.toLawsCore) hinj EX w → (j < D.R.m → 0 < G.iet ∧ EtVal h j hj G.iet G.et) → CombBound G S c (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro hH D T h j hj hinj EX w c hO hR ka wF S G hS hEt
  refine combBound_of_depth_le G c hR.2.2.2.1 (fun la y => ?_) hEt
  rw [hS]
  exact GlobalTheory.T.thetaLattice_depth_le_unscaled_add_boundary hH D T h j hj hinj EX w c hO hR la y

end GlobalTheory.PtTie
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).1, GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c,
    GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.tendsto_levelZero_form_cutoff_pow_mul_of_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ), NFHyp Cb Cc p f A₀ p₀ χ N → LimEvT p χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  first | exact @GlobalTheory.limEvT_pow_mul_of_topDomination | exact GlobalTheory.limEvT_pow_mul_of_topDomination | (intros; apply GlobalTheory.limEvT_pow_mul_of_topDomination <;> assumption)
end
