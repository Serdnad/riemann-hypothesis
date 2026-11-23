module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle141
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle193
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
public import Formalism.HermitianCurvature.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle192
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle161
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaLattice_depth_le_unscaled_add_boundary : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  first | exact @GlobalTheory.RecDepth.depth_le | exact GlobalTheory.RecDepth.depth_le | (intros; apply GlobalTheory.RecDepth.depth_le <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth2_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepth2 N O := by
  intro hAv hHT D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (lR Tp hK j).n := by
    intro j _
    show _ ≤ Tp.nWn
    refine le_trans ?_ Tp.nW_lo.1
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  have hL : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun hM EX _ _ _ _ _ hn
  refine GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι N (numOf D L)
    hR.E_eq hR.σ_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hL.piSplit hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ?_
  intro la hla j
  obtain ⟨Ap, hAp0, hAp, hle⟩ := GlobalTheory.T.sizes_bound_at_two_first_rows_weights D L Pm Tp hK T.Q hM.pins hx hb O.C hPg.1 (ι j) (hR.inR j)
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨hsp, h2, hvd, hup⟩ := GlobalTheory.T.hostField_two_conjugate_places_over_two D T.Q.H hM.pins.1.1 (resCharOf la) (hR.sm_eq ▸ hla)
  refine ⟨_, ?_, GlobalTheory.T.unscaledDepth_le_placeOverTwo (resCharOf la) (hAv _) (hHT _) D.host.E T.Q.H (T.Q.Dw (ι j)) T.Q.l (T.Q.Xo (ι j)) T.Q.c
    hR.star_eq D.R.f (D.host.vdH (resCharOf la)) hvd hsp h2 la rfl _ _ _ (fun τ _ _ h => (hL.wts _ (hR.inR j)).1 τ h)
    (DepthTie.card_of_laws T _ hL hM.pins (ι j) (hR.inR j)) Ap hAp0 hAp⟩
  unfold OnObj.sC OnObj.Se
  rw [hR.T_eq, hR.m_eq, hR.vd_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Nat.cast_nonneg _)) hle
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hAp0
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  first | exact @GlobalTheory.LargePkg.pkgZero | exact GlobalTheory.LargePkg.pkgZero | (intros; apply GlobalTheory.LargePkg.pkgZero <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.packages_exist_frobeniusComplexConjugation : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  first | exact @GlobalTheory.PkgConj.packages_conj | exact GlobalTheory.PkgConj.packages_conj | (intros; apply GlobalTheory.PkgConj.packages_conj <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  first | exact @GlobalTheory.InertPackage.pkgInert | exact GlobalTheory.InertPackage.pkgInert | (intros; apply GlobalTheory.InertPackage.pkgInert <;> assumption)
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  first | exact @GlobalTheory.SplitPackage.pkgSplit | exact GlobalTheory.SplitPackage.pkgSplit | (intros; apply GlobalTheory.SplitPackage.pkgSplit <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

namespace GlobalTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem limEvT_pow_mul_of_topDomination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ), NFHyp Cb Cc p f A₀ p₀ χ N → LimEvT p χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  intro hX hP hDom Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.levelZeroForm_cutoff_tendsto_of_density_domination hX hP Cb
  obtain ⟨C2, h2⟩ := hDom Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') a5
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') a5
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) :=
    fun g₀ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩
  exact h1 Wp Wq P p _ χ _ N Y a2 a1 (ckOn_fpm p p₀ a3 hid) (inCC_fpm_id p p₀ a4) hC1
    (fun w hw hN => h2 Wp Wq P p f A₀ p₀ χ Y N ⟨a1, a2, a3, a4, hC2, a6⟩ w hw hN)

end GlobalTheory
end
