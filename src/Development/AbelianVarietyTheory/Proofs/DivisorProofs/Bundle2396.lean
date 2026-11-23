module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle200
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle101
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

theorem _root_.GlobalTheory.T.intersectionNumber_pullback_proportional_of_proportional : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → letI := algebraΓOfHom p; letI := algebraΓOfHom (f ≫ p); ∀ (L L' : LB W), L.IsLB → L'.IsLB → ∀ (a b : ℕ), (∀ C : Closeds W, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L] = b * interNumRed ℂ C ![L']) → ∀ C : Closeds M, IsCompleteCurve ℂ C → (a : ℤ) * interNumRed ℂ C ![L.pull f] = b * interNumRed ℂ C ![L'.pull f] := by
  first | exact @GlobalTheory.NumPull.interNumRed_pull_proportional | exact GlobalTheory.NumPull.interNumRed_pull_proportional | (intros; apply GlobalTheory.NumPull.interNumRed_pull_proportional <;> assumption)
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.ShareNumbers

theorem real_bounds (PP TO Dp k f m r nW : ℝ) (hm : 1 ≤ m) (hf : 1 ≤ f) (hk : 1 ≤ k) (hD : 1 ≤ Dp) (hr : 1 ≤ r)
    (hPP : (2 * f * m) ^ 4 * nW ≤ PP) (hn40 : 40 ≤ nW) (hnk : k ≤ nW) (hnr : f * r ^ 2 ≤ nW)
    (hTO : PP ^ 4 * Dp ^ 3 * k * f / m ≤ TO) :
    54 * f * r ^ 4 ≤ TO ∧ 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ TO := by
  have hm0 : 0 < m := by linarith
  have hc : 16 ≤ (2 * f * m) ^ 4 := by
    have : 2 ≤ 2 * f * m := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 4
  have hfm : f * m ≤ (2 * f * m) ^ 4 := by
    have h1 : 1 ≤ 2 * f * m := by nlinarith
    calc f * m ≤ 2 * f * m := by nlinarith
      _ = (2 * f * m) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)
  have hn0 : 0 ≤ nW := by linarith
  have hP640 : 640 ≤ PP := by nlinarith
  have hPm : m * nW ≤ PP := by nlinarith
  have hPfk : f * k ≤ PP := by nlinarith
  have hPfr : f * r ^ 2 ≤ PP := by nlinarith
  have hP0 : 0 ≤ PP := by linarith

  have h4 : PP ^ 3 ≤ PP ^ 4 / m := by
    rw [le_div_iff₀ hm0]
    have : m ≤ PP := by nlinarith
    calc PP ^ 3 * m ≤ PP ^ 3 * PP := by gcongr
      _ = PP ^ 4 := by ring
  have hDkf : 1 ≤ Dp ^ 3 * k * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD) hk) hf
  have hT : PP ^ 3 * (Dp ^ 3 * k * f) ≤ TO := by
    calc PP ^ 3 * (Dp ^ 3 * k * f) ≤ PP ^ 4 / m * (Dp ^ 3 * k * f) := by gcongr
      _ = PP ^ 4 * Dp ^ 3 * k * f / m := by ring
      _ ≤ TO := hTO
  have hP3 : 0 ≤ PP ^ 3 := by positivity
  constructor
  · have e1 : 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP ^ 3 := by
      have a : 54 * (f * r ^ 2) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * r ^ 2 := by positivity
      calc 54 * (f * r ^ 2) * (f * r ^ 2) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 54 * f * r ^ 4 ≤ 54 * (f * r ^ 2) * (f * r ^ 2) := by
      have : 0 ≤ r ^ 4 := by positivity
      have hff : f ≤ f * f := by nlinarith
      calc 54 * f * r ^ 4 = 54 * r ^ 4 * f := by ring
        _ ≤ 54 * r ^ 4 * (f * f) := by gcongr
        _ = _ := by ring
    calc 54 * f * r ^ 4 ≤ PP ^ 3 := e2.trans e1
      _ = PP ^ 3 * 1 := (mul_one _).symm
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT
  · have e1 : 28 * (f * k) * (f * k) ≤ PP ^ 3 := by
      have a : 28 * (f * k) ≤ PP * PP := by nlinarith
      have b : 0 ≤ f * k := by positivity
      calc 28 * (f * k) * (f * k) ≤ PP * PP * PP := by gcongr
        _ = PP ^ 3 := by ring
    have e2 : 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by
      have hfk : 0 ≤ (f * k) ^ 3 := by positivity
      have hD2 : Dp * (Dp + 6) ≤ 7 * Dp ^ 3 := by
        have h1 : Dp ≤ Dp ^ 2 := by nlinarith
        have h2 : Dp ^ 2 ≤ Dp ^ 3 := by nlinarith
        nlinarith
      calc 4 * (f * k) ^ 3 * (Dp * (Dp + 6)) ≤ 4 * (f * k) ^ 3 * (7 * Dp ^ 3) := by gcongr
        _ = 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := by ring
    calc _ ≤ 28 * (f * k) * (f * k) * (Dp ^ 3 * k * f) := e2
      _ ≤ PP ^ 3 * (Dp ^ 3 * k * f) := by gcongr
      _ ≤ TO := hT


open Formalism.BasicNotions in
theorem params_bounds {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) (p0 : ℕ) (hp : p0 ≤ D.R.r) :
    2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) + 2 ≤ T.TO ∧
      (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) * (((D.R.f * (D.R.r * (D.R.r - 1) / 2) : ℕ) : ℝ) + 6) / (T.TO : ℝ) ≤
        1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3)) := by
  have hf2 : 2 ≤ D.R.f := by
    have h1 : 0 < D.R.ord := D.R.ord_pos
    have h2 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hDp : T.Dp = D.R.f * (D.R.r * (D.R.r - 1) / 2) := by rw [T.Dp_eq, Nat.choose_two_right]
  have hD1 : 1 ≤ T.Dp := by
    rw [T.Dp_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hnk : D.R.k ≤ T.nWn := by
    have h := T.nW_lo.2.1
    have h' : D.R.k - 1 ≤ (D.R.k - 1) * D.R.f := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hnr : D.R.f * D.R.r ^ 2 ≤ T.nWn := by
    have h := T.nW_lo.1
    have h' : D.R.f * D.R.r * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ (by omega)
    calc D.R.f * D.R.r ^ 2 = D.R.f * D.R.r * D.R.r := by ring
      _ ≤ _ := h'.trans h
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast hm1
  have hTO : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
    have hn : 0 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f := by
      have : 0 ≤ T.PP ^ 4 := by positivity
      positivity
    have hd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    have hdm : (D.R.m : ℝ) * L.de2 ≤ D.R.m := mul_le_of_le_one_right hm0.le L.thickDensity_le_one
    calc T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / D.R.m
        ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f / ((D.R.m : ℝ) * L.de2) := div_le_div_of_nonneg_left hn hd hdm
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hn hx1) hd.le
  obtain ⟨A, B⟩ := real_bounds T.PP T.TO T.Dp D.R.k D.R.f D.R.m D.R.r T.nWn (by exact_mod_cast hm1)
    (by exact_mod_cast (show 1 ≤ D.R.f by omega)) (by exact_mod_cast hk1) (by exact_mod_cast hD1)
    (by exact_mod_cast (show 1 ≤ D.R.r by omega)) T.PP_nW (by exact_mod_cast T.nW_40) (by exact_mod_cast hnk)
    (by exact_mod_cast hnr) hTO
  constructor
  · have hA : 54 * (D.R.f * D.R.r ^ 4) ≤ T.TO := by
      have : ((54 * (D.R.f * D.R.r ^ 4) : ℕ) : ℝ) ≤ T.TO := by push_cast; linarith
      exact_mod_cast this
    have h1 : p0 * (D.R.r - p0) ≤ D.R.r * D.R.r := Nat.mul_le_mul hp (Nat.sub_le _ _)
    have h2 : 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * (D.R.f * D.R.r ^ 4) := by
      calc 50 * D.R.r ^ 2 * (D.R.f * (p0 * (D.R.r - p0))) ≤ 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r)) := by gcongr
        _ = 50 * (D.R.f * D.R.r ^ 4) := by ring
    have h3 : D.R.r ≤ D.R.r ^ 4 := Nat.le_self_pow (by norm_num) _
    have h4 : 1 ≤ D.R.r ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h5 : D.R.r ^ 4 ≤ D.R.f * D.R.r ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [← hDp]
    have hT0 : (0 : ℝ) < T.TO := by
      have : 1 ≤ T.TO := le_trans (by omega) T.TO_40
      exact_mod_cast this
    have hq : (0 : ℝ) < 4 * ((D.R.f : ℝ) * D.R.k) ^ 3 := by
      have : (0 : ℝ) < D.R.f := by exact_mod_cast (show 0 < D.R.f by omega)
      have : (0 : ℝ) < D.R.k := by exact_mod_cast hk1
      positivity
    rw [div_le_div_iff₀ hT0 hq]
    linarith

end GlobalTheory.ShareNumbers


open GlobalTheory.ShareNumbers in
theorem GlobalTheory.ShareNumbers.numbers_along_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ (ι : Fm.Ix x) (p0 : ℕ), p0 ≤ (Fm.D x ι).R.r → 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * (p0 * ((Fm.D x ι).R.r - p0))) + 2 ≤ (Fm.parT x hx ι).TO ∧ ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) * ((((Fm.D x ι).R.f * ((Fm.D x ι).R.r * ((Fm.D x ι).R.r - 1) / 2) : ℕ) : ℝ) + 6) / (Fm.parT x hx ι).TO ≤ 1 / (4 * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.k) ^ 3)) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun x hx _ ι p0 hp => params_bounds (Fm.parT x hx ι) p0 hp⟩⟩⟩
end
end

section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem tieAdmG_of_record (D : Formalism.BasicNotions.D7) : TieAdmG D :=
  fun k => ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

theorem wg_le_badBound (g m N q : ℝ) (n : ℕ) (r : ℝ) (hg : 2 ≤ g) (hm : 0 ≤ m) (hr : 100 ≤ r) (hrN : r ≤ N) :
    3 * (n : ℝ) / g + 23 * (n : ℝ) * Real.log g / Real.sqrt g +
        2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) + r / 2 * (7 / 8 : ℝ) ^ n +
        Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ badBound g n m N q := by
  unfold badBound
  have hf : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : 0 < r := by linarith
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlN : Real.log r ≤ Real.log N := Real.log_le_log hr0 hrN
  have hg1 : 0 < g - 1 := by linarith
  have t3 : 2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log r) / (g - 1)) ≤
      2 * (n : ℝ) * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) := by
    have : (1 + Real.log r) / (g - 1) ≤ (1 + Real.log N) / (g - 1) :=
      div_le_div_of_nonneg_right (by linarith) hg1.le
    have h0 : 0 ≤ 2 * (n : ℝ) * m := by positivity
    nlinarith
  have t4 : r / 2 * (7 / 8 : ℝ) ^ n ≤ N / 2 * (7 / 8 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    have : 0 ≤ (7 / 8 : ℝ) ^ n := by positivity
    nlinarith
  have t5 : Real.exp (-(n : ℝ) / (5 * Real.log r)) ≤ Real.exp (-((n : ℝ) / (10 * Real.log N))) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hf (by positivity) (by linarith)
  linarith

end GlobalTheory.BadNumOnto

namespace GlobalTheory.BadNumOnto

open GlobalTheory.BadShare

theorem badShare_numbers_onto : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ), Fm.x1 < x → x0 ≤ x → ∀ (ι : Fm.Ix x), 100 ≤ (Fm.D x ι).R.r ∧ TieAdmG (Fm.D x ι) ∧ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) ≤ 1 / 4 ∧ ∀ k : Fin 2, 2 ^ 12 ≤ (Fm.D x ι).host.g k ∧ 4 * (3 * ((Fm.D x ι).R.f : ℝ) / ((Fm.D x ι).host.g k : ℝ) + 23 * ((Fm.D x ι).R.f : ℝ) * Real.log ((Fm.D x ι).host.g k : ℝ) / Real.sqrt ((Fm.D x ι).host.g k : ℝ) + 2 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.m : ℝ) * (1 / (4 * ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ)) + (1 + Real.log ((Fm.D x ι).R.r : ℝ)) / (((Fm.D x ι).host.g k : ℝ) - 1)) + ((Fm.D x ι).R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ (Fm.D x ι).R.f + Real.exp (-((Fm.D x ι).R.f : ℝ) / (5 * Real.log ((Fm.D x ι).R.r : ℝ)))) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  refine ⟨1, one_pos, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨xs, hs⟩ := GlobalTheory.family_eventually_size_bounds eps Fm 5 (by norm_num)
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  have hezle : Fm.ez ≤ eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.ez_le
    rwa [Fm.L_ez 0 i, Fm.L_eps 0 i] at this
  obtain ⟨xb, hb⟩ := badBound_numbers Fm.ez 5 hez (hezle.trans he1)
  have he7 : 0 < Fm.ez / 7 := by positivity
  obtain ⟨xe, hxe⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop he7).eventually_ge_atTop (4 : ℝ)).and
      (((tendsto_rpow_atTop he).eventually_ge_atTop (512 : ℝ)).and (Filter.eventually_ge_atTop (1 : ℝ))))
  refine ⟨max (max xs xb) xe, fun x hx1 hx ι => ?_⟩
  have hxs : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxb : xb ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  obtain ⟨h7, h512, hx1'⟩ := hxe x ((le_max_right _ _).trans hx)
  rw [Fm.L_x x ι hx1, Fm.L_ez x ι]
  have hE : Real.exp (-(x ^ (Fm.ez / 7))) ≤ 1 / 4 := by
    have h1 : (4 : ℝ) ≤ Real.exp (x ^ (Fm.ez / 7)) := by
      have := Real.add_one_le_exp (x ^ (Fm.ez / 7)); linarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h1
  have hr100 : 100 ≤ (Fm.D x ι).R.r := (hs x hxs ι 0).2.2.2.2.1
  refine ⟨hr100, tieAdmG_of_record _, hE, fun k => ?_⟩
  obtain ⟨hg, hf2, hf5, hm5, -, hr5, hq⟩ := hs x hxs ι k
  have hg12 : (2 : ℝ) ^ 12 ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans ?_ hg
    have := Real.add_one_le_exp (8 * x ^ eps)
    norm_num
    linarith
  refine ⟨by exact_mod_cast hg12, ?_⟩
  have hr100' : (100 : ℝ) ≤ ((Fm.D x ι).R.r : ℝ) := by exact_mod_cast hr100
  have hepsC : x ^ Fm.ez ≤ x ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hgz : Real.exp (8 * x ^ Fm.ez) ≤ ((Fm.D x ι).host.g k : ℝ) := by
    refine le_trans (Real.exp_le_exp.2 ?_) hg
    have := Real.rpow_le_rpow_of_exponent_le hx1' hezle
    linarith
  obtain ⟨-, hbb0, hbb⟩ := hb x hxb ((Fm.D x ι).host.g k) ((Fm.D x ι).R.f) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) hgz
    (by rw [Real.rpow_two]; exact hf2) hf5 (Nat.cast_nonneg _) hm5 (le_max_right _ _) (max_le hr5 hepsC) hq
  have hW := wg_le_badBound ((Fm.D x ι).host.g k) ((Fm.D x ι).R.m)
    (max ((Fm.D x ι).R.r : ℝ) (x ^ Fm.ez)) ((min (Fm.D x ι).host.q (Fm.D x ι).host.d : ℕ) : ℝ) ((Fm.D x ι).R.f)
    ((Fm.D x ι).R.r) (by linarith) (Nat.cast_nonneg _) hr100' (le_max_left _ _)
  linarith

end GlobalTheory.BadNumOnto
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cloud_mem_Icc_Sc {D : D7} (L : SizeData₂ D) (τ i : ℕ) :
    0 ≤ cloud D τ i ∧ (cloud D τ i : ℝ) ≤ L.Sc := by
  unfold cloud
  split_ifs with h
  · dsimp only [GlobalTheory.SignedHC.GridData.ofHCParam]
    unfold GlobalTheory.SignedHC.GridData.extend
    split_ifs with h2
    · obtain ⟨h0, h1⟩ := L.cloud_v ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩) ⟨i - 2, h2⟩
      refine ⟨Int.floor_nonneg.mpr (by exact_mod_cast h0), ?_⟩
      have hf := Int.floor_le ((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩)
      have hf' : (((⌊(D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩⌋ : ℤ) : ℚ) : ℝ) ≤
          (((D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)).v ⟨i - 2, h2⟩ : ℚ) : ℝ) := by exact_mod_cast hf
      push_cast at hf' ⊢
      linarith
    · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩
  · exact ⟨le_rfl, by simpa using L.Sc_pos.le⟩

theorem Lc_le_of_cloud_le {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (S : ℝ) (h0 : 0 ≤ S) (hcl : ∀ τ i, 0 ≤ O.cl τ i ∧ (O.cl τ i : ℝ) ≤ S) :
    (O.Lc : ℝ) ≤ S := by
  have hL : O.Lc ≤ ⌊S⌋₊ := by
    unfold FunData.Lc
    refine Finset.sup_le fun τ _ => ?_
    rw [Nat.le_floor_iff h0]
    obtain ⟨a0, a1⟩ := hcl τ 2
    obtain ⟨b0, -⟩ := hcl τ O.k
    have h : ((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) ≤ O.cl τ 2 := by omega
    have h' : (((O.cl τ 2 - O.cl τ O.k).toNat : ℤ) : ℝ) ≤ ((O.cl τ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (O.Lc : ℝ) ≤ (⌊S⌋₊ : ℝ) := by exact_mod_cast hL
    _ ≤ S := Nat.floor_le h0

theorem Sc_le_scale_b {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : L.Sc ≤ L.sc.b := by
  have hk := P.kS_le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn : (1 : ℝ) ≤ D.R.n := by
    unfold Ranks.n
    exact_mod_cast D.R.ord_pos
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hw : L.sc.w'' D.R.n ≤ L.sc.b := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [div_le_iff₀ (by positivity)]
    calc L.sc.x * L.sc.b / L.sc.X' ≤ L.sc.x * L.sc.b := div_le_self (by positivity) hX
      _ ≤ L.sc.b * (L.sc.x * D.R.n) := by nlinarith [mul_nonneg (mul_pos hx hb).le (sub_nonneg.2 hn)]
  have hS := L.Sc_pos
  nlinarith

theorem mul_pow_le_exp_rpow {eps : ℝ} (heps : 0 < eps) (a : ℕ) (A : ℝ) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x, x0 ≤ x → A * x ^ a ≤ Real.exp (x ^ eps) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((a : ℝ) + 1) ≤ eps * n := ⟨⌈((a : ℝ) + 1) / eps⌉₊, by
    have := Nat.le_ceil (((a : ℝ) + 1) / eps)
    rw [div_le_iff₀ heps] at this
    linarith⟩
  refine ⟨max 1 (|A| * n.factorial), le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 ≤ x ^ eps := Real.rpow_nonneg hx0 _
  have h1 := Real.pow_div_factorial_le_exp (x ^ eps) hy n
  have h2 : (x ^ eps) ^ n = x ^ (eps * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have h3 : x ^ (((a + 1 : ℕ)) : ℝ) ≤ x ^ (eps * n) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  rw [Real.rpow_natCast] at h3
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hAx : |A| * n.factorial ≤ x := (le_max_right _ _).trans hx
  have hxa : 0 ≤ x ^ a := pow_nonneg hx0 a
  have e2 : |A| * x ^ a * n.factorial ≤ x ^ (a + 1) :=
    calc |A| * x ^ a * n.factorial = x ^ a * (|A| * n.factorial) := by ring
      _ ≤ x ^ a * x := mul_le_mul_of_nonneg_left hAx hxa
      _ = x ^ (a + 1) := (pow_succ x a).symm
  have e3 : |A| * x ^ a ≤ x ^ (a + 1) / n.factorial := by rw [le_div_iff₀ hf]; exact e2
  rw [h2] at h1
  calc A * x ^ a ≤ |A| * x ^ a := mul_le_mul_of_nonneg_right (le_abs_self A) hxa
    _ ≤ x ^ (a + 1) / n.factorial := e3
    _ ≤ x ^ (eps * n) / n.factorial := by gcongr
    _ ≤ _ := h1

theorem design_lines_of_ranks (x eps B : ℝ) (c k m f t : ℕ) (hx : 20480 ≤ x) (heps : eps ≤ 1)
    (hm : 2 ≤ m) (hmf : m ≤ f) (hfk : f ≤ k) (hkt : k + m + 4 ≤ t)
    (ht : (t : ℝ) ≤ x ^ c) (hto : x ^ 377 ≤ (t : ℝ)) (hk : (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * eps))
    (hB : 25 * x ^ (6 * c) ≤ B) :
    (m : ℝ) * f * (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) ^ 2 ≤ B ∧
      80 * ((k : ℝ) + m - 1) ^ 4 ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  constructor
  · have hN : k + m * (t + (k + m + 5) + 1) ≤ 5 * t ^ 2 := by
      have h1 : t + (k + m + 5) + 1 ≤ 4 * t := by omega
      have h2 : m * (t + (k + m + 5) + 1) ≤ t * (4 * t) := Nat.mul_le_mul (by omega) h1
      nlinarith
    have hP : m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ 25 * t ^ 6 := by
      have h1 : m * f ≤ t * t := Nat.mul_le_mul (by omega) (by omega)
      have h2 : (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (5 * t ^ 2) ^ 2 := Nat.pow_le_pow_left hN 2
      calc m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 ≤ (t * t) * (5 * t ^ 2) ^ 2 := Nat.mul_le_mul h1 h2
        _ = 25 * t ^ 6 := by ring
    have hP' : ((m * f * (k + m * (t + (k + m + 5) + 1)) ^ 2 : ℕ) : ℝ) ≤ ((25 * t ^ 6 : ℕ) : ℝ) := by
      exact_mod_cast hP
    push_cast at hP'
    have ht6 : (t : ℝ) ^ 6 ≤ (x ^ c) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) ht 6
    rw [← pow_mul, mul_comm c 6] at ht6
    push_cast
    linarith
  · have hkr : (k : ℝ) ≤ 2 * x ^ 15 := by
      have e : x ^ (9 / 2 + 10 * eps) ≤ x ^ ((15 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
      rw [Real.rpow_natCast] at e
      linarith
    have hmk : (m : ℝ) ≤ k := by exact_mod_cast (le_trans hmf hfk)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hr0 : 0 ≤ (k : ℝ) + m - 1 := by linarith
    have hr : (k : ℝ) + m - 1 ≤ 4 * x ^ 15 := by linarith
    have hr4 : ((k : ℝ) + m - 1) ^ 4 ≤ (4 * x ^ 15) ^ 4 := pow_le_pow_left₀ hr0 hr 4
    have e1 : (4 * x ^ 15) ^ 4 = 256 * x ^ 60 := by ring
    have e2 : 20480 * x ^ 60 ≤ x ^ 377 := by
      have a1 : 20480 * x ^ 60 ≤ x * x ^ 60 := mul_le_mul_of_nonneg_right hx (pow_nonneg hx0 _)
      have a2 : x * x ^ 60 = x ^ 61 := by ring
      have a3 : x ^ 61 ≤ x ^ 377 := pow_le_pow_right₀ hx1 (by norm_num)
      linarith
    have e3 : (t : ℝ) ≤ (((k + m * (t + (k + m + 5) + 1) : ℕ) : ℝ)) := by
      have : t ≤ k + m * (t + (k + m + 5) + 1) := by nlinarith
      exact_mod_cast this
    nlinarith

end GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigTop.Fun
end
end

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.level_geometry_weight_bound : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E), Even G.2 → ∀ (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (AllWt.modelWt (U σ) G k) τ) ≤ w) → ∀ (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ D.R.r) ∈ AllWt.framesOn (U σ) Z → AllWt.bergOn (U σ) (D.sp.W j) (dict σ) Z G y ≤ ENNReal.ofReal (GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d l.M w) := by
  first | exact @GlobalTheory.BergComp.bergOn_le_supConst | exact GlobalTheory.BergComp.bergOn_le_supConst | (intros; apply GlobalTheory.BergComp.bergOn_le_supConst <;> assumption)
end
