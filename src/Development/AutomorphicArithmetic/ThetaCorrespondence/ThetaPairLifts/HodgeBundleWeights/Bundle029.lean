module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspRegularLevelDeterminant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle025
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle026
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleAmpleOnRegularLocus
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerIsoFlagTangentPsiSet
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057

@[expose] public section

section

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
namespace GlobalTheory.ShortDet
section Weight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weight

theorem exists_short_integral_vector : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  intro hP hGr hQ hS hK hN
  obtain ⟨C₁, hC₁, hb⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨C₃, hC₃, h3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP
  refine ⟨C₃ + 240 + C₁ + 2 * C₃, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' he hg hf hr fr
  obtain ⟨-, -, -, -, -, hdeg, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  obtain ⟨hpq, -, -⟩ := hJ j hj
  obtain ⟨hp', hq', -⟩ := hT.pins.2.2.2 j hj
  obtain ⟨-, h0, hcz⟩ := cZero_spec D j
  have hgap : ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ cZero D j := by
    have h1 := (cZeroN_isLeast D j).1.2.1
    have h2 := le_choose hf hr hp hq hpq
    rw [hp', hq'] at h2
    exact Int.ofNat_le.2 (by omega)
  have hanti := antitone_smul_hodgeWt (T.Q.Dw j) h0
  have hgp := gap_smul_hodgeWt (T.Q.Dw j) hp hq (cZero D j)
  have hsz := size_smul_hodgeWt (T.Q.Dw j) h0
  have hcard := card_levelAut_le (T.Q.Dw j) Y.d.l₂
  rw [hdeg, congrArg (Nat.cast : ℕ → ℝ) hpq] at hsz
  rw [hdeg, hpq, Nat.mul_div_cancel_left _ two_pos] at hcard
  have hf' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (100 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hcz' : (cZero D j : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hcz
  have hs0 : 0 ≤ ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| := by positivity
  have hb' := hb D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho _ hanti
  have h3' := h3 D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' _ hanti fun τ => (hgp τ).symm ▸ hgap
  generalize ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| = s at hs0 hsz hb' h3'
  have ha : (1 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
  have hs : s ≤ ((D.R.f : ℝ) * D.R.r) ^ 5 := by
    refine hsz.trans ?_
    push_cast
    calc _ ≤ 2 * (D.R.f : ℝ) * (D.R.r * (22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4)) := by gcongr
      _ = 44 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by ring
      _ ≤ (D.R.f : ℝ) ^ 2 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by gcongr; nlinarith
      _ = _ := by ring
  have hls : Real.log s ≤ 5 * Lb := by
    rcases hs0.eq_or_lt with rfl | h
    · rw [Real.log_zero]; linarith
    · refine (Real.log_le_log h hs).trans ?_
      rw [Real.log_pow]; push_cast; linarith
  have hcard' : (Nat.card (grpHR fr) : ℝ) ≤ Real.exp (120 * ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb) := by
    have h1 : (Nat.card (grpHR fr) : ℝ) ≤ (Y.d.l₂.M : ℝ) ^ (2 * (D.R.f * D.R.r)) ^ 2 := by
      exact_mod_cast (Subgroup.card_le_card_group _).trans hcard
    refine h1.trans ((pow_le_pow_left₀ (by positivity) ((Real.le_exp_log _).trans (Real.exp_le_exp.2 hM)) _).trans ?_)
    rw [← Real.exp_nat_mul]
    push_cast
    exact le_of_eq (by congr 1; ring)
  have haZ : (D.R.f : ℝ) * D.R.r ≤ D.R.f * D.R.r * Lb := le_mul_of_one_le_right (by positivity) hL
  have hZ2 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ (D.R.f * D.R.r * Lb) ^ 2 := by
    rw [mul_pow _ Lb]; gcongr; nlinarith
  replace hs := hs.trans (pow_le_pow_left₀ (by positivity) haZ 5)
  have hZ := ha.trans haZ
  rw [mul_assoc] at hcard'
  generalize (D.R.f : ℝ) * D.R.r * Lb = Z at hb' h3' hs hZ hZ2 ⊢
  have hw : ∀ k, k ≤ 9 → Z ^ k ≤ Z ^ 9 := fun k hk => pow_le_pow_right₀ hZ hk
  have hA : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hG.lev.2]; exact Nat.coprime_one_left _
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨u₀, h₀, hd₀⟩ := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGr hQ hS hK hN D T hT j hp hq hE hj Y e o hG he hg fr _ (Or.inl rfl)
  obtain ⟨u, hu, hd, hsup⟩ := exists_short (β := Real.exp (C₁ * Z ^ 3)) (Λ := Real.exp (2 * C₃ * Z ^ 9))
    (N := Real.exp (C₃ * Z ^ 3)) hpos hA hG.unf (grpHR fr) _ (Real.one_le_exp (by positivity)) (Real.exp_pos _).le
    (Real.exp_pos _).le (fun W => (hb' (by linarith) W).2.1)
    (fun W => ((_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hE hj Y e o hG _ hanti fun τ => by rw [hgp]; omega).2 W).2.2)
    (fun W => by
      obtain ⟨n, w, abelian₂, a1, a2, a3⟩ := h3' (by linarith) W
      refine ⟨n, w, abelian₂, a1, (Real.le_exp_log _).trans (Real.exp_le_exp.2 (a2.trans ?_)),
        (Real.le_exp_log _).trans (Real.exp_le_exp.2 a3)⟩
      have h1 : Z ^ 3 * s ≤ Z ^ 8 := (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
      have h2 := hw 8 (by norm_num)
      have h4 := hw 5 (by norm_num)
      rw [mul_comm 2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hC₃) h₀ hd₀
  refine ⟨u, hu, hd, normW_mul_pull_le hpos hA (fun σ hσ => ?_) (fun G hGe => ?_) (AllWt.even_wtOf _ _) (Real.exp_pos _).le
    fun σ z => (hsup σ z).trans ?_⟩
  · obtain ⟨th, hr, -, h⟩ := hG.dictU σ hσ
    exact h.2.2.2.1
  · obtain ⟨k₁, k₂⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hT j hp hq hE hj Y e o hG G hGe
    exact ⟨k₁, fun γ f g h => (k₂ γ f g h).2⟩
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard' 2)
      (by positivity)) (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have h1 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₁
    have h2 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₃
    have h4 := hw 2 (by norm_num)
    push_cast
    linarith
end GlobalTheory.ShortDet
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

theorem _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  first | exact @_root_.GlobalTheory.ShortDet.exists_short_integral_vector | exact _root_.GlobalTheory.ShortDet.exists_short_integral_vector | (intros; apply _root_.GlobalTheory.ShortDet.exists_short_integral_vector <;> assumption)
end
end

section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem exists_canonical_section_ne_zero_at : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ (hV : IsVariety₀ TF.X Z) (la : AllWt.Weight Dw), GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → letI := hV.1; ∀ y ∈ U₀ TF.X Z, ∃ g : H0 (str₀ TF.X Z) (tens (CanonLB.all (str₀ TF.X Z) (dimFlag Dw)).bundle (L₀ TF.X Z (la - FlagTan.kap Dw))) ⊤, y ∈ nonzeroLocus (toSec g) := by
  intro hP hN hNa hS hT hL E _ _ _ H Dw l Xo c TF Z hF hD hV la hg
  letI := hV.1
  intro y hy
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) with hstd_def
  set m : ℕ := (dimFlag Dw + 1).choose 2 + 1 with hm_def
  have hstd : GapGe 1 std := gapGe_stdWt Dw
  have hmu : GapGe 0 (la - FlagTan.kap Dw - m • std) := gapGe_sub_smul m _ hg
  letI := algebraΓOfHom (str₀ TF.X Z)
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL E H Dw l Xo c TF Z hF w hw
  obtain ⟨mu, hmu0, m', hm', hA⟩ := _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus hP hN hS hT E H Dw l Xo c TF Z hF std hstd y hy
  have C := common₀ TF.X Z
  have e₁ : m' • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) =
      cls (L₀ TF.X Z (m' • std - mu)) (isLB_L₀ TF.X Z _) + cls (L₀ TF.X Z mu) (isLB_L₀ TF.X Z mu) := by
    have h := cls_common_add (common₀ TF.X Z) (m' • std - mu) mu
    rw [sub_add_cancel] at h
    rw [← h]
    exact (cls_common_nsmul (common₀ TF.X Z) m' std).symm
  have e₂ : cls (L₀ TF.X Z (la - FlagTan.kap Dw)) (isLB_L₀ TF.X Z _) =
      m • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) + cls (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (isLB_L₀ TF.X Z _) := by
    have h := cls_common_add (common₀ TF.X Z) (m • std) (la - FlagTan.kap Dw - m • std)
    rw [add_sub_cancel] at h
    rw [h]
    exact congrArg (· + _) (cls_common_nsmul (common₀ TF.X Z) m std)
  obtain ⟨s, hs⟩ := GlobalTheory.T.effective_generation_canonical_nef_numberField hNa hN c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) hV.2.1 hV.2.2 hD
    (CanonLB.all _ _) (L₀ TF.X Z std) (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (L₀ TF.X Z (la - FlagTan.kap Dw))
    (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) m' m y (nef std (hstd.mono (by norm_num))) (nef _ hmu)
    (by omega) ⟨_, _, isLB_L₀ TF.X Z (m' • std - mu), isLB_L₀ TF.X Z mu, hm', e₁, hA, nef mu hmu0⟩ e₂
  refine ⟨H0.ofSec _ ⊤ s, ?_⟩
  rwa [show toSec (H0.ofSec (str₀ TF.X Z) ⊤ s) = s from H0.bijective_ofSec_top.1 (ofSec_toSec _)]
theorem globally_generated_on_open_of_weight_gap_ge : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  intro hP hG hQ hNa hPr hS hT hL E _ _ _ H Dw l Xo c TF Z r U hF hD la hg hC
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag E _ _ _ H Dw l Xo c TF Z hF
  have hpq : 1 ≤ Dw.p + Dw.q := by
    by_contra h
    have h0 : Dw.p + Dw.q = 0 := by omega
    have : dimFlag Dw = 0 := by
      unfold GlobalTheory.FlagTan.dimFlag
      rw [h0]
      simp
    omega
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hG E H Dw l Xo c K y hpq)
  intro y hy
  rw [mem_support_baseIdeal]
  push_neg
  obtain ⟨g, hgy⟩ := _root_.GlobalTheory.HSApp.exists_canonical_section_ne_zero_at hP hQ.nef hNa hS hT hL E H Dw l Xo c TF Z hF hD hV la hg y hy
  haveI := hV.1
  haveI : SmoothOfRelativeDimension (dimFlag Dw) (𝟙 (Y₀ TF.X Z) ≫ str₀ TF.X Z) := M.smooth
  obtain ⟨g', hg'⟩ := GlobalTheory.ModifRefl.exists_sec_canon_tens_pull_id c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) _ (isLB_L₀ TF.X Z _) g y hgy
  have hyM : (y : M.X) ∈ M.off := by
    rw [M.off_eq]
    exact hy
  obtain ⟨s, hs, hsy⟩ := _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp hP hG E H Dw l Xo c TF Z hF M ω la g' y hyM hg'
  exact ⟨s, hC.2 hs, hsy⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  first | exact @_root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | exact _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | (intros; apply _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge <;> assumption)
end
end
