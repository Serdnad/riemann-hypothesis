module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle008
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Imports
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle078
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowFormHeightOfArch
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralOfLintegral
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SpecializesIff
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.StCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound

@[expose] public section

section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem ChowFormHeightComparison₂.chow_form_height_bound (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  ChowFormHeightComparison₂.CF.chowFormHeight_of_arch (ChowFormHeightComparison₂.CF.stArch ChowFormHeightComparison₂.CF.stPts (ChowFormHeightComparison₂.CF.stCharts ChowFormHeightComparison₂.CF.stPts)) GlobalTheory.T.mahler_section_statement_holds h.p4.arExists
theorem ChowFormHeightComparison₂.chow_form_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun h => _root_.PositivityTheory.UnitarySelfGeneration.weil_height_inequality (_root_.ChowFormHeightComparison₂.chow_form_height_bound h) h
end
end

section

section
noncomputable section
namespace MainStatements.Tam.Plug
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
theorem tamagawa_pairs_compatible : _root_.GlobalTheory.T.CovolumeRatioIdentity := _root_.MainStatements.Tam.Plug.tamagawa_number_upper_bound
theorem tamagawa_pairs_product : _root_.GlobalTheory.T.FieldOfDefinitionDescentProp := fun _ => low
section
open ReciprocityTheory.L2DbarEstimates GlobalTheory.SupConstSize Real
end
end MainStatements.Tam.Plug
end
end
end

section

section
set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers
variable {R : Type} [CommRing R]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
theorem kodaira_spencer_direct_sum : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X),
    1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x →
    ∀ N : ι → HIx Dw (psiSet H) → K,
      (∀ k, IsKS (psiSet H) y (spMap (dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) →
      ∀ M : ι → K, IsKS (psiSet H) y (spMap (dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  intro Pr E _ _ _ H Dw l Xo c K _ _ y ι _ _ X hpq hXs hXy N hN M
  have P := Pr.p5
  have e₀ : ∀ m : ι → K, DeRham.epsRed K ≫ spMap (dir c m).toRingHom =
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom := fun m => by
    rw [← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => fst_dir (c := c) m z)
  have tan : IsTanX y (spMap (dir c M).toRingHom ≫ X) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hXs]
      unfold sOf
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun r => (dir c M).commutes _)
    · rw [← Category.assoc, ← hXy]
      exact congrArg (· ≫ X) (e₀ M)
  obtain ⟨M₀, A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, what₂⟩ :=
    _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent Pr E H Dw l Xo c K y _ hpq tan
  obtain ⟨C, _, πC, hC⟩ := exists_isGrpPullback Xo.univ.t.G X
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have aC := PolPull.isAbelianScheme_of_isGrpPullback hU hC
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hC.1 hg
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hL := (P.2.1 K A _ hA gA).1
  obtain ⟨φ, hφ, eφ⟩ : ∃ φ : A'.left ⟶ C.left, IsGrpPullback A' C (spMap (dir c M).toRingHom) φ ∧ φ ≫ πC = π' := by
    have w : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ spMap (dir c M).toRingHom) ≫ X :=
      hπ'.1.w.trans (Category.assoc _ _ _).symm
    exact ⟨hC.1.lift _ _ w, hC.cancel (hπ'.congr rfl (hC.1.lift_fst _ _ w).symm) (hC.1.lift_snd _ _ w),
      hC.1.lift_fst _ _ w⟩
  have h₀ := (hi.comp hφ).congr (e₀ M) rfl
  refine ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, fun τ a => ?_⟩
  obtain ⟨-, -, f, hf, hd, -⟩ := what₂ τ a
  obtain ⟨gs, hgs⟩ := exists_isFilLift_dir P aC gC h₀ hf
  have row : ∀ k, ∃ w, IsLieComb (fun b => N k ⟨τ, a, b⟩) (ub τ.1) w ∧ DeRham.IsLieImage (gs k) w := fun k => by
    obtain ⟨B, _, χ, hχ⟩ := exists_isGrpPullback C (spMap (dir c (Pi.single k (1 : K))).toRingHom)
    have w : (i ≫ φ) ≫ C.hom = (A.hom ≫ DeRham.epsRed K) ≫ spMap (dir c (Pi.single k (1 : K))).toRingHom := by
      rw [Category.assoc _ (DeRham.epsRed K), e₀]
      exact h₀.1.w
    have sq : hχ.1.lift _ _ w ≫ χ = i ≫ φ := hχ.1.lift_fst _ _ _
    have hj : IsGrpPullback A B (DeRham.epsRed K) (hχ.1.lift _ _ w) :=
      hχ.cancel (h₀.congr (e₀ _).symm sq.symm) (hχ.1.lift_snd _ _ _)
    obtain ⟨v, hc, hv⟩ := (hN k).row P hj hπ (hχ.comp hC)
      (by rw [← Category.assoc, sq, Category.assoc, eφ, hiπ]) hpol hu hl τ a hf hd
    obtain ⟨v', hv', -⟩ := hL.1 (gs k)
    have fl := hgs (Pi.single k 1) B χ _ hj hχ sq
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at fl
    obtain rfl := IsKSValue.unique P (PolPull.isAbelianScheme_of_isGrpPullback aC hχ)
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hχ.1 gC) hv ⟨_, fl, hv'⟩
    exact ⟨_, hc, hv'⟩
  choose w hwc hwl using row
  let e := (Fintype.equivFin ι).symm
  refine ⟨lieComb (fun q => M (e q)) (fun q => w (e q)), ?_, f, hf, hd, _, ?_,
    isLieImage_lieComb _ (f := fun q => gs (e q)) fun q => hwl _⟩
  · obtain ⟨V, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
    choose n hn using fun σ k => (htan _).1 (y.tan σ k)
    have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → V) (w : epsR K ⟶ A),
        (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
      fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
    have hun : ∀ j, (ub τ.1 j).left ≫ π = v (n τ.1 j) := fun j => (hu _ j).trans (hn _ j).symm
    rw [key _ _ _ _ hun, (key _ _ _ _ fun q => (key _ _ _ _ hun).1 (hwc (e q))).1 (isLieComb_lieComb _ _),
      e.sum_comp fun k => M k • ∑ j, N k ⟨τ, a, j⟩ • n τ.1 j]
    congr 1
    simp only [Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  · rw [e.sum_comp fun k => M k • gs k]
    exact hgs M A' φ i hi hφ rfl
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.kodaira_spencer_of_direct_sum_deformation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum <;> assumption)
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogPole
theorem exists_kodaira_spencer_comparison_log_pole : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  intro PP E _ _ _ H Dw l Xo c TF
  obtain ⟨s, hs0, hcore⟩ := _root_.GlobalTheory.T.cech_kodaira_spencer_class_constant PP
  refine ⟨s, hs0, ?_⟩
  intro U n e v hv D Θ hΘ K _ _ P hU hP y' hU' hy' hev
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, g, hπ, hπ', hi, hpol, hu, hbl, hrow, hA, hgA, hA', hgA', hL⟩ :=
    _root_.GlobalTheory.T.kodaira_spencer_map_compatibilities PP E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  have hC := GlobalTheory.T.cechDeformation_gluing_of_logKodairaSpencer E H Dw l Xo c TF U n e v hv D Θ hΘ K P hU hP y' hU' hy' hev A A' π π' i ub h hπ hπ' hi hu
  have hbal := GlobalTheory.T.cechKodairaSpencerMatrix_eq_zero_off_conj_blocks E H Dw l Xo c TF U n e v hv D Θ hΘ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK := hcore K A A' i h g hA hgA hA' hgA' _ hL ψ hpol n (fun a => ub (e.symm a).1 (e.symm a).2)
    (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) (fun a => (hbl _ _).1) hC
    (fun b => hb (e.symm b)) (fun b => hbl _ _)
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, ψ, ub, hb, hπ, hπ', hi, hpol, hu, fun σ k => hbl σ k,
    fun τ a => ?_⟩
  exact GlobalTheory.T.kodairaSpencerRow_of_kodairaSpencerValue_hodgeFil E H Dw K A A' i h hA ψ ub hb n e _ (s : K) (fun σ k => (hbl σ k).1)
    (fun a b hab => by simp only [Matrix.of_apply, hbal a b hab, map_zero]) hK τ.1 a (hrow τ a)
end GlobalTheory.LogPole
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem _root_.GlobalTheory.T.kodaira_spencer_comparison_along_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  first | exact @_root_.GlobalTheory.LogPole.exists_kodaira_spencer_comparison_log_pole | exact _root_.GlobalTheory.LogPole.exists_kodaira_spencer_comparison_log_pole | (intros; apply _root_.GlobalTheory.LogPole.exists_kodaira_spencer_comparison_log_pole <;> assumption)
end
end
