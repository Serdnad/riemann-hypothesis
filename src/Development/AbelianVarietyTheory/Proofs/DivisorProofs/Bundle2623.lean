module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadEigenFrameLieAlgebraToroidalComponen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.LieGram

theorem form_eq_hermForm {K : Type} [Field K] {n g m : ℕ} (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin n → K)) (σ : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Wc : Fin n → Fin g → ℂ)
    (hform : ∀ i j, h.form σ (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (Wc j) (Wc i))
    (v : Fin m → Fin n → K) (i j : Fin m) :
    h.form σ (v i) (v j) = Real.pi * hermForm Hm (∑ k, σ (v j k) • Wc k) (∑ k, σ (v i k) • Wc k) := by
  have hsum : ∀ a : Fin n → K, a = ∑ k, a k • Pi.single k (1 : K) := fun a => by
    ext t; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hsum (v i), hsum (v j)]
  rw [GlobalTheory.HermFamFrame.form_sum_left]
  simp_rw [GlobalTheory.HermFamFrame.form_sum_right, hform]
  simp only [hermForm, Matrix.mulVec_sum, Matrix.mulVec_smul, star_sum, star_smul, dotProduct_sum,
    sum_dotProduct, smul_dotProduct, dotProduct_smul, Finset.mul_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def]
  ring

theorem gram_det_re_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ), GoodEmb c (σ.comp (algebraMap c.F K)) → ∀ (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (k : (U (σ.comp (algebraMap c.F K))).Comp) (w : ((U (σ.comp (algebraMap c.F K))).X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt (U (σ.comp (algebraMap c.F K))) k w) (Wu : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnitAt W), z.x = ((U (σ.comp (algebraMap c.F K))).un k w).x → ∀ (C : Fin (Dw.mult ρ) → Fin (Dw.mult ρ) → CAt (σ.comp (algebraMap c.F K))), (∀ i, IsCombAt ((U (σ.comp (algebraMap c.F K))).un k w).x (((U (σ.comp (algebraMap c.F K))).un k w).u ρ) (C i) (z.u ρ i)) → (h.gram σ v).det.re = (Matrix.of fun i j : Fin (Dw.mult ρ) => (Real.pi : ℂ) * hermForm Wu.Hm (∑ l, toC (C j l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ)) (∑ l, toC (C i l) • Pi.single (W.e.symm ⟨ρ, l⟩) (1 : ℂ))).det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL K _ _ _ y B t₀ m1 m2 F h hH ρ v hv σ hσ φ hφ z hz k w W Wu hzx C hC
  obtain ⟨Q, ψ, v', u, Hm, χ, Wc, hfib, hAH, hvec, hform⟩ := hH σ
  obtain ⟨T, m, u', χ', hA', hw'⟩ := GlobalTheory.T.exists_fibre_uniformisation_appellHumbert_unit E H Dw l Xo c r _ _ hL.pos k w W Wu ρ z hzx C hC
  obtain ⟨f, hf, hLB, hq⟩ := GlobalTheory.T.complex_fibre_iso_universal_group_framed_point E H Dw l Xo c K y B t₀ m1 m2 F ρ v hv σ φ hφ z hz Q ψ v' hfib (fun i => (hvec i).1) T m
  choose w' hw'1 hw'2 using hw'
  have htan : ∀ i, IsTangent (v' i) := fun i => GlobalTheory.IsVecOver.isTangent hfib.2.1 (hvec i).1 (F.basis.1 i)
  obtain ⟨Lm, hL1, hL2⟩ := GlobalTheory.T.exists_linear_lift_preserving_appellHumbert_form Q T.pol W.g u Hm χ u' Wu.Hm χ' hAH hA' f hf hLB F.P₀.g v' Wc
    (fun i => ⟨htan i, (hvec i).2⟩) (Dw.mult ρ) (fun i k => σ (v i k)) w' _ hw'2
    (fun i q hq' => hq i q hq' (w' i) (hw'1 i))
  congr 2
  ext i j
  simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply]
  rw [form_eq_hermForm h σ Hm Wc hform v i j, ← hL1, hL2, hL2]

end GlobalTheory.LieGram
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ZConv

theorem zconv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∃ z : GA D (G.V (.grid i j)) →₀ ℂ, zdeg z ≠ 0 ∧
    (∀ g, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j)))) := by
  intro D T L sc G hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hB g₁
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, hv⟩ := hT M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ := GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ g u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro g u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.T.smallRouteKernel_left_invariant_rationalUnitary hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))

  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  have hVl := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  haveI : IsFiniteMeasure ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hVl.1 hVl.2).ne
  have hcont := GlobalTheory.T.continuous_translates_kernel_route_small_vertex hL W B ρ t i j Θ Θ' hΘ g₁ z
  have hRD := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨Bd, hBd⟩ := hRD.decay k
  refine ⟨z, hz, fun g => ?_, ?_⟩
  · exact Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
      (.of_forall fun u => hbd g u)
  · have h0 : (0 : ℝ) ≤ |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k :=
      mul_nonneg (mul_nonneg (abs_nonneg C₀) (abs_nonneg C)) (pow_nonneg (by have := GlobalTheory.Grow.height_pos _ g₁; positivity) k)
    refine Integrable.of_bound ((hRD.continuous.comp continuous_fst).mul hcont).aestronglyMeasurable
      (|C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * Bd) (.of_forall fun p => ?_)
    rw [norm_mul]
    calc ‖F p.1‖ * ‖translates z (kerSmall W Θ' p.1 g₁) p.2‖ ≤
          ‖F p.1‖ * (|C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ p.1 * GlobalTheory.Grow.height _ g₁) ^ k) :=
          mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)
      _ = |C₀| * |C| * (2 * GlobalTheory.Grow.height _ g₁) ^ k * (‖F p.1‖ * GlobalTheory.Grow.quotHeight _ p.1 ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBd _) h0
end GlobalTheory.ZConv

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


theorem _root_.GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (a : Γ(TF.Y.X, U.1)), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U → (∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) → ∃ z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ⟶ Y₀ TF.X Z, ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z₁ ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r, ev (z₁ ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) (MvPolynomial.C r)) ∧ ((z₁ ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))))).Nonempty ∧ ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (σ : E →+* ℂ), ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧ ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _ (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) = ∑ m, b i m * ev (spMap ψ ≫ z₁) W hW ((L σ * N σ) m j) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section_away | exact GlobalTheory.LogPole.exists_cell_section_away | (intros; apply GlobalTheory.LogPole.exists_cell_section_away <;> assumption)
end

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

namespace GlobalTheory.FrameSpread

open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {F : EigFrame Z φ x}
    {F' : EigFrame Z φ' x'} {F'' : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''} (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) a F')
    (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (b.comp a) F'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F' embτ basisIdx) b F'' := fun τ i => by
  rw [h2 τ i, h1 τ i, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.dualMap_comp]

end

theorem unitAt_det_co : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk x ≫ s₀ TF.Y Z = spMap φ → ∃ U : (X₀ TF.Y Z).Opens, x ∈ U ∧ ∀ y ∈ U, ∀ (φ' : c.F →+* (X₀ TF.Y Z).presheaf.stalk y) (f' : GlobalTheory.ShFam.EigFrame TF.Y φ' ((X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι)) (φK : c.F →+* (X₀ TF.Y Z).functionField) (fK fK' : GlobalTheory.ShFam.EigFrame TF.Y φK ((X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)), (X₀ TF.Y Z).fromSpecStalk y ≫ s₀ TF.Y Z = spMap φ' → (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ s₀ TF.Y Z = spMap φK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK → (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) (algebraMap _ (X₀ TF.Y Z).functionField) fK' → ∀ τ, UnitAt y (fK'.co fK τ).det := by
  intro E _ _ _ H Dw l Xo c TF Z _ x φ f hφ
  haveI : IsIso (genι TF.Y) := GlobalTheory.VarFlag.isIso_genι
  let e : X₀ TF.Y Z ⟶ gen TF.Y := (barComp TF.Y Z).ι ≫ inv (genι TF.Y)
  have he : e ≫ genι TF.Y = (barComp TF.Y Z).ι := by simp [e]
  have hstrY : genStr TF.Y = genι TF.Y ≫ TF.Y.s := by
    have h0 : genι TF.Y ≫ TF.Y.s = genStr TF.Y ≫ spMap (RingHom.id c.F) := pullback.condition
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    rw [h1, Category.comp_id] at h0
    exact h0.symm
  obtain ⟨U, hU, φU, F, hxU, hUstr, -⟩ :=
    GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y (e x)
  let ψ : ∀ p : X₀ TF.Y Z, e p ∈ U → (Γ(gen TF.Y, U) →+* (X₀ TF.Y Z).presheaf.stalk p) := fun p hp =>
    (e.stalkMap p).hom.comp ((gen TF.Y).presheaf.germ U (e p) hp).hom
  have hψ : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ e = spMap (ψ p hp) ≫ hU.fromSpec := by
    intro p hp
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hU.fromSpecStalk_eq_fromSpecStalk hp, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  have hmono : ∀ {R : Type} [CommRing R] (a b : Γ(gen TF.Y, U) →+* R),
      spMap a ≫ hU.fromSpec = spMap b ≫ hU.fromSpec → a = b := fun a b h =>
    GlobalTheory.ShFam.EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 h)
  have hring : ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X₀ TF.Y Z) (ρ : c.F →+* R) (a : Γ(gen TF.Y, U) →+* R),
      q ≫ s₀ TF.Y Z = spMap ρ → q ≫ e = spMap a ≫ hU.fromSpec → ρ = a.comp φU := by
    intro R _ q ρ a h1 h2
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h1, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hUstr, ← Category.assoc (spMap a), ← h2, hstrY]
    simp only [Category.assoc]
    rw [← Category.assoc e, he]
  have hpt : ∀ p hp, (X₀ TF.Y Z).fromSpecStalk p ≫ (barComp TF.Y Z).ι = spMap (ψ p hp) ≫ hU.fromSpec ≫ genι TF.Y := by
    intro p hp
    rw [← he, ← Category.assoc, hψ p hp, Category.assoc]
  have hgen : ∀ p : X₀ TF.Y Z, (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk p :=
    fun p =>
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec (X₀ TF.Y Z)).specializes (Set.mem_univ p))).symm
  obtain ⟨Fx, hFx⟩ := F.exists_isMap (ψ x hxU) (hring _ φ _ hφ (hψ x hxU)) (hpt x hxU)
  have hWx : ∀ τ, UnitAt x (algebraMap _ (X₀ TF.Y Z).functionField (Fx.co f τ).det) :=
    fun τ => ⟨_, EigFrame.isUnit_det_co Fx f τ, rfl⟩
  choose W hxW hW using fun τ => (hWx τ).exists_nhds
  refine ⟨⟨(e ⁻¹ᵁ U : Set (X₀ TF.Y Z)) ∩ ⋂ τ, (W τ : Set (X₀ TF.Y Z)),
    (e ⁻¹ᵁ U).isOpen.inter (isOpen_iInter_of_finite fun τ => (W τ).isOpen)⟩,
    ⟨hxU, Set.mem_iInter.2 hxW⟩, ?_⟩
  rintro y ⟨hyU, hyW⟩ φ' f' φK fK fK' hφ' hφK hfK hfK' τ
  rw [Set.mem_iInter] at hyW
  have hyU' : e y ∈ U := hyU
  obtain ⟨Fy, hFy⟩ := F.exists_isMap (ψ y hyU') (hring _ φ' _ hφ' (hψ y hyU')) (hpt y hyU')
  have hKp : ∀ p hp, spMap ((algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField).comp (ψ p hp)) ≫
      hU.fromSpec = (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ e := by
    intro p hp
    rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk p) (X₀ TF.Y Z).functionField)
      (ψ p hp), Category.assoc, ← hψ, ← Category.assoc, ← hgen]
  have hK : (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU') =
      (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (ψ x hxU) :=
    hmono _ _ ((hKp y hyU').trans (hKp x hxU).symm)
  have hKpt := (hKp y hyU').symm
  obtain ⟨FK, hFK⟩ := F.exists_isMap
    ((algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField).comp (ψ y hyU'))
    (x' := (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι)
    (hring _ φK _ hφK hKpt) (by rw [← he]; exact (reassoc_of% hKpt) (genι TF.Y))
  have hFyK : Fy.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFy hFK
  have hFxK : Fx.IsMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) FK :=
    isMap_trans hFx (by rw [← hK]; exact hFK)
  have hy : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk y) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk y ≫ (barComp TF.Y Z).ι := by
    rw [hgen y, Category.assoc]
  have hx : (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z)) ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField) ≫ (X₀ TF.Y Z).fromSpecStalk x ≫ (barComp TF.Y Z).ι := by
    rw [hgen x, Category.assoc]
  have e1 := EigFrame.IsMap.co (τ := τ) hfK' hFyK hy
  have e2 := EigFrame.IsMap.co (τ := τ) hFxK hfK hx
  have dmap : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R),
      (M.map g).det = g M.det := fun g _ M => (RingHom.map_det g M).symm
  rw [← EigFrame.co_mul fK' FK fK τ, Matrix.det_mul, e1, dmap]
  refine UnitAt.mul ⟨_, EigFrame.isUnit_det_co f' Fy τ, rfl⟩ ?_
  convert hW τ y (hyW τ) using 1
  erw [e2]
  exact dmap _ _

end GlobalTheory.FrameSpread
end

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

theorem _root_.GlobalTheory.T.exists_spread_eigenFrame_lieAlgebra_toroidalComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (_ : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) ∧ (∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) := by
  first | exact @GlobalTheory.LogKSDiv.exists_spread_eigFrame | exact GlobalTheory.LogKSDiv.exists_spread_eigFrame | (intros; apply GlobalTheory.LogKSDiv.exists_spread_eigFrame <;> assumption)
end

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

theorem _root_.GlobalTheory.T.exists_spread_genericEigenFrame_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ (GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι)), GlobalTheory.LogKSDiv.genPt TF Z ≫ s₀ TF.Y Z = spMap φ₀ → ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι ∧ (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧ (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧ (∀ τ i, f₀.v τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧ ∀ (a : 𝓞 E) (k : Fin n), IsCombAtG TF.Y.t (LogKS.chart U) v ((Matrix.diagonal fun j => constFn TF.Y.s U.1 (embK c (e.symm j).1 a)) k) (v k ≫ (TF.Y.t.act.act a).left) := by
  first | exact @GlobalTheory.LogKSDiv.spread_genFrame | exact GlobalTheory.LogKSDiv.spread_genFrame | (intros; apply GlobalTheory.LogKSDiv.spread_genFrame <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem tri_of_isFrameAt {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {S : Type} [CommRing S] {φ : c.F →+* S} (z : Sp S ⟶ Z) (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k)
    (hz' : ⊤ ≤ z ⁻¹ᵁ F.U k') (g g' : EigFrame Y φ (z ≫ π)) (hg : IsFrameAt F z k hz g)
    (hg' : IsFrameAt F z k' hz' g') : ∃ d, g.Tri (RingHom.id S) g' d := by
  have hh := GlobalTheory.FlagMod.le_preimage_inf hz hz'
  have h1 : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  refine ⟨fun τ i => F.TAt k k' z hh (some ⟨τ, i⟩), by rw [h2, Category.id_comp], rfl, fun τ i =>
    ⟨fun j => (F.B k k' τ).map (GlobalTheory.FlagMod.ev z _ hh) j i, rfl, fun j hj => F.B_map_tri k k' τ _ hj, ?_⟩⟩
  simp only [h1, Category.id_comp]
  have e : (fun j => g.v τ j) = fun j => (tv (F.vecAt k z hz rfl τ j)).left := funext (hg τ)
  rw [e, hg' τ i, GlobalTheory.LieMet.isComb_iff]
  exact F.vecAt_eq_sum k k' z hz hz' hh rfl τ i

end GlobalTheory.VarFlag

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_congr {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x x' : Sp K ⟶ Y.X} (h : x = x') (g : EigFrame Y φ x) (g' : EigFrame Y φ x')
    (hv : ∀ τ i, g.v τ i = g'.v τ i) (p : Sp K ⟶ C.Y.X) : C.Carries p g ↔ C.Carries p g' := by
  subst h
  obtain ⟨v, a1, a2, a3⟩ := g
  obtain ⟨v', b1, b2, b3⟩ := g'
  have e : v = v' := funext fun τ => funext fun i => hv τ i
  subst e
  rfl

theorem carries_of_tri {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {g' : EigFrame Y φ' x'}
    {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ} (h : g.Tri (RingHom.id K) g' d) {p : Sp K ⟶ C.Y.X}
    (hp : C.Carries p g) : C.Carries p g' := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  exact ⟨y, ψ, φ₁, f, t, _, h1, h2, GlobalTheory.ShFam.FlatSec.tri_trans h3 h⟩

theorem carries_over {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {g : EigFrame Y φ x} {p : Sp K ⟶ C.Y.X} (hp : C.Carries p g) :
    p ≫ C.π ≫ genι Y = x := by
  obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hp
  rw [h1, Category.assoc, ← h3.1]

theorem uniq_rel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ GlobalTheory.Toroidal.gen Y) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ GlobalTheory.Toroidal.genStr Y = spMap χ → ∀ g : GlobalTheory.ShFam.EigFrame Y χ (x ≫ GlobalTheory.Toroidal.genι Y), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g) → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z), ∃! p : Sp K ⟶ C.Y.X, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hlifts hbar K _ z
  set zz := z ≫ GlobalTheory.CompHS.inc₀ X Z with hzz

  let φ : c.F →+* K := (Spec.preimage (zz ≫ X.π ≫ Y.s)).hom
  have hφ : zz ≫ X.π ≫ Y.s = spMap φ := (Spec.map_preimage _).symm

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover zz
  obtain ⟨g, hg⟩ := hFE K φ zz k hk hφ

  let xg : Sp K ⟶ gen Y := zz ≫ X.π ≫ inv (genι Y)
  have hxg : xg ≫ genι Y = zz ≫ X.π := by simp [xg]
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hstr : xg ≫ genStr Y = spMap φ := by
    have e : genStr Y = genι Y ≫ Y.s := by
      calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
        _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
    rw [e, ← Category.assoc, hxg, Category.assoc, hφ]

  have hr : Set.range xg ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    refine (hbar _).1 ?_
    have e : genι Y (xg a) = X.π (GlobalTheory.CompHS.inc₀ X Z (z a)) := by
      rw [← Scheme.Hom.comp_apply, hxg]; rfl
    rw [e]
    have hm : GlobalTheory.CompHS.inc₀ X Z (z a) ∈ X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z := by
      have := (Scheme.Opens.range_ι (X.π ⁻¹ᵁ GlobalTheory.CompHS.barComp Y Z)).le ⟨z a, rfl⟩
      exact this
    exact hm
  let x' := IsOpenImmersion.lift j xg hr
  have hx' : x' ≫ j = xg := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ (xg ≫ genι Y), ∀ τ i, g0.v τ i = g.v τ i := by
    rw [hxg]; exact ⟨g, fun _ _ => rfl⟩
  obtain ⟨p, ⟨hp1, hp2⟩, hpu⟩ := hlifts K φ xg x' hx' hstr g0
  refine ⟨p, ⟨φ, k, hk, g, hφ, hg, (carries_congr C hxg g0 g hg0 p).1 hp2⟩, ?_⟩
  rintro p' ⟨φ', k', hk', g', hφ', hg', hc'⟩
  have e : φ' = φ := by
    have h0 : spMap φ' = spMap φ := hφ'.symm.trans hφ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst e
  obtain ⟨d, hd⟩ := tri_of_isFrameAt X.F zz k' k hk' hk g' g hg' hg
  have hc : C.Carries p' g := carries_of_tri C hd hc'
  have hc0 : C.Carries p' g0 := (carries_congr C hxg g0 g hg0 p').2 hc
  refine hpu p' ⟨?_, hc0⟩
  have h1 : p' ≫ C.π = xg := by
    rw [← cancel_mono (genι Y), Category.assoc]
    exact carries_over C hc0
  rw [← cancel_mono j, Category.assoc, ← hπ, h1, hx']

end GlobalTheory.VarFlag
end
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.dense_flagBundle_preimage_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | exact GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage | (intros; apply GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem _root_.GlobalTheory.T.eigenbundleFrameAffineAtlas_isFlagFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p), IsCover (RingHom.id c.F) Y.s A.V A.alpha A.cv A.Dv := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.atlas_isCover | exact GlobalTheory.FlagMod.FieldFlag.atlas_isCover | (intros; apply GlobalTheory.FlagMod.FieldFlag.atlas_isCover <;> assumption)
end
