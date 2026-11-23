module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle055
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (pairDet hasChars_iff)

theorem hasChars_frame_of_hasAF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X f xs r hAF hr
  have hp0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
    have : X.v (p : X.C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hxs0 : (0 : ℝ) < (xs : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 r) hr
  have hxs : xs ≠ 0 := fun h => by rw [h] at hxs0; simp at hxs0
  obtain ⟨-, χ, hχ, hmin⟩ := exists_flag_characters X.C X.v X.O X.ints _ _ _ _ xs hAF hxs
  let lf : Fin (rk f) → Fin (chD Ch.ch) → X.C := fun b j =>
    algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE (rk_le f) b)) j)
  have hl : ∀ b, IsCharLog (fgl Ch X) (lf b) := fun b =>
    GlobalTheory.T.chart_character_is_logarithm E H Dw l Xo c p T io y Ch X _ (hχ _)
  have hdet : pairDet lf (frame Ch X f) = algebraMap X.O X.C (Matrix.of fun a b : Fin (f.2.val + 1) =>
      ∑ j, X.ι (Ch.uvecT ⟨f.1, Fin.castLE f.2.isLt a⟩ j) *
        ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE f.2.isLt b)) j).det := by
    rw [RingHom.map_det]
    unfold pairDet
    congr 1
    ext a b

    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, frame, lieVec, jX,
    RingHom.comp_apply, X.comp, lf]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hm := hmin f.2
  rw [← hdet] at hm
  set D := pairDet lf (frame Ch X f) with hD
  have hDpos : (0 : ℝ) < (X.v D : ℝ) := lt_of_lt_of_le hxs0 (by exact_mod_cast hm)
  have hD0 : D ≠ 0 := fun h => by rw [h, map_zero] at hDpos; simp at hDpos
  have hlog := log_v_p_neg X
  have hval : ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) ≤ r := by
    have h1 : r * Real.log (X.v (p : X.C) : ℝ) ≤ Real.log (X.v D : ℝ) := by
      rw [← Real.log_rpow hp0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hp0 r) (hr.trans (by exact_mod_cast hm))
    have h2 := mul_le_mul_of_nonpos_left h1 (inv_lt_zero.2 hlog).le
    rwa [← mul_assoc, mul_comm _ r, mul_assoc, inv_mul_cancel₀ hlog.ne, mul_one] at h2
  have hvD : vX_vp X D = (((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ) : ℝ) : WithTop ℝ) :=
    vX_vp_apply X hD0
  refine ⟨(hasChars_iff (isSatFrame_frame Ch X f) _).2 ⟨lf, hl, ?_⟩, fun k => ?_⟩
  · rw [← hD, hvD]
    exact EReal.coe_le_coe_iff.2 hval
  · refine (nuFac_le Ch X f k).trans ?_
    refine (GlobalTheory.FGDepth.CharBound.detDepth_le_char X.C (vX_vp X) (rk f) _ k (fgl Ch X) (frame Ch X f) lf hl).trans ?_
    have e : Matrix.det (Matrix.of fun a b => ∑ e, lf b e * frame Ch X f a e) = D := rfl
    rw [e, AddValuation.map_pow, hvD, ← WithTop.coe_nsmul, nsmul_eq_mul]
    show ((k * ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) : ℝ) : EReal) ≤ _
    exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg k))

end GlobalTheory.RefSum
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.gridSquare_skewSumSpace_isSkewHermitianSelfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (e : Num G i j) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
      Spc.IsSkew D.sp.cm.sig B
        (Spc.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) Λ (fun w => (blk e (W.cart (.grid (i : ℕ) ((j : ℕ) + 1)) (τf w)) (W.cart (.grid ((i : ℕ) + 1) (j : ℕ)) (τf w))).map conj) bas)
        ((spW G i j).rank + (spW₁ G i j).rank - ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2))
        ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) := by
  first | exact @GlobalTheory.SkewLat.bigSpace_isSkew | exact GlobalTheory.SkewLat.bigSpace_isSkew | (intros; apply GlobalTheory.SkewLat.bigSpace_isSkew <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_linearModel_intertwiner_goodSplitPlace : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ), Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι := by
  first | exact @GlobalTheory.LinBarExist.exists_isLinBar | exact GlobalTheory.LinBarExist.exists_isLinBar | (intros; apply GlobalTheory.LinBarExist.exists_isLinBar <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.lowerRank_cuspForms_detWeight_oneComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ, (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧ ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  first | exact @GlobalTheory.ShareOn.lowerRank_oneComponent | exact GlobalTheory.ShareOn.lowerRank_oneComponent | (intros; apply GlobalTheory.ShareOn.lowerRank_oneComponent <;> assumption)
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

open GlobalTheory.LamT (CMPt)

theorem _root_.GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (AddMonoidAlgebra.coeff G μ) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  first | exact @GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | exact GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det | (intros; apply GlobalTheory.FrameCoeffLoc.coeff_mul_prod_mem_det <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem top_le_fromSpecStalk {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens) (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem val_fromSpecStalk {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B ⊤)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y (memTop y) hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  have hV : y ∈ (⊤ : Y.Opens) ⊓ B.U i := memInf (memTop y) hi
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ ((⊤ : Y.Opens) ⊓ B.U i) := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open (IsOpen.inter isOpen_univ (B.U i).isOpen) hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_congr' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr'' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _



theorem evI_ofSpace_eq_prod_mul_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (x₀ : Sp T.Fr ⟶ Y₀ X Z), (X.ptY y'.1 = x₀ ≫ inc₀ X Z) → ∀ (j' : (L₀ X Z la).ι) (hO : ⊤ ≤ x₀ ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)) (hj : ⊤ ≤ x₀ ⁻¹ᵁ (L₀ X Z la).U j') (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit)) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr (j' PUnit.unit) (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) = (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix).val * H0.val x₀ j' hO hj w.1 := by
  intro E _ _ _ H Dw l Xo c Y X Z r U la w T io y' x₀ hx j' hO hj hz Q t hQ ht
  letI := io.toAlgebra
  let fS : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0) := ⟨_, cusp_le_secZ Z U la (ofSpace X Z U la w).2⟩
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf fS hOf hQ ht
  show evR Xo c fS.1 y'.1 = _
  rw [a]
  congr 1
  have hx' : X.pt y'.1 ≫ X.inc = x₀ ≫ inc₀ X Z := (X.pt_inc _).trans hx
  have hU₀ : ⊤ ≤ x₀ ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  have hk' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (j' PUnit.unit) := hx' ▸ hz
  have hO' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hx' ▸ hOf
  rw [val_congr' hx' _ hOf hO' hz hk']
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) x₀ j' hU₀ hj hO' hk' (secOf X _ fS)
  rw [← b1]
  have hs : H0.pull (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X _ fS) = H0.restr le_top w.1 := cuspSec_ofSpace X Z U la w
  rw [hs, val_restr'' le_top x₀ j' hO hU₀ hj]



theorem germ_eq_unit_mul_evI_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (y : Y₀ X Z) (T : CDVR)
    (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z)
    (j' : (L₀ X Z la).ι) (hj' : y ∈ (L₀ X Z la).U j') :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) =
      algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) := by
  letI := io.toAlgebra
  have hk : inc₀ X Z y ∈ X.F.U (j' PUnit.unit) := mem_pull.1 hj'
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hO := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ⊤ (memTop y)
  have hj := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ((L₀ X Z la).U j') hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j' PUnit.unit) := by
    have := top_le_fromSpecStalk y g (inc₀ X Z ⁻¹ᵁ X.F.U (j' PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j' PUnit.unit) hz
  have e2 := evI_ofSpace_eq_prod_mul_val X Z U la w T io y' _ hx₀ j' hO hj hz Q t hQ ht
  have e1 := val_fromSpecStalk y j' hj' ((algebraMap T.V T.Fr).comp g) w.1 hO hj
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j' PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ GlobalTheory.AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, e1, Units.coe_map, RingHom.comp_apply, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one,
    one_mul]

end GlobalTheory.HSApp
end
end

section

noncomputable section

section WeilOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.WeilOver

open GlobalTheory.LatVac GlobalTheory.PlaceDatum GlobalTheory.PlaceModel Formalism.IndefR.Mult

variable {D : D7}

theorem exists_weil_over_of_clauses (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) {Γ : Type} [Group Γ] [Fintype Γ]
    {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hlev : R.toLevCh.Is A.μ0) (hch : R.IsChain) (hmod : R.IsModels)
    (sc : Consts) (G : GridData R.toLevCh sc) : ∃ W : G.Weil, W.Over R := by
  have hψ := (hch.ωX A.μ0).std
  obtain ⟨W, hWψ⟩ := GlobalTheory.T.exists_weilRepresentation_vacuum_cosetVectors_grid hW D T R.toLevCh A.μ0 hlev sc G R.ψ hψ
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have lt : ∀ j, j < D.R.m → G.V (.grid 0 j) = Yc D j := fun j h => congrArg LSp.sp (colY_lt R.toLevCh h)
  have top : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m R.toLevCh)
  have h1 : ∀ X : Node, ∃ s B, (X.InRange D.R.m → IsMaj (G.V X) s B) ∧
      (∀ j, j < D.R.m → X = .grid 0 j → HEq s (cart (R.MY j)) ∧ HEq B (onb (R.MY j))) ∧
      (X = .grid 0 D.R.m → HEq s (cart R.MX) ∧ HEq B (onb R.MX)) := fun X => by
    by_cases h : ∃ j, j < D.R.m ∧ X = .grid 0 j
    · obtain ⟨j, hj, rfl⟩ := h
      obtain ⟨s, B, a, b⟩ := exists_maj_heq (lt j hj) (R.MY j)
      refine ⟨s, B, fun _ => a, fun k _ hk => ?_, fun hk => ?_⟩
      · cases hk; exact b
      · exact absurd (Node.grid.inj hk).2 hj.ne
    by_cases h' : X = .grid 0 D.R.m
    · subst h'
      obtain ⟨s, B, a, b⟩ := exists_maj_heq top R.MX
      exact ⟨s, B, fun _ => a, fun k hk e => absurd ⟨k, hk, e⟩ h, fun _ => b⟩
    exact ⟨W.cart X, W.onb X, fun hX τ => ⟨W.cart_is X hX τ, W.onb_is X hX τ⟩, fun k hk e => absurd ⟨k, hk, e⟩ h,
      fun e => absurd e h'⟩
  have h2 : ∀ p : Pair T, ∃ ω, (p.InRange D.R.m → IsWeilDatumO R.ψ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) ω) ∧
      (∀ t k, k + 1 < D.R.m → p = .mu t 0 k → HEq ω (R.ωY t k)) ∧
      (∀ t k, k + 1 = D.R.m → p = .mu t 0 k → HEq ω (R.ωX t)) := fun p => by
    by_cases h : ∃ t k, k + 1 < D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h
      have := hch.ωY t k hk
      rw [← G.chr_mu_zero t hk.le] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (lt k (by omega)) (lt (k + 1) hk) this
      refine ⟨ω, fun _ => a, fun t' k' _ e => ?_, fun t' k' hk' e => ?_⟩
      · cases e; exact b
      · cases e; omega
    by_cases h' : ∃ t k, k + 1 = D.R.m ∧ p = .mu t 0 k
    · obtain ⟨t, k, hk, rfl⟩ := h'
      have e0 := G.chr_mu_zero t hk.le
      rw [hk] at e0
      have := hch.ωX t
      rw [← e0] at this
      obtain ⟨ω, a, b⟩ := exists_om_heq (S' := G.V (.grid 0 k)) (T' := G.V (.grid 0 (k + 1)))
        ((lt k (by omega)).trans (congrArg (Yc D) (by omega))) (hk ▸ top) this
      refine ⟨ω, fun _ => a, fun t' k' hk' e => ?_, fun t' k' _ e => ?_⟩
      · cases e; omega
      · cases e; exact b
    exact ⟨W.om p, fun hp => hWψ ▸ W.om_is p hp, fun t k hk e => absurd ⟨t, k, hk, e⟩ h,
      fun t k hk e => absurd ⟨t, k, hk, e⟩ h'⟩
  choose s B hs sY sX using h1
  choose om hom oY oX using h2
  obtain ⟨W', a1, a2, a3, a4, a5⟩ := exists_weil G (fun i hi => by
    have : (G.node (.grid i 0)).IsV (rankV D i 0) ((D.R.m - 0) / 2) := by
      cases i with
      | zero => exact GlobalTheory.T.gridFirstColumnSpace_rank_signature_selfDual D T R.toLevCh A.μ0 hlev 0 hi
      | succ i => exact G.sp.V_is (i + 1) 0 (by omega) hi (Nat.zero_le _)
    exact ⟨this.sigOK, this.sd⟩) he hψ hmod.inf s B hs om hom
  exact ⟨W', a1, a2, fun j hj => a3 ▸ (sY _ j hj rfl).1, a3 ▸ (sX _ rfl).1, fun j hj => a4 ▸ (sY _ j hj rfl).2,
    a4 ▸ (sX _ rfl).2, fun t k hk => a5 ▸ oY _ t k hk rfl, fun t k hk => a5 ▸ oX _ t k hk rfl⟩

end GlobalTheory.ChiGrid.WeilOver

end WeilOver

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

end GlobalTheory.BigTop.Fun

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_no_primitive_O2 : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  first | exact @GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing | exact GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing | (intros; apply GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.PrimF A := by
  first | exact @GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme | exact GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.axes_vanishing_noetherian_abelian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → AxesVanishingStructureSheafDegOne A := by
  first | exact @GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme | exact GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme <;> assumption)
end
