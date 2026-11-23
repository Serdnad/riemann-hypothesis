module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle137
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle142
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle136
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle179
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthBd.nuWt_bounds | exact GlobalTheory.DepthBd.nuWt_bounds | (intros; apply GlobalTheory.DepthBd.nuWt_bounds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.runDepthData_laws_and_finite_local_depth : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)], LawsM T → (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → LawsPi T (depOf T EX Tp hK) ∧ LawsDep T ∧ NuFinAt T (depOf T EX Tp hK) := by
  first | exact @GlobalTheory.RunDepth.laws_and_nuFinAt | exact GlobalTheory.RunDepth.laws_and_nuFinAt | (intros; apply GlobalTheory.RunDepth.laws_and_nuFinAt <;> assumption)
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem numOf_sizes_le (D : D7) (L : SizeData₂ D) (hk : (1 : ℝ) ≤ D.R.k) (hm : (1 : ℝ) ≤ D.R.m) :
    (numOf D L).Sc + (numOf D L).eta ≤ L.Sc + L.etaSz := by
  have hS := L.Sc_pos
  have hE := L.Sc_eq
  have he := L.etaSz_pos
  have hDel : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have h1 : (numOf D L).Sc ≤ L.Sc := by
    show (D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)) ≤ L.Sc
    rw [hE]
    have := Nat.floor_le hDel
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (numOf D L).eta ≤ L.etaSz := by
    show (D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ) ≤ L.etaSz
    have hm0 : (0 : ℝ) < D.R.m := by linarith
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    have h0 : 0 ≤ LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; positivity
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le h0) hm0.le
  linarith

theorem card_RPl (R : Ranks) : Fintype.card (RPl R) = R.f := by
  simp [RPl, Ranks.f, Ranks.n, R.card_A]



theorem leafGood_run : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.depthTable_goodPrimeLeaf 100 (by norm_num)
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm R hPk hC hPg hSz hCn hx5 hx hkb tF
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe Scale.b Scale.L
    rw [R.x_eq, R.eps_eq]
  have hL : O.L = L.sc.L := by
    unfold OnObj.L
    rw [hb, Scale.b, Real.log_exp]
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hk1 : (1 : ℝ) ≤ D.R.k := R.k_eq ▸ hPg.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := R.m_eq ▸ hPg.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := R.f_eq ▸ hPg.2.2.2.1
  have hlog : Real.log D.R.k ≤ L.sc.L := by
    have := hSz.2.2.2.2.2.2.1
    rwa [R.k_eq, hL] at this
  refine hC0 D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι Nm (numOf D L)
    (fun z => DV.tauEmb D (plOf D z)) hC R.E_eq R.σ_eq R.T_eq ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
    (piSplit_depDataOf ..) (levelQ_depDataOf _ _ _ _ _ _ _ _ _ hT) R.star_eq
    (fun j => (GlobalTheory.T.exists_integral_chart_integral_framed_point _ _ _ _ _ _).2.1 R.star_eq) hPk (GlobalTheory.T.realPlaces_match_cmTypeFrobenius D L T hT.pins) (fun j => ?_) ?_ hPg tF
    ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
  · have hj := R.inR j
    have hd := hT.pins.2.2.2 _ hj
    refine ⟨hj.1, hj.2, hd.1, hd.2.1, fun τ i i' h => (dom_wtA (lR Tp hK (ι j))).1 τ h, ?_⟩
    rw [hb, hL]
    exact GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters D L Pm Tp hK T hT.pins hCn hx5 hx hkb hlog _ hj
  · refine ⟨R.k_eq, R.m_eq, R.f_eq, ?_, R.depthNumbers_threshold_eq, R.th_eq, R.ad_eq, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · unfold OnObj.Se
      rw [R.Sc_eq, R.eta_eq]
      exact numOf_sizes_le D L hk1 hm1
    · rw [R.wt_eq]
      have h := (GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK (ι j) (R.inR j) hx hkb).2
      calc (∑ z, (numOf D L).w (ι j) z) ≤ ∑ _z : RPl D.R, 2 * L.sc.b := Finset.sum_le_sum fun z _ => (h z).2
        _ = 2 * (D.R.f : ℝ) * L.sc.b := by
          rw [Finset.sum_const, Finset.card_univ, card_RPl, nsmul_eq_mul]; ring
    · rw [R.wt_eq, hb]; nlinarith
    · have h := (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hT.pins (ι j) (R.inR j) (lR Tp hK (ι j))).1
      have h2 := R.DF_ge j
      rw [← h] at h2
      exact h2

end GlobalTheory.GoodDepth
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_levelChangeAction_on_cuspForms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)), ∃ act, IsLevAct T h j w ℓ act := by
  first | exact @GlobalTheory.FormTies.exists_isLevAct | exact GlobalTheory.FormTies.exists_isLevAct | (intros; apply GlobalTheory.FormTies.exists_isLevAct <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

theorem _root_.GlobalTheory.T.pointStatements_on_copies_hold : RPointT ∧ GenPointT ∧ JetsOnCopiesCompatibleFrames ∧ GermOfFamT ∧ ThetaFrameF ∧ PowPELF := by
  first | exact @GlobalTheory.PowGerm.pointStatements_on_copies | exact GlobalTheory.PowGerm.pointStatements_on_copies | (intros; apply GlobalTheory.PowGerm.pointStatements_on_copies <;> assumption)
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.JetBoundEqualTypesReg.main | exact GlobalTheory.JetBoundEqualTypesReg.main | (intros; apply GlobalTheory.JetBoundEqualTypesReg.main <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  first | exact @GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | exact GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | (intros; apply GlobalTheory.LevelFormsReal.levelZero_im_eq_zero <;> assumption)
end
