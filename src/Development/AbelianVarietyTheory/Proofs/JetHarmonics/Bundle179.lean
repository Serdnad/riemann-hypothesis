module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle041
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle135
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle120
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ShortMulThetaMemSpan
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle177
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle085
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle132
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.Bundle006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle167
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle082
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle178
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle176
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle169
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle148
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthBd

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem nuW_eq_zero (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n)
    (hl : Formalism.L2.Pj.DF Dw a < resCharOf la) : nuW Xo c la k a n = 0 := by
  refine max_eq_left ?_
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  letI := io.toAlgebra
  exact (iInf_le _ C).trans ((crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).2 hl)

theorem nuLocC_le_nuW (hI : ChartIndep Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (z : IntFr Xo c T io) (hz : z.IsAlg) (C : IntegralChartA3 Xo c T io z) :
    nuLocC C e k a n ≤ nuW Xo c la k a n := by
  have h1 : nuLocC C e k a n ≤ nuLoc z e k a n := le_iInf fun C' => (hI T io z C C' e k a n).le
  refine h1.trans (le_trans ?_ (le_max_right _ _))
  unfold nuSup
  exact le_iSup_of_le T (le_iSup_of_le io (le_iSup_of_le e (le_iSup_of_le ho (le_iSup_of_le z
    (le_iSup_of_le hz le_rfl)))))
end Gen

theorem ereal_unit {x : EReal} {r d q : ℝ} (hr : 0 < r) (hd : 0 ≤ d) (hq : 0 < q) (h0 : 0 ≤ x)
    (h1 : x ≤ max 0 ((r * d / q : ℝ) : EReal)) :
    x = ((r * (x.toReal / r) : ℝ) : EReal) ∧ 0 ≤ x.toReal / r ∧ x.toReal / r ≤ d / q := by
  have hb : (0 : ℝ) ≤ r * d / q := by positivity
  rw [max_eq_right (by exact_mod_cast hb)] at h1
  have ht : x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
  have hb' : x ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
  lift x to ℝ using ⟨ht, hb'⟩
  have h0' : 0 ≤ x := by exact_mod_cast h0
  have h1' : x ≤ r * d / q := by exact_mod_cast h1
  rw [EReal.toReal_coe]
  refine ⟨by rw [mul_div_cancel₀ _ hr.ne'], by positivity, ?_⟩
  rw [div_le_iff₀ hr]
  calc x ≤ r * d / q := h1'
    _ = d / q * r := by ring

theorem nuWt_bounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  intro D T h j hj w hn la
  letI := T.Q.H.starRing
  have hst : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a := fun _ => rfl
  obtain ⟨hDF, hdom, -, -, hcard, -⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hE : IntChartEx (T.Q.Xo j) T.Q.c :=
    (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hst
  have hI : ChartIndep (T.Q.Xo j) T.Q.c := GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hst
  have hS : ChartSaturated (T.Q.Xo j) T.Q.c := SaturatedCharts.saturation_charts_holds _ _
  have hn' := hcard.trans hn
  have hr : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (GlobalTheory.GoodDepth.ramOverZ_ne_zero' la)
  have hq : (0 : ℝ) < (resCharOf la : ℝ) - 1 := by
    have : (1 : ℝ) < resCharOf la := by exact_mod_cast (Crude.resCharOf_prime la).one_lt
    linarith
  have hle := nuW_le_crude hE hS la T.Q.l.M (wtA w) w.n hdom hn'
  rw [hDF] at hle
  obtain ⟨a1, a2, a3⟩ := ereal_unit hr (Nat.cast_nonneg (WeightAlgebra.DF w)) hq (le_max_left _ _) hle
  refine ⟨a1, a2, a3, fun hl => ?_, fun T' io e ho z hz C => ?_⟩
  · unfold nuWt
    rw [nuW_eq_zero hE hS la T.Q.l.M (wtA w) w.n hdom hn' (hDF ▸ hl)]
    simp
  · exact (nuLocC_le_nuW hI la T.Q.l.M (wtA w) w.n T' io e ho z hz C).trans a1.le

end GlobalTheory.DepthBd
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem laws_and_nuFinAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)], LawsM T → (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → LawsPi T (depOf T EX Tp hK) ∧ LawsDep T ∧ NuFinAt T (depOf T EX Tp hK) := by
  intro D L Pm Tp hK T EX _ h hs
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn : 2 * D.R.f * D.R.r ≤ Tp.nWn := by
    refine le_trans ?_ Tp.nW_lo.1
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hP : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun h EX _ _ _ _ _ fun j _ => hn
  have hD : LawsDep T :=
    ⟨hs, fun j _ => (GlobalTheory.IntChartExists.intChart_exists _ _ _ _ (T.Q.Xo j) T.Q.c).2.1 hs,
      fun j _ => GlobalTheory.ChartCmp.chartIndep_holds _ _ _ _ (T.Q.Xo j) T.Q.c hs⟩
  exact ⟨hP, hD, nuFinAt_of T h.pins _ hP.wts hD.chartEx
    fun j _ => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo j) T.Q.c⟩

end GlobalTheory.RunDepth
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem exists_isLevAct : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)), ∃ act, IsLevAct T h j w ℓ act := by
  intro D T h j hj w P ℓ
  have e : cutR T.C j w = T.cuspA j (wtA w) w.n := cutR_eq T.C hj w
  refine ⟨fun g F => (⟨actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) (ℓ g) F.1, ?_⟩ : cutR T.C j w), fun g F => rfl⟩
  exact e.ge (GlobalTheory.T.levelAction_mem_cuspForms D T h j hj w (ℓ g) F.1 (e.le F.2))

end GlobalTheory.FormTies
end

section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem productsShort_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn :=
  productsShort_of_oneFactor GlobalTheory.ShortTimesTheta.short_mul_theta_mem_span

end GlobalTheory.FormTies
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

namespace GlobalTheory.PowGerm

theorem pointStatements_on_copies :
    RPointT ∧ GenPointT ∧ JetsOnCopiesCompatibleFrames ∧ GermOfFamT ∧ ThetaFrameF ∧ PowPELF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have ht := GlobalTheory.twistBaseChange_and_valuation_statements.1
  exact ⟨GlobalTheory.SmallTranslate.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.GeneratorsAtPoint.main h1 h2 h3 h4 h5 ht,
    GlobalTheory.PowJets.jets_on_copies h1 h2 h4 ht,
    GlobalTheory.PowGerm.germOfFam_holds h1 h2 h4 ht,
    GlobalTheory.PowThetaFrame.main h1 h2 h4 ht,
    GlobalTheory.PowGerm.powPEL_of_laws h1 h2 h3 h4 h5 ht⟩

end GlobalTheory.PowGerm
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundEqualTypesReg

theorem of_compact : P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₂, Cc, hC₂, hPt⟩ := GlobalTheory.PointwiseBoundDecay.main hA Cb
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetBoundShifted.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, Cc, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d χ nnp nnm
    Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm hth
    hAms hReg hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := normaliser_across_places P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hzp hzp' hzm hzm' hAms
  have hdp := shifted_decay P Wp Wq Wqp up up' pp f Ap A₀ d p₀ hfA hAp
  have hdm := shifted_decay P Wp Wq Wqm um um' pm f Am A₀ d p₀ hfA hAm
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ _ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hdp hth hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ _ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hdm hth hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ n₀ p₀ hb hΛ hΛb hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ :=
  fun _ => of_compact

end GlobalTheory.JetBoundEqualTypesReg
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelFormsReal

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · simp only [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨by simp, hc l⟩
  · simp [D.ptSize, List.map_ofFn, Function.comp_def]

theorem ofFn_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l))
      = (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
  rw [List.ofFn_succ']
  simp

theorem integral_im_eq_zero {f : ℂ → ℂ} (hf : ∀ t, t ≠ 0 → (f t).im = 0) :
    (∫ t : ℂ, f t).im = 0 := by
  have h : f =ᵐ[volume] fun t => (((f t).re : ℝ) : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with t ht
    exact Complex.ext (by simp) (by simp [hf t ht])
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

theorem levelZero_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have key : ∀ (n j : ℕ), j + n = P.r + 1 → ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
      (p.RR H j w (List.ofFn fun l => ((1 : ℕ), c l)) (List.ofFn fun l => ((1 : ℕ), c l))).im = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc
      obtain rfl : j = P.r + 1 := hj
      exact (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.1
    | succ n ih =>
      intro j hj c hc
      rw [(GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (by omega) (isLocPt_ofFn c hc)).2]
      refine integral_im_eq_zero fun t ht => ?_
      have h := ih (j + 1) (by omega) (Fin.snoc c t) (fun l => by
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using ht
        · simpa using hc i)
      rw [ofFn_snoc] at h
      simp [Complex.mul_im, h]
  simpa using key (P.r + 1) 0 (by omega) (fun l => l.elim0) (fun l => l.elim0)

end GlobalTheory.LevelFormsReal
end
