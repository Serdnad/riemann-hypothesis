module

public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamily
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGenerator
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle167
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle157
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle096
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle105
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle149
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle166
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle163
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle158
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.normalisedPullback_section_expands_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (α : 𝓞 E) (N k q : ℕ) (e : k * N = q), α * star α = (N : 𝓞 E) → 0 < N → (k = 1 ∨ 4 ≤ k) → ∀ (σ : P.U.toUnifPre.SecGF F k) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo xF))) (θ : Fam P.D.toPre F k) (σ₁ : P.U.toUnifPre.SecGF F q) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (θα : Fam P.D.toPre F (k * N)), SecTieF I P F xF k σ s → P.U.toUnifPre.ExpandsG F k σ θ → IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) (q : ℤ) (k : ℤ) s s₁ → SecTieF I P F xF q σ₁ s₁ → PullAl P.D F P.oD α k N θ θα → P.U.toUnifPre.ExpandsG F q σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) e θα) := by
  first | exact @GlobalTheory.NormPullExp.main | exact GlobalTheory.NormPullExp.main | (intros; apply GlobalTheory.NormPullExp.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.thetaFrame_expansion_framedPoint_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (σ : P.U.toUnifPre.SecGF F 1) (θ : Fam P.D.toPre F 1), SecTieF I P F yF.x 1 σ yF.s → P.U.toUnifPre.ExpandsG F 1 σ θ → ThFrame P.D ϖ F θ := by
  first | exact @GlobalTheory.GeneratorFrame.main | exact GlobalTheory.GeneratorFrame.main | (intros; apply GlobalTheory.GeneratorFrame.main <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.wordBound_smooth_decaying_coefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → w.length ≤ N → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ∃ (e : ℕ) (A : ℝ), CutPow e φ ∧ B.CkOn ⊤ (B.GV P.k P.r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧ Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - (2 * (P.r : ℝ) + 2) * e) := by
  first | exact @GlobalTheory.HatNF.wordBound_decay | exact GlobalTheory.HatNF.wordBound_decay | (intros; apply GlobalTheory.HatNF.wordBound_decay <;> assumption)
end

section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem mem_nfSpan_zero_zero_one_of_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par}
    (d : Q.NFData P A) (T : Set A) {x : A} (hx : x ∈ T) : x ∈ nfSpan d T 0 0 1 := by
  refine Submodule.subset_span ⟨1, (bmon d).one_mem, [x], rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    exact hh ▸ hx
  · simp

theorem basicLiftAll_zero : BasicLiftAll (fun _ => 0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN x hx
  obtain ⟨y, -, h | h | h | h⟩ := hx
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm Wp Wq P Bs X μ L st l0 d hD hN y)
  · exact mem_nfSpan_zero_zero_one_of_mem d _ (h ▸ GlobalTheory.T.polynomial_lift_dual_operator_combination Wp Wq P Bs X μ L st l0 d hD hN y)

end GlobalTheory.HatNF
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

theorem _root_.GlobalTheory.T.exists_productData_copies_trivialisation_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  first | exact @GlobalTheory.PowData.exists_powData | exact GlobalTheory.PowData.exists_powData | (intros; apply GlobalTheory.PowData.exists_powData <;> assumption)
end

section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open GlobalTheory.UnitFrameGen MeasureTheory
open scoped Matrix

noncomputable section

namespace GlobalTheory.LevelCusp

theorem cabs_gen_eq_one_of_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hmv hb hx hx'
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  obtain ⟨P, -, hp, hu, -, hA⟩ := hP k x
  obtain ⟨P', -, hp', hu', -, hA'⟩ := hP k' x'
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA' hx'
  clear hA hA' hP
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : (U.un k' x').x = (U.un k x).x ≫ ρ := hb.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  generalize ik k = i at *
  generalize ik k' = i' at *
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_sabMap F ν hp hp'
    ((congrArg (· ≫ ρ) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F.ex i P z).left ≫ ν.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex i P z).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = ((U.un k x).x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F.ex i P 0).left = ((U.un k x).x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F.ex i P z).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0, hxρ]
        exact o4 _ _ _ _ hz0 hz)
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x y'.x
      (U.un k' x').s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk ((U.un k x).x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2)⁻¹ *
        (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.LevelCusp
end
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  first | exact @GlobalTheory.limBd_fpm_and_fpmSh | exact GlobalTheory.limBd_fpm_and_fpmSh | (intros; apply GlobalTheory.limBd_fpm_and_fpmSh <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

theorem _root_.GlobalTheory.T.frameFree_finiteOrder_rule_const_periodSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (f : Rul Xo c), f ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c f y' = evR Xo c f y) → (∃ N : ℕ, 0 < N ∧ ∀ y : FrPt Xo c (CAt σ), evR Xo c f y ^ N = 1) → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H Dw.p Dw.q ty → ∀ (i : Fin F.n) (P P' : (F.Di i).La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → y.x = F.u i P → y'.x = F.u i P' → evR Xo c f y = evR Xo c f y' := by
  first | exact @GlobalTheory.FiniteOrderConst.const_on_period_space | exact GlobalTheory.FiniteOrderConst.const_on_period_space | (intros; apply GlobalTheory.FiniteOrderConst.const_on_period_space <;> assumption)
end
