module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle554
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.FubiniStudyChowHeight.FubiniStudyChowHeightOfArExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoSec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero

@[expose] public section

section

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

abbrev _root_.GlobalTheory.T.FieldOfDefinitionDescentProp : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP Cl.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (Formalism.L2.Theta.GA D (Wc D i))) (𝓕 : Set (Formalism.L2.Theta.GA D (Wc D i))), Formalism.IndefR.Lev.IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i P) μ 𝓕 → ENNReal.ofReal (Real.exp (-(C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|)))) ≤ μ 𝓕
end
end

section

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

abbrev _root_.GlobalTheory.T.FlatDegreeHypotheses : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt
end
end

section

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
namespace GlobalTheory.UnifTrait
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Frames
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
section Split
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
end Split
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
open IsLocalRing

theorem exists_extension_integral_frame_uniformizer : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  intro _ E _ _ _ H Dw l Xo c TF T io
  letI := io.toAlgebra
  intro P w hw
  have hz : FlagMod.frX P ≫ TF.Y.j = spMap (algebraMap T.V T.Fr) ≫ w := by
    rw [hw, (TF.X.lies_ptY P).1]
  have hzs : FlagMod.frX P ≫ pullback.snd _ _ = spMap io := FlagMod.frX_snd P
  obtain ⟨y₀, tt, hB⟩ := exists_intFr_frBor T io c.F (RingHom.id c.F) TF.Y w (FlagMod.frX P) hz hzs P
    (FlagMod.frX_fst P).symm
  obtain ⟨G₀, ⟨m₀⟩⟩ : ∃ G₀ : SAB H (Sp T.V), Nonempty (SABMap G₀ TF.Y.t w) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull w TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₀, m1₀, m2₀, -⟩ := genFibre Xo c Out.CubePf.cubePull T io c.F (RingHom.id c.F) TF.Y w _ hz hzs G₀ m₀
  have : CharZero (ResidueField T.V) := charZero_residue_of_map T.V (w ≫ TF.Y.s)
  obtain ⟨W, _, _, _, _, _, hf, hi, hS⟩ := exists_split_baseChange T.V G₀.G G₀.semi
  have : CharZero W := charZero_of_injective_ringHom hi
  let T' : CDVR := { V := W }
  let j : T.V →+* T'.V := algebraMap T.V W
  have hfin : j.Finite := RingHom.finite_algebraMap.2 hf
  obtain ⟨i, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' j hi hfin
  letI := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
    T.Fr T'.Fr ψ y₀.1
  let y' : IntFr Xo c T' (i.comp io) := ⟨z', GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T'.Fr z',
    GlobalTheory.IntegralExt.integral_baseChange T T' io (i.comp io) j hi ψ hφ y₀.1 z' hz' y₀.2.2⟩
  obtain ⟨G, ⟨mG⟩⟩ : ∃ G : SAB H (Sp T'.V), Nonempty (SABMap G TF.Y.t (spMap j ≫ w)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap j ≫ w) TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  have hι : i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j := RingHom.ext hφ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap j = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hι]
  have hz2 : (spMap i ≫ FlagMod.frX P) ≫ TF.Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap j ≫ w := by
    rw [Category.assoc, hz, ← Category.assoc, ← hio, Category.assoc]
  have hzs2 : (spMap i ≫ FlagMod.frX P) ≫ pullback.snd _ _ = spMap (i.comp io) := by
    rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T' (i.comp io) c.F (RingHom.id c.F) TF.Y
    (spMap j ≫ w) _ hz2 hzs2 G mG
  have hx' : y'.1.x = (spMap i ≫ FlagMod.frX P) ≫ pullback.fst _ _ := by
    rw [Category.assoc, FlagMod.frX_fst, ← hB.1]
    exact hz'.1
  obtain ⟨Pu, -⟩ := GlobalTheory.IntegralExt.exists_unif_of_split T T' j i hφ m1₀ m2₀ (Category.assoc _ _ _) m1 m2 hS
  have hloc : IsLocalHom j := hfin.to_isIntegral.isLocalHom hi
  refine ⟨T', i, j, r, y', G, mG, Pu, t', (by rw [hx']; exact m1), m2, hr0, hv, hι, fun a ha => map_nonunit j a ha,
    ?_⟩
  rw [TF.X.ptY_frBor hB, ← TF.X.ptY_frMap hz']
end GlobalTheory.UnifTrait
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.exists_uniformizing_integral_frame_extension : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  first | exact @_root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | exact _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | (intros; apply _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer <;> assumption)
end
end

section

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
namespace GlobalTheory.PeriodMinPos
theorem period_minimum_phi_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  intro _ E _ _ _ H Dw l Xo c T io y φ hφ G t' m1 m2 hG
  obtain ⟨G₀, t₀, m1₀, m2₀, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := hφ
  obtain ⟨m⟩ := GlobalTheory.SlopeRec.nonempty_sabMap_of_models m1 m2 m1₀ m2₀
  have hG₀ : (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G₀.G := fun h =>
    hG ((abLocus_pullback abLocusOne G.semi m.cart.1 _).2 h)
  have hnt : ¬ Subsingleton P.D.toPre.X := fun h =>
    hG₀ ((GlobalTheory.TorRef.closed_mem_abLocus_iff T P).2 h)
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨a, ha⟩ := exists_ne (0 : P.D.toPre.X)
  have hQa : 1 ≤ Q a := ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos hϖ P.D hQ ha
  have hint : ∀ a c, ∃ z : ℤ, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a c = z := by
    intro a c
    refine ⟨Q (a + c) - Q a - Q c, ?_⟩
    have h1 := hβ (a + c)
    have hs := β.2.1 c a
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hβ a, hβ c] at h1
    push_cast
    linarith
  have hpos : ∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)
  have hne : β ≠ 0 := fun e => by
    have h1 := hβ a
    rw [e] at h1
    have : (1 : ℝ) ≤ Q a := by exact_mod_cast hQa
    simp at h1
    linarith
  haveI : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have h1 := GlobalTheory.LeastExponentProbe.one_le_phiC (fun _ => rfl) β hint hpos hne
  linarith
end GlobalTheory.PeriodMinPos
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.minimal_period_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  first | exact @_root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | exact _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | (intros; apply _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos <;> assumption)
end
end

section

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
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvInterior
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}
section Moves
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)
end Moves
section Lift
variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
end Lift
section Move
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Move
section Laws
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Laws
theorem equivariant_action_preserves_interior : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.mul_asIso]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).asIso.hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).asIso.hom ≫ w') ≫ toU TF Z = (ρ γ).asIso.hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]
end GlobalTheory.EqvInterior
end
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

theorem _root_.GlobalTheory.T.interior_equivariant_action_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  first | exact @_root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | exact _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | (intros; apply _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior <;> assumption)
end
end

section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ProjSpace ChowFormHeightComparison₂.CF
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FubiniStudyChowHeightFormula₂.Fs
variable (R : Type) [CommRing R] (N : ℕ)
end FubiniStudyChowHeightFormula₂.Fs
theorem FubiniStudyChowHeightFormula₂.fubiniStudy_chowHeight_formula (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.FubiniStudyChowHeight :=
  FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of h.p4
end
end
end

section

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CanonBirat
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.TopForm GlobalTheory.MorJac GlobalTheory.Cartier
section General
variable {X Y : Scheme.{0}}
end General
section Flag
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
end Flag
theorem canonicalExtension_extends_iff_modification : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z _ hKS hV ω₀ M ω b s hs m
  haveI := hV.1
  haveI := hV.2.2
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) _
  have hI : IsIntegral (Y₀ TF.X Z) := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsIntegral (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := hI
  refine extends_iff_of_hom hKS (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) M M.σ (Category.comp_id _) ?_ ω₀ ω hs m
  rw [Modif.off_eq]
  exact M.iso
end GlobalTheory.CanonBirat
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

theorem _root_.GlobalTheory.T.canonicalExtension_birational_invariance : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @_root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification | exact _root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification | (intros; apply _root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification <;> assumption)
end
end
