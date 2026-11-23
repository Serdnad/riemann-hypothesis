module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle297
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DetLatticeTensorIsDegOnMuTwDeg
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscComponentGrowth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle300
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOrbitBound
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPadicEmbedding
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.PairIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle298
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.hodge_cpt_global_nef_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → 1 ≤ D.p → 1 ≤ D.q → ∀ (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → 2 < p → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ mu : GlobalTheory.CompanionTheory.Ar.Top.Wt (CMType H) (D.p + D.q), GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold D.p p mu → M.NefAt p mu 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness | exact GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.good_embedding_component_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | exact GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | (intros; apply GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.CompanionTheory.Relay.comp_laws_root_model_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → letI := Small.cstAlg Or; ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  first | exact @ModelDimension.component_laws_unif_frame | exact ModelDimension.component_laws_unif_frame
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_datum_degree_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (bb : ∀ τ, Fin Dc.N → W τ) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (lam : Ω), (∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)) → Hd.Λ = lam • PiTensorProduct.tprod Ω (fun τ => quotWedge (Hd.F τ) Dc.j_le_N (bb τ)) → (∀ τ, LinearIndependent Ω (s τ)) ∧ (Lat.tens (fun τ => detLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ Dc.y (muTwDeg Hd B) (lam⁻¹ * ∏ p ∈ Dc.SB B, MvPolynomial.aeval Dc.y (Dc.vden p) / MvPolynomial.aeval Dc.y (Dc.vnum p)) := by
  first | exact @LevelTowerAlt.det_lattice_tensor_isDegOn_muTwDeg | exact LevelTowerAlt.det_lattice_tensor_isDegOn_muTwDeg
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.holomorphic_disc_component_growth : (∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω), A.FG → Algebra.Smooth ℚ A → (∀ x : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ x * b = a) → ∀ g h b : A, (h : Ω) ≠ 0 → (b : Ω) ≠ 0 → (g : Ω) / h ∉ A → ∃ (ψ : ℂ → (A →+* ℂ)) (C : ℝ), (∀ a : A, DifferentiableOn ℂ (fun z => ψ z a) (Metric.ball 0 1)) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ψ z b ≠ 0 ∧ ψ z h ≠ 0 ∧ ‖ψ z h‖ ≤ C * ‖z‖ * ‖ψ z g‖) → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) (Hb : ((Σ k, ι k) → ℂ) → ℝ) (w f₀ : MRing ι), Birational y → SmoothGenericFibreM y → Small.IsFormOff (mCoordIdeal y) w → Small.IsFormOff (mCoordIdeal y) f₀ → (∀ z ∈ mcPts (mCoordIdeal y), MvPolynomial.aeval z w ≠ 0 → Small.ValLe y a s z (Hb z)) → (∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → MvPolynomial.aeval (Zf z) f₀ ≠ 0) → ∃ (C ρ : ℝ) (M : ℕ), 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Hb (Zf z) ≤ C * (1 + |Real.log ‖z‖|) ^ M) → ∃ N : ℕ, 0 < N ∧ (N : Ω) * s ∈ chartLatNm y a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc | exact GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.VsReg.Chart.mem_chartLatNm_of_disc <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.root_origin_exists_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), ∃ f : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) f ∧ ∀ w ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval w f ≠ 0 → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' := by
  first | exact @GlobalTheory.CompanionTheory.RootForm.exists_form | exact GlobalTheory.CompanionTheory.RootForm.exists_form | (intros; apply GlobalTheory.CompanionTheory.RootForm.exists_form <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.holomorphic_disc_orbit_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : PB.AnSys D σ) (P : Ideal (MRing ι)) (Re : PB.Realis S P), Re.J = ⊤ → ∀ Zf : ℂ → (Σ k, ι k) → ℂ, (∀ p, DifferentiableOn ℂ (fun z => Zf z p) (Metric.ball 0 1)) → (∀ z ∈ Metric.ball (0 : ℂ) 1, Zf z ∈ mcPts P) → (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → Re.π x ∈ S.open') → ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → ∀ x : Re.R.X, SameOrbit (Re.R.lift x x) (Zf z) → ReciprocityTheory.AnForm.P.rW S.L S.s (Re.π x) ≤ C * (1 + |Real.log ‖z‖|) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | exact GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.rW_le_log_disc <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr

theorem ev_genValue_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Z : Comp Xo c) (ex : Ix Dw → ℤ) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c ex → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (A : Subring (Om Z)) (ev : A →+* T.Fr), FinTr.RegAt h Z io A ev y.1 → evI y f ≠ 0 → ∀ hb : evC h Z f ∈ A, ev ⟨_, hb⟩ ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U h e hL Z ex f hf T io y A ev hR hy hb h0
  letI := io.toAlgebra
  obtain ⟨-, q, φ, ψ, yq, z, t, h1, h2, h3, h4⟩ := hR
  have hg : evC h Z f = φ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q φ yq (genFr h Z) h1
  have hz : evR Xo c f z = ψ (f q yq) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hL.evalWD f hf.1 q ψ yq z h2
  obtain ⟨hr, hψ⟩ := h3 (f q yq)
  have hψ0 : ψ (f q yq) = 0 := by
    rw [hψ, ← h0]
    exact congrArg ev (Subtype.ext hg.symm)
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex hf T.Fr t z y.1 h4
  apply hy
  show evR Xo c f y.1 = 0
  rw [hw, hz, hψ0, mul_zero]

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr
end
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi


theorem _root_.GlobalTheory.T.complete_dvr_padic_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (p : ℕ) [Fact p.Prime], OverLa la T.V io e₀ → T.FinRes → (p : 𝓞 c.F) ∈ la.asIdeal → ∃ ι : T.Fr →+* PadicAlgCl p, ∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Embed.exists_isometric_embedding <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.section_count_tendsto_geomDeg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.nefCount | exact GlobalTheory.CompanionTheory.Ar.Plug.nefCount | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.nefCount <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  first | exact @PositivityTheory.UnitarySelfGeneration.pair_iso | exact PositivityTheory.UnitarySelfGeneration.pair_iso
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem isIso_appTop_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (V : S.Opens) [IsAffine V.toScheme] :
    IsIso (A.hom ∣_ V).appTop := by
  let R : Type := Γ(V.toScheme, ⊤)
  let e : V.toScheme ≅ Sp R := V.toScheme.isoSpec
  let f : Sp R ⟶ S := e.inv ≫ V.ι
  have hf : e.hom ≫ f = V.ι := by simp [f]
  obtain ⟨S₀, B, _, φ, -, hfin, hB, hpb⟩ :=
    GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R ((Over.pullback f).obj A) ∅ (isAbelianScheme_pullback A hA f)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have w : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = (A.hom ∣_ V ≫ e.hom) ≫ f := by
    rw [Category.assoc, hf]
    exact (isPullback_morphismRestrict A.hom V).flip.w
  have sq : IsPullback (pullback.lift _ _ w) (A.hom ∣_ V) (pullback.snd A.hom f) e.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.fst A.hom f) (v₁₃ := A.hom) (h₂₂ := f) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  exact GlobalTheory.ProperFunctions.isIso_appTop_baseChange (sq.paste_horiz hpb.1)

theorem isIso_app_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ U : S.Opens, IsIso (A.hom.app U) := fun _ A _ hA U ↦
  GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens A.hom (fun V ↦
    have : IsAffine V.1.toScheme := V.2
    isIso_appTop_restrict A hA V.1) U

end GlobalTheory.CompanionTheory.Ar.Approx
end
