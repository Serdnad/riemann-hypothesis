module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle300
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle321
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.frame_function_two_models_relay : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | exact GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.frame_function_two_models_relay <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi


theorem _root_.GlobalTheory.T.uniform_all_root_origin_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → Ref.UnifAll Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → FinTr.Linked Rd → ∀ B₁ : Finset RM.Ω, ∃ (B₂ : Finset RM.Ω) (B₃ : Finset (Om Z)), ∀ (A : Subring RM.Ω), (↑B₁ : Set RM.Ω) ⊆ A → (↑B₂ : Set RM.Ω) ⊆ A → ∀ (A' : Subring (Om Z)), (↑B₃ : Set (Om Z)) ⊆ A' → ∀ (p : ℕ) [Fact p.Prime] (ev₁ : A →+* PadicAlgCl p), (∀ x, IsAlgebraic ℤ (ev₁ x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ) (y : IntFr Xo c T io) (ι : T.Fr →+* PadicAlgCl p) (ev : A' →+* T.Fr), (p : 𝓞 c.F) ∈ la.asIdeal → OverLa la T.V io e₀ → y.IsAlg → (∀ x, ‖ι x‖ = FinRd.absT p la T e₀ x) → FinTr.RegAt h Z io A' ev y.1 → (∀ a : A', ∃ ha : Rd.φ a ∈ A, ev₁ ⟨_, ha⟩ = ι (ev a)) → ∃ z ∈ Small.algPts p (mCoordIdeal RM.y), ∃ rec : RootIx Dw → ℝ, (∀ b (hb : b ∈ A), b ∈ B₁ → Small.HasVal RM.y 0 b z (ev₁ ⟨b, hb⟩)) ∧ (∀ r', 0 < rec r' ∧ |Real.log (Small.supMet (RM.xdeg r') z) - Real.log (rec r')| ≤ (if p ∈ SS then 1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr E) : ℝ) / Module.finrank ℚ E else 0) * Real.log p) ∧ ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∀ f ∈ Rec.secZ Xo c a, ∃ v, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z v ∧ ∀ s : ℝ, nval T.V e₀ (evI y f) = ((ramOverZ la * s : ℝ) : EReal) → ‖v‖ = (p : ℝ) ^ (-s) * ∏ r', rec r' ^ n' (some r') := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | exact GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_all_root_origin_bound <;> assumption)
end

section


theorem _root_.GlobalTheory.T.flat_first_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGeneratorComponent := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem.flat_first_of_resolution_gaga <;> assumption)
end
