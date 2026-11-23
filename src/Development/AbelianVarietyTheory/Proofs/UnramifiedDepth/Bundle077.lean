module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle075
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NotNondegenerateOfDegenerateSeriesDirection
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.alphaP_homomorphism_cubicalWeil_trivial_rational_torsion : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  first | exact @GlobalTheory.AlphaPair.cubWeil_alpha_rational | exact GlobalTheory.AlphaPair.cubWeil_alpha_rational | (intros; apply GlobalTheory.AlphaPair.cubWeil_alpha_rational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.frame_partial_laws_nilpotent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), IsFrameG t (𝟙 (Sp V)) d x F act ph1 ph2 sy ad e → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtCube (spMap β) t.G t.cub (fun j => MvPowerSeries.map β (F j)) (MvPowerSeries.map β ph1) (MvPowerSeries.map β ph2) P := by
  first | exact @GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame | exact GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame | (intros; apply GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (d : ℕ) (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![pt Ω d 0, 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph2 = 1 → IsPtLaw s G F P → IsPtUniv s G P → IsPtCube s G c F ph1 ph2 P → Degenerate p F ph2 → ¬ NonDeg p s G c := by
  first | exact @GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | exact GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | (intros; apply GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate <;> assumption)
end
