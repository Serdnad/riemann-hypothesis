module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle035
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_adjointness_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → (∀ a : 𝓞 E, star a = H.bar a) → Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → FamAd t (𝟙 (Sp V)) d x B.A.act B.ad e → FamAd t (𝟙 (Sp V)) d x' B'.A.act B'.ad e' → ∀ a, JEq m (B'.ad a * ev (n := 2) ![pt V (n := 2) d 0, comp1 (B'.A.act (star a)) (pt V (n := 2) d 1)] ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] (B.ad a) * ev (n := 2) ![comp1 (B'.A.act a) (pt V (n := 2) d 0), pt V (n := 2) d 1] ε) := by
  first | exact @GlobalTheory.FrameRatioAdj.ratio_adj | exact GlobalTheory.FrameRatioAdj.ratio_adj | (intros; apply GlobalTheory.FrameRatioAdj.ratio_adj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_first_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh1 t (𝟙 (Sp V)) d x B.G.F B.ph1 e → FamPh1 t (𝟙 (Sp V)) d x' B'.G.F B'.ph1 e' → JEq m (B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph1 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε * ev (n := 3) ![pt V (n := 3) d 1, pt V (n := 3) d 2] ε)) := by
  first | exact @GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt | exact GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt | (intros; apply GlobalTheory.RatioPh1.frame_ratio_first_partial_law_alt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_second_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh2 t (𝟙 (Sp V)) d x B.G.F B.ph2 e → FamPh2 t (𝟙 (Sp V)) d x' B'.G.F B'.ph2 e' → JEq m (B'.ph2 * ev (n := 3) ![pt V (n := 3) d 0, addOf B'.G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph2 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 1] ε * ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε)) := by
  first | exact @GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law | exact GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law | (intros; apply GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.frame_ratio_symmetry_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamSy t (𝟙 (Sp V)) d x B.sy e → FamSy t (𝟙 (Sp V)) d x' B'.sy e' → JEq m (B'.sy * ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] B.sy * ev (n := 2) ![pt V (n := 2) d 1, pt V (n := 2) d 0] ε) := by
  first | exact @GlobalTheory.FrameRatioSym.frameRatio_sy | exact GlobalTheory.FrameRatioSym.frameRatio_sy | (intros; apply GlobalTheory.FrameRatioSym.frameRatio_sy <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.integral_charts_complete_dvr : IntChartStatement := by
  first | exact @GlobalTheory.intChart | exact GlobalTheory.intChart | (intros; apply GlobalTheory.intChart <;> assumption)
end
