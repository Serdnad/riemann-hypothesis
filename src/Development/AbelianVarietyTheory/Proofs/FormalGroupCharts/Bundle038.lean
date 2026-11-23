module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle025
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle008
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
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

theorem _root_.GlobalTheory.T.chartsWithFrames_related_allOrders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jRel_of_charts_frames | exact GlobalTheory.ChartCmp.jRel_of_charts_frames | (intros; apply GlobalTheory.ChartCmp.jRel_of_charts_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem _root_.GlobalTheory.T.harmonicValue_germs_independent_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → chartVal C k f P = chartVal C' k f' P := by
  first | exact @GlobalTheory.ChartField.chartVal_indep | exact GlobalTheory.ChartField.chartVal_indep | (intros; apply GlobalTheory.ChartField.chartVal_indep <;> assumption)
end

section

namespace GlobalTheory

open Formalism.MainNotions.ModuliIntegralCharts.H1

theorem harmonicValue_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  have hAct : ExpActOfSt := by
    refine expActOf_of_eig ?_
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i
    exact EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  refine chartIndep2_verb ?_ (GlobalTheory.BalancedTwist.frTruncFix_iff.mp frTruncFix_holds) germFix_holds (harmInv_of hAct)
  refine chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
    (gaugeUniq_of_global globalFns_holds) (killAddVal_of ?_)
  intro E _ _ _ H
  exact psiCover_holds H

end GlobalTheory
end
