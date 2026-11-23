module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle118
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle036
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentials
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle123
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem hv_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  intro E _ _ _ H Dw l Xo c inst hstar nab hnab S _ _ y a N k k' haN hk n F F' hF w P hP
  have e : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star _ _ (fun x => (hstar x).trans rfl)
  subst e

  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 c.F)) P.support
    (fun m => P.coeff m)
  have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hbM ((IsFractionRing.injective (𝓞 c.F) c.F) (by rw [h0, map_zero]))

  have hsmul : ∀ (k0 : ℕ) (G : Fin n → SecN Xo y.x k0),
      hv Xo c nab y k0 G (algebraMap (𝓞 c.F) c.F b • P) =
        algebraMap c.F S (algebraMap (𝓞 c.F) c.F b) * hv Xo c nab y k0 G P := by
    intro k0 G
    unfold hv
    rw [MvPolynomial.support_smul_eq hb0, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

  have hQ : algebraMap (𝓞 c.F) c.F b • P ∈ harmA c w n := by
    unfold HH HHa at hP
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨⟨Submodule.smul_mem _ _ h1, fun σ i i' hi t => by rw [map_smul, h2 σ i i' hi t],
      fun m hm σ i => h3 m (MvPolynomial.support_smul hm) σ i⟩, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · obtain ⟨r, hr⟩ := hb m hm
      have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F b * P.coeff m := by
        rw [hr, Algebra.smul_def]
      rw [← hr']
      exact r.2
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      exact Subring.zero_mem _
  have key : hv Xo c nab y k' F' (algebraMap (𝓞 c.F) c.F b • P) =
      algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F (algebraMap (𝓞 c.F) c.F b • P) :=
    GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab S y a N k (k' : ℤ) (by rw [hstar]; exact haN)
      (by exact_mod_cast hk) n F F' (fun i => hF i) w _ hQ
  rw [hsmul, hsmul, _root_.mul_left_comm] at key
  exact mul_left_cancel₀ ((map_ne_zero _).mpr hb0) key
end GlobalTheory.PlaceInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  first | exact @GlobalTheory.PlaceInt.evC_spec | exact GlobalTheory.PlaceInt.evC_spec | (intros; apply GlobalTheory.PlaceInt.evC_spec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.normalisedPullback_commutes_symmetric_translations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  first | exact @GlobalTheory.PlaceInt.moves_of_pulls | exact GlobalTheory.PlaceInt.moves_of_pulls | (intros; apply GlobalTheory.PlaceInt.moves_of_pulls <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_adapted_similitude_data_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  first | exact @GlobalTheory.PlaceInt.AdaptExists.exists_adapt | exact GlobalTheory.PlaceInt.AdaptExists.exists_adapt | (intros; apply GlobalTheory.PlaceInt.AdaptExists.exists_adapt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonicValue_bound_of_column_products : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_of_columns | exact GlobalTheory.PlaceInt.chBound_of_columns | (intros; apply GlobalTheory.PlaceInt.chBound_of_columns <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.isNormalisedPullbackSection_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  first | exact @GlobalTheory.PullComp.pulls_mul | exact GlobalTheory.PullComp.pulls_mul | (intros; apply GlobalTheory.PullComp.pulls_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.gauge_thirdDifference_symmetry_integral_exponentials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → (∃ Θ : PS V 3 d, IsTheta B K h w0 Θ) ∧ ∃ jo : PS V 1 d, IsIota B K h w0 jo := by
  first | exact @GlobalTheory.PlaceInt.exists_isTheta_and_isIota | exact GlobalTheory.PlaceInt.exists_isTheta_and_isIota | (intros; apply GlobalTheory.PlaceInt.exists_isTheta_and_isIota <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.regular_section_integral_germ_unique_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), (Regular C k F → ∃ f, GermIs C k F f) ∧ (∀ f f', GermIs C k F f → GermIs C k F f' → f = f') ∧ ∀ (F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch)), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j) → GermIs C k F f → GermIs C k F' (r • f) := by
  first | exact @GlobalTheory.RegularGerm.regular_germ | exact GlobalTheory.RegularGerm.regular_germ | (intros; apply GlobalTheory.RegularGerm.regular_germ <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.torsion_rational_over_finite_extension_level_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) := by
  first | exact @GlobalTheory.torsion_rational_over_finite_extension | exact GlobalTheory.torsion_rational_over_finite_extension | (intros; apply GlobalTheory.torsion_rational_over_finite_extension <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.integralChart_formalBiextension_gauge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  first | exact @GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | exact GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | (intros; apply GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  first | exact @GlobalTheory.PullExpansion.expands_pull_of_four_le | exact GlobalTheory.PullExpansion.expands_pull_of_four_le | (intros; apply GlobalTheory.PullExpansion.expands_pull_of_four_le <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralSection

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem exists_eq_of_nonneg (hϖ : Irreducible ϖ) {v : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) v) {c : FractionRing V} (h : 0 ≤ v c) :
    ∃ b : V, c = algebraMap V (FractionRing V) b := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, (map_zero _).symm⟩
  obtain ⟨n, u, hu⟩ := hasVal_of_ne_zero hϖ hc

  have hvc : v c = ((n : ℚ) : WithTop ℚ) := hv c n ⟨u, hu⟩
  have hn : (0 : ℤ) ≤ n := by
    rw [hvc] at h
    have h' : (0 : ℚ) ≤ (n : ℚ) := WithTop.coe_le_coe.mp h
    exact_mod_cast h'

  lift n to ℕ using hn
  refine ⟨ϖ ^ n * (u : V), ?_⟩
  rw [hu, map_mul, map_pow, zpow_natCast]

theorem exists_int_of_vge_zero (hϖ : Irreducible ϖ) {D : DegData V (maximalIdeal V)}
    {v : AddValuation (FractionRing V) (WithTop ℚ)} (hv : ValOver ϖ (FractionRing V) v) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    (hs : VGe D (FractionRing V) v k α s 0) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := hs

  have hint : ∀ i, ∃ b : V, a i = algebraMap V (FractionRing V) b := fun i =>
    exists_eq_of_nonneg hϖ hv (by simpa using ha i)
  choose b hb using hint

  refine ⟨FamInt.secLin (fun i => constFn D.toPre.P.A.hom ⊤ (b i)) σ, ?_⟩
  refine SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_
  rw [SectionScalarValuation.sval_lin _ σ (fun j => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF
      (fun j => (hsum j).trans (by simp only [constBF_eq]; rfl)) _ y hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SectionScalarValuation.secScal_sval (hσ i) (𝟙 _) y hJ]
  congr 1
  clear hsum hσ ha hJ
  rw [gs_constFn]
  · rw [hb i]

    have e1 := gs_pull (𝟙 _) (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) (b i)))
    rw [Category.id_comp] at e1
    have e1' : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) (b i))) =
        cst (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y (algebraMap V (FractionRing V) (b i)) := e1
    rw [e1', ← cst_comp, Category.id_comp]
    congr 1

    have h1 := Over.w (DegPre.prB D.toPre (FractionRing V))
    have h2 := Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)
    rw [h1]
    rw [← h2]
    congr 1

    unfold TF spMap
    change jFK _ ≫ jK V = _
    unfold jFK jK
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · trivial

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E → (∀ α, VGe D (FractionRing V) vK k α (E.s α) 0) → ∃ σ : H0 U.LG.L k, GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK V)) 1 := by
  intro V _ _ _ ϖ hϖ D vK hvK A G _ _ U k s E hE hvE
  obtain ⟨r, hr, σ, f, hσ, hf, hexp⟩ := hE
  have hg : ∀ α, ∃ g : D.toPre.SecB k α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α)
      (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1 :=
    fun α => exists_int_of_vge_zero hϖ hvK (hvE α)
  choose g hg using hg
  have hfg : ∀ α, SecIsMul D.toPre.P.A.hom r (f α) (g α) := fun α =>
    secIsMul_of_secScal D.toPre.P.isLB D.toPre.P.A.hom (prB_app_injective D.toPre) (hg α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing V))]; exact hf α)
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ

  have hmul : ∀ α, ∃ g' : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ m) (f α) g' := by
    intro α
    obtain ⟨g', hg'⟩ := exists_secIsMul D.toPre.P.A.hom (u : V) (g α)
    obtain ⟨F', hF'⟩ := exists_secIsMul D.toPre.P.A.hom (ϖ ^ m) g'
    have hc := SecIsMul.comp hF' hg'
    have hF'f : F' = f α := SecOps.sec_ext fun j => by
      rw [hc j, hfg α j, hu, mul_comm (u : V)]
    exact ⟨g', hF'f ▸ hF'⟩
  choose g' hg' using hmul

  have hdiv : ∃ τ : H0 U.LG.L k, SecIsMul G.hom (ϖ ^ m) σ τ := by
    rcases m with _ | e
    · refine ⟨σ, fun j => ?_⟩
      simp [scal]
    · exact exists_div_of_expandsAt hϖ U e k σ g' f hg' (hexp e)
  obtain ⟨τ, hτ⟩ := hdiv

  obtain ⟨σ', hσ'⟩ := exists_secIsMul G.hom ((u⁻¹ : Vˣ) : V) τ
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have hlin : ∀ {a : V} {t t' : H0 U.LG.L k}, SecIsMul G.hom a t' t →
      sval t' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
        gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y ⊤ (scal G.hom a) * sval t (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J := by
    intro a t t' ht
    have hl := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal G.hom a) (fun _ => t)
      (fun j => by rw [Fin.sum_univ_one]; exact ht j) (𝟙 _ ≫ pullback.fst G.hom (jK V)) y hJ
    rwa [Fin.sum_univ_one] at hl
  have hgs : ∀ {X : Scheme.{0}} (r' : _ ⟶ X) (p : X ⟶ Spec (CommRingCat.of V)) (a : V),
      gs r' y ⊤ (scal p a) = cst (r' ≫ p) y a := fun r' p a => gs_pull r' p y ⊤ trivial _
  have hq : (𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom = 𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V := by
    rw [Category.assoc, pullback.condition]
  have key := GlobalTheory.IntegralExpansion.sval_of_secScal hσ (𝟙 _) y hJ
  rw [hlin hτ, hgs, hgs, hq, hu, cst_mul] at key
  rw [hlin hσ', hgs, hq]

  have hunit : IsUnit (cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (ϖ ^ m)) := by
    have hK : algebraMap V (FractionRing V) (ϖ ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr (pow_ne_zero _ hϖ.ne_zero)
    rw [← Category.assoc]
    change IsUnit (cst (_ ≫ spMap (algebraMap V (FractionRing V))) y _)
    rw [cst_comp]
    have h1 := (cst_mul (𝟙 _ ≫ pullback.snd G.hom (jK V)) y (algebraMap V (FractionRing V) (ϖ ^ m))
      (algebraMap V (FractionRing V) (ϖ ^ m))⁻¹).symm.trans (by rw [mul_inv_cancel₀ hK, cst_one])
    exact ⟨⟨_, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩
  have hT : sval τ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst (𝟙 _ ≫ pullback.snd G.hom (jK V) ≫ jK V) y (u : V) * sval s (𝟙 _) y J :=
    hunit.mul_left_cancel (by rw [key]; ring)
  rw [hT, ← _root_.mul_assoc, ← cst_mul, Units.inv_mul, cst_one, _root_.one_mul]

end GlobalTheory.IntegralSection
end
end
