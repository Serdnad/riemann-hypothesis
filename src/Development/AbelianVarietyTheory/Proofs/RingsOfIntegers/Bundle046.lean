module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle038
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricLiftOrderSymmetryMultiplicativity
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle045
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalThetaSeriesMulQuadraticPartials
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle014

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonicValue_bound_integralChart_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  first | exact @GlobalTheory.PlaceInt.ChartRam.chBound_ramified | exact GlobalTheory.PlaceInt.ChartRam.chBound_ramified | (intros; apply GlobalTheory.PlaceInt.ChartRam.chBound_ramified <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.kills_formalPoints_iff_mem_coordinateKernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) (𝓞 E)) (a : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (α : Fin n → Fin (chD C.ch) → T.V), (∀ b, FormPt C (a b) (α b)) → (Kills Xo mu a ↔ α ∈ kerM B mu) := by
  first | exact @GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM | exact GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM | (intros; apply GlobalTheory.PlaceInt.FormKer.kills_iff_mem_kerM <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem hv_eq_chartVal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  intro E _ _ _ H Dw l Xo c _ hst nab hnab S _ _ _ y C k n F f hf w P hP
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 S y
  choose f₀ hf₀ using fun b => hex k (F b)
  have e₀ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₀.B.nabVal S C₀.h H.w0 k (f₀ b) C₀.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)
  obtain ⟨N, hN, hA, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c w n P hP
  have h := GlobalTheory.T.harmonicValue_germs_independent_of_chart E H Dw l Xo c hst S y C₀ C k n F f₀ f hf₀ hf w _ hA
  have hu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  simp only [chartVal, hs, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc, ← Finset.mul_sum] at h
  simp only [hv, chartVal, e₀]
  exact hu.mul_left_cancel h

end GlobalTheory.PlaceInt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.symmetricLift_order_symmetry_multiplicativity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (wP : PrimTyG t), wP.IsGen → ∀ (k : ℕ) (a : baseOver S ⟶ t.G) (U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver S)), SymLift t.G t.PP.L (k : ℤ) k a U → ∀ (T : Over S) (σ : T ⟶ baseOver S) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → LiftLaws (cubV t.cub z J) (fun p : T ⟶ t.G => val wP p.left z J) (fun p : T ⟶ t.G => GlobalTheory.CommPairing.tval U (lift σ p).left z J) (fun p : T ⟶ t.G => p ≫ t.act.act H.w0) (σ ≫ a) k := by
  first | exact @GlobalTheory.TransUnit.liftLaws_of_symLift | exact GlobalTheory.TransUnit.liftLaws_of_symLift | (intros; apply GlobalTheory.TransUnit.liftLaws_of_symLift <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.constantSection_eq_limitChart_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  first | exact @GlobalTheory.TransUnit.ptOf_const_left | exact GlobalTheory.TransUnit.ptOf_const_left | (intros; apply GlobalTheory.TransUnit.ptOf_const_left <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.exists_powerSeries_limit_of_compatible_jetPoints : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) → ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  first | exact @GlobalTheory.TransUnit.LimEx.exists_isLimit | exact GlobalTheory.TransUnit.LimEx.exists_isLimit | (intros; apply GlobalTheory.TransUnit.LimEx.exists_isLimit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.spec_powerSeries_hom_ext_of_jets : ∀ (V : Type) [CommRing V] [IsLocalRing V] (κ : Type) [Fintype κ] [DecidableEq κ] (Y : Scheme.{0}) (f g : Sp (MvPowerSeries κ V) ⟶ Y), (∀ m, spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ f = spMap (jetA (V := V) κ m : MvPowerSeries κ V →+* Jet V κ m) ≫ g) → f = g := by
  first | exact @GlobalTheory.TransUnit.hom_ext_of_jets | exact GlobalTheory.TransUnit.hom_ext_of_jets | (intros; apply GlobalTheory.TransUnit.hom_ext_of_jets <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.eval_iotaSeries_eq_quadratic_inversion_partials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ jo : PS V 1 d, IsIota B K h w0 jo → ∀ (n : ℕ) (x : Sm B n), evA ![x] jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) x).val := by
  first | exact @GlobalTheory.TransUnit.evA_iota_eq_quadN | exact GlobalTheory.TransUnit.evA_iota_eq_quadN | (intros; apply GlobalTheory.TransUnit.evA_iota_eq_quadN <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

theorem _root_.GlobalTheory.T.eval_thetaSeries_mul_quadratic_partials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ Θ : PS V 3 d, IsTheta B K h w0 Θ → ∀ (n : ℕ) (x y z : Sm B n), evA ![x, y, z] Θ * (quadQ (u3 p₁) (u3 p₂) (Sm.act B w0) x y z).val = 1 := by
  first | exact @GlobalTheory.TransUnit.evA_theta_mul_quadQ | exact GlobalTheory.TransUnit.evA_theta_mul_quadQ | (intros; apply GlobalTheory.TransUnit.evA_theta_mul_quadQ <;> assumption)
end

section

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ShortClause

theorem val_mul {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vLa la (a * b) = vLa la a + vLa la b := by
  unfold vLa
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem val_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) :
    vLa la (a ^ n) = n * vLa la a := by
  unfold vLa
  rw [map_pow, WithZero.log_pow]
  simp

theorem val_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  unfold vLa
  have h1 : la.valuation K (p : K) ≤ 1 := by
    have := la.valuation_le_one (K := K) (p : 𝓞 K)
    simpa using this
  by_cases h0 : la.valuation K (p : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem thc_le_of_eq_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) = 0) :
    X.Thc s w ≤ B.Mlat j w := by
  intro F hF
  obtain ⟨F1, hF1, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  rw [hsc, zero_smul]
  exact (B.Mlat j w).zero_mem

end ShortClause


open ShortClause in
theorem thc_le_of_shortBound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  intro hSB D T h hs j hj hinj EX hO w a b s ha hb hsE
  by_cases hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) = 0
  · exact thc_le_of_eq_zero (recPJ h j hj) s w hsc
  refine Pf.Thc_le_Mlat (recPJ h j hj) s w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j w) := hG
  have key := Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la))
    (fun g hg => hSB D T h hs j hj hinj EX hO w g hg la y) _ hG'
  refine le_trans ?_ (key.trans (recPJ_vAt_inc h j hj la y w G).ge)
  rw [EReal.coe_le_coe_iff, neg_le_neg_iff]
  set nn : 𝓞 T.Q.c.F := nnW (recB h.toLawsCore) hinj EX w with hnn
  have e : ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) := by
    rw [hsE, zOwnP]
    push_cast
    ring
  have hne : (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) ≠ 0 := by
    rw [← e]
    exact fun h0 => hsc (RingOfIntegers.coe_eq_zero_iff.1 h0)
  have h4 := right_ne_zero_of_mul hne
  have h123 := left_ne_zero_of_mul hne
  have h3 := right_ne_zero_of_mul h123
  have h12 := left_ne_zero_of_mul h123
  have h2 := right_ne_zero_of_mul h12
  have h1 := left_ne_zero_of_mul h12
  have hv : vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F))
      ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      ((DF w + 2 * D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) + vLa la (nn : T.Q.c.F) +
        vLa la ((pPow D a b b : ℕ) : T.Q.c.F) +
        ((D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) := by
    rw [e, val_mul _ h123 h4, val_mul _ h12 h3, val_mul _ h1 h2, val_pow, val_pow]
  have hr := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w a b ha hb
  have hp : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) := by
    exact_mod_cast val_nat_nonneg _ _
  have hk : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
      ((D.R.f : ℝ) * D.R.r * w.n) := mul_nonneg hp (by positivity)
  refine le_trans ?_ (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) hv).symm)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  generalize ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) = x
  push_cast
  nlinarith [hr, hk]

end GlobalTheory.PlaceTop
end
end
