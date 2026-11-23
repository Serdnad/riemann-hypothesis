module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle040
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnit
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralExponentialSimilitudeGauge
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrix
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirections
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantDvdTraceOfJacobianFiniteColength
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  first | exact @GlobalTheory.PlaceInt.hv_pulls | exact GlobalTheory.PlaceInt.hv_pulls | (intros; apply GlobalTheory.PlaceInt.hv_pulls <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => MvPowerSeries.pderiv (R := V) j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) = MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  first | exact @GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | exact GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | (intros; apply GlobalTheory.PlaceInt.MatJac.det_jacobian_matV <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_integral_exponential_similitude_gauge : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∃ κ : PS V n d, IsKappa B K h w0 mu N κ ∧ MvPowerSeries.constantCoeff κ = 1 := by
  first | exact @GlobalTheory.PlaceInt.exists_isKappa | exact GlobalTheory.PlaceInt.exists_isKappa | (intros; apply GlobalTheory.PlaceInt.exists_isKappa <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.formal_group_points_of_integral_chart_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → (FormPt C 1 0) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (a = a' ↔ al = al')) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' δ : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (cpt δ : Pt T.V 0 (chD C.ch)) = addV B.G.F (cpt al) (cpt al') → FormPt C (a * a') δ) ∧ (∀ (a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al δ : Fin (chD C.ch) → T.V) (o : 𝓞 E), FormPt C a al → (cpt δ : Pt T.V 0 (chD C.ch)) = compV (B.A.act o) (cpt al) → FormPt C (a ≫ Xo.univ.t.act.act o) δ) ∧ ∀ al : Fin (chD C.ch) → T.V, Small al → ∃ a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G), FormPt C a al := by
  first | exact @GlobalTheory.PlaceFormPt.formPt_spec | exact GlobalTheory.PlaceFormPt.formPt_spec | (intros; apply GlobalTheory.PlaceFormPt.formPt_spec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.harmonic_value_integral_of_unit_discriminant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsUnit ((NumberField.discr E : ℤ) : T.V) → ∀ (e : ℕ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e 0 w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr | exact GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr | (intros; apply GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.maximal_ideal_formal_points_form_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  first | exact @GlobalTheory.PlaceInt.smallPts_module | exact GlobalTheory.PlaceInt.smallPts_module | (intros; apply GlobalTheory.PlaceInt.smallPts_module <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.constantCoeff_invariant_operator_along_matrix : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS K n d), MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P (ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) g)) = MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) g) := by
  first | exact @GlobalTheory.MatChain.constantCoeff_dpolyN_matV | exact GlobalTheory.MatChain.constantCoeff_dpolyN_matV | (intros; apply GlobalTheory.MatChain.constantCoeff_dpolyN_matV <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie

theorem ramLoss_le_vLa_pPow (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ)
    (w : WeightFamilies.Wt D j) (a b : ℕ) (ha : c2 D w ≤ a) (hb : Formalism.MainNotions.DIV.Cons.cHalf w ≤ b) :
    ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  obtain ⟨hs, hq, hd, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  have hN : pPow D a b b ≠ 0 := by
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hqp.ne_zero)) (pow_ne_zero _ hdp.ne_zero)
  have hl := Crude.resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hl⟩
  have ha' : (DF w : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (DF w : ℝ) / 2 ≤ b := Nat.ceil_le.1 hb
  have hD : (0 : ℝ) ≤ (DF w : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ (ramOverZ la : ℝ) := Nat.cast_nonneg _
  have hR : ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) = (padicValNat (resCharOf la) (pPow D a b b) : ℝ) * ramOverZ la := by
    rw [Crude.crv_vLa_natCast la hN, Int.cast_natCast, Nat.cast_mul]
  have hz : ∀ p ∈ D.host.condN.primeFactors, p ≠ resCharOf la →
      ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p * (DF w : ℝ) / 2 = 0 := fun p hp hne => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [Crude.crv_vLa_natCast la hpp.ne_zero, Nat.padicValNat_def, multiplicity_primes hne.symm]; simp
  rw [ramLoss, hR]
  by_cases hm : resCharOf la ∈ D.host.condN.primeFactors
  · rw [Finset.sum_eq_single_of_mem _ hm hz, Crude.crv_vLa_natCast la hl.ne_zero, Nat.padicValNat_def, Nat.Prime.multiplicity_self]
    have key : D.host.vdH (resCharOf la) * (DF w : ℝ) / 2 ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) := by
      have hv0 := D.host.vdH_nonneg (resCharOf la)
      have hle : ∀ k : ℕ, resCharOf la ^ k ∣ pPow D a b b → (k : ℝ) ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) :=
        fun k hk => by exact_mod_cast ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN).1 hk
      rcases (D.host.dvd_condN_iff_small hl).1 (Nat.dvd_of_mem_primeFactors hm) with h | h | h
      · have h1 := hle (padicValNat (resCharOf la) D.host.QS * a) (by
          rw [pow_mul]; exact ((pow_dvd_pow_of_dvd (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) a).mul_right _).mul_right _)
        have h2 := (hs _ h).1
        push_cast at h1
        nlinarith [mul_le_mul h2 ha' hD (Nat.cast_nonneg _), mul_nonneg hv0 hD]
      · have h1 := hle b (by rw [h]; exact (Dvd.intro_left _ rfl).mul_right _)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hq hD]
      · have h1 := hle b (by rw [h]; exact Dvd.intro_left _ rfl)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hd hD]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right key he]
  · rw [Finset.sum_eq_zero fun p hp => hz p hp fun h => hm (h ▸ hp)]
    positivity

end GlobalTheory.PlaceTop
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortUnits

open GlobalTheory.LatticeIndex GlobalTheory.TrivLattice

section Val
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem valuation_nat {k : ℕ} (hk : (k : 𝓞 K) ∉ la.asIdeal) : la.valuation K (k : K) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 K) K)]
  exact la.valuation_eq_one_iff_notMem.2 hk

theorem not_mem_of_coprime' {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) :
    (b : 𝓞 K) ∉ la.asIdeal := fun hb => by
  obtain ⟨u, v, e⟩ : IsCoprime (a : 𝓞 K) (b : 𝓞 K) := h.cast
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ ha) (la.asIdeal.mul_mem_left _ hb)))

end Val

theorem vLa_beta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (la : HeightOneSpectrum (𝓞 c.F)) (hA : PullbackSections.AdaptAt Λ la) (β : c.F)
    (hβ : BetaIs (Dw := Dw) c Λ β) : vLa la β = 0 := by
  obtain ⟨k, hk, hk1, hk2⟩ := hA
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  let w := la.valuation c.F
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hw ⟨_, map_isIntegral_int (embF c τ) r.isIntegral_coe⟩
  have hnat : ∀ τ, w.comap (embF c τ) (k : E) = 1 := fun τ => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valuation_nat la hk
  have hm : ∀ (A : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := fun A a1 a2 => by
    have := hasMax_prod hw Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) fun τ => by
      obtain ⟨a, y, hy, b⟩ := detSet_max _ (hwτ τ) A (hnat τ) a1 a2
      have h : HasMax w (idealAt c A τ) 1 := by
        refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
        rintro _ ⟨y, hy, rfl⟩
        exact a y hy
      simpa using h.pow hw (Dw.mult τ)
    simpa using this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {β}) (w β) := hasMax_span hw (by simp) (by simp)
  have f1 := hb.mul (hm Λ.La h1 h2)
  rw [hβ] at f1
  have f := f1.unique (hm Λ.Ln (fun v hv => h1 v hv.1)
    (fun v hv => ⟨h2 v hv, (stdLat E n).toAddSubgroup.nsmul_mem hv k⟩))
  rw [_root_.mul_one] at f
  have f' : la.valuation c.F β = 1 := f
  simp [vLa, f']

theorem vLa_betaH {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ} (Λ : GenLat D.host.E n)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D)) (hA : PullbackSections.AdaptAt Λ la) :
    vLa la (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 0 := by
  have h := hF.sh.beta j hj n (hF.p.kPsi j hj) Λ hU hT
  refine vLa_beta (Dw := T.Q.Dw j) T.Q.c Λ la hA _ ?_
  unfold betaH
  rw [dite_eq_left h]
  exact h.choose_spec.2.1

end GlobalTheory.ShortUnits
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → letI := io.toAlgebra; ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (cc : (E →+* ℂ) → π) (s : (E →+* ℂ) → Bool), (∀ τ, cc (ComplexEmbedding.conjugate τ) = cc τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧ ∃ (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr), (∀ ℓ i, (((-((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E))) : ℝ) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧ (∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 → ∑ i, (algebraMap T.V T.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (0, ψ ℓ)) := by
  first | exact @GlobalTheory.PlaceInt.exists_ramified_eigenLifts | exact GlobalTheory.PlaceInt.exists_ramified_eigenLifts | (intros; apply GlobalTheory.PlaceInt.exists_ramified_eigenLifts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.lattice_trivial_at_prime_indices_and_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → Λ.TrivAt ℓ → (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (T : CDVR) (io : c.F →+* T.Fr), ¬ IsUnit (ℓ : T.V) → (∀ β : c.F, β ≠ 0 → BetaIs (Dw := Dw) c Λ β → vV T.V (io β) = 0) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n := by
  first | exact @GlobalTheory.TrivLattice.trivAt_units | exact GlobalTheory.TrivLattice.trivAt_units | (intros; apply GlobalTheory.TrivLattice.trivAt_units <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.constant_dvd_trace_of_jacobian_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∀ (δ : V) (U : (MvPowerSeries σ V)ˣ), δ ≠ 0 → Matrix.det (Matrix.of fun i j : σ => MvPowerSeries.pderiv (R := V) j (φ i)) = MvPowerSeries.C δ * (U : MvPowerSeries σ V) → ∀ (r : ℕ) (b : Fin r → MvPowerSeries σ V), (∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i) → ∀ (f : MvPowerSeries σ V) (M : Matrix (Fin r) (Fin r) (MvPowerSeries σ V)), (∀ j, f * b j = ∑ i, MvPowerSeries.subst φ (M i j) * b i) → MvPowerSeries.C δ ∣ M.trace := by
  first | exact @GlobalTheory.C_dvd_trace_of_jacobian | exact GlobalTheory.C_dvd_trace_of_jacobian | (intros; apply GlobalTheory.C_dvd_trace_of_jacobian <;> assumption)
end
