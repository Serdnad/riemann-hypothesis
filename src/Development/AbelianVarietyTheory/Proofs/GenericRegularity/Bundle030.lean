module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (h : GenFrEx Xo c) (A : Type) [CommRing A] [IsDomain A] [Algebra c.F A] (j : Sp A ⟶ Xo.XF c) (yA : FrPt Xo c A), IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) → Algebra.Smooth c.F A → yA.x = j ≫ pullback.fst _ _ → ∀ σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), ∃ C : FChart h, ∀ (L : Type) [Field L] [Algebra c.F L] (f : A →ₐ[c.F] L) (z₀ y : FrPt Xo c L) (x : FlagVar Dw → L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), FrMap f yA z₀ → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Reframe (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) z₀ y → ∃ (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y := by
  first | exact @GlobalTheory.Reg.exists_fChart_cell | exact GlobalTheory.Reg.exists_fChart_cell | (intros; apply GlobalTheory.Reg.exists_fChart_cell <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_section_of_generic_values_regular_on_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, wchar (ex Dw a n) C.t * b C.Z ∈ C.R) → ∃ g ∈ sec Xo c a n, ∀ Z, evC h Z g = b Z := by
  exact @GlobalTheory.Reg.SecGlue.exists_sec_of_regular
end

section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.exists_idem_section : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c → ∀ h : _root_.Formalism.L2.Pj.GenFrEx Xo c,
      _root_.GlobalTheory.Reg.Atlas h → ∀ Z : _root_.Formalism.L2.Pj.Comp Xo c, ∃ χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0,
        χ * χ = χ ∧ _root_.Formalism.L2.Pj.evC h Z χ = 1 ∧ ∀ Z', Z' ≠ Z → _root_.Formalism.L2.Pj.evC h Z' χ = 0 := by
  intro E _ _ _ H Dw l Xo c hev h hcov Z
  classical
  have hexp : _root_.Formalism.L2.Pj.ex Dw 0 0 = 0 := by
    unfold _root_.Formalism.L2.Pj.ex
    funext x
    cases x <;> rfl
  have hreg : ∀ C : _root_.GlobalTheory.Reg.FChart h,
      _root_.Formalism.L2.Pj.wchar (_root_.Formalism.L2.Pj.ex Dw 0 0) C.t *
        (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) C.Z ∈ C.R := by
    intro C
    rw [hexp]
    unfold _root_.Formalism.L2.Pj.wchar
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, _root_.one_mul]
    split_ifs
    · exact C.R.one_mem
    · exact C.R.zero_mem
  obtain ⟨χ, hχ, hval⟩ := _root_.GlobalTheory.Reg.SecGlue.exists_sec_of_regular E H Dw l Xo c hev h
    hcov 0 0 (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) hreg
  refine ⟨χ, hχ, ?_, by simp [hval], fun Z' hZ' => by simp [hval, hZ']⟩
  have hsq : χ * χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := by simpa using _root_.Formalism.L2.Pj.sec_mul Xo c 0 0 0 0 hχ hχ
  have hmem : χ * χ - χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := Submodule.sub_mem _ hsq hχ
  refine sub_eq_zero.mp (_root_.GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hev h hcov
    0 0 _ hmem fun Z' => ?_)
  have hmul : _root_.Formalism.L2.Pj.evC h Z' (χ * χ) = _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_mul _ _ _ _ _
  have hadd : _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ + χ) =
      _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ) + _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_add _ _ _ _ _
  have hidem : _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ = _root_.Formalism.L2.Pj.evC h Z' χ := by
    rw [hval]
    split_ifs <;> simp
  rw [sub_add_cancel, hmul, hidem] at hadd
  exact add_eq_right.mp hadd.symm

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_normalCharts_everyFinitePlace : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → ∀ la : HeightOneSpectrum (𝓞 c.F), ModelAt Xo c la → (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ := by
  first | exact @GlobalTheory.Reg.exists_sCharts | exact GlobalTheory.Reg.exists_sCharts | (intros; apply GlobalTheory.Reg.exists_sCharts <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

theorem _root_.GlobalTheory.T.numerical_consequences_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  first | exact @GlobalTheory.PinNum.numerics_of_pins | exact GlobalTheory.PinNum.numerics_of_pins | (intros; apply GlobalTheory.PinNum.numerics_of_pins <;> assumption)
end
