module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemOpenOfForms
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCount
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientFamilyEigenFrame
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.semicharacter_theta_characteristic : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | exact GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Nform.exists_half_canMult <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.theta_function_canonical_multiplier : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (a c : Fin g → ℝ) (θ : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv τ) (h.mulVec z) (h.mulVec w)) →
    Differentiable ℂ θ →
    (∀ (m n : Fin g → ℤ) (lam : Fin g → ℂ), h.mulVec lam = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      ∀ z, θ (z + lam) = GlobalTheory.CanTh.canMult a c m n *
        Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) * θ z) →
    ∃ κ : ℂ, ∀ z, θ z = κ * GlobalTheory.CanTh.canTh τ a c (h.mulVec z) := by
  first | exact @GlobalTheory.CompanionTheory.CanThLine.level_one_line | exact GlobalTheory.CompanionTheory.CanThLine.level_one_line | (intros; apply GlobalTheory.CompanionTheory.CanThLine.level_one_line <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_weight_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | exact GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_degree_count_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms | exact GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.FormsVal.mem_open_of_forms <;> assumption)
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_degree_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ w ∈ mcPts (mCoordIdeal RM.y), ∃ (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) ∧ aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf ∧ aeval RM.y Hf ≠ 0 ∧ aeval w Hf ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep | exact GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.origin_section_rep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.psh_log_growth_bounded_near_puncture : ∀ (n a : ℕ) (ρ C : ℝ) (u : (Fin n → ℂ) → ℝ), 0 < ρ → ρ ≤ 1 → ReciprocityTheory.AnForm.A.IsPsh (Flat.punct n a ρ) u → (∀ t ∈ Flat.punct n a ρ, u t ≤ C * (1 + Real.log (Flat.logSize a t))) → ∃ C' : ℝ, ∀ t ∈ Flat.punct n a (ρ / 2), u t ≤ C' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture | exact GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture | (intros; apply GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.continuous_first_minimum_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | exact GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.linearIndependent_real_periods_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ), LinearIndependent ℝ (fun j => R.P (b j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_basis_periods_linearIndependent <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.eigen_component_polynomial_in_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ), ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum | exact GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula.eigComp_eq_sum <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.isometry_preserves_hermitian_and_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | exact GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.continuous_cusp_norm_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have hcont : Continuous fun x => (R x).nzOf σ I h.choose_spec.choose :=
      GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nzOf R hP hH σ I _
    simpa only [RiemLat.nz, dite_eq_left h] using hcont
  · simpa only [RiemLat.nz, dite_eq_right h] using
      (continuous_const : Continuous fun _ : X => (1 : ℝ))
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.quotient_family_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) (r k : ℕ) (v : Fin r → Λ) (x : Fin k → Fin g → ℂ), IsIsoSub R.form I → IsNzFamily I r v → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → (∀ y z, (∀ u ∈ I, R.ip (R.P u) y = 0) → R'.ip (q y) (q z) = R.ip y z) → (∀ j, x j ∈ eigSp R.B s) → (R.gram (Fin.append (fun a => eigComp R.B s (R.P (v a))) x)).det = (R.gram (fun a => eigComp R.B s (R.P (v a)))).det * (R'.gram (fun j => q (x j))).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq <;> assumption)
end
