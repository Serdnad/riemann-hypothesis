module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle006
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle001
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle005
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory

theorem _root_.GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) →
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.hasDerivAt_diag_sum_prod_pairing | exact GlobalTheory.hasDerivAt_diag_sum_prod_pairing | (intros; apply GlobalTheory.hasDerivAt_diag_sum_prod_pairing <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hasSum_and_summable_on_ball_of_hasSum_on_interval : ∀ {ι : Type} (deg : ι → ℕ), (∀ k, {i | deg i = k}.Finite) → ∀ (a : ι → ℂ) (b : ι → ℝ) (C δ ρ : ℝ) (P P' : ℂ → ℂ), 0 < δ → (∀ i, 0 ≤ b i) → (∀ i, ‖a i‖ ≤ C * b i) → DifferentiableOn ℂ P (Metric.ball 0 ρ) → DifferentiableOn ℂ P' (Metric.ball 0 ρ) → (∀ x : ℝ, 0 < x → x < δ → HasSum (fun i => a i * (x : ℂ) ^ deg i) (P x) ∧ HasSum (fun i => (b i : ℂ) * (x : ℂ) ^ deg i) (P' x)) → ∀ X : ℂ, ‖X‖ < ρ → HasSum (fun i => a i * X ^ deg i) (P X) ∧ Summable (fun i => b i * ‖X‖ ^ deg i) := by
  first | exact @GlobalTheory.gradedSeries_continuation_dominated | exact GlobalTheory.gradedSeries_continuation_dominated | (intros; apply GlobalTheory.gradedSeries_continuation_dominated <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_isometry_inner_product_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ),
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  first | exact @GlobalTheory.schwartz_L2_isometry_preserves_inner | exact GlobalTheory.schwartz_L2_isometry_preserves_inner | (intros; apply GlobalTheory.schwartz_L2_isometry_preserves_inner <;> assumption)
end

section

open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' : ∀ (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ)), (∀ (j : l) (x : EuclideanSpace ℝ l), fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0) → ∀ x, h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.schwartz_eq_zero_of_wrong_sign_gaussian_relation : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  first | exact @GlobalTheory.WrongSignGauss.vanish | exact GlobalTheory.WrongSignGauss.vanish | (intros; apply GlobalTheory.WrongSignGauss.vanish <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.uniformly_negDefinite_near_of_continuous_quadForm_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    Continuous (fun p : ℝ × V => M p.1 p.2 p.2) → (∀ t v, v ≠ 0 → (M t v v).re < 0) →
    ∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2) := by
  first | exact @GlobalTheory.quadForm_unif_target | exact GlobalTheory.quadForm_unif_target | (intros; apply GlobalTheory.quadForm_unif_target <;> assumption)
end

section

open MeasureTheory


theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → ∀ c g : G → ℂ, Integrable c μ → Continuous g → (∃ B : ℝ, ∀ w, ‖g w‖ ≤ B) → ∫ w, c w * g w ∂μ = ∫ w in 𝓕, ∑' γ : Γ, c ((γ : G) + w) * g ((γ : G) + w) ∂μ := by
  first | exact @GlobalTheory.unfold_integral_fundamentalDomain | exact GlobalTheory.unfold_integral_fundamentalDomain | (intros; apply GlobalTheory.unfold_integral_fundamentalDomain <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  first | exact @GlobalTheory.unfold_tsum_along_subgroup | exact GlobalTheory.unfold_tsum_along_subgroup | (intros; apply GlobalTheory.unfold_tsum_along_subgroup <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.continuous_right_convolution_bounded_integrable : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (m : Measure H) (α : H → ℂ), Integrable α m → ∀ (φ : G → ℂ), Continuous φ → ∀ B : ℝ, (∀ g, ‖φ g‖ ≤ B) → Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  first | exact @GlobalTheory.conv_right_continuous | exact GlobalTheory.conv_right_continuous | (intros; apply GlobalTheory.conv_right_continuous <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G), μ 𝓕 < ⊤ → ∀ (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (ψ φ : G → ℂ), Continuous ψ → Continuous φ → ∀ (A B : ℝ), (∀ g, ‖ψ g‖ ≤ A) → (∀ g, ‖φ g‖ ≤ B) → IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧ Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧ ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  first | exact @GlobalTheory.fubini_right_convolution_bounded_continuous | exact GlobalTheory.fubini_right_convolution_bounded_continuous | (intros; apply GlobalTheory.fubini_right_convolution_bounded_continuous <;> assumption)
end
