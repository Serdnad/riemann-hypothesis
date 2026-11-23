module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle008
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle003
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory.HaarAlg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] in
theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem mul_avg {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    M * avg κ F = avg κ fun g => M * F g := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem avg_mul {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι] in
theorem avg_const (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]

variable [κ.IsMulLeftInvariant]

omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι] in
theorem avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h

theorem rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]

theorem avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]

theorem isAlgebraic_integral (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (Γ : Set K) (hΓ : Dense Γ)
    (halg : ∀ γ ∈ Γ, ∀ a b, IsAlgebraic ℚ (ρ γ a b)) (a b : ι) : IsAlgebraic ℚ (∫ g, ρ g a b ∂κ) := by
  set P := avg κ ρ with hP
  let Q := algebraicClosure ℚ ℂ
  have key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s := fun s => by
    have hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ := fun γ hγ => by
      ext a b
      exact s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    have l : ∀ g, ρ g * P.map s = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show ρ γ * P.map s = P.map s
          rw [← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g
    have r : ∀ g, P.map s * ρ g = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show P.map s * ρ γ = P.map s
          rw [← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g
    constructor
    · conv_lhs => rw [hP]
      rw [avg_mul κ hρ]
      simp only [← hP, l, avg_const]
    · conv_lhs => rw [hP]
      rw [mul_avg κ hρ]
      simp only [← hP, r, avg_const]
  have fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P := fun s => by
    have h1 := congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1
    have e : (P.map s.symm).map s = P := by ext a b; simp
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    simp only [hm, e] at h1
    rw [← (key s).2, h1]
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b)
    fun s => congrFun (congrFun (fix s) a) b
  have : P a b ∈ Q := hq ▸ q.2
  exact mem_algebraicClosure_iff.1 this

end GlobalTheory.HaarAlg
end

section


theorem _root_.GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  first | exact @GlobalTheory.bilinear_bound_of_dense_right | exact GlobalTheory.bilinear_bound_of_dense_right | (intros; apply GlobalTheory.bilinear_bound_of_dense_right <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mem_closure_of_forall_clm_vanish : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  first | exact @GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | exact GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | (intros; apply GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_skewHermitian_log_of_unitary : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  first | exact @GlobalTheory.unitary_exists_skew_log | exact GlobalTheory.unitary_exists_skew_log | (intros; apply GlobalTheory.unitary_exists_skew_log <;> assumption)
end

section

open MeasureTheory

namespace GlobalTheory

theorem trigPoly_dense_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ x, ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | (apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx ..)

end GlobalTheory
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.summable_norm_coset_out' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  first | exact @GlobalTheory.summable_norm_coset_out | exact GlobalTheory.summable_norm_coset_out | (intros; apply GlobalTheory.summable_norm_coset_out <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) → ∀ x, F x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | exact GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | (intros; apply GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant <;> assumption)
end

section

open MeasureTheory


theorem _root_.GlobalTheory.T.integrable_of_tsum_norm_translate_le : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ := by
  first | exact @GlobalTheory.integrable_of_tsum_translate_norm_le | exact GlobalTheory.integrable_of_tsum_translate_norm_le | (intros; apply GlobalTheory.integrable_of_tsum_translate_norm_le <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_clm_of_gram_eq_smul' : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  first | exact @GlobalTheory.exists_clm_of_gram_eq_smul | exact GlobalTheory.exists_clm_of_gram_eq_smul | (intros; apply GlobalTheory.exists_clm_of_gram_eq_smul <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.norm_creationAnnihilation_word_le_numberOperator_pow : ∀ (T H κ : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype κ] (Φ : T →ₗ[ℂ] H) (a c : κ → Module.End ℂ T) (M : Module.End ℂ T) (r r' : ℝ), 1 ≤ r → r' ≤ r → (∀ j x y, inner ℂ (Φ (c j x)) (Φ y) = inner ℂ (Φ x) (Φ (a j y))) → (∀ j, a j * c j - c j * a j = (r' : ℂ) • 1) → M = ∑ j, c j * a j + (r : ℂ) • 1 → (∀ j, M * a j = a j * (M - (r : ℂ) • 1)) → (∀ j, M * c j = c j * (M + (r : ℂ) • 1)) → ∀ (l : List (Module.End ℂ T)) (d : ℕ), (∀ X ∈ l, X ∈ Submodule.span ℂ (Set.range a ∪ Set.range c)) → l.length ≤ d → ∃ C : ℝ, ∀ x, ‖Φ (l.prod x)‖ ≤ C * ‖Φ ((M ^ d) x)‖ := by
  first | exact @GlobalTheory.norm_word_le_number_pow | exact GlobalTheory.norm_word_le_number_pow | (intros; apply GlobalTheory.norm_word_le_number_pow <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.dense_span_tensor_of_dense_subspaces' : ∀ {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs) (W : ∀ i, Submodule ℂ (H i)), (∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → (∀ i, Dense (W i : Set (H i))) → Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) : Set Hs) := by
  first | exact @GlobalTheory.dense_span_tensor_of_dense_subspaces | exact GlobalTheory.dense_span_tensor_of_dense_subspaces | (intros; apply GlobalTheory.dense_span_tensor_of_dense_subspaces <;> assumption)
end
