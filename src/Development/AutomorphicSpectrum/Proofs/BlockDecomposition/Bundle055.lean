module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle014
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle012
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.uniform_lower_bound_near_injective : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  first | exact @GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | exact GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | (intros; apply GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective <;> assumption)
end

section


theorem _root_.GlobalTheory.T.lt_one_of_power_bound : ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | exact GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | (intros; apply GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.le_one_of_power_bounds : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | exact GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | (intros; apply GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula : ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ), ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ → tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) → g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det → ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 * (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | exact GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | (intros; apply GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.induced_generated_by_K_finite : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | exact GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | (intros; apply GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_joint_eigenvector_nonzero : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J] (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) → ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m → ((∑ j, c j • H (s j)) ^ m) v ≠ 0 → ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | exact GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | (intros; apply GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eigenvector_lift_of_surjection : ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'), Function.Surjective f → f ∘ₗ T = S ∘ₗ f → ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  first | exact @GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | exact GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | (intros; apply GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.iwasawa_unitary_upper_triangular : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ), IsUnit g → ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ, g = k * b ∧ b.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | exact GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitary_extension_of_block : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ), s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' → b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | exact GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | (intros; apply GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.antitone_diagonal_conjugate : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | exact GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder | (intros; apply GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.centralizer_regular_commutes : ∀ {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * H * U).IsDiag → (Uᴴ * A * U).IsDiag → (∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j) → H * Y = Y * H → Y * A = A * Y := by
  first | exact @GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | exact GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag | (intros; apply GlobalTheory.CompanionTheory.MatrixComm.commute_of_dominated_diag <;> assumption)
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.SimDiag

theorem exists_unitary_isDiag {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ A ∈ S, Aᴴ = A) (hC : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
    fun M => Matrix.toEuclideanLin M
  have hL : ∀ M v, L M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := fun _ _ => rfl
  obtain ⟨m, b, hb⟩ := Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting (L '' S)
    (by
      rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      refine LinearMap.ext fun v => ?_
      change L M (L N v) = L N (L M v)
      simp only [hL, Matrix.mulVec_mulVec, hC M hM N hN])
    (by
      rintro _ ⟨M, hM, rfl⟩
      refine ⟨M, hM, ?_⟩
      change Matrix.toEuclideanLin M = LinearMap.adjoint (Matrix.toEuclideanLin M)
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH M hM])
  have hm : m = n := by
    have := Module.finrank_eq_card_basis b.toBasis
    simpa [finrank_euclideanSpace] using this.symm
  subst hm
  have hinner : ∀ j k, ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i =
      if j = k then 1 else 0 := by
    intro j k
    have := orthonormal_iff_ite.1 b.orthonormal j k
    rw [PiLp.inner_apply] at this
    simpa [RCLike.inner_apply, mul_comm] using this
  let U : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i k => WithLp.ofLp (b k) i
  refine ⟨U, ?_, fun A hA => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, U, Matrix.of_apply]
    exact hinner j k
  · intro j k hjk
    obtain ⟨μ, hμ⟩ := hb k (L A) ⟨A, hA, rfl⟩
    have hv : A *ᵥ WithLp.ofLp (b k) = μ • WithLp.ofLp (b k) := by
      have := congrArg WithLp.ofLp hμ
      simpa [hL] using this
    have hAU : ∀ i, (A * U) i k = μ * WithLp.ofLp (b k) i := by
      intro i
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, U] using this
    have h0 := hinner j k
    rw [if_neg hjk] at h0
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hAU]
    calc ∑ i, Uᴴ j i * (μ * WithLp.ofLp (b k) i)
        = μ * ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.conjTranspose_apply, U, Matrix.of_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]

end GlobalTheory.CompanionTheory.SimDiag
end
