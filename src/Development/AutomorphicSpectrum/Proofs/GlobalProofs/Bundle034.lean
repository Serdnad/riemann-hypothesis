module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle032
public import Development.WeilBound.CoreStatements.ProjectiveValuations.CompactSpaceComplexPointsOfProper
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

theorem _root_.GlobalTheory.T.regular_function_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsSeparated p → LocallyOfFiniteType p → ∀ (V : Y.Opens), IsAffineOpen V → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)), ∀ (W : Y.Opens), IsAffineOpen W → ∀ g : Γ(Y, V ⊓ W), ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W), ‖ev p (RingHom.id ℂ) (V ⊓ W) g y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_gens_bound | exact GlobalTheory.CompanionTheory.Gaga.exists_gens_bound | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_gens_bound <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem compactSpace_cxPts_of_isProper :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → CompactSpace (CxPts p (RingHom.id ℂ)) :=
  DifferentiableLines.compactSpace_complex_points_of_proper

end GlobalTheory.CompanionTheory.Gaga
end

section

open Matrix Formalism.REAL
open GlobalTheory.SmoothGlob (lieSet)

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.KStable

variable {n : ℕ} {ε : Fin n → Bool}

theorem skew_of_commute {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) :
    Xᴴ = -X := by
  have h : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]
    _ = (Xᴴ * Jm ε) * Jm ε := by rw [Matrix.mul_assoc]
    _ = -(X * (Jm ε * Jm ε)) := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -X := by rw [Formalism.REAL.Jm_mul_self, Matrix.mul_one]

theorem exp_mem_Kset {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (hc : X * Jm ε = Jm ε * X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Kset ε := by
  have hs := skew_of_commute hX hc
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hs]
    have hneg : star t • -X = -(t • X) := by simp
    have hcm : Commute (t • X) (-(t • X)) := (Commute.refl _).neg_right
    rw [hneg, ← Matrix.exp_add_of_commute _ _ hcm]
    simp
  · exact ((show Commute X (Jm ε) from hc).smul_left t).exp_left

end GlobalTheory.CompanionTheory.Hypotheses₂.KStable

end
end

section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem differentiableOn_tsum_weighted_DL_halfplane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  intro ι _ r a b ha hb B N cs u hN hu hsupp
  classical
  obtain ⟨Cu, hCu⟩ := hu
  have hCu0 : 0 ≤ Cu := (abs_nonneg _).trans (hCu 0)
  have hopen : ∀ R : ℕ, IsOpen {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := fun R =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have key : ∀ R : ℕ, DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m)
      {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := by
    intro R
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.real_difference_cone_bound ι r a b ha hb B R cs 0
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun m : Fin r → ℕ => Cu * C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹)
      ((GlobalTheory.T.summable_inverse_square_product r).mul_left _) ?_ (hopen R) ?_
    · intro m
      exact ((GlobalTheory.T.finite_difference_cone_term_differentiable ι r a b ha hb cs m).const_mul _).differentiableOn
    · intro m s hs
      have hprod : 0 ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ :=
        Finset.prod_nonneg fun i _ => by positivity
      by_cases hum : u m = 0
      · simp only [hum, Rat.cast_zero, zero_mul, norm_zero]
        positivity
      · have hcount : ∀ i, cs.count i = N ∨ m i = 0 := by
          intro i
          rcases hsupp i with h | h
          · exact Or.inl h
          · exact Or.inr (by_contra fun hne => hum (h m hne))
        have hbound := hC s hs.1.le hs.2.le (fun i => (m i : ℝ)) (fun i => Nat.cast_nonneg _)
        simp only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at hbound
        have hsize := GlobalTheory.T.size_power_le_inverse_square_product r (Fintype.card ι) B N cs m hN hcount
        have hDL : ‖DL cs (coneTerm a b s) m‖ ≤ C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
          rw [GlobalTheory.T.finite_difference_cone_term_eq ι r a b s cs m]
          exact hbound.trans (mul_le_mul_of_nonneg_left hsize hC0)
        rw [norm_mul, Complex.norm_ratCast, mul_assoc]
        exact mul_le_mul (hCu m) hDL (norm_nonneg _) hCu0
  intro s hs
  obtain ⟨R, hR⟩ := exists_nat_gt ‖s‖
  have hmem : s ∈ {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := ⟨hR, hs⟩
  exact ((key R s hmem).differentiableAt ((hopen R).mem_nhds hmem)).differentiableWithinAt

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

theorem _root_.GlobalTheory.T.cone_tiling_by_sign_regions : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] {κ : Type} [Fintype κ] (P : ConvexCone ℚ V)
    (b : Module.Basis κ ℚ V), (∀ i, b i ∈ P) → ∀ (Λ : Set (V →ₗ[ℚ] ℚ)), Λ.Finite → ∀ (E : Set V),
    (∀ x ∈ E, ∀ i, 0 < b.repr x i) →
    (∀ x y, (∀ i, 0 < b.repr x i) → (∀ i, 0 < b.repr y i) →
      (∀ l ∈ Λ, SignType.sign (l x) = SignType.sign (l y)) → x ∈ E → y ∈ E) →
    Tile (P : Set V) (fun _ => True) E := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.SignTiles.tile_of_signs <;> assumption)
end
