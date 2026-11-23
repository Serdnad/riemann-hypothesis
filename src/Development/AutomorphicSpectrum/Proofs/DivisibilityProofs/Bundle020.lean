module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle006
public import Development.WeilBound.CoreStatements.FlagImmersions.RestDegreePowerBound
public import Development.WeilBound.CoreStatements.FlagImmersions.AntisymmetryTowerTheorem
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle007
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle017
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
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem identOnDecomposedForm : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) :=
  @RootFieldNumerics.tower_point_count_identity

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem mean_slope_of_volume_eq : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval :=
  @RootFieldNumerics.mean_slope_of_proportional_volume

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kappa_bound_of_decomp : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (u : Wt Ψ N) (g : ℝ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → WeightHyp j u g → IsDecomp (linRoot u ^ (dimFl Ψ N + 1)) Q → ∀ (τ : Ψ) (σ : Ψ ⊕ Ψ) (k : ℕ), 2 ≤ k → k ≤ N → |k * degFl (pLie j (k - 1) σ * Q τ k)| ≤ ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) * ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
  intro Ψ _ _ N j u g Q _ hjN hW hD τ σ k hk2 hkN
  obtain ⟨τ', I, hcard, hsmall, heq⟩ :=
    RootFieldNumerics.M5.small_block j hjN σ (k - 1) (by omega) (Q τ k)
  have hbound : ∀ i ∈ I,
      |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| ≤
        ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
    fun i hi => RootFieldNumerics.M5.one_bound j u g Q hW hD τ τ' k hk2 hkN i (hsmall i hi)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |(k : ℝ) * degFl (pLie j (k - 1) σ * Q τ k)|
      = (k : ℝ) * |RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (pLie j (k - 1) σ * Q τ k)| := by
        rw [RootFieldNumerics.M5.degFl_eq, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg hk0]
    _ = (k : ℝ) * |∑ i ∈ I, RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [heq]
    _ = |∑ i ∈ I, (k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| := by
        rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hk0]
    _ ≤ ∑ i ∈ I, |(k : ℝ) * RootFieldNumerics.M5.alt RootFieldNumerics.M5.rho (MvPolynomial.X (τ', i) ^ (k - 1) * Q τ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, ((dimFl Ψ N : ℝ) + 1) * flagDeg u *
          (2 ^ (k - 1) / (k.factorial : ℝ) * ((⨆ i, u τ i) - ⨅ i, u τ i) *
            (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) :=
        Finset.sum_le_sum hbound
    _ = ((dimFl Ψ N : ℝ) + 1) * flagDeg u * ((min j (N - j) : ℕ) * (2 ^ (k - 1) / (k.factorial : ℝ)) *
          ((⨆ i, u τ i) - ⨅ i, u τ i) * (N * (1 + 2 * (‖u‖ / g))) ^ (k - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.cycle_number_mul_expand : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * cycNum Z cls H (classList cls μ ++ Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_mul <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.root_power_sum_mixed_expansion : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ), Q.IsHomogeneous (d + 1 - k) → ∃ Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ, (∀ i, (Hs i).IsHomogeneous (d - k)) ∧ (k = d + 1 → ∀ i, Hs i = 0) ∧ IsMixExpansion d (mixDiff (rootPs τ k * Q)) (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | exact GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootPs_mul_mixExpansion <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem thmB_functional : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh :=
  @RootFieldNumerics.antisymmetry_tower_theorem

end GlobalTheory.CompanionTheory.Ar.Top
end

section


theorem _root_.GlobalTheory.T.sum_log_prime_div_pred_bound : ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | exact GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.arith_intersection_multilinear : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_combLine <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem intersection_combLine_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) :=
  @RootFieldNumerics.intersection_multilinear_expansion

end GlobalTheory.CompanionTheory.Ar.Top
end
