module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle057
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle058
public import Mathlib.RingTheory.Ideal.Maximal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.Instances.Matrix
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Mathlib.LinearAlgebra.Matrix.Block
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.ShiftLine

theorem integral_vertical_line_eq {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ) (hab : a ≤ b)
    (hd : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b})
    (hb : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) :
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  have hpt : ∀ c y : ℝ, (⟨c, y⟩ : ℂ) = (c : ℂ) + (y : ℂ) * Complex.I := by
    intro c y
    apply Complex.ext <;> simp
  simp only [hpt]
  have hint : ∀ c ∈ Set.Icc a b,
      Integrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I)) := by
    intro c hc
    have hcont : Continuous fun y : ℝ => f ((c : ℂ) + (y : ℂ) * Complex.I) :=
      hd.continuousOn.comp_continuous (by fun_prop) (fun y => by simpa using hc)
    refine ((integrable_exp_neg_mul_sq one_pos).const_mul M).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have := hb ((c : ℂ) + (y : ℂ) * Complex.I) (by simpa using hc)
    simpa using this
  have hhor : ∀ s : ℝ,
      ‖∫ x in a..b, f ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ M * Real.exp (-s ^ 2) * (b - a) := by
    intro s
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := M * Real.exp (-s ^ 2)) (f := fun x : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I)) ?_
    · rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    · intro x hx
      rw [Set.uIoc_of_le hab] at hx
      have := hb ((x : ℂ) + (s : ℂ) * Complex.I) (by simp; exact ⟨hx.1.le, hx.2⟩)
      simpa using this
  have hrect : ∀ R : ℝ, 0 ≤ R →
      ((∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
          ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) +
        Complex.I • (∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I • (∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    intro R _
    refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -R⟩ ⟨b, R⟩ ?_
    refine hd.mono fun z hz => ?_
    exact (Set.uIcc_of_le hab).subset (Complex.mem_reProdIm.mp hz).1
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have hH : Tendsto (fun R : ℝ => (∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) -
      ∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)) atTop (𝓝 0) := by
    have hT : Tendsto (fun R : ℝ => 2 * (M * Real.exp (-R ^ 2) * (b - a))) atTop (𝓝 0) := by
      simpa using ((hexp.const_mul M).mul_const (b - a)).const_mul 2
    refine squeeze_zero_norm (fun R => ?_) hT
    calc _ ≤ ‖∫ x in a..b, f ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ +
            ‖∫ x in a..b, f ((x : ℂ) + (R : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ M * Real.exp (-(-R) ^ 2) * (b - a) + M * Real.exp (-R ^ 2) * (b - a) :=
          add_le_add (hhor (-R)) (hhor R)
      _ = 2 * (M * Real.exp (-R ^ 2) * (b - a)) := by
          rw [neg_sq]
          ring
  have hVa : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((a : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint a ⟨le_rfl, hab⟩) tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f ((b : ℂ) + (y : ℂ) * Complex.I)) atTop
      (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hint b ⟨hab, le_rfl⟩) tendsto_neg_atTop_atBot tendsto_id
  have hlim := (hH.add (hVb.const_smul Complex.I)).sub (hVa.const_smul Complex.I)
  have heq : (0 : Y) + Complex.I • (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr'
      ((eventually_ge_atTop 0).mono fun R hR => (hrect R hR).symm))
  rw [zero_add, ← smul_sub, smul_eq_zero] at heq
  rcases heq with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.mp h).symm

theorem shift_vertical_line : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (f : ℂ → Y) (a b M : ℝ), a ≤ b → DifferentiableOn ℂ f {z : ℂ | z.re ∈ Set.Icc a b} →
    (∀ z : ℂ, z.re ∈ Set.Icc a b → ‖f z‖ ≤ M * Real.exp (-z.im ^ 2)) →
    ∫ y : ℝ, f ⟨a, y⟩ = ∫ y : ℝ, f ⟨b, y⟩ := by
  intro Y _ _ _ f a b M hab hd hb
  exact integral_vertical_line_eq f a b M hab hd hb

end GlobalTheory.CompanionTheory.TubeFourier.ShiftLine
end

section

open ValuativeRel MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CharLattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def annihilator (ψ : AddChar k Circle) (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := fun t _ => by simp
  add_mem' := fun {x y} hx hy t ht => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := fun {x} hx t ht => by
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]

theorem isOpen_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) (hb : b ≠ 0) :
    IsOpen (annihilator ψ n b : Set (Fin n → k)) := by
  obtain ⟨γ, hγ0, hγ⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  apply AddSubgroup.isOpen_of_mem_nhds
  have hball : {z : k | valuation k z < γ} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ0
  have hmul : {y : k | valuation k (b * y) < γ} ∈ nhds (0 : k) := by
    have h := (continuous_const.mul continuous_id : Continuous fun y : k => b * y).tendsto' 0 0 (mul_zero b)
    exact h hball
  have hU : (Set.univ.pi fun _ : Fin n => {y : k | valuation k (b * y) < γ}) ∈ nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ (fun j _ => hmul)
  refine Filter.mem_of_superset hU ?_
  intro x hx t ht
  apply hγ
  show valuation k (b * ∑ i, t i * x i) < γ
  rw [Finset.mul_sum]
  refine (valuation k).map_sum_lt hγ0 fun j _ => ?_
  have hxj : valuation k (b * x j) < γ := hx j (Set.mem_univ j)
  have htj : valuation k (t j) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (ht j)
  refine lt_of_le_of_lt ?_ hxj
  calc valuation k (b * (t j * x j)) = valuation k (t j) * valuation k (b * x j) := by
        rw [← map_mul]; ring_nf
    _ ≤ 1 * valuation k (b * x j) := mul_le_mul_left htj _
    _ = valuation k (b * x j) := one_mul _

theorem isClosed_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) :
    IsClosed (annihilator ψ n b : Set (Fin n → k)) := by
  have e : (annihilator ψ n b : Set (Fin n → k)) =
      ⋂ (t : Fin n → k) (_ : ∀ j, t j ∈ 𝒪[k]), {x | ψ (b * (t ⬝ᵥ x)) = 1} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [e]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (hψ.comp (continuous_const.mul (continuous_const.dotProduct continuous_id)))
      continuous_const

theorem annihilator_subset (ψ : AddChar k Circle) (n : ℕ) (b : k) (hb : b ≠ 0) (y₀ : k)
    (hy : ψ y₀ ≠ 1) :
    (annihilator ψ n b : Set (Fin n → k)) ⊆
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (y₀ / b)}) := by
  intro x hx j _
  have hx' : ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1 := hx
  show valuation k (x j) ≤ valuation k (y₀ / b)
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  have hxj : x j ≠ 0 := by
    intro h
    rw [h, map_zero] at hlt
    exact not_lt_zero hlt
  have ht : ∀ i, (Pi.single j (y₀ / b / x j) : Fin n → k) i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, map_div₀]
      exact (div_le_one₀ ((valuation k).pos_iff.2 hxj)).2 hlt.le
    · rw [Pi.single_eq_of_ne hij, map_zero]
      exact zero_le_one
  have h := hx' _ ht
  have e : b * ((Pi.single j (y₀ / b / x j) : Fin n → k) ⬝ᵥ x) = y₀ := by
    rw [single_dotProduct]
    field_simp
  rw [e] at h
  exact hy h

theorem isCompact_isOpen_annihilator :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 →
      IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧
      IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  intro k _ _ _ _ ψ hψ hne n b hb
  have e : {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} =
      (annihilator ψ n b : Set (Fin n → k)) := rfl
  rw [e]
  obtain ⟨y₀, hy⟩ : ∃ y₀, ψ y₀ ≠ 1 := by
    by_contra h
    exact hne (AddChar.ext ψ 1 fun y => by
      rw [AddChar.one_apply]
      by_contra hy
      exact h ⟨y, hy⟩)
  refine ⟨?_, isOpen_annihilator ψ hψ n b hb⟩
  exact (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _).of_isClosed_subset
    (isClosed_annihilator ψ hψ n b) (annihilator_subset ψ n b hb y₀ hy)

end GlobalTheory.CompanionTheory.CharLattice
end
end

section

open ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CharConductor

theorem exists_conductor_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  intro k _ _ _ _ ψ hψ a c ha hc
  classical
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hc0 : valuation k c ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    exact hc (by rw [h0, AddChar.map_zero_eq_one])
  obtain ⟨m, hm⟩ := exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)] at hm
  have hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1 := by
    refine ⟨m, fun μ hμ => hball _ ?_⟩
    have hμ1 : valuation k μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
    rw [map_mul, map_mul, map_pow]
    calc valuation k μ * valuation k a ^ m * valuation k c
        ≤ 1 * valuation k a ^ m * valuation k c := by gcongr
      _ = valuation k a ^ m * valuation k c := by rw [one_mul]
      _ < γ := hm
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hfind
    exact hc (by simpa using hfind 1 (one_mem _))
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (m := r) (by omega)
  push Not at hmin
  obtain ⟨μ, hμ, hne⟩ := hmin
  refine ⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩
  have h := hfind (s * μ) (mul_mem hs hμ)
  rw [hr] at h
  have e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c := by ring
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CharConductor
end

section

open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_rank_completion_symmetry : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | exact GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | (intros; apply GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.tensor_eval_fixed_of_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  first | exact @GlobalTheory.CompanionTheory.FrobFix.extension_fixed | exact GlobalTheory.CompanionTheory.FrobFix.extension_fixed | (intros; apply GlobalTheory.CompanionTheory.FrobFix.extension_fixed <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fundamental_domain_fibration_volume : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ : Subgroup N) [Countable Γ] (𝓕N : Set N), IsFundamentalDomain Γ 𝓕N ν → ν 𝓕N < ⊤ → ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (dA : Measure V) [dA.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (D : Set V), IsAddFundamentalDomain Λ D dA → dA D = 1 → ∀ l : N → V, Continuous l → (∀ x y, l (x * y) = l x + l y) → Function.Surjective l → (∀ γ ∈ Γ, l γ ∈ Λ) → ∀ f : V → ℝ≥0∞, Measurable f → ∫⁻ m in 𝓕N, ∑' a : Λ, f ((a : V) + l m⁻¹) ∂ν = ν 𝓕N * ∫⁻ x, f x ∂dA := by
  first | exact @GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | exact GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq | (intros; apply GlobalTheory.CompanionTheory.SW.PeriodisedMean.setLIntegral_tsum_comp_inv_eq <;> assumption)
end

section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_fundamental_domain_split : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.exists_borel_section_ker | exact GlobalTheory.CompanionTheory.SplitExtLat.exists_borel_section_ker | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.exists_borel_section_ker <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.eventually_haar_det_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k), MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | exact GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.integers_bounded_archimedean_count : ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
    {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
    ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N := by
  first | exact @GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | exact GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le | (intros; apply GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.idempotent_local_induction : ∀ {S : Type} [CommRing S] (Q : S → Prop), Q 0 → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → Q e → Q (e * e')) → (∀ e e' : S, IsIdempotentElem e → IsIdempotentElem e' → e * e' = 0 → Q e → Q e' → Q (e + e')) → (∀ m : Ideal S, m.IsMaximal → ∃ e, IsIdempotentElem e ∧ e ∉ m ∧ Q e) → Q 1 := by
  first | exact @GlobalTheory.CompanionTheory.Idem.glue_idempotent_property | exact GlobalTheory.CompanionTheory.Idem.glue_idempotent_property | (intros; apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property <;> assumption)
end
