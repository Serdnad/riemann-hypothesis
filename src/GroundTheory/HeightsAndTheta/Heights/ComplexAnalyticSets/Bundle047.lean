module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem zeroSet_subset_biUnion_minimalPrimes {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by
  intro x hx
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  exact Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)

theorem withBot_enat_le_pred {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      have hm : m < d := by exact_mod_cast h
      refine ⟨by omega, ?_⟩
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))

theorem minimalPrime_tube_bound (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by
  have hprime : P.IsPrime := hP.1.1
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨hd, hk⟩ := withBot_enat_le_pred hnn (hle.trans_lt hdim)
  obtain ⟨C, hC, hCr⟩ := h n (d - 1) P K hprime hk hK
  refine ⟨C, hC, fun r hr => ?_⟩
  have he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d := by omega
  simpa [he] using hCr r hr

theorem SmallSetTubeVolume.proof (h : PrimeTubeVolume.Statement) : SmallSetTubeVolume.Statement := by
  intro n d I K hdim hK
  set e : ℤ := (2 * n + 2 : ℤ) - 2 * d
  have key : ∀ F : Finset (Ideal (MvPolynomial (Fin n) ℂ)), (↑F : Set _) ⊆ I.minimalPrimes →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (⋃ P ∈ F, zeroSet P ∩ K)) ≤ ENNReal.ofReal (C * r ^ e) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, le_rfl, fun r _ => by simp⟩
    | insert a F ha ih =>
      intro hsub
      obtain ⟨C₁, hC₁, h₁⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      obtain ⟨C₂, hC₂, h₂⟩ := minimalPrime_tube_bound h hdim hK (hsub (Finset.mem_insert_self a F))
      refine ⟨C₂ + C₁, add_nonneg hC₂ hC₁, fun r hr => ?_⟩
      have hre : 0 ≤ r ^ e := zpow_nonneg hr.1.le e
      rw [Finset.set_biUnion_insert, Metric.thickening_union, add_mul,
        ENNReal.ofReal_add (mul_nonneg hC₂ hre) (mul_nonneg hC₁ hre)]
      exact (measure_union_le _ _).trans (add_le_add (h₂ r hr) (h₁ r hr))
  obtain ⟨F, hF⟩ := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).exists_finset_coe
  obtain ⟨C, hC, hCr⟩ := key F hF.le
  refine ⟨C, hC, fun r hr => le_trans (measure_mono (Metric.thickening_subset_of_subset r ?_)) (hCr r hr)⟩
  intro x ⟨hxI, hxK⟩
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 (zeroSet_subset_biUnion_minimalPrimes I hxI)
  rw [← hF] at hP
  exact Set.mem_iUnion₂.2 ⟨P, hP, hxP, hxK⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def BranchIntDecompose.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (ψ i)) →
          varInt J (d + 1) f ψ =
            ∑ b, ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
              (Metric.ball 0 (γ b).radius)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def BranchProperAtPoint.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u p x : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 x, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {y | GroundTheory.Heights₂.Heights.linEval u y = 0}) →
    ∀ b, ∀ s ∈ Metric.ball 0 (γ b).radius, (γ b).toFun s = x →
      ∀ P ∈ 𝓝 s, ∃ ε > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius,
        (γ b).toFun τ ∈ Metric.ball x ε → τ ∈ P

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def BranchSheetAE.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (p : Fin n → ℂ)
    (γ : VarBranch J d p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∀ᵐ t ∂(volume.restrict (Metric.ball (0 : Fin d → ℂ) γ.radius)), ∃ s, IsSheetAt J A (γ.toFun t) s

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ChartChangeSheetNull.Statement : Prop :=
  ∀ (n d : ℕ) (J J' : Ideal (MvPolynomial (Fin n) ℂ)) (A A' : Matrix (Fin d) (Fin n) ℂ)
    (u u' : Fin n → ℂ) (U U' : Set (Fin n → ℂ)) (Φ Ψ : (Fin n → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    J'.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') = d →
    linForm u ∉ J → linForm u' ∉ J' → IsFiniteProjection J A → IsFiniteProjection J' A' →
    IsOpen U → IsOpen U' → zeroSet J \ {x | linEval u x = 0} ⊆ U →
    zeroSet J' \ {x | linEval u' x = 0} ⊆ U' →
    DifferentiableOn ℂ Φ U' → DifferentiableOn ℂ Ψ U →
    Set.MapsTo Φ (zeroSet J' \ {x | linEval u' x = 0}) (zeroSet J \ {x | linEval u x = 0}) →
    Set.MapsTo Ψ (zeroSet J \ {x | linEval u x = 0}) (zeroSet J' \ {x | linEval u' x = 0}) →
    (∀ x ∈ zeroSet J' \ {x | linEval u' x = 0}, Ψ (Φ x) = x) →
    (∀ x ∈ zeroSet J \ {x | linEval u x = 0}, Φ (Ψ x) = x) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ (linEval u x ≠ 0 ∧ ∃ s', IsSheetAt J' A' (Ψ x) s')}) = 0

namespace ChartChange

end ChartChange

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def ChartIntSumOffHyperplane.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (u : Fin n → ℂ)
    (m : ℕ) (f : (Fin n → ℂ) → ℝ) (F : Fin m → (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    linForm u ∉ J →
    (∀ x ∈ zeroSet J, linEval u x ≠ 0 → f x = ∑ b, F b x) →
    (∀ b, Integrable (chartDens J A (F b) φ)) →
      chartInt J A f φ = ∑ b, chartInt J A (F b) φ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def ChartMassCompact.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    (HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) →
      Integrable (chartAbsDens J A f ψ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsExists.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ), ConeAvoids J A N

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsFinite.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ConeAvoids J A N → (projHom J A).toRingHom.Finite

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsOpen.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsZariskiOpen {A : Matrix (Fin d) (Fin n) ℂ | ConeAvoids J A N}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

noncomputable section

def CutOffBoundaryBound.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    HasCompactSupport F →
      ∃ R C : ℝ, ∀ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ →
        |chartInt J A G (vecCons (fun x => χ x * F x) φ) -
            chartInt J A (fun x => χ x * G x) (vecCons F φ)| ≤
          C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1) (vecCons χ φ) y) +
            Real.sqrt (energyInt J A (Metric.closedBall 0 R) χ))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def CutOffDominated.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (χ : ℕ → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A → P ≠ 0 →
    (∀ k, Measurable (χ k)) → (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    Integrable (chartAbsDens J A f ψ) →
      Tendsto (fun k => chartInt J A (fun x => χ k x * f x) ψ) atTop (𝓝 (chartInt J A f ψ))

end

end GroundTheory.Heights₂.Heights
end
