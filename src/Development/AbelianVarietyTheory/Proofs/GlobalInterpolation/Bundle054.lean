module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle052
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle025
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle053
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLe
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke


theorem _root_.GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add : ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | exact GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | (intros; apply GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → (∀ μ : Measure (Fin N → AF F), μ.IsAddHaarMeasure → Integrable Φ μ) ∧ (∀ u, Summable fun ξ : Fin N → F => ‖Φ (rat ξ + u)‖) ∧ Continuous fun u => ∑' ξ : Fin N → F, Φ (rat ξ + u) := by
  first | exact @GlobalTheory.decay_integrable_periodise | exact GlobalTheory.decay_integrable_periodise | (intros; apply GlobalTheory.decay_integrable_periodise <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.CongIndex

theorem relIndex_congPre (O K : Type) [CommRing O] [IsLocalRing O] [CommRing K] (ι : O →+* K)
    (hι : Function.Injective ι) (n : ℕ) (H : Subgroup (GL (Fin n) (O ⧸ IsLocalRing.maximalIdeal O))) :
    (congPre ι (IsLocalRing.maximalIdeal O) H).relIndex (bc (n := Fin n) ι).range = H.index := by
  have hinj : Function.Injective (bc (n := Fin n) ι) := by
    intro g h e
    apply Units.ext
    ext a b
    apply hι
    exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) e
  have hs : Function.Surjective (redGL (n := Fin n) (IsLocalRing.maximalIdeal O)) :=
    GlobalTheory.MeasTupleEq.map_residue_surjective O n
  unfold congPre
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ hs]

end GlobalTheory.CongIndex
end

section

noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise


open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dite_eq_left (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
end
end

section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  intro Γ k _ _ _ n ρ₀ ρ ρ' η₀ χ₁ χ₂ hρ hρ' hs hs' hno htr
  obtain ⟨P, hP⟩ := GlobalTheory.T.conj_on_inter_quadraticKernels_of_trace_eq Γ k n ρ ρ' χ₁ χ₂ hs hs' htr
  have hzero : ∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂) →
      ∀ X : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ (⊤ : Subgroup Γ), ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X =
        ((c g : ℤ) : k) • (X * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0 := by
    intro c hc X hX
    obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ₀ ρ₀ ⊤ c η₀ X (by
      intro g hg h
      have := hX g hg
      rwa [hρ g h, hρ' g h] at this)
    have hA0 : A = 0 := hno c (by tauto) A (fun g => hA g trivial)
    have hB0 : B = 0 := hno (c * η₀) (by rcases hc with rfl | rfl | rfl <;> simp) B
      (fun g => hB g trivial)
    rw [hAB, hA0, hB0, add_zero]
  obtain ⟨Y₁, Y₂, hY, hY₁, hY₂⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ χ₂.ker 1 χ₁
    (P : Matrix (Fin n) (Fin n) k) (by
      intro g hg h
      have h1 : ρ g * P = P * ρ' g := by rw [hP g h hg]; group
      have h2 := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) h1
      simpa using h2)
  obtain ⟨A, B, hAB, hA, hB⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ 1 χ₂ Y₁ (fun g _ h => hY₁ g h)
  obtain ⟨C, D, hCD, hC, hD⟩ := GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' Γ k n ρ' ρ ⊤ (1 * χ₁) χ₂ Y₂ (fun g _ h => hY₂ g h)
  have hB0 : B = 0 := hzero _ (by simp) B hB
  have hC0 : C = 0 := hzero _ (by simp) C hC
  have hD0 : D = 0 := hzero _ (by simp) D hD
  have hPA : (P : Matrix (Fin n) (Fin n) k) = A := by
    rw [hY, hAB, hCD, hB0, hC0, hD0]; simp
  intro g
  have h1 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (P : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    have := hA g trivial
    rw [← hPA] at this
    simpa using this
  have h2 : ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (P : Matrix (Fin n) (Fin n) k) * ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  rw [h2, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]

end GlobalTheory
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  first | exact @GlobalTheory.ZeroCells.ncard_cells_le | exact GlobalTheory.ZeroCells.ncard_cells_le | (intros; apply GlobalTheory.ZeroCells.ncard_cells_le <;> assumption)
end

end

section

@[expose] public section

open Formalism.MainNotions.N
theorem _root_.GlobalTheory.T.intertwiner_zero_of_quadratic_twists : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  first | exact @GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner | exact GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner | (intros; apply GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner <;> assumption)

end
end
