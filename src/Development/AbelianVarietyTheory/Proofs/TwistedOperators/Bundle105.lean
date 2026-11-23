module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle098
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle010
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq : ∀ (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂), (∀ s t, U₁ (s + t) = U₁ s * U₁ t) → (∀ s t, U₂ (s + t) = U₂ s * U₂ t) → U₁ 0 = 1 → U₂ 0 = 1 → (∀ t x, ‖U₂ t x‖ = ‖x‖) → ∀ (w₁ : ℕ → H₁) (w₂ : ℕ → H₂), (∀ k, HasDerivAt (fun t : ℝ => U₁ t (w₁ k)) (w₁ (k + 1)) 0) → (∀ k, HasDerivAt (fun t : ℝ => U₂ t (w₂ k)) (w₂ (k + 1)) 0) → (∀ k, ‖w₁ k‖ = ‖w₂ k‖) → AnalyticAt ℝ (fun t : ℝ => U₁ t (w₁ 0)) 0 → AnalyticOnNhd ℝ (fun t : ℝ => U₂ t (w₂ 0)) Set.univ := by
  first | exact @GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq | exact GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq | (intros; apply GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem map_withDensity_of_jacobian_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (J : E → ℝ) (ψ : E → E) (hψ : Continuous ψ)
    (hb : Function.Bijective ψ)
    (h : ∀ B, ∃ P : E →L[ℝ] E, HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) :
    Measure.map ψ (μ.withDensity fun B => ENNReal.ofReal (J B)) =
      μ.withDensity fun B => ENNReal.ofReal (J B) := by

  choose P hP hJ using h
  have hm : Measurable ψ := hψ.measurable
  ext A hA
  rw [Measure.map_apply hm hA, withDensity_apply _ hA, withDensity_apply _ (hm hA)]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hm hA)
    (fun x _ => (hP x).hasFDerivWithinAt) hb.injective.injOn (fun y => ENNReal.ofReal (J y))
  rw [Set.image_preimage_eq A hb.surjective] at hcv
  rw [hcv]
  refine lintegral_congr (fun x => ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), hJ x]

theorem map_withDensity_of_jacobian : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by

  intro p q J ψ _ hψ hb h
  haveI hrow : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; infer_instance
  haveI hall : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  exact map_withDensity_of_jacobian_gen (volume : Measure (Fin p → Fin q → ℂ)) J ψ hψ hb h

end GlobalTheory
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open Kronecker in
theorem abs_det_unitary_mul_mul : ∀ (p q : ℕ), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∀ T : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ), (∀ B, Matrix.of (T B) = U * Matrix.of B * V) → |LinearMap.det T| = 1 := by
  classical
  intro p q U hU V hV T hT

  let e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    { toFun := fun B j i => B i j
      invFun := fun C i j => C j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  let L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))

  let R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))
  let C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    ((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ
      (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R
  have hTC : T = C.restrictScalars ℝ := by
    apply LinearMap.ext
    intro B
    funext i j
    have h := congrFun (congrFun (hT B) i) j
    simp only [Matrix.of_apply] at h
    rw [h, Matrix.mul_assoc]
    simp [C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hL : LinearMap.det L = U.det ^ q := by
    simp [L, LinearMap.det_pi, LinearMap.det_toLin']
  have hR : LinearMap.det R = V.det ^ p := by
    simp [R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]
  have hC : LinearMap.det C = U.det ^ q * V.det ^ p := by
    simp only [C]
    rw [LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]
  have hu : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hv : ‖V.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)
  rw [hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]
  simp

end GlobalTheory.PolarU
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.exists_linearMap_tensor_of_pairing : ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  first | exact @GlobalTheory.PairingTensor.exists_linearMap_tensor | exact GlobalTheory.PairingTensor.exists_linearMap_tensor | (intros; apply GlobalTheory.PairingTensor.exists_linearMap_tensor <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  first | exact @GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | exact GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | (intros; apply GlobalTheory.FactorialJet.eq_zero_of_factorial_bound <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_exp_add_smul_duhamel (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X V : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (X + t • V))
      (∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X)) 0 := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Continuous (NormedSpace.exp : A → A) := NormedSpace.exp_continuous
  set f : ℝ → ℝ → A := fun t s =>
    NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • (X + t • V)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    exact ((hc.comp (by fun_prop)).mul continuous_const).mul (hc.comp (by fun_prop))
  set F : ℝ → A := fun t => ∫ s in (0 : ℝ)..1, f t s with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc 0 1
  have key : ∀ t : ℝ, NormedSpace.exp (X + t • V) = NormedSpace.exp X + t • F t := by
    intro t
    have hd : ∀ s : ℝ, HasDerivAt
        (fun s : ℝ => NormedSpace.exp ((1 - s) • X) * NormedSpace.exp (s • (X + t • V)))
        (t • f t s) s := by
      intro s
      have h0 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
        simpa using (hasDerivAt_id s).const_sub 1
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (1 - s)).scomp s h0
      have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (X + t • V) s
      have h3 := h1.mul h2
      refine h3.congr_deriv ?_
      simp only [hf, Function.comp_apply, neg_smul, one_smul, add_mul, mul_add, mul_assoc,
        neg_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have hi : IntervalIntegrable (fun s => t • f t s) volume 0 1 :=
      ((hfc.comp (Continuous.prodMk_right t)).const_smul t).intervalIntegrable 0 1
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
    rw [intervalIntegral.integral_smul] at h
    simp only [sub_self, zero_smul, NormedSpace.exp_zero, one_mul, one_smul, sub_zero,
      mul_one] at h
    simp only [hF]
    rw [h]
    abel
  have hF0 : F 0 = ∫ s in (0 : ℝ)..1,
      NormedSpace.exp ((1 - s) • X) * V * NormedSpace.exp (s • X) := by
    simp [hF, hf]
  rw [← hF0, hasDerivAt_iff_tendsto_slope_zero]
  have ht : Filter.Tendsto F (nhdsWithin 0 {0}ᶜ) (nhds (F 0)) :=
    hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  have ht0' : t ≠ 0 := ht0
  rw [key (0 + t), key 0]
  simp [smul_smul, inv_mul_cancel₀ ht0']

end GlobalTheory
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_unitary_mul_diagonal_real_mul_conjTranspose : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ, B = U * (Matrix.of fun (i : Fin p) (j : Fin q) => if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  first | exact @GlobalTheory.RectSVD.exists_svd | exact GlobalTheory.RectSVD.exists_svd | (intros; apply GlobalTheory.RectSVD.exists_svd <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem exists_biinvariant_probability_on_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  intro G _ _ _ _ _ _ _ K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : BorelSpace K := Subtype.borelSpace (fun x => x ∈ (K : Set G))
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    simpa using this⟩
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hv : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  refine ⟨μ.map Subtype.val, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    rw [this]; simp
  · intro k hk
    rw [Measure.map_map (measurable_const_mul k) hv]
    have h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ := map_mul_left_eq_self μ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl
  · intro k hk
    rw [Measure.map_map (measurable_mul_const k) hv]
    have h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ := by
      have : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure :=
        Measure.isHaarMeasure_map_mul_right μ _
      exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_mul_const _)]
    rfl

end GlobalTheory
end

end

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.map_withDensity_of_jacobian_complexMatrices : ∀ (p q : ℕ) (J : (Fin p → Fin q → ℂ) → ℝ) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous J → Continuous ψ → Function.Bijective ψ → (∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * J (ψ B) = J B) → Measure.map ψ (volume.withDensity fun B => ENNReal.ofReal (J B)) = volume.withDensity fun B => ENNReal.ofReal (J B) := by
  first | exact @GlobalTheory.map_withDensity_of_jacobian | exact GlobalTheory.map_withDensity_of_jacobian | (intros; apply GlobalTheory.map_withDensity_of_jacobian <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_biinvariant_probability_on_compact_subgroup' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  first | exact @GlobalTheory.exists_biinvariant_probability_on_compact_subgroup | exact GlobalTheory.exists_biinvariant_probability_on_compact_subgroup | (intros; apply GlobalTheory.exists_biinvariant_probability_on_compact_subgroup <;> assumption)

end
end
