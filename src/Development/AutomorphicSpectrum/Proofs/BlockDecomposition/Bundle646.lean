module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle626
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin

theorem sigR_fixed_eq_algebraMap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E),
    sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  intro F E _ _ _ _ _ σ h K _ _ a ha
  have hsigma (x : E) : σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hmoved : ∃ y, σ y ≠ y := by
    by_contra hc
    push_neg at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hc x] at this
      exact this.symm)
    have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal
  have hex : ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E),
      θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
    obtain ⟨y, hy⟩ := hmoved
    have hE2 : (2 : E) ≠ 0 := two_ne_zero
    have hσθ : σ (y - σ y) = -(y - σ y) := by
      rw [map_sub, hsigma]
      ring
    have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    generalize y - σ y = θ at hσθ hθ
    have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      simp only [Algebra.smul_def, mul_one] at hst
      have h1 := congrArg σ hst
      simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
      have hs : (2 : E) * algebraMap F E s = 0 := by
        linear_combination hst + h1
      have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
        linear_combination hst - h1
      have hs0 : s = 0 := by
        have := (mul_eq_zero.1 hs).resolve_left hE2
        exact (map_eq_zero _).1 this
      have ht0 : t = 0 := by
        have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
        exact (map_eq_zero _).1 this
      exact ⟨hs0, ht0⟩
    let B : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
    have hB0 : B 0 = 1 := by simp [B]
    have hB1 : B 1 = θ := by simp [B]
    have hsum := B.sum_repr (θ * θ)
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    generalize B.repr (θ * θ) 0 = a at hsum
    generalize B.repr (θ * θ) 1 = b at hsum
    have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
      simpa only [Algebra.smul_def, mul_one] using hsum
    have hconj := congrArg σ hsum'
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
    have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
      linear_combination hsum' - hconj
    have hb0 : algebraMap F E b = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
    have hsq : θ * θ = algebraMap F E a := by
      rw [← hsum', hb0, zero_mul, add_zero]
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hsq
      exact hθ (mul_self_eq_zero.1 hsq)
    exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := hex
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  have hsK : ∀ x : K, sigR K σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
    intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hsT : sigR K σ ((1 : K) ⊗ₜ[F] θ) = -((1 : K) ⊗ₜ[F] θ) := by
    change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  have hz := C.sum_repr a
  rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
  generalize C.repr a 0 = x at hz
  generalize C.repr a 1 = y at hz
  subst hz
  rw [map_add (f := _), map_mul, hsK, hsK, hsT] at ha
  have h2 : algebraMap K (K ⊗[F] E) 0 + algebraMap K (K ⊗[F] E) (2 * y) * ((1 : K) ⊗ₜ[F] θ) = 0 := by
    rw [map_zero, map_mul, map_ofNat]
    linear_combination -ha
  have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![0, 2 * y] (by
    rw [Fin.sum_univ_two, hC0, hC1]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using h2)
  have hy : y = 0 := by
    have := hl 1
    simp only [Matrix.cons_val_one] at this
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact ⟨x, by rw [hy, map_zero, zero_mul, add_zero]⟩

end GlobalTheory.CompanionTheory.KFin

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound

theorem compactOpen_mass_le : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ h P hPc hPo hPZ
  have hPm : MeasurableSet P := hPo.measurableSet
  let φ : V → ℝ := P.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hPo.frontier_eq, hPc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hPc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ Z := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hPc.isClosed) hPZ
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(m s) = (m s P).toReal := fun s => by
    simp [φ, integral_indicator hPm, Measure.real]
  have hfin : ∀ s, m s P ≠ ⊤ := fun s => by
    have h := hI s (Set.mem_univ s)
    rw [integrable_indicator_iff hPm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : ContinuousOn (fun s => (m s P).toReal) (Q '' P) := by
    have h' : ContinuousOn (fun s => (m s P).toReal) Set.univ := by
      simpa only [hint] using hC
    exact h'.mono (Set.subset_univ _)
  obtain ⟨C, hCb⟩ := (hPc.image hQ).exists_bound_of_continuousOn hcont
  have hoff : ∀ s, s ∉ Q '' P → m s P = 0 := fun s hs => by
    have hae := GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.ae_lift_eq h (g := Q) (fun _ => rfl) Function.injective_id s
    refine measure_mono_null (t := {x | ¬ Q x = s}) ?_ hae
    intro x hx hxs
    exact hs ⟨x, hx, hxs⟩
  have hbd : ∀ s, m s P ≤ (C.toNNReal : ℝ≥0∞) := fun s => by
    by_cases hs : s ∈ Q '' P
    · have h1 : (m s P).toReal ≤ C := le_trans (le_abs_self _) (by simpa using hCb s hs)
      rw [← ENNReal.ofReal_toReal (hfin s)]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [hoff s hs]
      exact bot_le
  refine ⟨C.toNNReal, fun S hS => ?_⟩
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.fibre_mass_on h (g := Q) (fun _ => rfl) Function.injective_id hQ.measurable hPm hS
    (fun x hx => hPZ hx.1)]
  calc ∫⁻ s in S, m s P ∂lam ≤ ∫⁻ _ in S, (C.toNNReal : ℝ≥0∞) ∂lam := lintegral_mono hbd
    _ = (C.toNNReal : ℝ≥0∞) * lam S := by rw [setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound
end
