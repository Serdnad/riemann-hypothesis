module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle198
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle021
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle199
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle197
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle201
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Convex
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped ContDiff

theorem _root_.GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first | exact @GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | exact GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | (intros; apply GlobalTheory.hasDerivAt_of_continuous_additive_to_mul <;> assumption)
end

section

open MeasureTheory

namespace GlobalTheory

theorem sobolev_iterated_one_parameter_subgroups_words : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by
  intro G _ _ _ N c s hs hc
  obtain ⟨enc, hinj, h1, h2⟩ : ∃ enc : List (Fin N) → ℝ, Function.Injective enc ∧
      (∀ l, 1 ≤ ‖enc l‖) ∧ ∀ l, ‖enc l‖ ≤ 2 := by
    have hpos : ∀ l : List (Fin N), (0 : ℝ) < 1 / ((Encodable.encode l : ℝ) + 1) := fun l => by
      positivity
    have hle : ∀ l : List (Fin N), 1 / ((Encodable.encode l : ℝ) + 1) ≤ 1 := fun l => by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (Encodable.encode l : ℝ) := Nat.cast_nonneg _
      linarith
    refine ⟨fun l => 1 + 1 / ((Encodable.encode l : ℝ) + 1), ?_, fun l => ?_, fun l => ?_⟩
    · intro a b hab
      have h : (1 : ℝ) / ((Encodable.encode a : ℝ) + 1) = 1 / ((Encodable.encode b : ℝ) + 1) :=
        add_left_cancel hab
      rw [one_div, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
      exact Encodable.encode_injective h
    · have := hpos l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
    · have := hpos l
      have := hle l
      rw [Real.norm_of_nonneg (by linarith)]
      linarith
  have hdec : ∀ l, Function.invFun enc (enc l) = l := Function.leftInverse_invFun hinj
  have hK : 0 ≤ (2 / s + 2 * s * 2 ^ 2) ^ N := by positivity
  refine ⟨(2 / s + 2 * s * 2 ^ 2) ^ N * 4, by positivity, ?_⟩
  intro F hF hD y M hM
  have hM0 : 0 ≤ M :=
    le_trans (integral_nonneg fun t => by positivity) (hM [] (Nat.zero_le _))
  have main := sobolev_iterated_one_parameter_subgroups G ℝ ℂ N 0 c
    (fun p => enc '' {l | l.length ≤ p}) (fun i u => enc (i :: Function.invFun enc u))
    (fun u => F (Function.invFun enc u)) s 2 M y hs (by norm_num) hM0 hc
    (fun p q hpq => Set.image_mono fun l hl => le_trans hl hpq) ?_ ?_ ?_ (enc [])
    ⟨[], Nat.le_refl 0, rfl⟩
  · rw [hdec] at main
    have h4 : ‖enc []‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h2 _) 2
    calc _ ≤ _ := main
      _ ≤ (2 / s + 2 * s * 2 ^ 2) ^ N * M * 2 ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hK hM0)
      _ = _ := by ring
  · rintro p _ ⟨l, hl, rfl⟩
    simp only [hdec]
    exact ⟨hF l, fun i => ⟨⟨i :: l, Nat.succ_le_succ hl, rfl⟩, hD l i⟩⟩
  · rintro p _ _ ⟨l, hl, rfl⟩ i
    have := h1 l
    have := h2 (i :: Function.invFun enc (enc l))
    linarith
  · rintro _ ⟨l, hl, rfl⟩
    simp only [hdec]
    have hl' : l.length ≤ N := by simpa using hl
    exact (hM l hl').trans (le_mul_of_one_le_right hM0 (one_le_pow₀ (h1 l)))

end GlobalTheory
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  first | exact @GlobalTheory.UnitaryChar.char_eq_det_zpow | exact GlobalTheory.UnitaryChar.char_eq_det_zpow | (intros; apply GlobalTheory.UnitaryChar.char_eq_det_zpow <;> assumption)
end

section


theorem _root_.GlobalTheory.T.modulated_schwartz_seminorm_polynomial : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (h : SchwartzMap V ℂ) (v : V → SchwartzMap V ℂ),
    (∀ μ x, v μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x) →
    ∀ k n : ℕ, ∃ C : ℝ, ∀ μ, SchwartzMap.seminorm ℂ k n (v μ) ≤ C * (1 + ‖μ‖) ^ n := by
  first | exact @GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | exact GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth | (intros; apply GlobalTheory.CharModGrowth.seminorm_char_mul_polynomial_growth <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.schwartz_family_phase_bound : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  first | exact @GlobalTheory.CharFamily.charMul_family | exact GlobalTheory.CharFamily.charMul_family | (intros; apply GlobalTheory.CharFamily.charMul_family <;> assumption)
end

section

open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.LinearPhase.seminorm_phase_sub_le | exact GlobalTheory.LinearPhase.seminorm_phase_sub_le | (intros; apply GlobalTheory.LinearPhase.seminorm_phase_sub_le <;> assumption)
end

section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

theorem _root_.GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | exact GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | (intros; apply GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le <;> assumption)
end

section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

theorem _root_.GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  first | exact @GlobalTheory.fourier_prod_coord_complex | exact GlobalTheory.fourier_prod_coord_complex | (intros; apply GlobalTheory.fourier_prod_coord_complex <;> assumption)
end

section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.hermitian_unitary_group_one_parameter_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  first | exact @GlobalTheory.UnitaryGroupChart.unitary_chart | exact GlobalTheory.UnitaryGroupChart.unitary_chart | (intros; apply GlobalTheory.UnitaryGroupChart.unitary_chart <;> assumption)
end

section

open Filter Topology

namespace GlobalTheory.StripGrowth

theorem int_coord_const (g m : ℕ) (U : Set ℂ) (hU : IsPreconnected U) (μ ν : ℂ → Fin m → Fin g → ℂ)
    (hμ : ContinuousOn μ U) (hν : ContinuousOn ν U) (hli : ∀ s ∈ U, LinearIndependent ℝ (μ s))
    (hn : ∀ s ∈ U, ∀ j, ∃ n : Fin m → ℤ, ν s j = ∑ i, n i • μ s i) :
    ∃ P : Fin m → Fin m → ℤ, ∀ s ∈ U, ∀ j, ν s j = ∑ i, P j i • μ s i := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨0, by simp⟩
  choose! n hnE using hn
  have key : ∀ j, ∀ s ∈ U, n s j = n s₀ j := by
    intro j
    have hcont : ContinuousOn (fun s i => ((n s j i : ℤ) : ℝ)) U := by
      refine GlobalTheory.T.continuousOn_coords_of_linearIndependent' g m U μ (fun s => ν s j) (fun s i => (n s j i : ℝ)) hμ ?_ hli ?_
      · exact (continuous_apply j).comp_continuousOn hν
      · intro s hs
        rw [hnE s hs j]
        simp [Int.cast_smul_eq_zsmul]
    have hcz : ContinuousOn (fun s => n s j) U := by
      rw [continuousOn_pi] at hcont ⊢
      intro i
      exact (Int.isUniformEmbedding_coe_real.isEmbedding.continuousOn_iff).2 (hcont i)
    intro s hs
    exact hU.constant hcz hs hs₀
  exact ⟨n s₀, fun s hs j => by rw [hnE s hs j, key j s hs]⟩

theorem strip_growth : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  intro g m lam C k hcont hli hspan hB
  have hU : IsPreconnected {s : ℂ | s.re < 0} := (convex_halfSpace_re_lt 0).isPreconnected
  have hre : ∀ s : ℂ, (s + 2 * Real.pi * Complex.I).re = s.re := by intro s; simp
  have hshift : ContinuousOn (fun s => lam (s + 2 * Real.pi * Complex.I)) {s : ℂ | s.re < 0} :=
    hcont.comp (continuousOn_id.add continuousOn_const) (fun s hs => by
      simpa [Set.mem_setOf_eq, hre] using hs)
  have hli' : ∀ s ∈ {s : ℂ | s.re < 0}, LinearIndependent ℝ (lam (s + 2 * Real.pi * Complex.I)) :=
    fun s hs => hli _ (by simpa [hre] using hs)
  have hsingle : ∀ (v : Fin m → Fin g → ℂ) (j : Fin m), v j = ∑ i, (Pi.single j 1 : Fin m → ℤ) i • v i := by
    intro v j
    classical
    simp [Pi.single_apply]
  obtain ⟨P, hP⟩ := int_coord_const g m _ hU lam (fun s => lam (s + 2 * Real.pi * Complex.I)) hcont hshift
    (fun s hs => hli s hs) (fun s hs j => (hspan s hs _).1 ⟨Pi.single j 1, hsingle _ j⟩)
  obtain ⟨Q, hQ⟩ := int_coord_const g m _ hU (fun s => lam (s + 2 * Real.pi * Complex.I)) lam hshift hcont
    hli' (fun s hs j => (hspan s hs _).2 ⟨Pi.single j 1, hsingle _ j⟩)
  exact GlobalTheory.T.polyGrowth_strip_of_integral_monodromy g m lam C k P Q (fun s hs j => hP s hs j) (fun s hs j => hQ s hs j) hB

end GlobalTheory.StripGrowth
end

section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_continuous_representative_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  first | exact @GlobalTheory.LocRep.exists_continuous_rep_average | exact GlobalTheory.LocRep.exists_continuous_rep_average | (intros; apply GlobalTheory.LocRep.exists_continuous_rep_average <;> assumption)
end

section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.representative_parametric_integral_continuous_family : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  first | exact @GlobalTheory.LocRep.rep_parametric_integral | exact GlobalTheory.LocRep.rep_parametric_integral | (intros; apply GlobalTheory.LocRep.rep_parametric_integral <;> assumption)
end
