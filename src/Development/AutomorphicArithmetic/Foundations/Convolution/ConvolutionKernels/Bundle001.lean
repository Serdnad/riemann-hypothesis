module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open MeasureTheory

theorem UpperTheory.ConvolutionTheory.K.intEst :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (h : X → ℝ) (k c o : X → ℂ) (Z A B : ℝ),
      Measurable h → Integrable c ν → AEStronglyMeasurable o ν → 0 ≤ A → 0 ≤ B → (∀ x, k x = c x + o x) → (∀ x, Z < h x → k x = 0) →
      (∀ x, h x ≤ Z → ‖o x‖ ≤ A) → (∀ x, Z < h x → ‖c x‖ ≤ B) →
      ‖∫ x, k x ∂ν - ∫ x, c x ∂ν‖ ≤ ν.real Set.univ * A + ν.real Set.univ * B := by
  intro X _ ν _ h k c o Z A B hh hc ho hA hB hk h0 hoA hcB
  set S : Set X := {x | h x ≤ Z}
  have hS : MeasurableSet S := measurableSet_le hh measurable_const
  have e1 : ∀ x, k x - c x = S.indicator o x - Sᶜ.indicator c x := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx, hk x]
    · simp [hx, h0 x (not_le.1 hx)]
  have b1 : ∀ x, ‖S.indicator o x‖ ≤ A := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hoA x hx
    · simpa [hx] using hA
  have b2 : ∀ x, ‖Sᶜ.indicator c x‖ ≤ B := fun x => by
    by_cases hx : x ∈ S
    · simpa [hx] using hB
    · simpa [hx] using hcB x (not_le.1 hx)
  have i1 : Integrable (S.indicator o) ν := Integrable.of_bound (ho.indicator hS) A (Filter.Eventually.of_forall b1)
  have i2 : Integrable (Sᶜ.indicator c) ν := hc.indicator hS.compl
  have ik : Integrable k ν := by
    have : k = fun x => (S.indicator o x - Sᶜ.indicator c x) + c x := funext fun x => by rw [← e1]; ring
    rw [this]
    exact (i1.sub i2).add hc
  rw [← integral_sub ik hc]
  simp_rw [e1]
  rw [integral_sub i1 i2]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b1)
  · rw [mul_comm]; exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall b2)
end

section

theorem UpperTheory.ConvolutionTheory.K.commProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (V : Submodule ℂ H) [V.HasOrthogonalProjection]
      (U : H →L[ℂ] H), (∀ v ∈ V, U v ∈ V) → (∀ v ∈ V, ContinuousLinearMap.adjoint U v ∈ V) →
      U ∘L V.starProjection = V.starProjection ∘L U := by
  intro H _ _ _ V _ U h1 h2
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact h1 _ (V.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (h2 w hw)
end

section

open MeasureTheory

theorem UpperTheory.ConvolutionTheory.K.presOfOrder :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (e : G ≃ₜ* G) (m : ℕ),
      0 < m → (∀ g, (⇑e)^[m] g = g) → MeasurePreserving e μ μ := by
  intro G _ _ _ _ _ _ _ _ μ _ e m hm he
  have hme : Measurable (e : G → G) := e.continuous.measurable
  haveI : (Measure.map e μ).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map e μ = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hit : ∀ k : ℕ, Measure.map ((⇑e)^[k]) μ = c ^ k • μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ', ← Measure.map_map hme (hme.iterate k), ih,
        Measure.map_smul _ hme.aemeasurable, hc, smul_smul, pow_succ]
  have h1 : μ = c ^ m • μ := by
    rw [← hit m, show (⇑e)^[m] = id from funext he, Measure.map_id]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hK1 : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (1 : ENNReal) * μ K = ((c ^ m : NNReal) : ENNReal) * μ K := by
    rw [one_mul]
    conv_lhs => rw [h1]
    rfl
  have h3 : c ^ m = 1 := by
    have := (ENNReal.mul_left_inj hK0 hK1).1 h2
    exact_mod_cast this.symm
  have h4 : c = 1 := (pow_eq_one_iff_of_nonneg (zero_le) hm.ne').1 h3
  exact ⟨hme, by rw [hc, h4, one_smul]⟩
end

section

theorem UpperTheory.ConvolutionTheory.K.autOrder :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K ≃+* K), ∃ m : ℕ, 0 < m ∧ σ ^ m = 1 := by
  intro K _ _ σ
  let τ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := σ) (fun x => by simp)
  refine ⟨orderOf τ, orderOf_pos τ, ?_⟩
  have h : ∀ m : ℕ, ∀ x, (σ ^ m) x = (τ ^ m) x := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ, pow_succ]; exact ih _
  ext x
  rw [h, pow_orderOf_eq_one]
  rfl
end
