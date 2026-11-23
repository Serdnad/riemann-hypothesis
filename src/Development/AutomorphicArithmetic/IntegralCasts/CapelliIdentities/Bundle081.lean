module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle063
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle051
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle053
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
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
import Mathlib.RingTheory.Valuation.Integral
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

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l inst c x hx
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hv : ∀ y, y ∈ v.integer ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
  have h1 : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have h2 : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := fun a => by
    rw [hv, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
    exact a.2
  have h3 : IsIntegral v.integer x :=
    h1.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer h2) (RingHom.id _) rfl
  exact (hv x).1 ((Valuation.integer.integers v).mem_of_integral h3)
end

section

theorem UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have h1 : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  have h2 : IsIntegral ℤ_[l] x := h1.map c.O.val
  have h3 : IsIntegral ℚ_[l] x := h2.tower_top
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic h3),
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h2]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

section

theorem UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have hi : IsIntegral ℤ_[l] x :=
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
  have hm : minpoly ℚ_[l] x = (minpoly ℤ_[l] x).map (algebraMap ℤ_[l] ℚ_[l]) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hm,
    spectralValue_le_one_iff ((minpoly.monic hi).map _)]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

section

theorem UpperTheory.Reformulated.B.Gs5b.cd_norm_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) {R : Type} [inst_1 : CommRing R] [inst_2 : IsLocalRing R]
      [inst_3 : Algebra (↥c.O) R] (y : R →ₐ[↥c.O] PadicAlgCl l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → PadicAlgCl l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha
end

section

theorem UpperTheory.Reformulated.B.Gs4b.pt_lt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {c : UpperTheory.V.HV.Coef l} {R : Type} [inst_1 : CommRing R]
      [inst_2 : Algebra (↥c.O) R] [inst_3 : IsLocalRing R] (y : R →ₐ[↥c.O] Formalism.ConjugateSelfDual.Qbar l),
      ∀ a ∈ IsLocalRing.maximalIdeal R, ‖(y : R → Formalism.ConjugateSelfDual.Qbar l) a‖ < (1 : ℝ) := by
  intro l _ c R _ _ _ y a ha
  exact UpperTheory.Reformulated.B.NormLtOne.norm_lt_one (l := l) (O := ↥c.O) y a ha
end

section

namespace UpperTheory.Reformulated.B.CoefficientRingContainingIntegers

theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : UpperTheory.V.HV.Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  have hD : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.dvr_of_norm_integral K (fun x hx => UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x hx)
  have hF : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 (UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x h1), rfl⟩

end UpperTheory.Reformulated.B.CoefficientRingContainingIntegers
end

section

open MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 in
theorem UpperTheory.Reformulated.B.BlochKatoDuality.haarInvFromUnique :
    Formalism.FourierDecayAlt.B2.HaarInvFromUnique := by
  intro huniq k r U μ hU hμ
  have hm : Measurable (invM : Mt k r → Mt k r) := UpperTheory.measurable_matrix_inv _
  have hUc : IsClosed (X := Mt k r) U := hU.closed
  have hmem : ∀ x : Mt k r, x ∈ U → invM x ∈ U := fun x hx => hU.inv_mem x hx
  have hinv : ∀ x : Mt k r, x ∈ U → invM (invM x) = x := fun x hx =>
    Matrix.nonsing_inv_nonsing_inv (Matrix.of x) (hU.unit x hx)
  have hae : ∀ᵐ x ∂μ, (x : Mt k r) ∈ U := hμ.conc
  have hcont : ContinuousOn (invM : Mt k r → Mt k r) U := by
    intro x hx
    obtain ⟨u, hu⟩ := hU.unit x hx
    have h1 : ContinuousAt Ring.inverse (Matrix.of x : Mat k r).det := by
      have h2 := NormedRing.inverse_continuousAt u
      rw [hu] at h2
      exact h2
    exact (continuousAt_matrix_inv (Matrix.of x : Mat k r) h1).continuousWithinAt
  have hfin := UpperTheory.involution_map_compact_finite (Mt k r) μ U invM hm hUc hcont hmem hinv hμ.conc hμ.finite_compact
  have hconc : (μ.map invM) (Uᶜ : Set (Mat k r)) = 0 := by
    have h : ∀ᵐ x ∂(μ.map invM), (x : Mt k r) ∈ U :=
      (ae_map_iff hm.aemeasurable hUc.measurableSet).2 (hae.mono hmem)
    exact h
  have hleft : ∀ a ∈ U, (μ.map invM).map (lmulM a) = μ.map invM := by
    intro a ha
    have hl : Measurable (lmulM a : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_const (y := a)) (continuous_id (X := Mat k r)))
    have hr : Measurable (rmulF a⁻¹ : Mt k r → Mt k r) :=
      Continuous.measurable (α := Mt k r) (γ := Mt k r)
        (Continuous.matrix_mul (continuous_id (X := Mat k r)) (continuous_const (y := a⁻¹)))
    have he : (lmulM a ∘ invM : Mt k r → Mt k r) = invM ∘ rmulF a⁻¹ := by
      funext x
      change a * (Matrix.of x : Mat k r)⁻¹ = (Matrix.of x * a⁻¹ : Mat k r)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv a (hU.unit a ha)]
    rw [Measure.map_map hl hm, he, ← Measure.map_map hm hr, hμ.right _ (hU.inv_mem a ha)]
  obtain ⟨c, hc⟩ := huniq k r U μ (μ.map invM) hU hμ hconc hleft hfin
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  exact UpperTheory.map_involution_eq_self (Mt k r) μ invM c hm (hae.mono hinv) hc
end

section

attribute [local instance] Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult :
    ∀ (D : Formalism.BasicNotions.D7)
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (v : (Formalism.MainNotions.S.VS D).V),
        ∃ (n : ℤ),
          n ≠ (0 : ℤ) ∧
            (↑n : D.host.E) • v ∈
              Λ := by
  intro D Λ h v
  obtain ⟨⟨t, ht⟩, hv⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v
    (h.span_eq_top ▸ Submodule.mem_top)
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht
  refine ⟨n, hn, ?_⟩
  have hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t := by rw [mul_comm]; simpa using hc
  have e : (n : D.host.E) • v = c • t • v := by
    rw [smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]
  rw [Submodule.span_eq] at hv
  exact e ▸ Λ.smul_mem c hv
end
