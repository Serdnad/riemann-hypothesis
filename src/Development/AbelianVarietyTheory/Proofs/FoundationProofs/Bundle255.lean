module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle245
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_gaussian_unitary_pos : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, 0 < κ ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos, fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.adelicHermitianCharacterPairing_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  first | exact @GlobalTheory.FinWeil.gamA_alg | exact GlobalTheory.FinWeil.gamA_alg | (intros; apply GlobalTheory.FinWeil.gamA_alg <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.theta_point_additive_form : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  first | exact @GlobalTheory.FinWeil.WdCocycle.wd_cocycle | exact GlobalTheory.FinWeil.WdCocycle.wd_cocycle | (intros; apply GlobalTheory.FinWeil.WdCocycle.wd_cocycle <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  first | exact @GlobalTheory.CompletedLattice.completed_lattice | exact GlobalTheory.CompletedLattice.completed_lattice | (intros; apply GlobalTheory.CompletedLattice.completed_lattice <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  first | exact @GlobalTheory.FinWeil.AdelicChar.exists_psi | exact GlobalTheory.FinWeil.AdelicChar.exists_psi | (intros; apply GlobalTheory.FinWeil.AdelicChar.exists_psi <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_goodIndexNormalization_negative_inert : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  first | exact @GlobalTheory.FinWeil.exists_goodNorm | exact GlobalTheory.FinWeil.exists_goodNorm | (intros; apply GlobalTheory.FinWeil.exists_goodNorm <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem translate_modifiedSigma_add_mul_sub_at_zero :
    ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ →
      U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 =
        (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  intro Λ hΛ P Q hP hQ
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ
  have hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) =
      (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2 := by
    linear_combination hlaw
  simp only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]
  have hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x) := by
    intro x; rw [← Complex.exp_nat_mul]; norm_num
  have key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) =
      Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 *
      Complex.exp (-(↑Real.pi * Q * (starRingEnd ℂ) Q / (2 * ↑(area Λ)))) ^ 2 := by
    rw [hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add (f := _), map_sub]
    ring
  calc _ = (sgStar Λ (P + Q) * sgStar Λ (P - Q)) *
      (Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ))))) := by ring
    _ = _ := by rw [hσ, key]; ring

end GlobalTheory
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ThetaLaw

open GlobalTheory.ThetaParam

theorem pull_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  intro Λ hΛ t₀ ht y N hy ω hω z
  have hlaw : ∀ x ∈ Λ, ∀ v, sgStar Λ (v + x) = (if x / 2 ∈ Λ then 1 else -1) * sgStar Λ v *
      Complex.exp ((Real.pi : ℂ) * v * (starRingEnd ℂ) x / (area Λ : ℂ) +
        (Real.pi : ℂ) * x * (starRingEnd ℂ) x / (2 * (area Λ : ℂ))) := by
    intro x hx v
    have e := hΛ.sg_law hx v
    simp only [U1] at e
    rw [← e, mul_assoc, ← Complex.exp_add]
    ring_nf
    simp
  have hne : ∃ z, sgStar Λ z ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1
    rw [show sgStar Λ = fun _ => 0 from funext h] at hd
    simp at hd
  have hsl : ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
    fun ω hω z => hΛ.sg_law hω z
  have hx : (N : ℂ) * ω ∈ Λ := by simpa [nsmul_eq_mul] using nsmul_mem hω N
  have c1 : cocy Λ ((N : ℂ) * ω) y ^ 2 = 1 := by
    have e := cocy_pow Λ ω y N 1
    have r := cocy_root (m := 1) (n := N) hne hsl (by simpa using hω) hy
    simp only [Nat.cast_one, one_mul, mul_one] at e r
    rw [e, ← pow_mul, r]
  have c2 : cocy Λ ((N : ℂ) * ω) t₀ ^ 4 = 1 := by
    have r := cocy_root (m := 1) (n := 2) hne hsl (a := (N : ℂ) * ω) (b := t₀) (by simpa using hx) (by simpa using ht)
    simpa using r
  have hψ : ∀ x : ℂ, (if x / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro x; split_ifs <;> norm_num
  have hprod : ∀ v, U1 Λ y (GL3Theta.th0 Λ t₀) v * GL3Theta.th0 Λ t₀ v =
      sgStar Λ (v + y + t₀) * sgStar Λ (v + t₀) *
        (Complex.exp (-(Real.pi : ℂ) * (v + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * v * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) /
        (U1 Λ t₀ (sgStar Λ) 0) ^ 2 := by
    intro v
    simp only [GL3Theta.th0, U1]
    ring
  have hE : Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + y + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      Complex.exp ((Real.pi : ℂ) * ((N : ℂ) * z + t₀) * (starRingEnd ℂ) ((N : ℂ) * ω) / (area Λ : ℂ) +
        (Real.pi : ℂ) * ((N : ℂ) * ω) * (starRingEnd ℂ) ((N : ℂ) * ω) / (2 * (area Λ : ℂ))) *
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω) + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * (z + ω)) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) =
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) *
      (cocy Λ ((N : ℂ) * ω) y ^ 2 * cocy Λ ((N : ℂ) * ω) t₀ ^ 4) := by
    simp only [cocy, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_add (f := _), map_natCast]
    push_cast
    ring
  rw [c1, c2, mul_one, mul_one] at hE
  rw [hprod, hprod,
    show (N : ℂ) * (z + ω) + y + t₀ = ((N : ℂ) * z + y + t₀) + (N : ℂ) * ω by ring,
    show (N : ℂ) * (z + ω) + t₀ = ((N : ℂ) * z + t₀) + (N : ℂ) * ω by ring,
    hlaw _ hx, hlaw _ hx, hlaw _ hω z, mul_pow, mul_pow, pow_mul (if ω / 2 ∈ Λ then (1 : ℂ) else -1) 2 (N ^ 2), hψ ω, one_pow, one_mul]
  linear_combination (sgStar Λ ((N : ℂ) * z + y + t₀) * sgStar Λ ((N : ℂ) * z + t₀) * sgStar Λ z ^ (2 * N ^ 2) /
      (U1 Λ t₀ (sgStar Λ) 0) ^ 2) * ((if (N : ℂ) * ω / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 * hE +
      (Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z + y) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) y / (area Λ : ℂ) -
            (Real.pi : ℂ) * y * (starRingEnd ℂ) y / (2 * (area Λ : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * ((N : ℂ) * z) * (starRingEnd ℂ) t₀ / (area Λ : ℂ) -
            (Real.pi : ℂ) * t₀ * (starRingEnd ℂ) t₀ / (2 * (area Λ : ℂ)))) *
      Complex.exp ((Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) +
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) ^ (2 * N ^ 2) * hψ ((N : ℂ) * ω))

end GlobalTheory.ThetaLaw
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.SerRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_finsum_le {ι : Type*} (F : ι → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ᶠ i, F i‖ ≤ B := by
  refine finsum_induction (p := fun x => ‖x‖ ≤ B) (by simpa using hB) (fun x y hx hy => ?_) h
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem norm_coeff_mul_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hA

theorem norm_coeff_add_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f + g)‖ ≤ max A B := by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_sub_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f - g)‖ ≤ max A B := by
  rw [map_sub]
  exact (norm_sub_le_max' _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_C_le (c : K) (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.C c)‖ ≤ ‖c‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem intSer_mul {f g : PowerSeries K} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := fun n => by
  simpa using norm_coeff_mul_le f g 1 1 hf hg n

theorem intSer_pow {f : PowerSeries K} (hf : IntSer f) (d : ℕ) : IntSer (f ^ d) := by
  induction d with
  | zero => intro n; simpa using norm_coeff_C_le (1 : K) n
  | succ d ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_inv {f : PowerSeries K} (hf : IntSer f) (h0 : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · simp [h0]
    · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      split_ifs with hx
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hx)
      · simp

theorem norm_coeff_subst_le (f h : PowerSeries K) (B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hh : IntSer h) (h0 : PowerSeries.constantCoeff h = 0) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries K)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  refine norm_finsum_le _ hB fun d => ?_
  rw [smul_eq_mul, norm_mul]
  simpa using mul_le_mul (hf d) (intSer_pow hh d n) (norm_nonneg _) hB

theorem series_ring_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  intro p _
  refine ⟨fun f g hf hg => ⟨fun n => ?_, fun n => ?_, intSer_mul hf hg⟩,
    fun f g ⟨A, hf⟩ ⟨B, hg⟩ => ⟨⟨_, norm_coeff_add_le f g A B hf hg⟩, ⟨_, norm_coeff_sub_le f g A B hf hg⟩,
      ⟨_, norm_coeff_mul_le f g A B hf hg⟩⟩,
    fun c => ⟨⟨_, norm_coeff_C_le c⟩, fun hc n => (norm_coeff_C_le c n).trans hc⟩, fun n => ?_,
    fun f => intSer_inv, norm_coeff_subst_le, norm_coeff_mul_le⟩
  · simpa using norm_coeff_add_le f g 1 1 hf hg n
  · simpa using norm_coeff_sub_le f g 1 1 hf hg n
  · rw [PowerSeries.coeff_X]
    split_ifs <;> simp

end GlobalTheory.EvenTheta.SerRing
end
end
