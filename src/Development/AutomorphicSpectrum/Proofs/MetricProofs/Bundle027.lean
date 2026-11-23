module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle017
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem log_div_self_anti (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a :=
  Real.log_div_self_antitoneOn ha (show Real.exp 1 ≤ b from ha.trans hab) hab

theorem epsT_mono (C t t' : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htt : t ≤ t')
    (ht' : t' ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C t' := by
  have ht'0 : 0 < t' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht'0 ht').1
  have h2 : Real.log (1 / t') ≤ Real.log (1 / t) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv]
    linarith [Real.log_le_log ht htt]
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_left (log_div_self_anti _ _ h1 h2) hC

theorem le_epsT (C t : ℝ) (hC : 1 ≤ C) (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    t ≤ epsT C t := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  set ℓ := Real.log (1 / t) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hle : ℓ ≤ 1 / t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / t by positivity)
    linarith
  have htl : t * ℓ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hle ht.le
    rwa [mul_one_div_cancel ht.ne'] at this
  have hA : t ≤ 1 / ℓ := by rw [le_div_iff₀ hℓ0]; exact htl
  have hB : 1 / ℓ ≤ Real.log ℓ / ℓ := div_le_div_of_nonneg_right h2 hℓ0.le
  have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
  have hC' : Real.log ℓ / ℓ ≤ C * (Real.log ℓ / ℓ) := le_mul_of_one_le_left hq hC
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  linarith

theorem epsT_tendsto (C : ℝ) : Tendsto (epsT C) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    simpa [Function.comp_def, one_div] using this
  have h := (hl.comp hL).const_mul C
  rw [mul_zero] at h
  have e : epsT C = fun t => C * ((fun x : ℝ => Real.log x / x) ∘ (fun t : ℝ => Real.log (1 / t))) t := by
    funext t
    rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
    rfl
  rw [e]
  exact h

theorem epsT_le_one (C : ℝ) : ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1 := by
  have hev : {t : ℝ | epsT C t < 1} ∈ 𝓝[>] (0 : ℝ) :=
    (epsT_tendsto C) (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by linarith, fun t ht hta => ?_⟩
  exact (hsub ⟨ht, by linarith⟩ : epsT C t < 1).le

theorem fin_pos_lower (n : ℕ) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j := by
  by_cases h : Nonempty (Fin n)
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty a,
      (Finset.lt_inf'_iff _).2 (fun j _ => ha j), fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
  · exact ⟨1, one_pos, fun j => (h ⟨j⟩).elim⟩

theorem epsT_numerics :
    (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧
    (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧
    (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧
    (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧
    (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) :=
  ⟨log_div_self_anti, epsT_mono, le_epsT, epsT_tendsto, epsT_le_one, fin_pos_lower⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_eq_of_const {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x y, (Ψ i).φ x y = (Φ i).φ x y + c i) : maMeasure A Ψ = maMeasure A Φ := by
  have hH : ∀ (F : (Fin e → ℂ) → ℝ) (a : ℝ) (y : Fin e → ℂ),
      hessC (fun z => F z + a) y = hessC F y := by
    intro F a y
    have h1 : fderiv ℝ (fun z => F z + a) = fderiv ℝ F := funext fun z => fderiv_add_const a
    unfold hessC
    rw [h1]
  have hD : ∀ j, locDens A Ψ j = locDens A Φ j := by
    intro j
    funext y
    unfold locDens maDens
    have hk : (fun k => hessC (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      funext k
      simp only [h k]
      exact hH _ _ y
    rw [hk]
  unfold maMeasure
  simp only [hD]

theorem exists_pos_le_all {e : ℕ} (f : Fin e → ℝ) (hf : ∀ i, 0 < f i) (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∀ i, b ≤ f i := by
  have hne : (insert a (Finset.univ.image f)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨_, (Finset.lt_min'_iff _ hne).2 fun x hx => ?_,
    Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf i

theorem tail_uniform : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∃ K t₁ : ℝ, 0 < t₁ ∧ (0 < t₀ → t₁ ≤ t₀) ∧ ∀ τ : Fin e → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ t₁) → (∀ i, IsPotential A (th i + LocPot.ofFun (phT i (τ i)) + Θ) ∧ IsPsh A (th i + LocPot.ofFun (phT i (τ i)) + Θ)) ∧ ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  choose t₂ ht₂ ht₂₀ hfix using fun i =>
    fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm (hW i) (hR i)
  obtain ⟨a, ha, hε⟩ := epsT_small C
  obtain ⟨t₁, ht₁, ht₁a, ht₁0, ht₁2⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ a ∧ (0 < t₀ → t₁ ≤ t₀) ∧
      ∀ i, t₁ ≤ t₂ i := by
    obtain ⟨b, hb, hba, hbf⟩ := exists_pos_le_all t₂ ht₂ a ha
    by_cases h0 : 0 < t₀
    · exact ⟨min b t₀, lt_min hb h0, (min_le_left _ _).trans hba, fun _ => min_le_right _ _,
        fun i => (min_le_left _ _).trans (hbf i)⟩
    · exact ⟨b, hb, hba, fun h => absurd h h0, hbf⟩
  have hB := fun i => hfix i t₁ ht₁ (ht₁2 i)
  obtain ⟨Ct, hCt⟩ := hTB A (fun i => th i + LocPot.ofFun (phT i t₁) + Θ) L s m W
    (fun i => (hB i).1) (fun i => (hB i).2.2.1) hL hS hSNC hnorm
  have hC₁ : 0 ≤ |C₅| + |C| + 1 := by positivity
  refine ⟨Ct * (|C₅| + |C| + 1 + 3), t₁, ht₁, ht₁0, fun τ hτ => ⟨fun i => ?_, fun R hRe => ?_⟩⟩
  · have hτ0 : τ i ≤ t₀ := ((hτ i).2.trans (ht₁2 i)).trans (ht₂₀ i)
    obtain ⟨hsm, -, -, -, hpsh, -, -, -⟩ := (hR i).2.2 (τ i) (hτ i).1 hτ0
    have hth := (hW i).1
    have hεi := (abs_le.1 (hε (τ i) (hτ i).1 ((hτ i).2.trans ht₁a)).1).2
    refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) hΘ,
      isPsh_of_le A Θ (th i) (phT i (τ i)) hΘ hpos hth hsm (epsT C (τ i)) 1 0 (by linarith) hpsh _
        (fun x z hz => ⟨hz.1.1, hz.2⟩) (fun x z => ?_)⟩
    show (th i).φ x z + phT i (τ i) z + Θ.φ x z = _
    ring
  · have hL' := fun i => (hB i).2.2.2 (τ i) (hτ i).1 (hτ i).2
    have hm : maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) =
        maMeasure A (fun i => (th i + LocPot.ofFun (phT i t₁) + Θ) +
          LocPot.ofFun (fun y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁)) :=
      maMeasure_eq_of_const A _ _ (fun _ => C * epsT C t₁) fun i x y => by
        show (th i).φ x y + phT i (τ i) y + Θ.φ x y =
          (th i).φ x y + phT i t₁ y + Θ.φ x y +
            (phT i (τ i) y - phT i t₁ y - C * epsT C t₁) + C * epsT C t₁
        ring
    rw [hm]
    exact hCt (|C₅| + |C| + 1) (fun i y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁) hC₁
      (fun i => (hL' i).1) (fun i => (hL' i).2.1)
      (fun i y hy => ⟨(hL' i).2.2.2 y hy, (hL' i).2.2.1 y⟩) R hRe

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.monge_ampere_density_change_of_variables : ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ) (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) → (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) → maDensity (fun (_ : Fin n) => ψ) t = ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul <;> assumption)
end
