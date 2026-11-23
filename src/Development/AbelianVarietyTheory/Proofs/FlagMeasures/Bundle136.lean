module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.IntegralDomain

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem kerProj_re_inner_reg (T : E →L[ℂ] F) (t : ℝ) (w : E) :
    (⟪w, (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) w⟫_ℂ).re
      = ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem kerProj_isUnit_reg (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) :
    IsUnit (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  have hinj : Function.Injective B := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    have h := kerProj_re_inner_reg T t w
    rw [← hB, hw] at h
    simp only [inner_zero_right, Complex.zero_re] at h
    have h1 : t * ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖T w‖]
    have h2 : ‖w‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos ht hc]
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact norm_eq_zero.mp this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[ℂ] E))).mp hinj⟩

theorem kerProj_reg_estimate (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) (k : E) (z : F)
    (hk : T k = 0) :
    ‖(t : ℂ) • Ring.inverse (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E))
      (k + ContinuousLinearMap.adjoint T z) - k‖ ^ 2 ≤ t * ‖z‖ ^ 2 := by
  have hu := kerProj_isUnit_reg T ht
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  set w := (t : ℂ) • Ring.inverse B (k + ContinuousLinearMap.adjoint T z) - k with hw
  have hBk : B k = (t : ℂ) • k := by simp [hB, hk]
  have hBw : B w = (t : ℂ) • ContinuousLinearMap.adjoint T z := by
    have : B (Ring.inverse B (k + ContinuousLinearMap.adjoint T z))
        = k + ContinuousLinearMap.adjoint T z := by
      rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]; rfl
    rw [hw, map_sub, map_smul, this, hBk, smul_add]; abel
  have h := kerProj_re_inner_reg T t w
  rw [← hB, hBw, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    Complex.re_ofReal_mul] at h
  have h1 : (⟪T w, z⟫_ℂ).re ≤ ‖T w‖ * ‖z‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 ≤ t * (‖T w‖ * ‖z‖) := by
    rw [← h]; exact mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * ‖w‖ ^ 2 ≤ t * (t * ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖T w‖ - t * ‖z‖), sq_nonneg ‖T w‖, sq_nonneg (t * ‖z‖)]
  exact le_of_mul_le_mul_left h3 ht

theorem kerProj_reg_tendsto (T : E →L[ℂ] F) (v : E) :
    Filter.Tendsto (fun j : ℕ => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint T ∘L T
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) v) Filter.atTop
      (nhds ((LinearMap.ker (T : E →ₗ[ℂ] F)).starProjection v)) := by
  set K := LinearMap.ker (T : E →ₗ[ℂ] F) with hK
  have hmem : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have horth : Kᗮ = LinearMap.range (LinearMap.adjoint (T : E →ₗ[ℂ] F)) :=
    LinearMap.orthogonal_ker _
  rw [horth] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz' : ContinuousLinearMap.adjoint T z = v - K.starProjection v := by
    rw [← hz]; rfl
  have hk : T (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hv : v = K.starProjection v + ContinuousLinearMap.adjoint T z := by rw [hz']; abel
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun j : ℕ => Real.sqrt ((1 / ((j : ℝ) + 1)) * ‖z‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖z‖ ^ 2)).sqrt
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
  apply Real.le_sqrt_of_sq_le
  have := kerProj_reg_estimate T (t := 1 / ((j : ℝ) + 1)) (by positivity) _ z hk
  rwa [← hv] at this

theorem measurable_starProjection_ker_clm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace E] [BorelSpace E] (T : X → E →L[ℂ] F) (v : X → E)
    (hT : Continuous T) (hv : Continuous v) :
    Measurable fun x => (LinearMap.ker (T x : E →ₗ[ℂ] F)).starProjection (v x) := by
  refine measurable_of_tendsto_metrizable (f := fun (j : ℕ) x => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) (v x)) (fun j => ?_) ?_
  · apply Continuous.measurable
    apply Continuous.const_smul
    refine Continuous.clm_apply ?_ hv
    have hc : Continuous fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E) :=
      ((ContinuousLinearMap.adjoint.continuous.comp hT).clm_comp hT).add continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨u, hu⟩ := kerProj_isUnit_reg (T x) (t := 1 / ((j : ℝ) + 1)) (by positivity)
    have h1 := NormedRing.inverse_continuousAt u
    rw [hu] at h1
    exact ContinuousAt.comp (f := fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) h1 hc.continuousAt
  · rw [tendsto_pi_nhds]
    intro x
    exact kerProj_reg_tendsto (T x) (v x)

end

end GlobalTheory
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem norm_unitsChar_apply {C : Type} [CommGroup C] [Fintype C] (θ : C →* ℂˣ) (z : C) :
    ‖(θ z : ℂ)‖ = 1 := by
  have h : (θ z : ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

theorem sum_unitsChar_mul_inv {C : Type} [CommGroup C] [Fintype C] (θ η : C →* ℂˣ) :
    ∑ z : C, (θ z : ℂ) * (η z⁻¹ : ℂ) = if θ = η then (Fintype.card C : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have : ∀ z : C, (θ z : ℂ) * (θ z⁻¹ : ℂ) = 1 := by
      intro z
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    simp only [this]
    simp
  · have hne : (Units.coeHom ℂ).comp (θ * η⁻¹) ≠ 1 := by
      intro h1
      apply h
      ext z
      have h2 := DFunLike.congr_fun h1 z
      have h3 : θ z * (η z)⁻¹ = 1 := by
        apply Units.ext
        simpa using h2
      rw [mul_inv_eq_one] at h3
      rw [h3]
    have := sum_hom_units_eq_zero _ hne
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp

theorem card_le_card_mul_card_support :
    ∀ (C : Type) [CommGroup C] [Fintype C] (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ), (∃ z : C, ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0) → Fintype.card C ≤ S.card * (Finset.univ.filter fun z : C => ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card := by
  intro C _ _ S c hz
  obtain ⟨z₁, hz₁⟩ := hz
  set f : C → ℂ := fun z => ∑ θ ∈ S, c θ * (θ z : ℂ) with hf
  set T : Finset C := Finset.univ.filter fun z : C => f z ≠ 0 with hT
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_max_image Finset.univ (fun z => ‖f z‖) ⟨z₁, Finset.mem_univ _⟩
  have hM : 0 < ‖f z₀‖ := lt_of_lt_of_le (norm_pos_iff.mpr hz₁) (hz₀ z₁ (Finset.mem_univ _))
  have hinv : ∀ η ∈ S, (Fintype.card C : ℂ) * c η = ∑ z ∈ T, f z * (η z⁻¹ : ℂ) := by
    intro η hη
    have h1 : ∑ z ∈ T, f z * (η z⁻¹ : ℂ) = ∑ z : C, f z * (η z⁻¹ : ℂ) := by
      rw [hT]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => ?_
      have : f z = 0 := by simpa using hz
      rw [this, zero_mul]
    rw [h1]
    simp only [hf, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_unitsChar_mul_inv, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' S η, if_pos hη, mul_comm]
  have hc : ∀ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ ≤ T.card * ‖f z₀‖ := by
    intro η hη
    have h1 : ‖(Fintype.card C : ℂ) * c η‖ = (Fintype.card C : ℝ) * ‖c η‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h1, hinv η hη]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
    exact hz₀ z (Finset.mem_univ _)
  have hf0 : ‖f z₀‖ ≤ ∑ η ∈ S, ‖c η‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
  have hfin : (Fintype.card C : ℝ) * ‖f z₀‖ ≤ ((S.card : ℝ) * T.card) * ‖f z₀‖ := by
    calc (Fintype.card C : ℝ) * ‖f z₀‖ ≤ (Fintype.card C : ℝ) * ∑ η ∈ S, ‖c η‖ :=
          mul_le_mul_of_nonneg_left hf0 (Nat.cast_nonneg _)
      _ = ∑ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ := Finset.mul_sum _ _ _
      _ ≤ S.card • ((T.card : ℝ) * ‖f z₀‖) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = _ := by rw [nsmul_eq_mul, mul_assoc]
  have := le_of_mul_le_mul_right hfin hM
  exact_mod_cast this

end GlobalTheory.GLm
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem prod_max_inv_le_prod_max {ι : Type} [Fintype ι] (x : ι → ℝ) (hx : ∀ v, 0 < x v) (h1 : 1 ≤ ∏ v, x v) :
    ∏ v, max 1 (x v)⁻¹ ≤ ∏ v, max 1 (x v) := by
  have key : ∀ v, max 1 (x v) = x v * max 1 (x v)⁻¹ := by
    intro v
    rcases le_total 1 (x v) with h | h
    · rw [max_eq_right h, max_eq_left (inv_le_one_of_one_le₀ h), mul_one]
    · rw [max_eq_left h, max_eq_right ((one_le_inv₀ (hx v)).2 h), mul_inv_cancel₀ (hx v).ne']
  have h0 : 0 ≤ ∏ v, max 1 (x v)⁻¹ :=
    Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _)
  calc ∏ v, max 1 (x v)⁻¹ = 1 * ∏ v, max 1 (x v)⁻¹ := (one_mul _).symm
    _ ≤ (∏ v, x v) * ∏ v, max 1 (x v)⁻¹ := mul_le_mul_of_nonneg_right h1 h0
    _ = ∏ v, max 1 (x v) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (key v).symm

theorem fold_max_le_prod_max {n : ℕ} (x : Fin n → ℝ) :
    Finset.univ.fold max 1 x ≤ ∏ l, max 1 (x l) := by
  have hge : ∀ l, (1 : ℝ) ≤ max 1 (x l) := fun l => le_max_left _ _
  have hone : ∀ s : Finset (Fin n), (1 : ℝ) ≤ ∏ l ∈ s, max 1 (x l) := by
    intro s
    calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ l ∈ s, max 1 (x l) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun l _ => hge l)
  refine (Finset.fold_max_le _).2 ⟨hone _, fun l _ => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  calc x l ≤ max 1 (x l) * 1 := by rw [mul_one]; exact le_max_right _ _
    _ ≤ max 1 (x l) * ∏ m ∈ Finset.univ.erase l, max 1 (x m) :=
      mul_le_mul_of_nonneg_left (hone _) (le_trans zero_le_one (hge l))

theorem prod_fold_inv_le {ι : Type} [Fintype ι] {n : ℕ} (P : ℝ) (hP : 1 ≤ P) (Dm : ι → Fin n → ℝ) (De sg : ι → ℝ)
    (hD : ∀ l, (∀ v, Dm v l = 0) ∨ ((∀ v, 0 < Dm v l) ∧ 1 ≤ ∏ v, Dm v l))
    (hDe : ∀ v, De v = Finset.univ.fold max 1 fun l => (Dm v l)⁻¹)
    (hsg : ∀ v, sg v = Finset.univ.fold max 1 fun l => Dm v l / P) :
    ∏ v, De v ≤ ∏ v, (P * sg v) ^ n := by
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  have hsg1 : ∀ v, 1 ≤ sg v := fun v => by
    rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have hPsg : ∀ v, 1 ≤ P * sg v := fun v => one_le_mul_of_one_le_of_one_le hP (hsg1 v)
  have hcol : ∀ l, ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, P * sg v := by
    intro l
    rcases hD l with h0 | ⟨hpos, hprod⟩
    · calc ∏ v, max 1 (Dm v l)⁻¹ = ∏ _v : ι, (1 : ℝ) :=
            Finset.prod_congr rfl fun v _ => by simp [h0 v]
        _ ≤ ∏ v, P * sg v := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun v _ => hPsg v)
    · calc ∏ v, max 1 (Dm v l)⁻¹ ≤ ∏ v, max 1 (Dm v l) :=
            prod_max_inv_le_prod_max (fun v => Dm v l) hpos hprod
        _ ≤ ∏ v, P * sg v := by
          refine Finset.prod_le_prod₀ (fun _ _ => le_trans zero_le_one (le_max_left _ _)) (fun v _ => ?_)
          have h1 : Dm v l / P ≤ sg v := by
            rw [hsg v]; exact (Finset.le_fold_max _).2 (Or.inr ⟨l, Finset.mem_univ _, le_rfl⟩)
          refine max_le (hPsg v) ?_
          calc Dm v l = P * (Dm v l / P) := by field_simp
            _ ≤ P * sg v := mul_le_mul_of_nonneg_left h1 hP0.le
  calc ∏ v, De v ≤ ∏ v, ∏ l, max 1 (Dm v l)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun v _ => ?_) (fun v _ => ?_)
        · rw [hDe v]; exact le_trans zero_le_one ((Finset.le_fold_max _).2 (Or.inl le_rfl))
        · rw [hDe v]; exact fold_max_le_prod_max (fun l => (Dm v l)⁻¹)
    _ = ∏ l, ∏ v, max 1 (Dm v l)⁻¹ := Finset.prod_comm
    _ ≤ ∏ _l : Fin n, ∏ v, P * sg v :=
        Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun v _ => le_trans zero_le_one (le_max_left _ _))
          (fun l _ => hcol l)
    _ = ∏ v, (P * sg v) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]

theorem const_loss_le (r : ℕ) (hr : 1 ≤ r) (H : ℝ) (hH : 1 ≤ H) :
    16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
      ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) ≤ (8 * r * H) ^ (80 * r ^ 4) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hB8 : (8 : ℝ) ≤ 8 * r * H := by nlinarith
  have hB1 : (1 : ℝ) ≤ 8 * r * H := by linarith
  have hH0 : (0 : ℝ) ≤ 2 * H := by linarith
  have e1 : (16 : ℝ) ≤ (8 * r * H) ^ 2 := by nlinarith
  have e2 : (4 * r + 4 : ℝ) ≤ (8 * r * H) ^ 1 := by rw [pow_one]; nlinarith
  have e3 : (4 * r : ℝ) ≤ 8 * r * H := by nlinarith
  have e4 : 2 * H ≤ 8 * r * H := by nlinarith
  have hexp : 2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2)) ≤ 80 * r ^ 4 := by
    have p1 : r ^ 1 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : r ^ 2 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p3 : r ^ 3 ≤ r ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p0 : 1 ≤ r ^ 4 := Nat.one_le_pow _ _ (by omega)
    rw [pow_one] at p1
    nlinarith
  calc 16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H) ^ (16 * r ^ 3 + 4 * r) *
        ((2 * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2))
      ≤ (8 * r * H) ^ 2 * (8 * r * H) ^ 1 * (8 * r * H) ^ (4 * r ^ 2) * (8 * r * H) ^ (16 * r ^ 3 + 4 * r) *
        ((8 * r * H) ^ (2 * r)) ^ ((r + 1) * (8 * r ^ 2 + 2)) := by
        have a1 := mul_le_mul e1 e2 (by positivity) (by positivity)
        have a2 := mul_le_mul a1 (pow_le_pow_left₀ (by positivity) e3 (4 * r ^ 2)) (by positivity) (by positivity)
        have a3 := mul_le_mul a2 (pow_le_pow_left₀ hH0 e4 (16 * r ^ 3 + 4 * r)) (pow_nonneg hH0 _) (by positivity)
        exact mul_le_mul a3 (pow_le_pow_left₀ (pow_nonneg hH0 _) (pow_le_pow_left₀ hH0 e4 _) _)
          (pow_nonneg (pow_nonneg hH0 _) _) (by positivity)
    _ = (8 * r * H) ^ (2 + 1 + 4 * r ^ 2 + (16 * r ^ 3 + 4 * r) + 2 * r * ((r + 1) * (8 * r ^ 2 + 2))) := by
        rw [← pow_mul]; simp only [← pow_add]
    _ ≤ (8 * r * H) ^ (80 * r ^ 4) := pow_le_pow_right₀ hB1 hexp

theorem size_loss_le (C' : ℝ) (C₁ k r : ℕ) (hC : C' + 2 ≤ C₁) (hr : 1 ≤ r) (hk : 40 * r ^ 4 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    s ^ ((r + 1) * (8 * r ^ 2 + 2)) * s ^ (-((((C₁ * k * r : ℕ) : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r)) ≤ s ^ (-(C' * k)) := by
  have hs0 : 0 < s := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hk' : 40 * (r : ℝ) ^ 4 ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [← Real.rpow_natCast, ← Real.rpow_add hs0]
  apply Real.rpow_le_rpow_of_exponent_le hs
  push_cast
  have hsplit : ((C₁ : ℝ) * k * r - 16 * r ^ 3 - 4 * r - 1) / r = C₁ * k - 16 * r ^ 2 - 4 - 1 / r := by
    field_simp
  have hinv : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr0]; exact hr'
  have hCk : (C' + 2) * k ≤ C₁ * k := mul_le_mul_of_nonneg_right hC hk0
  have q1 : (r : ℝ) ≤ r ^ 2 := by nlinarith
  have q2 : (r : ℝ) ^ 2 ≤ r ^ 3 := by nlinarith
  have q3 : (r : ℝ) ^ 3 ≤ r ^ 4 := by nlinarith
  nlinarith

end GlobalTheory.Amp
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem two_mul_pi_pow_le_four_pow (k : ℕ) (hk : 3 ≤ k) : 2 * Real.pi ^ k ≤ (4 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := Real.pi_pos.le
  have h1 : Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := pow_le_pow_left₀ h0 Real.pi_lt_d2.le 3
  have h2 : Real.pi ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ h0 Real.pi_le_four m
  have h3 : 2 * Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by norm_num at h1 ⊢; linarith
  rw [pow_add, pow_add, ← mul_assoc]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

theorem box_volume_arith : ∀ (r j n₁ n₂ n₃ : ℕ) (M : ℝ), 1 ≤ j → j ≤ r → 2 * n₁ ≤ r * (r - 1) → 2 * n₂ ≤ r * (r - 1) → n₃ ≤ r → 1 ≤ M → (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2)) ≤ (4 * r : ℝ) ^ (4 * r ^ 2) * M ^ (8 * r ^ 2) := by
  intro r j n₁ n₂ n₃ M hj hjr h1 h2 h3 hM
  have hr : 1 ≤ r := hj.trans hjr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hM0 : 0 ≤ M := by linarith
  have hA : (1 : ℝ) ≤ 4 * r := by linarith
  have hrr : r * (r - 1) + r = r ^ 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]; ring
  have hjj : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have e : (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2))
      = (Real.pi ^ n₁ * (Real.pi * (2 * r) ^ 2) ^ n₂ * (4 * r) ^ n₃ * (2 * Real.pi ^ (2 * j + j ^ 2))) *
        M ^ (2 * n₁ + 4 * n₂ + 2 * n₃ + 4 * j + 2 * j ^ 2) := by
    have a1 : Real.pi * (2 * r * M ^ 2) ^ 2 = (Real.pi * (2 * r) ^ 2) * M ^ 4 := by ring
    have a2 : 2 * (2 * r * M ^ 2) = (4 * (r : ℝ)) * M ^ 2 := by ring
    rw [a1, a2, mul_pow Real.pi, mul_pow _ (M ^ 4), mul_pow _ (M ^ 2), mul_pow Real.pi (M ^ 2)]
    generalize Real.pi * (2 * (r : ℝ)) ^ 2 = B
    generalize 4 * (r : ℝ) = C
    ring
  rw [e]
  have b1 : Real.pi ^ n₁ ≤ (4 * r : ℝ) ^ n₁ := pow_le_pow_left₀ hpi (by linarith) _
  have b2 : (Real.pi * (2 * r) ^ 2) ^ n₂ ≤ (4 * r : ℝ) ^ (2 * n₂) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (0 : ℝ) ≤ (2 * r) ^ 2 := by positivity
    nlinarith
  have b4 : 2 * Real.pi ^ (2 * j + j ^ 2) ≤ (4 * r : ℝ) ^ (2 * j + j ^ 2) :=
    (two_mul_pi_pow_le_four_pow _ (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hM (by omega)) (by positivity) (by positivity)
  calc _ ≤ (4 * r : ℝ) ^ n₁ * (4 * r : ℝ) ^ (2 * n₂) * (4 * r) ^ n₃ * (4 * r : ℝ) ^ (2 * j + j ^ 2) := by
        gcongr
    _ = (4 * r : ℝ) ^ (n₁ + 2 * n₂ + n₃ + (2 * j + j ^ 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hA (by omega)

end GlobalTheory.Amp
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem volume_product_le : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  intro r R₀ De hr hR hD
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hm : 2 * ((s + 1) * (s + 1 - 1) / 2) ≤ (s + 1) * s := by
    rw [Nat.add_sub_cancel]; omega
  generalize (s + 1) * (s + 1 - 1) / 2 = m at hm ⊢
  have e1 : 4 * (s + 1) - 2 = 4 * s + 2 := by omega
  have e2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e1, e2]
  have hx : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hr
  generalize ((s + 1 : ℕ) : ℝ) = x at hx ⊢
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have h24 : (2 : ℝ) ≤ 4 := by norm_num
  have hms : 2 * m * s ≤ (s + 1) * s * s := Nat.mul_le_mul_right s hm
  calc _ ≤ ((4 : ℝ) * (R₀ ^ (2 * (s + 1)) * De) ^ 2) ^ m * ((4 * (x * R₀ ^ (4 * s + 2) * De ^ 2) ^ 2) ^ m * (4 * (x * R₀ ^ (4 * s + 2) * De ^ 2)) ^ (s + 1)) * ((4 * (x * R₀ ^ (2 * s + 1) * De) ^ 2) ^ (3 * (s + 1)) * 4 * (x * R₀ ^ (2 * s + 1) * De) ^ (2 * (s + 1) ^ 2 + 2 * (s + 1)) * 4 ^ ((s + 1) ^ 2)) := by
        gcongr
    _ = (4 : ℝ) ^ (2 * m + (s + 1) + 3 * (s + 1) + 1 + (s + 1) ^ 2) *
          x ^ (2 * m + (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          R₀ ^ (4 * (s + 1) * m + (4 * s + 2) * 2 * m + (4 * s + 2) * (s + 1) + (2 * s + 1) * 2 * (3 * (s + 1)) + (2 * s + 1) * (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          De ^ (6 * m + 2 * (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) := by
        simp only [mul_pow, ← pow_mul]
        generalize (4 : ℝ) = c
        ring
    _ ≤ (4 : ℝ) ^ (11 * (s + 1) ^ 2) * x ^ (11 * (s + 1) ^ 2) * R₀ ^ (20 * (s + 1) ^ 3) * De ^ (12 * (s + 1) ^ 2) := by
        have h4 : (1 : ℝ) ≤ 4 := by norm_num
        gcongr
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s), Nat.zero_le (s * s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
    _ = _ := by rw [mul_pow]

end GlobalTheory.Amp
end
