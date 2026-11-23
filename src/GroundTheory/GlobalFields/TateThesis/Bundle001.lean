module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Covering.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

namespace GroundTheory.Global

open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap

noncomputable section

section DualLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem innerₗ_nondegenerate : (innerₗ E : LinearMap.BilinForm ℝ E).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun y hy => inner_self_eq_zero.mp (hy y)⟩

def dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice {L : Submodule ℤ E} {μ : E} :
    μ ∈ dualLattice L ↔ ∀ ℓ ∈ L, ∃ k : ℤ, ⟪μ, ℓ⟫ = k := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    innerₗ_apply_apply, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun ℓ _ => exists_congr fun k => eq_comm

theorem dualLattice_span_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    dualLattice (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ
      (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ _ b

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem dualLattice_eq_span : dualLattice L = Submodule.span ℤ
    (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E) innerₗ_nondegenerate
      ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))) := by
  classical
  conv_lhs => rw [← (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ]
  exact dualLattice_span_eq _

instance : DiscreteTopology (dualLattice L) := by
  rw [dualLattice_eq_span L]; infer_instance

end DualLattice

section Summability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


omit [FiniteDimensional ℝ E] in
theorem exists_norm_le_inv_one_add_pow (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity,
    fun x => ?_⟩
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this

theorem exists_summable_bound_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ ∀ ℓ : Λ, ∀ x : E, ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := exists_norm_le_inv_one_add_pow g k
  set R' := max R 0
  refine ⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro ℓ x hx
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
          _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ C * ((1 + ‖x + ℓ‖) ^ k)⁻¹ := hg _
      _ = C * ((1 + R') ^ k * (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr
      _ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring

theorem summable_norm_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g ‖x‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)

theorem continuous_tsum_comp_add [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)
  have hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun ℓ x hx => hb ℓ x (by simpa using hx))
  exact hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))

end Summability

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open Topology Filter

def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

theorem norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have h1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have : z + 1 = 2 - (1 - z) := by ring
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    have h4 : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    calc (3 : ℝ) / 2 ≤ ‖(2 : ℂ)‖ - ‖1 - z‖ := by rw [h3, h4]; linarith
      _ ≤ ‖(2 : ℂ) - (1 - z)‖ := norm_sub_norm_le _ _
      _ = ‖z + 1‖ := by rw [this]
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (z - 1)]

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ}
    (hz : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := norm_sq_sub_one_ge (hz k)
      rw [← pow_mul, ← pow_succ] at h
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ _ := h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := lt_of_le_of_lt (key k) (hz k)
  rw [div_lt_iff₀ (by positivity)] at hk
  nlinarith

theorem eq_one_of_sq_mem {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k ↦ hs _ ?_
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact hsq _ ih

namespace Circle

theorem subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup Circle)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Circle.coe_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set Circle)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem noSmallSubgroups : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Circle

namespace Complex

theorem units_subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Units.val_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set ℂˣ)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem units_noSmallSubgroups : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    units_subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : ℂˣ ↦ ‖(z : ℂ) - 1‖ :=
    (Units.continuous_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Complex

section Kernel

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

theorem isOpen_ker_of_noSmallSubgroups
    (hG : ∀ W ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (f : G →* H) (hf : Continuous f) : IsOpen (f.ker : Set G) := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : f ⁻¹' U ∈ 𝓝 (1 : G) := hf.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V, hV⟩ := hG _ hW
  have hmap : V.toSubgroup.map f = ⊥ := by
    refine hsmall _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hV hx
  refine Subgroup.isOpen_mono (H₁ := V.toSubgroup) ?_ V.isOpen
  rwa [← Subgroup.map_eq_bot_iff]

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

end Kernel

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open _root_.Complex

theorem isCoveringMap_circleExp : IsCoveringMap (Circle.exp : ℝ → Circle) :=
  Circle.isCoveringMap_exp

theorem existsUnique_circleExp_of_continuous (χ : ℝ → Circle) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) : ∃! τ : ℝ, ∀ t, χ t = Circle.exp (τ * t) := by
  have cov := isCoveringMap_circleExp
  have h0 : χ 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := χ 0) (by rw [mul_one]; exact h.symm)
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts ⟨χ, hχ⟩ (0 : ℝ) (0 : ℝ) (by simp [h0])
  have hF' : ∀ t, Circle.exp (F t) = χ t := fun t => congrFun hF t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s
    have key := cov.eq_of_comp_eq (g₁ := fun t => F (s + t) - F s - F t)
      (g₂ := fun _ => (0 : ℝ)) (by fun_prop) continuous_const (by
        funext t
        simp only [Function.comp_apply, Circle.exp_sub, hF', hmul, Circle.exp_zero]
        simp) 0 (by simp [hF0])
    intro t
    have := congrFun key t
    linarith
  have hlin : ∀ t, F t = F 1 * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' F hadd) F.continuous t 1
    simpa [mul_comm] using this
  refine ⟨F 1, fun t => by rw [← hlin, hF'], ?_⟩
  intro τ hτ
  have key := cov.eq_of_comp_eq (g₁ := fun t : ℝ => τ * t) (g₂ := fun t => F 1 * t)
    (by fun_prop) (by fun_prop)
    (by funext t; simp only [Function.comp_apply]; rw [← hτ, ← hlin, hF']) 0 (by simp)
  simpa using congrFun key 1

theorem eq_of_forall_exp_mul_eq {s s' : ℂ}
    (h : ∀ t : ℝ, Complex.exp (s * t) = Complex.exp (s' * t)) : s = s' := by
  have hd : ∀ u : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (u * t)) u 0 := by
    intro u
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul u).cexp
    simpa using this
  have e : (fun t : ℝ => Complex.exp (s * t)) = fun t : ℝ => Complex.exp (s' * t) := funext h
  have h' : HasDerivAt (fun t : ℝ => Complex.exp (s * t)) s' 0 := by rw [e]; exact hd s'
  exact (hd s).unique h'

theorem existsUnique_exp_of_continuous (χ : ℝ → ℂˣ) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) := by
  refine existsUnique_of_exists_of_unique ?_
    (fun s s' hs hs' => eq_of_forall_exp_mul_eq fun t => by rw [← hs, ← hs'])
  have hc : Continuous fun t => (χ t : ℂ) := Units.continuous_val.comp hχ
  have hnpos : ∀ t, 0 < ‖(χ t : ℂ)‖ := fun t => norm_pos_iff.mpr (χ t).ne_zero

  have ℓadd : ∀ s t, Real.log ‖(χ (s + t) : ℂ)‖ =
      Real.log ‖(χ s : ℂ)‖ + Real.log ‖(χ t : ℂ)‖ := by
    intro s t
    rw [hmul, Units.val_mul, norm_mul]
    exact Real.log_mul (hnpos s).ne' (hnpos t).ne'
  have ℓcont : Continuous fun t => Real.log ‖(χ t : ℂ)‖ := hc.norm.log fun t => (hnpos t).ne'
  have ℓlin : ∀ t, Real.log ‖(χ t : ℂ)‖ = Real.log ‖(χ 1 : ℂ)‖ * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' (fun t => Real.log ‖(χ t : ℂ)‖) ℓadd) ℓcont t 1
    simpa [mul_comm] using this

  let u : ℝ → Circle := fun t => ⟨(χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ),
    mem_sphere_zero_iff_norm.2 (by simp [(hnpos t).ne'])⟩
  have ucont : Continuous u := by
    apply Continuous.subtype_mk
    exact hc.div (Complex.continuous_ofReal.comp hc.norm) fun t => by
      exact_mod_cast (hnpos t).ne'
  have umul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    apply Circle.coe_injective
    rw [Circle.coe_mul]
    show (χ (s + t) : ℂ) / (‖(χ (s + t) : ℂ)‖ : ℂ) =
      (χ s : ℂ) / (‖(χ s : ℂ)‖ : ℂ) * ((χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ))
    rw [hmul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  obtain ⟨τ, hτ, -⟩ := existsUnique_circleExp_of_continuous u ucont umul
  refine ⟨Real.log ‖(χ 1 : ℂ)‖ + τ * I, fun t => ?_⟩
  have h1 : (χ t : ℂ) = (‖(χ t : ℂ)‖ : ℂ) * (u t : ℂ) := by
    show _ = _ * (_ / _)
    rw [mul_div_cancel₀]
    exact_mod_cast (hnpos t).ne'
  have h2 : (‖(χ t : ℂ)‖ : ℂ) = Complex.exp ((Real.log ‖(χ 1 : ℂ)‖ * t : ℝ)) := by
    rw [← ℓlin, ← Complex.ofReal_exp, Real.exp_log (hnpos t)]
  rw [h1, h2, hτ t, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end GroundTheory.Global
end

section

open Real Function
open scoped ContDiff Nat SchwartzMap

namespace GroundTheory.Global

noncomputable section

theorem one_add_pow_mul_exp_neg_pi_mul_sq_le {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * π)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp (N * r) := by
    calc (1 + r) ^ N ≤ Real.exp r ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
      _ = Real.exp (N * r) := by rw [← Real.exp_nat_mul]
  calc (1 + r) ^ N * Real.exp (-π * r ^ 2) ≤ Real.exp (N * r) * Real.exp (-π * r ^ 2) := by
        gcongr
    _ = Real.exp (N * r - π * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (N ^ 2 / (4 * π)) := by
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N : ℝ) - 2 * π * r), Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianFun (x : E) : ℂ := ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)

theorem contDiff_gaussianFun : ContDiff ℝ ∞ (gaussianFun (E := E)) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem norm_iteratedFDeriv_gaussian_le (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (gaussianFun (E := E)) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-π * ‖x‖ ^ 2) := by
  set q : E → ℝ := fun x ↦ -π * ‖x‖ ^ 2 with hq_def
  have hq : q.HasTemperateGrowth := (HasTemperateGrowth.const (-π)).mul (hasTemperateGrowth_norm_sq E)
  have hqs : ContDiff ℝ ∞ q := contDiff_const.mul (contDiff_norm_sq ℝ)
  obtain ⟨k, C, hC, hb⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * max C 1 ^ n, k * n, by positivity, fun x ↦ ?_⟩
  have hx1 : 1 ≤ (1 + ‖x‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg x])
  set D := max C 1 * (1 + ‖x‖) ^ k
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (le_max_right _ _) hx1
  have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ q) x‖ ≤ n ! * Real.exp (q x) * D ^ n := by
    refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hqs (by exact_mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_exp i (q x)).le) fun i hi1 hin ↦ ?_
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ C * (1 + ‖x‖) ^ k := hb i hin x
      _ ≤ D := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ D ^ i := le_self_pow₀ hD1 (by omega)
  have hG : gaussianFun (E := E) = (Complex.ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ (Real.exp ∘ q) := rfl
  rw [hG, LinearIsometry.norm_iteratedFDeriv_comp_left _
    (Real.contDiff_exp.comp hqs).contDiffAt (by exact_mod_cast le_top)]
  refine hcomp.trans (le_of_eq ?_)
  simp only [D, mul_pow, ← pow_mul, hq_def]
  ring

def gaussianSchwartz (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : 𝓢(E, ℂ) where
  toFun := gaussianFun
  smooth' := contDiff_gaussianFun
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_gaussian_le (E := E) n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n gaussianFun x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-π * ‖x‖ ^ 2)) :=
          mul_le_mul hk (hb x) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-π * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * π)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_pi_mul_sq_le (norm_nonneg x) _) hC

@[simp]
theorem gaussianSchwartz_apply (x : E) :
    gaussianSchwartz E x = ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) :=
  rfl

end

end GroundTheory.Global
end
