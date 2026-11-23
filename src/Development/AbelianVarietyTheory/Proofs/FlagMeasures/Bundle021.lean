module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
public import Mathlib.Analysis.Normed.Module.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle007
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBoundByDyadicSummation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Index
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Fourier.FourierTransform
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory

theorem henselStep_card_comap {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by
  have hsup : d.range ⊔ T2 = T1 := by
    apply le_antisymm
    · refine sup_le ?_ h21
      rintro _ ⟨w, rfl⟩
      exact hd1 w
    · intro t ht
      obtain ⟨w, hw⟩ := hd2 t ht
      have : t = d w + -(d w - t) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)
  have h1 : (T2.comap d).index = T2.relIndex T1 := by
    rw [AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]
  have h2 := AddSubgroup.card_mul_index (T2.comap d)
  have h3 := AddSubgroup.card_mul_index (T2.addSubgroupOf T1)
  have h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2 :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv
  rw [h4] at h3
  rw [← h2, ← h3, h1]
  unfold AddSubgroup.relIndex
  ring

theorem henselStep_count {V W T : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Finite V] [Finite W] [Finite T] (ι : W →+ V) (f : V → T) (P : Set V)
    (T1 T2 : AddSubgroup T) (τ : T) (h21 : T2 ≤ T1) (hP : ∀ y ∈ P, ∀ w, y + ι w ∈ P)
    (hd : ∀ y ∈ P, ∃ d : W →+ T, (∀ w, d w ∈ T1) ∧ (∀ t ∈ T1, ∃ w, d w - t ∈ T2) ∧
      ∀ w, f (y + ι w) - f y - d w ∈ T2) :
    Set.ncard {y | y ∈ P ∧ f y - τ ∈ T1} * Nat.card T2 =
      Set.ncard {y | y ∈ P ∧ f y - τ ∈ T2} * Nat.card T1 := by
  set S1 : Set V := {y | y ∈ P ∧ f y - τ ∈ T1} with hS1
  set S2 : Set V := {y | y ∈ P ∧ f y - τ ∈ T2} with hS2

  have ha : Nat.card (Σ y : S1, {w : W // (y : V) + ι w ∈ S2}) = S2.ncard * Nat.card W := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1 + ι p.2.1, p.2.2⟩, p.2.1)
        invFun := fun q => ⟨⟨q.1.1 + ι (-q.2), ?_⟩, ⟨q.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨⟨u, hu, hu2⟩, w⟩ := q
      refine ⟨hP u hu _, ?_⟩
      obtain ⟨d, h1, -, h3⟩ := hd u hu
      have : f (u + ι (-w)) - τ = (f (u + ι (-w)) - f u - d (-w)) + d (-w) + (f u - τ) := by
        abel
      simp only
      rw [this]
      exact T1.add_mem (T1.add_mem (h21 (h3 _)) (h1 _)) (h21 hu2)
    · simp
    · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
      have : y + ι w + ι (-w) = y := by simp
      refine Sigma.subtype_ext ?_ rfl
      exact Subtype.ext this
    · rintro ⟨⟨u, hu⟩, w⟩
      simp
  have hb : ∀ y : S1, Nat.card {w : W // (y : V) + ι w ∈ S2} * Nat.card T1 =
      Nat.card W * Nat.card T2 := by
    rintro ⟨y, hy, hy1⟩
    obtain ⟨d, h1, h2, h3⟩ := hd y hy
    rw [← henselStep_card_comap T1 T2 h21 d h1 h2]
    congr 1
    obtain ⟨w0, hw0⟩ := h2 _ (T1.neg_mem hy1)
    refine Nat.card_congr ((Equiv.subRight w0).subtypeEquiv ?_)
    intro w
    simp only [hS2, Set.mem_setOf_eq, Equiv.subRight_apply, AddSubgroup.mem_comap, map_sub]
    have key : f (y + ι w) - τ =
        (f (y + ι w) - f y - d w) + (d w0 - -(f y - τ)) + (d w - d w0) := by abel
    rw [key]
    constructor
    · rintro ⟨-, h⟩
      exact (T2.add_mem_cancel_left (T2.add_mem (h3 w) hw0)).1 h
    · intro h
      exact ⟨hP y hy w, T2.add_mem (T2.add_mem (h3 w) hw0) h⟩
  haveI := Fintype.ofFinite S1
  rw [Nat.card_sigma] at ha
  have hc : S2.ncard * Nat.card W * Nat.card T1 = S1.ncard * (Nat.card W * Nat.card T2) := by
    rw [← ha, Finset.sum_mul, Finset.sum_congr rfl (fun y _ => hb y), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hW : 0 < Nat.card W := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hW
  linarith [hc]

end GlobalTheory
end

section

open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace GlobalTheory

theorem integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)

theorem eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by
  rintro φ R hφ ⟨A, e, he, hb⟩ hz
  set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hre : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]
    constructor <;> linarith
  have hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|))) :=
    (integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hbound : ∀ s : ℝ, ∀ y ∈ U,
      ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|)) := by
    intro s y hy
    have hy' : |y.im| ≤ e / 2 := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    have h1 : (-(Complex.I * y * s)).re = y.im * s := by simp
    have h2 : y.im * s ≤ e / 2 * |s| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hy' (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, h1]
    calc Real.exp (y.im * s) * ‖φ s‖
        ≤ Real.exp (e / 2 * |s|) * (A * Real.exp (-(e * |s|))) :=
          mul_le_mul (Real.exp_le_exp.2 h2) (hb s) (norm_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-(e / 2 * |s|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdiff := (differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo
    (fun y _ => Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => Differentiable.differentiableOn (by fun_prop))
    (fun x hx => ⟨U, hUo.mem_nhds hx, _, hint, Eventually.of_forall hbound⟩)).1
  have han := hdiff.analyticOnNhd hUo
  have hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ),
      ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using (ne_of_gt hx)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hz x (le_of_lt hx)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected
    (hre R) hfr
  have hF : 𝓕 φ = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := hzero (hre (2 * Real.pi * w))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hinv := hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem continuous_prod_ofFn_curves {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (hc : ∀ i, Continuous (c i)) :
    Continuous fun t : Fin N → ℝ => (List.ofFn fun i => c i (t i)).prod := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hc 0).comp (continuous_apply 0)).mul
      ((ih (fun i => c i.succ) (fun i => hc i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

theorem integral_cube_succ_last (N : ℕ) (s : ℝ) (f : (Fin (N + 1) → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r))
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
    ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
  set T : Set (Fin N → ℝ) := Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s) with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_Icc
  have hG : Continuous fun z : (Fin N → ℝ) × ℝ => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) :=
    hf.comp (Continuous.finSnoc (n := N) (A := fun _ => ℝ) continuous_fst continuous_snd)
  refine ⟨?_, ?_⟩
  · exact (continuous_parametric_integral_of_continuous
      (f := fun t r => f (Fin.snoc (α := fun _ => ℝ) t r)) hG isCompact_Icc).continuousOn.integrableOn_compact hTc
  · let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hp : MeasurePreserving e (volume : Measure (Fin (N + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hsymm : ∀ z : ℝ × (Fin N → ℝ), e.symm z = Fin.snoc (α := fun _ => ℝ) z.2 z.1 := by
      intro z
      simp [e, MeasurableEquiv.piFinSuccAbove]
    have hS : Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) =
        e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_prod, hT, Set.mem_pi, Set.mem_univ, true_implies]
      rw [Fin.forall_fin_succ', and_comm]
      simp [e, Fin.init]
    have hsw : (fun z : (Fin N → ℝ) × ℝ => f (e.symm z.swap)) =
        fun z => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) := by
      funext z
      rw [hsymm]
      rfl
    calc ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t
        = ∫ t in e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T), f (e.symm (e t)) := by
          rw [hS]
          simp only [MeasurableEquiv.symm_apply_apply]
      _ = ∫ z in Set.Icc (0 : ℝ) s ×ˢ T, f (e.symm z) ∂((volume : Measure ℝ).prod volume) :=
          hp.setIntegral_preimage_emb e.measurableEmbedding (fun z => f (e.symm z)) _
      _ = ∫ z in T ×ˢ Set.Icc (0 : ℝ) s, f (e.symm z.swap)
            ∂((volume : Measure (Fin N → ℝ)).prod volume) :=
          (setIntegral_prod_swap _ _ _).symm
      _ = ∫ t in T, ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
          rw [setIntegral_prod]
          · simp only [hsymm, Prod.swap_prod_mk]
          · rw [hsw]
            exact hG.continuousOn.integrableOn_compact (hTc.prod isCompact_Icc)

private theorem sq_norm_le_sobolev_of_hasDerivAt {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (γ : ℝ → G) (hγc : Continuous γ) (hγ0 : γ 0 = 1) (hγ : ∀ a b, γ (a + b) = γ a * γ b)
    (f g : G → H) (hg : Continuous g) (hd : ∀ x, HasDerivAt (fun t => f (x * γ t)) (g x) 0)
    (s : ℝ) (hs : 0 < s) (x : G) :
    ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in Set.Icc (0 : ℝ) s, ‖f (x * γ r)‖ ^ 2) +
      2 * s * ∫ r in Set.Icc (0 : ℝ) s, ‖g (x * γ r)‖ ^ 2 := by
  have key := sobolev_endpoint_one_variable H (fun r => f (x * γ r)) (fun r => g (x * γ r)) s hs
    (fun r _ => by
      have h1 : HasDerivAt (fun t => f (x * γ r * γ t)) (g (x * γ r)) (r - r) := by
        rw [sub_self]
        exact hd _
      have h2 := h1.comp_sub_const r r
      convert h2 using 1
      funext t
      rw [mul_assoc, ← hγ, add_sub_cancel])
    (hg.comp (continuous_const.mul hγc)).continuousOn
  rw [intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at key
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  simp only [hγ0, mul_one] at key
  exact key

private theorem sobolev_iter_lemma_2 {G V H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : ℕ → Set V) (Fr : V → G → H) (s be : ℝ) (y : G) (P₀ : ℕ)
    (hs : 0 < s) (hA : Monotone A) (N : ℕ) :
    ∀ (c : Fin N → ℝ → G) (D : Fin N → V → V) (C : ℝ), 0 ≤ C →
      (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
      (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧
        ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) →
      (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) →
      (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) →
      ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  induction N with
  | zero =>
    intro c D C hC hc hF hb hI u hu
    have h := hI u hu
    have hset : Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) s) = Set.univ := by
      ext t
      simp
    rw [hset, Measure.restrict_univ, volume_pi, Measure.pi_of_empty, integral_dirac] at h
    simpa using h
  | succ N ih =>
    intro c D C hC hc hF hb hI u hu
    have hmain := ih (fun i => c i.castSucc) (fun i => D i.castSucc)
      ((2 / s + 2 * s * be ^ 2) * C) (by positivity) (fun i => hc i.castSucc)
      (fun p w hw => ⟨(hF p w hw).1, fun i => (hF p w hw).2 i.castSucc⟩)
      (fun p hp w hw i => hb p (by omega) w hw i.castSucc) ?_ u hu
    · calc ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * ((2 / s + 2 * s * be ^ 2) * C) * ‖u‖ ^ 2 :=
            hmain
        _ = (2 / s + 2 * s * be ^ 2) ^ (N + 1) * C * ‖u‖ ^ 2 := by ring
    · intro w hw
      have hw1 : w ∈ A (P₀ + (N + 1)) := hA (by omega) hw
      have hDw : D (Fin.last N) w ∈ A (P₀ + (N + 1)) := by
        have h := ((hF (P₀ + N) w hw).2 (Fin.last N)).1
        rwa [add_assoc] at h
      have hbw : ‖D (Fin.last N) w‖ ≤ be * ‖w‖ := hb (P₀ + N) (by omega) w hw (Fin.last N)
      have hpc : Continuous fun t : Fin (N + 1) → ℝ => (List.ofFn fun i => c i (t i)).prod :=
        continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
      have hpc' : Continuous fun t : Fin N → ℝ =>
          (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod :=
        continuous_prod_ofFn_curves N _ (fun i => (hc i.castSucc).1)
      have hcw : Continuous (Fr w) := (hF _ w hw).1
      have hcDw : Continuous (Fr (D (Fin.last N) w)) := (hF _ _ hDw).1
      obtain ⟨i1, e1⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcw.comp (continuous_const.mul hpc)).norm.pow 2)
      obtain ⟨i2, e2⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcDw.comp (continuous_const.mul hpc)).norm.pow 2)
      have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
          (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod =
            (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r := by
        intro t r
        rw [List.ofFn_succ']
        simp only [List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
          Fin.snoc_castSucc, Fin.snoc_last]
      simp only [hsn, ← mul_assoc] at i1 e1 i2 e2
      have hL : IntegrableOn (fun t : Fin N → ℝ =>
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2)
          (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
        ((hcw.comp (continuous_const.mul hpc')).norm.pow 2).continuousOn.integrableOn_compact
          (isCompact_univ_pi fun _ => isCompact_Icc)
      have hstep : ∀ t : Fin N → ℝ,
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2 ≤
            2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2 :=
        fun t => sq_norm_le_sobolev_of_hasDerivAt (c (Fin.last N)) (hc _).1 (hc _).2.1 (hc _).2.2 (Fr w) _ hcDw
          ((hF _ w hw).2 (Fin.last N)).2 s hs _
      have hDsq : ‖D (Fin.last N) w‖ ^ 2 ≤ (be * ‖w‖) ^ 2 := by gcongr
      calc _ ≤ ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
            (2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) :=
            setIntegral_mono hL ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s))) hstep
        _ = 2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) +
            2 * s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) := by
            rw [integral_add (i1.const_mul (2 / s)) (i2.const_mul (2 * s)), integral_const_mul,
              integral_const_mul, e1, e2]
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * ‖D (Fin.last N) w‖ ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left (hI w hw1) (by positivity))
              (mul_le_mul_of_nonneg_left (hI _ hDw) (by positivity))
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * (be * ‖w‖) ^ 2) := by gcongr
        _ = (2 / s + 2 * s * be ^ 2) * C * ‖w‖ ^ 2 := by ring

theorem sobolev_iterated_one_parameter_subgroups : ∀ (G V H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (N P₀ : ℕ) (c : Fin N → ℝ → G) (A : ℕ → Set V) (D : Fin N → V → V) (Fr : V → G → H) (s be C : ℝ) (y : G), 0 < s → 0 ≤ be → 0 ≤ C → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → Monotone A → (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧ ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) → (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) → (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) → ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  intro G V H _ _ _ _ _ _ _ N P₀ c A D Fr s be C y hs _ hC hc hA hF hb hI u hu
  exact sobolev_iter_lemma_2 A Fr s be y P₀ hs hA N c D C hC hc hF hb hI u hu

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  first | exact @GlobalTheory.squeeze_continuousAt_zero | exact GlobalTheory.squeeze_continuousAt_zero | (intros; apply GlobalTheory.squeeze_continuousAt_zero <;> assumption)
end

section

open MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_bound_by_dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r kk : ℕ) (H₁ De D K K' : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ r ∧ D ≤ max (S x) (S' x) ^ (2 * r) ∧ Y x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r ∧ Y' x ≤ (r * max (S x) (S' x) ^ (2 * r - 1) * De) ^ r) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ i * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < S x) ∧ S' x ≤ 2 ^ i' * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < S' x) ∧ S x ≤ 2 ^ i * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (Real.sqrt (K * K') * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ kk) := by
  first | exact @GlobalTheory.Dyadic.dyadic_summation | exact GlobalTheory.Dyadic.dyadic_summation | (intros; apply GlobalTheory.Dyadic.dyadic_summation <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exponent_divisor_sum_le : ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  first | exact @GlobalTheory.exponent_sum_le | exact GlobalTheory.exponent_sum_le | (intros; apply GlobalTheory.exponent_sum_le <;> assumption)
end

section

open Matrix Finset Real

theorem _root_.GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower' : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by
  first | exact @GlobalTheory.exp_quadratic_lower_and_log_linear_lower | exact GlobalTheory.exp_quadratic_lower_and_log_linear_lower | (intros; apply GlobalTheory.exp_quadratic_lower_and_log_linear_lower <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.iwasawa_slice_indicator_lintegral_le : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  first | exact @GlobalTheory.iwasawa_slice_lintegral_le | exact GlobalTheory.iwasawa_slice_lintegral_le | (intros; apply GlobalTheory.iwasawa_slice_lintegral_le <;> assumption)
end
