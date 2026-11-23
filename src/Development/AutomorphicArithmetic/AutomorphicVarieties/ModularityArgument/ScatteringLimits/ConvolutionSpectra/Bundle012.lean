module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle007
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W)

private theorem k1 {T : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : r ≤ 0) (h : H) : M.abelian₂ T T (M.F.U r (M.P (Ioi T) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T))).2.2.2.2 r).1 h
  have y1 : (fun x : ℝ => x + r) ⁻¹' Ioi T = Ioi (T - r) := by ext x; simp [sub_lt_iff_lt_add]
  have x2 := (hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T - r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.1 _

private theorem k2 {T δ : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : -δ ≤ r) (h : H) : M.abelian₂ T T (M.F.U r (M.P' (Ioi (T + δ)) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T + δ)) (measurableSet_Ioi (a := T))).2.2.2.2 r).2 h
  have y1 : (fun x : ℝ => x - r) ⁻¹' Ioi (T + δ) = Ioi (T + δ + r) := by ext x; simp [lt_sub_iff_add_lt]
  have x2 : M.P' (Ioi T) ∘L M.P' (Ioi (T + δ + r)) = M.P' (Ioi T ∩ Ioi (T + δ + r)) :=
    ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T + δ + r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.2.2.1 _

private theorem k3 {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0) (A : H →L[ℂ] H) (h : H)
    (hA : ∀ r, -δ ≤ r → r ≤ 0 → A (M.F.U r h) = 0) : A (M.F.av (fun t => (ψ t : ℂ)) h) = 0 := by
  obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).1 h
  rw [e, ← A.integral_comp_comm i]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (-δ) 0
  · simp [hA r hr.1 hr.2]
  · simp [hψ.supp r hr]

private theorem k4 {T ρ : ℝ} (hρ : 0 ≤ ρ) : M.P' (Ioi T) = M.P' (Ioc T (T + ρ)) + M.P' (Ioi (T + ρ)) := by
  have := ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := T) (b := T + ρ)) (measurableSet_Ioi (a := T + ρ))).2.2.2.1
    (Ioc_disjoint_Ioi le_rfl)
  rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this

private theorem k5 (T : ℝ) (h : H) : h = M.abelian₂ T T h + M.P (Ioi T) h + M.P' (Ioi T) h := by
  show h = h - M.P (Ioi T) h - M.P' (Ioi T) h + _ + _
  abel

private theorem k6 {X : H →L[ℂ] H} {κ : ℝ → V →L[ℂ] W} (hk : Ker κ) (hX : M.Carries X κ) {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsHilbertSchmidt (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ∧ IsHilbertSchmidt (M.P' (Ioc a b) ∘L X) ∧
    hsNorm (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ W * ∫ x, ψ x ^ 2) ∧
    hsNorm (M.P' (Ioc a b) ∘L X) ^ 2 = (b - a) * ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2 ∧
    M.P' (Ioc a b) ∘L M.P' (Ioc a b) = M.P' (Ioc a b) := by
  obtain ⟨hs, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  obtain ⟨b1, b2, b3, b4, -⟩ := bandHS M.swap _ _ (convAdj κ hk).1 (carLaws M X κ hk hX).2.1 (fun t => (ψ (-t) : ℂ)) a b
    (Complex.continuous_ofReal.comp (hψ.cont.comp continuous_neg))
    ((hs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun x : ℝ => (x : ℂ)) rfl) hab
  have e : M.swap.F.av (fun t => (ψ (-t) : ℂ)) = M.F.av fun t => (ψ t : ℂ) := by
    have := ((avSpec M.F).2.2.2 _ hi.comp_neg).2.2.2.1
    simp only [neg_neg] at this
    exact this
  rw [e] at b3 b4
  obtain ⟨p1, p2, -⟩ := (projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := a) (b := b)) (measurableSet_Ioc (a := a) (b := b))
  rw [inter_self] at p1
  have e2 : M.P' (Ioc a b) ∘L X = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint X ∘L M.swap.P (Ioc a b)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, p2.adjoint_eq]; rfl
  refine ⟨b3, e2 ▸ b1.adjoint, b4.trans ?_, by rw [e2, hsNorm_adjoint, b2], p1⟩
  have := integral_neg_eq_self (fun x => ψ x ^ 2) volume
  simp [this]
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceFar :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) ∧
      Tendsto (fun a : ℝ => trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T)) atTop (𝓝 0) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T hψ hT htc
  obtain ⟨ρ₀, hρ₀⟩ := hk.2.isCompact.isBounded.subset_closedBall 0
  have hρ : ∀ t, max ρ₀ 0 < |t| → κ t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport fun h => by
    have := hρ₀ h
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    linarith [le_max_left ρ₀ 0]
  set ρ := max ρ₀ 0
  have r0 : 0 ≤ ρ := le_max_right _ _
  obtain ⟨h1, h2, -, -, h3⟩ := k6 M hk hX hψ (a := T) (b := T + ρ) (by linarith)
  obtain ⟨-, -, l0, -, ln, -, l2, -⟩ := (projLaws M).2.2.2.2.2.2.2 T T (by linarith)
  set Λ := M.abelian₂ T T
  set Ψ := M.F.av (fun t => (ψ t : ℂ))
  set E := M.P' (Ioc T (T + ρ))
  let Z : H →L[ℂ] H := Ψ ∘L (Λ ∘L X ∘L Λ) + ((Ψ ∘L E) ∘L (E ∘L X)) ∘L Λ
  have hZ : IsTraceClass Z := (htc.comp_left Ψ).add ((isTraceClass_comp h1 h2).comp_right Λ)
  have key : ∀ t, 0 ≤ t → Λ ∘L M.F.U (-t) ∘L (Ψ ∘L X) ∘L Λ = (Λ ∘L M.F.U (-t)) ∘L Z := fun t ht => by
    ext h
    have a1 : (Λ ∘L M.F.U (-t)) (Ψ (M.P (Ioi T) (X (Λ h)))) = 0 := k3 M hψ _ _ fun r _ hr => by
      rw [ContinuousLinearMap.comp_apply, ← M.F.add]; exact k1 M hT (by linarith) _
    have a2 : M.P' (Ioi (T + ρ)) (X (Λ h)) = 0 := by
      have := DFunLike.congr_fun ((carLaws M X κ hk hX).2.2 ρ T hρ) (Λ h)
      have l : M.P (Ioi T) (Λ h) = 0 := DFunLike.congr_fun l2 h
      simpa [l] using this
    have a3 : E (E (X (Λ h))) = E (X (Λ h)) := DFunLike.congr_fun h3 _
    show (Λ ∘L M.F.U (-t)) (Ψ (X (Λ h))) = (Λ ∘L M.F.U (-t)) (Ψ (Λ (X (Λ h))) + Ψ (E (E (X (Λ h)))))
    conv_lhs => rw [k5 M T (X (Λ h)), k4 M r0, ContinuousLinearMap.add_apply, a2, add_zero, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), a1, add_zero]
    rw [a3, map_add (f := _)]
  constructor
  · have := key 0 le_rfl
    have e : M.F.U (-0) = 1 := by ext h; simpa using M.F.zero h
    rw [e] at this
    exact this ▸ hZ.comp_left _
  · have t := trWeak atTop (fun a : ℝ => Λ ∘L M.F.U (-(2 * a))) 0 Z hZ (fun a =>
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
        rw [ContinuousLinearMap.comp_apply]
        exact (Λ.le_opNorm _).trans (by rw [M.F.norm]; gcongr)) (fun x y => by
      have sa := ((projLaws M).2.2.2.2.2.2.2 T T (by linarith)).2.2.2.1
      have := ((projLaws M).1 y (Λ x)).2.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos))
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
      exact this.congr fun a => sa.isSymmetric.apply_clm _ _)
    have z : trace ((0 : H →L[ℂ] H) ∘L Z) = 0 := by
      have := trace_smul 0 hZ
      simpa using this
    rw [z] at t
    refine t.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [key _ (by linarith)]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem half {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (g : L V) (q a : ℝ) (hq : 0 < q) (h : WLe 2 g q) :
    ∫⁻ y in Ioi a, ‖g y‖ₑ ≤ ENNReal.ofReal (99 / 140 * Real.exp (-a) * q) := by
  set l := 5 / 7 * Real.exp (-a) / q with hl
  have l0 : 0 < l := by positivity
  have i1 : IntegrableOn (fun y => Real.exp (-2 * y)) (Ioi a) := integrableOn_exp_mul_Ioi (by norm_num) a
  have i2 : IntegrableOn (fun y => l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) (Ioi a) :=
    (h.1.integrableOn.const_mul _).add (i1.const_mul _)
  have pt : ∀ y, ‖g y‖ ≤ l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y) := fun y => by
    have e1 : Real.exp (-2 * y) = (Real.exp (2 * y))⁻¹ := by rw [← Real.exp_neg]; ring_nf
    have e0 := Real.exp_pos (2 * y)
    rw [e1]
    set E := Real.exp (2 * y)
    rw [← sub_nonneg]
    have : l / 2 * (E * ‖g y‖ ^ 2) + (2 * l)⁻¹ * E⁻¹ - ‖g y‖ = (l * E * ‖g y‖ - 1) ^ 2 / (2 * l * E) := by
      field_simp; ring
    rw [this]; positivity
  calc _ ≤ ∫⁻ y in Ioi a, ENNReal.ofReal (l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        lintegral_mono fun y => by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (pt y)
    _ = ENNReal.ofReal (∫ y in Ioi a, l / 2 * (Real.exp (2 * y) * ‖g y‖ ^ 2) + (2 * l)⁻¹ * Real.exp (-2 * y)) :=
        (ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun y => (norm_nonneg _).trans (pt y))).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_add (h.1.integrableOn.const_mul _) (i1.const_mul _), integral_const_mul, integral_const_mul,
          integral_exp_mul_Ioi (by norm_num)]
        have h1 : ∫ y in Ioi a, Real.exp (2 * y) * ‖g y‖ ^ 2 ≤ q ^ 2 :=
          (setIntegral_le_integral h.1 (Eventually.of_forall fun y => by positivity)).trans h.2
        refine (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) le_rfl).trans_eq ?_
        have e1 : Real.exp (-2 * a) = Real.exp (-a) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have e0 := Real.exp_pos (-a)
        rw [e1, hl]
        field_simp; ring

theorem UpperTheory.V.Z.IntegralApplyAeEq.tailB :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (φ : ℝ → ℂ) (e : V) (p : L W) (Q α β : ℝ), Continuous φ → (∀ x, 1 / 2 < |x| → φ x = 0) → ∫ x, ‖φ x‖ ≤ 1 → 0 ≤ Q →
      WLe (-2) p Q → α ≤ β → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (2 * M.T₀) * Q * Real.exp (-α) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M φ e p Q α β φc φs φi hQ hp hαβ
  set g : L V := M.J.symm (M.J' p) with hg
  have hcut : ∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (2 * M.T₀ - a)) p‖ := fun a => by
    have h1 := cutLaws (V := W) (Iic (2 * M.T₀ - a)) (Ioi (2 * M.T₀ - a)) measurableSet_Iic measurableSet_Ioi
    have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
    rw [Iic_union_Ioi, h1.2.2.2.1] at h2
    have h3 : p = cut W (Iic (2 * M.T₀ - a)) p + cut W (Ioi (2 * M.T₀ - a)) p := DFunLike.congr_fun h2 p
    have h4 := DFunLike.congr_fun ((projLaws M).2.2.2.2.2.2.2 a (2 * M.T₀ - a) (by linarith)).1 (M.J' p)
    change M.J (cut V (Ioi a) (M.J.symm (M.J' (cut W (Ioi (2 * M.T₀ - a)) (M.J'.symm (M.J' p)))))) = 0 at h4
    rw [M.J'.symm_apply_apply, M.J.map_eq_zero_iff] at h4
    have h5 : cut V (Ioi a) g = cut V (Ioi a) (M.J.symm (M.J' (cut W (Iic (2 * M.T₀ - a)) p))) := by
      rw [hg]
      conv_lhs => rw [h3]
      rw [map_add (f := _), map_add (f := _), map_add (f := _), h4, add_zero]
    rw [h5]
    refine ((cutLaws (V := V) (Ioi a) (Ioi a) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.1 _).trans_eq ?_
    rw [M.J.symm.norm_map, M.J'.norm_map]
  have hw := wBound g p (2 * M.T₀) Q hcut hp
  have φcs : HasCompactSupport φ := HasCompactSupport.intro (isCompact_Icc (a := -(1 / 2)) (b := 1 / 2)) fun x hx =>
    φs x (by rw [mem_Icc, ← abs_le, not_le] at hx; exact hx)
  have φI : Integrable φ := φc.integrable_of_hasCompactSupport φcs
  have hsv := ((svSpec (V := V)).1 φ (φc.memLp_of_hasCompactSupport φcs) e).1
  have gm : Measurable fun y => ‖g y‖ₑ := (Lp.stronglyMeasurable g).enorm
  have hcor : ∀ s, ‖M.cor φ e p s‖ₑ ≤ ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ := fun s => by
    have e1 : M.J' p = M.J g := by rw [hg, M.J.apply_symm_apply]
    rw [Sc.cor, e1, M.hJ, M.J.inner_map_map, L2.inner_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hsv, sh_ae V s g] with x h1 h2
    rw [h1, h2, ← enorm_smul]
    exact enorm_inner_le _ _
  have main : ∀ q, Real.exp (2 * M.T₀) * Q < q → ‖∫ s in α..β, M.cor φ e p s‖ ≤ 6 / 5 * ‖e‖ * Real.exp (-α) * q := by
    intro q hq
    have q0 : 0 ≤ Real.exp (2 * M.T₀) * Q := by positivity
    have q1 : 0 < q := q0.trans_lt hq
    have hB := half g q (α - 1 / 2) q1 ⟨hw.1, hw.2.trans (pow_le_pow_left₀ q0 hq.le 2)⟩
    set B := 99 / 140 * Real.exp (-(α - 1 / 2)) * q with hBd
    have B0 : 0 ≤ B := by positivity
    have h1 : ‖∫ s in α..β, M.cor φ e p s‖ₑ ≤ ENNReal.ofReal (‖e‖ * B) := by
      rw [intervalIntegral.integral_of_le hαβ]
      calc _ ≤ ∫⁻ s in Ioc α β, ∫⁻ x, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono hcor)
        _ = ∫⁻ x, ∫⁻ s in Ioc α β, ‖φ x‖ₑ * ‖e‖ₑ * ‖g (x + s)‖ₑ :=
            lintegral_lintegral_swap (((φc.measurable.enorm.comp measurable_snd).mul_const _).mul
              (gm.comp (measurable_snd.add measurable_fst))).aemeasurable
        _ ≤ ∫⁻ x, ‖φ x‖ₑ * (‖e‖ₑ * ENNReal.ofReal B) := by
            refine lintegral_mono fun x => ?_
            by_cases hx : 1 / 2 < |x|
            · simp [φs x hx]
            have gx : Measurable fun s => ‖g (x + s)‖ₑ := gm.comp (measurable_const.add measurable_id)
            rw [lintegral_const_mul _ gx, mul_assoc]
            gcongr
            refine le_trans ?_ hB
            rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioi,
              ← lintegral_add_left_eq_self (fun y => (Ioi (α - 1 / 2)).indicator (fun y => ‖g y‖ₑ) y) x]
            refine lintegral_mono fun s => ?_
            by_cases hs : s ∈ Ioc α β
            · have h7 : x + s ∈ Ioi (α - 1 / 2) := by
                have h5 := (abs_le.1 (not_lt.1 hx)).1
                have h6 := hs.1
                rw [mem_Ioi]
                linarith
              rw [indicator_of_mem hs]
              exact (indicator_of_mem h7 fun y => ‖g y‖ₑ).ge
            · rw [indicator_of_notMem hs]
              exact bot_le
        _ = (∫⁻ x, ‖φ x‖ₑ) * (‖e‖ₑ * ENNReal.ofReal B) := lintegral_mul_const _ φc.measurable.enorm
        _ ≤ 1 * (‖e‖ₑ * ENNReal.ofReal B) := by
            gcongr
            rw [← ofReal_integral_norm_eq_lintegral_enorm φI]
            exact ENNReal.ofReal_le_one.2 φi
        _ = _ := by rw [one_mul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine h1.trans ?_
    have h2 : Real.exp (1 / 2) ≤ 169 / 100 := by
      refine (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).1 ?_
      rw [← Real.exp_nat_mul]
      norm_num
      linarith [Real.exp_one_lt_d9]
    have h3 : Real.exp (-(α - 1 / 2)) = Real.exp (-α) * Real.exp (1 / 2) := by rw [← Real.exp_add]; ring_nf
    rw [hBd, h3]
    have h4 : 0 ≤ ‖e‖ * Real.exp (-α) * q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  have := ge_of_tendsto (x := 𝓝[>] (Real.exp (2 * M.T₀) * Q))
    (((continuous_const (y := 6 / 5 * ‖e‖ * Real.exp (-α))).mul continuous_id).tendsto _ |>.mono_left nhdsWithin_le_nhds)
    (eventually_mem_nhdsWithin.mono fun q hq => main q hq)
  refine this.trans_eq ?_
  simp only [Pi.mul_apply, id]; ring
end
