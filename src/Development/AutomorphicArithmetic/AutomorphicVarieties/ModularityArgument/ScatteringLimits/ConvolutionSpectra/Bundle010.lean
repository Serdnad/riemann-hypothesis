module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.OntoJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corLim :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (φ : ℝ → ℂ) (e : V) (p : L W) (c : ℝ), Continuous φ → HasCompactSupport φ → Bdd p →
      Continuous (M.cor φ e p) ∧ Tendsto (fun a => ∫ s in (c - a)..(c + a), M.cor φ e p s) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, N (∫ x, p x)⟫_ℂ)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN φ e p c h1 h2 hp
  have hc : ∀ a b : H, Continuous fun s => ⟪a, M.F.U s b⟫_ℂ := fun a b => continuous_const.inner (M.F.cont b)
  refine ⟨hc _ _, ?_⟩
  have t1 := (cobLaws M.F).2.2.2.2.2.2.1 (projLaws M).1 _ (M.J (sv V φ e)) c (nAll M N hN p hp)
  have t2 := corOne φ e (N (∫ x, p x)) c h1 h2
  have t3 := t1.add t2
  rw [zero_add] at t3
  refine t3.congr fun a => ?_
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V (N (∫ x, p x)))⟫_ℂ = ⟪M.J (sv V φ e), M.F.U s (M.J (one V (N (∫ x, p x))))⟫_ℂ :=
    fun s => by rw [M.hJ, M.J.inner_map_map]
  simp only [e1]
  rw [← intervalIntegral.integral_add ((hc _ _).intervalIntegrable _ _) ((hc _ _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Sc.cor, map_sub, inner_sub_right, sub_add_cancel]
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nEx :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) → ∃ N : W →ₗ[ℂ] V, M.IsN N := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M hs
  obtain ⟨c0, cadd, csmul, -, csh, -, -, -⟩ := cobLaws M.F
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨o1, o2, l0, -, -, l1, l2, l3, l4⟩ := hL M.T₀ M.T₀ (by linarith)
  set T := M.T₀ with hT
  set Λ := M.abelian₂ T T with hΛ
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have carry : ∀ p : L V, Tail p → M.F.Cob (M.J p - M.J (one V (∫ x, p x))) := fun p hp => by
    have := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _
      ((cobTail p).2 hp).2
    rwa [map_sub] at this
  have ex : ∀ w, ∃ n, M.F.Cob (M.J' (one W w) - M.J (one V n)) := by
    intro w
    set h := M.F.U (T - 1) (M.J' (one W w)) with hh
    have s0 : M.P' (Ioc 0 1) (M.J' (one W w)) = M.J' (one W w) := by
      show M.J' (cut W _ (M.J'.symm (M.J' _))) = _
      rw [M.J'.symm_apply_apply, ((cutLaws (Ioc 0 1) univ measurableSet_Ioc .univ).2.2.2.2.2.2.2.1 _).2]
      exact ((svSpec (V := W)).2 w).1.mono fun x hx hn => by rw [hx, indicator_of_notMem hn]
    have s1 : M.P' (Ioc (T - 1) T) h = h := by
      have := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) .univ).2.2.2.2 (T - 1)).2 (M.J' (one W w))
      have y : (fun x : ℝ => x - (T - 1)) ⁻¹' Ioc 0 1 = Ioc (T - 1) T := by
        ext x; simp only [mem_preimage, mem_Ioc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [y] at this
      simp only [ContinuousLinearMap.comp_apply, s0] at this
      exact this.symm
    have s2 : M.P' (Ioi T) h = 0 := by
      have a : M.P' (Ioi T) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi T ∩ Ioc (T - 1) T) := (hP' _ _ (mI T) measurableSet_Ioc).1
      have b : Ioi T ∩ Ioc (T - 1) T = ∅ := eq_empty_of_forall_notMem fun x hx => absurd hx.1 (not_lt.2 hx.2.2)
      rw [b, show M.P' ∅ = 0 from (projLaws M.swap).2.2.2.2.2.1] at a
      rw [← s1]; exact DFunLike.congr_fun a h
    have s3 : M.P (Ioi (T + 1)) h = 0 := by
      have a : M.P' (Ioi (T - 1)) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi (T - 1) ∩ Ioc (T - 1) T) := (hP' _ _ (mI _) measurableSet_Ioc).1
      rw [inter_eq_right.2 Ioc_subset_Ioi_self] at a
      rw [← s1, ← a]
      exact DFunLike.congr_fun (hL (T + 1) (T - 1) (by linarith)).1 _
    obtain ⟨k, hk⟩ := hs (Λ h)
    set R := M.F.av wR with hR
    have hk' : k - Λ (R (Λ k)) = Λ h := hk
    have ΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
    have kΛ : Λ k = k := by
      have := congrArg Λ hk'
      rw [map_sub, ΛΛ, ΛΛ, ← hk'] at this
      exact sub_left_injective this
    rw [kΛ] at hk'
    have k1 : M.P (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l2 k
    have k2 : M.P' (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l4 k
    have r2 : M.P' (Ioi T) (R k) = 0 := by
      obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avSpec M.F).2.1).1 k
      rw [hR, e, ← (M.P' (Ioi T)).integral_comp_comm i]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ 0
      · have a := DFunLike.congr_fun ((hP _ _ (mI (T - r)) .univ).2.2.2.2 r).2 k
        have y : (fun x : ℝ => x - r) ⁻¹' Ioi (T - r) = Ioi T := by ext x; simp
        have b : M.P' (Ioi (T - r)) ∘L M.P' (Ioi T) = M.P' (Ioi (T - r) ∩ Ioi T) := (hP' _ _ (mI _) (mI _)).1
        rw [inter_eq_left.2 (Ioi_subset_Ioi (by linarith))] at b
        rw [y, ← b] at a
        simp only [ContinuousLinearMap.comp_apply, k2, map_zero] at a
        simp [← a]
      · simp [wR, hr]
    have dec : h = (k - R k) + M.P (Ioi T) (R k) + M.P (Ioi T) h := by
      have a : Λ h = h - M.P (Ioi T) h - M.P' (Ioi T) h := rfl
      have b : Λ (R k) = R k - M.P (Ioi T) (R k) - M.P' (Ioi T) (R k) := rfl
      rw [a, b, s2, r2, sub_zero, sub_zero] at hk'
      linear_combination (norm := module) -hk'
    have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
    set u := M.J.symm k with hu
    have u1 : cut V (Iic T) u = u := by
      have a := (cl (Iic T) (Ioi T) measurableSet_Iic (mI T)).2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, (cl _ _ .univ .univ).2.2.2.1] at a
      have b : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun a u
      have c : cut V (Ioi T) u = 0 := M.J.injective (by rw [map_zero]; exact k1)
      rw [c, add_zero] at b
      exact b.symm
    have e1 : M.P (Ioi T) (R k) = M.J (cut V (Ioi T) ((shF V).av wR u)) := by
      have := DFunLike.congr_fun (((avSpec (shF V)).2.2.2 _ (avSpec M.F).2.1).2.2.2.2 M.F
        (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm) u
      have a : M.J ((shF V).av wR u) = R (M.J u) := this
      rw [hu, M.J.apply_symm_apply] at a
      show M.J (cut V _ (M.J.symm (R k))) = _
      rw [← a, M.J.symm_apply_apply]
    set v := cut V (Ioi T) (M.J.symm h) with hv
    have e2 : M.P (Ioi T) h = M.J v := rfl
    have bv : Bdd v := by
      refine ⟨|T| + 1, ?_⟩
      have a := (cl (Ioc T (T + 1)) (Ioi (T + 1)) measurableSet_Ioc (mI _)).2.2.1 (Ioc_disjoint_Ioi le_rfl)
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at a
      have c : cut V (Ioi (T + 1)) (M.J.symm h) = 0 := M.J.injective (by rw [map_zero]; exact s3)
      have b : v = cut V (Ioc T (T + 1)) (M.J.symm h) := by rw [hv, a, ContinuousLinearMap.add_apply, c, add_zero]
      have d := (cl (Icc (-(|T| + 1)) (|T| + 1)) (Ioc T (T + 1)) measurableSet_Icc measurableSet_Ioc).1
      have sub : Ioc T (T + 1) ⊆ Icc (-(|T| + 1)) (|T| + 1) := fun x hx =>
        ⟨by linarith [hx.1, neg_abs_le T], by linarith [hx.2, le_abs_self T]⟩
      rw [inter_eq_right.2 sub] at d
      rw [b]
      exact DFunLike.congr_fun d _
    have f1 := carry _ (resTail u T u1)
    have f2 := carry _ ((cobTail v).1 bv)
    have f3 := (cadd _ _ (cadd _ _ (cadd _ _ (csh (T - 1) (M.J' (one W w))) (resCob M.F k).1).1 f1).1 f2).1
    refine ⟨(∫ x, cut V (Ioi T) ((shF V).av wR u) x) + ∫ x, v x, ?_⟩
    convert f3 using 1
    rw [← e1, ← e2, map_add (f := _), map_add (f := _), ← hh, ← hR]
    linear_combination (norm := module) dec
  choose n hn using ex
  let b := Module.finBasis ℂ W
  refine ⟨b.constr ℂ fun i => n (b i), fun w => ?_⟩
  have e : M.J' (one W w) - M.J (one V (b.constr ℂ (fun i => n (b i)) w)) =
      ∑ i, b.repr w i • (M.J' (one W (b i)) - M.J (one V (n (b i)))) := by
    conv_lhs => rw [← b.sum_repr w]

    simp only [map_sum, map_smul, Module.Basis.constr_basis, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.sum_induction _ _ (fun x y hx hy => (cadd x y hx hy).1) c0 fun i _ => csmul _ _ (hn _)
end

section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.model :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), ∃ M : Sc H V W, M.T₀ = D.T₀ ∧ (∀ u, M.J u = D.J u) ∧ (∀ v, M.J' v = D.J' v) ∧
      ∀ T Λ, D.T₀ ≤ T → (IsTrunc D.J D.J' T Λ ↔ Λ = M.abelian₂ T T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  let D' : Datum H W V :=
    { J := D.J', J' := D.J, T₀ := D.T₀, B := D.B, β := D.β', β' := D.β
      span := fun h a b => D.span h b a
      shift := fun t u u' v v' a b => by
        rw [← inner_conj_symm, ← D.shift t v v' u u' b a, inner_conj_symm]
      causal := fun s u v a b => by
        rw [← inner_conj_symm, D.causal (2 * D.T₀ - s) v u b (by simpa using a), map_zero]
      β_ker := D.β'_ker, β'_ker := D.β_ker, β_unit := D.β'_unit, β'_unit := D.β_unit, B_sa := D.B_sa
      B_J := D.B_J', B_J' := D.B_J
      compact := fun T Λ hT h => D.compact T Λ hT ⟨h.1, h.2.1, fun x => (h.2.2 x).trans
        ⟨fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩, fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩⟩⟩ }
  let J := LinearIsometryEquiv.ofSurjective D.J (ontoJ D)
  let J' := LinearIsometryEquiv.ofSurjective D.J' (ontoJ D')
  have hJ : ∀ u, J u = D.J u := fun _ => rfl
  have hJ' : ∀ u, J' u = D.J' u := fun _ => rfl
  let F : Flow H :=
    { U := fun t => (J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sh V t ∘L (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
      zero := fun h => by
        show J ((shF V).U 0 (J.symm h)) = h
        rw [(shF V).zero, J.apply_symm_apply]
      add := fun s t h => by
        show J ((shF V).U (s + t) (J.symm h)) = J ((shF V).U s (J.symm (J ((shF V).U t (J.symm h)))))
        rw [(shF V).add, J.symm_apply_apply]
      norm := fun t h => by
        show ‖J ((shF V).U t (J.symm h))‖ = _
        rw [J.norm_map, (shF V).norm, J.symm.norm_map]
      cont := fun h => J.continuous.comp ((shF V).cont _) }
  have hU : ∀ t u, F.U t (J u) = J (sh V t u) := fun t u => by
    show J (sh V t (J.symm (J u))) = _
    rw [J.symm_apply_apply]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (cutSpec (Ioi s) measurableSet_Ioi u).mono fun x h hx => by rw [h, indicator_of_notMem (by simpa using hx)]
  have caus : ∀ (s : ℝ) (u : L V) (v : L W), ⟪J (cut V (Ioi s) u), J' (cut W (Ioi (2 * D.T₀ - s)) v)⟫_ℂ = 0 :=
    fun s u v => D.causal s _ _ (sup s u) (sup _ v)
  refine ⟨⟨J, J', F, D.T₀, hU, fun t v => ?_, caus⟩, rfl, hJ, hJ', fun T Λ hT => ?_⟩
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := J.surjective h
    have e : J u = F.U t (J (sh V (-t) u)) := by rw [← hU, ← F.add, add_neg_cancel, F.zero]
    conv_lhs => rw [e]
    refine ((⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).trans ?_
    exact D.shift (-t) u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  · rw [truncEq D.J D.J' T Λ fun u v => D.causal T _ _ (sup T u) ((sup T v).mono fun x h hx => h (by linarith))]
    have a1 : ContinuousLinearMap.adjoint D.J.toContinuousLinearMap = (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J.inner_map_map _ _).symm.trans (by
        show ⟪J (J.symm x), J y⟫_ℂ = _
        rw [J.apply_symm_apply]; rfl)).symm
    have a2 : ContinuousLinearMap.adjoint D.J'.toContinuousLinearMap = (J'.symm.toContinuousLinearEquiv : H →L[ℂ] L W) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J'.inner_map_map _ _).symm.trans (by
        show ⟪J' (J'.symm x), J' y⟫_ℂ = _
        rw [J'.apply_symm_apply]; rfl)).symm
    rw [a1, a2]
    rfl
end
