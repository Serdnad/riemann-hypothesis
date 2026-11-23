module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle008
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.DiagOnly
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointTrace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {m : ℕ}

private def compR (D : InfD σ m) (i : Fin (m + 1)) :
    mixedEmbedding.mixedSpace E →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp
      (D.e.toRingHom.comp (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom))

private theorem continuous_compR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (compR D i) := by
  have he : ⇑(GroundTheory.Global.homeomorphMixedSpace E).symm =
      ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace E).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply,
      Homeomorph.apply_symm_apply]
  have h1 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
    rw [← he]; exact (GroundTheory.Global.homeomorphMixedSpace E).symm.continuous
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = ⇑(GroundTheory.Global.homeomorphMixedSpace F) := by
      funext x; rw [GroundTheory.Global.homeomorphMixedSpace_apply]
    rw [this]; exact (GroundTheory.Global.homeomorphMixedSpace F).continuous
  exact h2.comp ((continuous_apply i).comp (D.cont.comp h1))

private def compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  RingHom.mapMatrix (m := Fin n) (compR D i)

private theorem continuous_compM (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (compM D n i) := by
  change Continuous fun M : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E) => M.map (compR D i)
  exact continuous_id.matrix_map (continuous_compR D i)

private theorem coe_compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      compM D n i (((g : (ArchMatrix E n)ˣ) : ArchMatrix E n)) := by
  rfl

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) (Y' : archLie F n)
    (h : compM D n i (Y : ArchMatrix E n) = Y') :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG Y' := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_compA, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG, ← h]
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (compM D n i) (continuous_compM D n i) _
    ((NormedSpace.expSeries_radius_eq_top ℝ (ArchMatrix E n)).symm ▸ edist_lt_top _ _)

private theorem compR_along (D : InfD σ m) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k) (z : ℂ)
    (i : Fin (m + 1)) :
    compR D i (along τ z) = if i = k then along (τ.comp (algebraMap F E)) z else 0 := by
  have e : D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) =
      Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)) := by
    rw [h z, RingEquiv.apply_symm_apply]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    (D.e ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z)) i) = _
  rw [e]
  by_cases hik : i = k
  · subst hik
    rw [Pi.single_eq_same, RingEquiv.apply_symm_apply, if_pos rfl]
  · rw [Pi.single_eq_of_ne hik, map_zero, if_neg hik]

private def xL {K : Type} [Field K] [NumberField K] (n : ℕ) (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) : archLie K n :=
  ⟨(Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)), Submodule.mem_top⟩

private theorem compM_xL (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (i : Fin (m + 1)) :
    compM D n i (xL n τ p q z : ArchMatrix E n) =
      if i = k then (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n) else 0 := by
  change (Matrix.single p q (along τ z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace E)).map (compR D i) = _
  by_cases hik : i = k
  · rw [if_pos hik]
    ext1 a b
    change _ = (Matrix.single p q (along (τ.comp (algebraMap F E)) z) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs
    · rw [compR_along D h, if_pos hik]
    · simp
  · rw [if_neg hik]
    ext1 a b
    change _ = (0 : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace F)) a b
    simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
    split_ifs
    · rw [compR_along D h, if_neg hik]
    · simp

private theorem compA_exp_self (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k : Fin (m + 1)} (h : InSlot D τ k)
    (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n k ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) =
      (isExpLieAlgebra F n).expG (t • xL n (τ.comp (algebraMap F E)) p q z) := by
  apply compA_expG
  change compM D n k (t • (xL n τ p q z : ArchMatrix E n)) = t • (xL n (τ.comp (algebraMap F E)) p q z : ArchMatrix F n)
  rw [map_real_smul (compM D n k) (continuous_compM D n k), compM_xL D n h, if_pos rfl]

private theorem compA_exp_ne (D : InfD σ m) (n : ℕ) {τ : E →+* ℂ} {k i : Fin (m + 1)} (h : InSlot D τ k)
    (hi : i ≠ k) (p q : Fin n) (z : ℂ) (t : ℝ) :
    compA D n i ((isExpLieAlgebra E n).expG (t • xL n τ p q z)) = 1 := by
  rw [compA_expG D n i _ 0, IsExpLieAlgebra.expG_zero]
  change compM D n i (t • (xL n τ p q z : ArchMatrix E n)) = 0
  rw [map_real_smul (compM D n i) (continuous_compM D n i), compM_xL D n h, if_neg hi, smul_zero]

private theorem lact_elem {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β)
    (τ : K →+* ℂ) (p q : Fin n) (z : ℂ) (x : archGroup K n) :
    HasDerivAt (fun t : ℝ => β (x * (isExpLieAlgebra K n).expG (t • xL n τ p q z))⁻¹)
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β x⁻¹) 0 := by
  obtain ⟨h, -, -, -, -, -, -, e⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  rw [e, inv_inv, elem, IsExpLieAlgebra.rightUAction_ι]
  exact (isExpLieAlgebra K n).hasDerivAt_rightDeriv
    (f := fun g => β g⁻¹) h (xL n τ p q z) x

private theorem leftAction_tensor_generator (D : InfD σ m) [_root_.NumberField.IsTotallyComplex F] (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)) (hk : InSlot D τ k)
    (φ : Fin (m + 1) → TI F n) (β : TI E n) (hφ : ∀ i, SmoothT (φ i)) (hβ : IsTens D φ β) (p q : Fin n) (z : ℂ) :
    IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k)))
      (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β) := by
  have hsm : SmoothT β := (UpperTheory.ConvolutionTheory.L1.tensSmooth F E σ m D n φ β hβ).1 hφ
  intro g
  set x := g⁻¹ with hx
  have hg : g = x⁻¹ := by rw [hx, inv_inv]
  set τ' := τ.comp (algebraMap F E)
  set C : ℂ := ∏ i ∈ Finset.univ.erase k, φ i (compA D n i g) with hC
  have h1 := lact_elem β hsm τ p q z x
  have h2 := lact_elem (φ k) (hφ k) τ' p q z (compA D n k x)
  have e : (fun t : ℝ => β (x * (isExpLieAlgebra E n).expG (t • xL n τ p q z))⁻¹) =
      fun t : ℝ => φ k (compA D n k x * (isExpLieAlgebra F n).expG (t • xL n τ' p q z))⁻¹ * C := by
    funext t
    rw [hβ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), map_inv (compA D n k), map_mul (compA D n k),
      compA_exp_self D n hk]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [map_inv (compA D n i), map_mul (compA D n i), compA_exp_ne D n hk (Finset.ne_of_mem_erase hi), mul_one, hx,
      map_inv (compA D n i), inv_inv]
  rw [e] at h1
  have h3 := h1.unique (h2.mul_const C)
  have hxk : (compA D n k x)⁻¹ = compA D n k g := by rw [hx, map_inv (compA D n k), inv_inv]
  rw [hxk, ← hg] at h3
  rw [h3, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  congr 1
  rw [hC]
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.lactGen :
    UpperTheory.ConvolutionTheory.L1.LactGen := by
  intro F E _ _ _ _ _ _ σ m D n τ k hk φ β hφ hβ p q z
  exact UpperTheory.ConvolutionTheory.L1.leftAction_tensor_generator D n τ k hk φ β hφ hβ p q z
end
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

private theorem cv_eq_conv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β : TI K n) (g : archGroup K n) : cv ν α β g = conv ν α β g := by
  rw [conv_apply]
  rfl

private theorem leftFin_cv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β γ : TI K n) (hγ : ∀ g, γ g = cv ν α β g) (hα : LeftFin α) : LeftFin γ := by
  unfold LeftFin at hα ⊢
  set W := Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => α ((k : archGroup K n) * g))
    with hW
  have hW' : ∀ f ∈ W, Continuous f ∧ HasCompactSupport f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(map_continuous α).comp (continuous_const.mul continuous_id),
        α.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft (k : archGroup K n))⟩
    | zero => exact ⟨continuous_zero, HasCompactSupport.zero⟩
    | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, hx.2.add hy.2⟩
    | smul c x _ hx => exact ⟨hx.1.const_smul c, hx.2.smul_left⟩
  have hint : ∀ f ∈ W, ∀ g : archGroup K n, Integrable (fun y => f y * β (y⁻¹ * g)) ν := by
    intro f hf g
    obtain ⟨h1, h2⟩ := hW' f hf
    exact (h1.mul ((map_continuous β).comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      h2.mul_right
  let T : W →ₗ[ℂ] (archGroup K n → ℂ) :=
    { toFun := fun f g => ∫ y, (f : archGroup K n → ℂ) y * β (y⁻¹ * g) ∂ν
      map_add' := by
        intro f f'
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint f f.2 g) (hint f' f'.2 g)
      map_smul' := by
        intro c f
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hle : Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => γ ((k : archGroup K n) * g)) ≤
      LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨fun g => α ((k : archGroup K n) * g), Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    funext g
    change ∫ y, α ((k : archGroup K n) * y) * β (y⁻¹ * g) ∂ν = γ ((k : archGroup K n) * g)
    rw [hγ, cv, ← integral_mul_left_eq_self (μ := ν)
      (fun y => α y * β (y⁻¹ * ((k : archGroup K n) * g))) (k : archGroup K n)]
    congr 1
    funext y
    simp [mul_assoc]
  exact Submodule.finiteDimensional_of_le hle

theorem UpperTheory.ConvolutionTheory.L1.lactCv :
    UpperTheory.ConvolutionTheory.L1.LactCv := by
  intro K _ _ _ n ν _ α β γ hα hγ
  have e : γ = conv ν α β := by
    ext g
    rw [hγ, cv_eq_conv]
  obtain ⟨hs, hu, hz⟩ := UpperTheory.ConvolutionTheory.Tf.lactConv K n ν α β hα
  refine ⟨e ▸ hs, leftFin_cv ν α β γ hγ, fun u g => ?_, fun hβ z hz' g => ?_⟩
  · rw [e, hu, ← cv_eq_conv]
  · rw [e, hu, hz inferInstance hβ z hz', ← cv_eq_conv]
end

section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem trace_starProjection {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [FiniteDimensional ℂ K] :
    trace K.starProjection = (Module.finrank ℂ K : ℂ) := by
  classical
  let e := stdOrthonormalBasis ℂ K
  have hP : ∀ x : H, K.starProjection x = ∑ j, ⟪(e j : H), x⟫_ℂ • (e j : H) := by
    intro x
    have h := congrArg (fun v : K => (v : H)) (e.sum_repr' ⟨K.starProjection x, K.starProjection_apply_mem x⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (e j).2]
  have h1 : ∀ j, ⟪(e j : H), (e j : H)⟫_ℂ = 1 := by
    intro j
    rw [← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, e.orthonormal.1 j]
    simp
  have hs := hasSum_sum (s := Finset.univ)
    (fun j _ => (stdHilbertBasis ℂ H).hasSum_inner_mul_inner (e j : H) (e j : H))
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  rw [← hs.tsum_eq, trace]
  refine tsum_congr fun i => ?_
  rw [hP, inner_sum]
  simp only [inner_smul_right]

private theorem trOn_one {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] :
    trOn W 1 = (Module.finrank ℂ W : ℂ) := by
  have hc : W.topologicalClosure = W := W.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ W.topologicalClosure := by rw [hc]; infer_instance
  have hp : prj W ∘L (1 : H →L[ℂ] H) ∘L prj W = W.topologicalClosure.starProjection := by
    ext x
    simp only [prj, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ x)
  rw [trOn, hp, trace_starProjection, hc]

theorem UpperTheory.ConvolutionTheory.L1.twTrace :
    UpperTheory.ConvolutionTheory.L1.TwTrace := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U hS y hy hfin
  obtain ⟨hle, hdiag⟩ := UpperTheory.ConvolutionTheory.L1.diagOnly Γ G H π V m ι E A U hS y hy hfin
  haveI hfin' : FiniteDimensional ℂ (UpperTheory.ConvolutionTheory.L1.jointEig V E A y) := Submodule.finiteDimensional_of_le hle
  obtain ⟨c, hc, htr⟩ := UpperTheory.ConvolutionTheory.L1.jointTrace Γ G H π V m ι E A U hS y hfin'
  refine ⟨c, hc, ?_, fun i₀ S h1 h2 => (hdiag i₀ S h1).trans (htr i₀ S h1 h2)⟩
  have h := (hdiag 0 1 fun _ _ _ => rfl).trans (htr 0 1 (fun _ _ _ => rfl) fun _ _ _ _ => rfl)
  rw [trOn_one] at h
  exact h
end
