module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction
public import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.GKModules.ZKFinite
import Mathlib.Algebra.Module.StablyFree.Basic
public import GroundTheory.AutomorphicForms.GKModules.Garding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
variable {U : Type*} [Ring U] [Algebra ℝ U]

private def UpperTheory.ConvolutionTheory.Tf.Crv (A : ℝ → U) (D : U) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ → ℝ) (c' : ι → ℝ) (v : ι → U),
    (∀ i, HasDerivAt (c i) (c' i) 0) ∧ (∀ t, A t = ∑ i, c i t • v i) ∧ D = ∑ i, c' i • v i

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.const (u : U) : UpperTheory.ConvolutionTheory.Tf.Crv (fun _ => u) (0 : U) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ => 0, fun _ => u, fun _ => hasDerivAt_const _ _,
    by simp, by simp⟩

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.add {A B : ℝ → U} {D E : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (hB : UpperTheory.ConvolutionTheory.Tf.Crv B E) : UpperTheory.ConvolutionTheory.Tf.Crv (fun t => A t + B t) (D + E) := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  obtain ⟨κ, _, d, d', w, hd, hB', rfl⟩ := hB
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim c d, Sum.elim c' d', Sum.elim v w, ?_, fun t => ?_, ?_⟩
  · rintro (i | j)
    · exact hc i
    · exact hd j
  · simp [Fintype.sum_sum_type, hA', hB']
  · simp [Fintype.sum_sum_type]

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.mul {A B : ℝ → U} {D E : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (hB : UpperTheory.ConvolutionTheory.Tf.Crv B E) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t => A t * B t) (D * B 0 + A 0 * E) := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  obtain ⟨κ, _, d, d', w, hd, hB', rfl⟩ := hB
  refine ⟨ι × κ, inferInstance, fun p t => c p.1 t * d p.2 t,
    fun p => c' p.1 * d p.2 0 + c p.1 0 * d' p.2, fun p => v p.1 * w p.2,
    fun p => (hc p.1).mul (hd p.2), fun t => ?_, ?_⟩
  · beta_reduce
    rw [hA', hB', Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [smul_mul_smul_comm]
  · rw [hA' 0, hB' 0, Finset.sum_mul_sum, Finset.sum_mul_sum, Fintype.sum_prod_type,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [add_smul, smul_mul_smul_comm, smul_mul_smul_comm]

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.lin {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [FiniteDimensional ℝ M] (L : M →ₗ[ℝ] U) {φ : ℝ → M} {φ' : M} (hφ : HasDerivAt φ φ' 0) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t => L (φ t)) (L φ') := by
  let b := Module.finBasis ℝ M
  have hsum : ∀ m : M, L m = ∑ i, b.coord i m • L (b i) := fun m => by
    calc L m = L (∑ i, b.repr m i • b i) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, Module.Basis.coord_apply]
  refine ⟨_, inferInstance, fun i t => b.coord i (φ t), fun i => b.coord i φ', fun i => L (b i),
    fun i => ?_, fun t => ?_, ?_⟩
  · exact (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt 0 hφ
  · exact hsum _
  · exact hsum _

private theorem UpperTheory.ConvolutionTheory.Tf.Crv.deriv {A : ℝ → U} {D : U} (hA : UpperTheory.ConvolutionTheory.Tf.Crv A D)
    (l : U →ₗ[ℝ] ℝ) : HasDerivAt (fun t => l (A t)) (l D) 0 := by
  obtain ⟨ι, _, c, c', v, hc, hA', rfl⟩ := hA
  have e : (fun t => l (A t)) = fun t => ∑ i, c i t * l (v i) := by
    funext t

    simp [hA', map_sum]
  rw [e]

  simp only [map_sum, map_smul, smul_eq_mul]
  exact HasDerivAt.fun_sum fun i _ => (hc i).mul_const _

end

section
attribute [local instance 100] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private noncomputable def UpperTheory.ConvolutionTheory.Tf.iotaL :
    𝔤 →ₗ[ℝ] UniversalEnvelopingAlgebra ℝ h.lieSubalgebra where
  toFun Y := UniversalEnvelopingAlgebra.ι ℝ (h.toLie Y)
  map_add' X Y := by
    show UniversalEnvelopingAlgebra.ι ℝ (h.toLie X + h.toLie Y) = _
    exact map_add _ _ _
  map_smul' r X := by
    show UniversalEnvelopingAlgebra.ι ℝ (r • h.toLie X) = _
    exact map_smul _ _ _

private theorem UpperTheory.ConvolutionTheory.Tf.crv_AdU (X : 𝔤) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    UpperTheory.ConvolutionTheory.Tf.Crv (fun t : ℝ => h.AdU (h.expG (t • X)) u)
      (UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * u -
        u * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X)) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, Algebra.commutes, sub_self]
    exact UpperTheory.ConvolutionTheory.Tf.Crv.const _
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    rw [e]
    simp only [IsExpLieAlgebra.AdU_ι]
    have key := UpperTheory.ConvolutionTheory.Tf.Crv.lin (UpperTheory.ConvolutionTheory.Tf.iotaL h) (h.hasDerivAt_Ad_expG X (h.ofLie x))
    have e2 : UpperTheory.ConvolutionTheory.Tf.iotaL h (h.bracket X (h.ofLie x)) =
        UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * UniversalEnvelopingAlgebra.ι ℝ x -
          UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) := by
      show UniversalEnvelopingAlgebra.ι ℝ ⁅h.toLie X, x⁆ = _
      rw [LieHom.map_lie, Ring.lie_def]
    rw [e2] at key
    exact key
  | mul a b ha hb =>
    have key := ha.mul hb
    simp only [map_mul]
    have e0 : ∀ w, h.AdU (h.expG ((0 : ℝ) • X)) w = w := by
      intro w
      rw [zero_smul, h.expG_zero, h.AdU_one, AlgHom.id_apply]
    simp only [e0] at key
    convert key using 1
    noncomm_ring
  | add a b ha hb =>
    have key := ha.add hb
    simp only [map_add (f := _)]
    convert key using 1
    noncomm_ring

private theorem UpperTheory.ConvolutionTheory.Tf.AdU_expG {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) (X : 𝔤) : h.AdU (h.expG X) z = z := by
  have hc : UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) * z -
      z * UniversalEnvelopingAlgebra.ι ℝ (h.toLie X) = 0 :=
    sub_eq_zero.2 (Subalgebra.mem_center_iff.1 hz _)
  have hcrv := UpperTheory.ConvolutionTheory.Tf.crv_AdU h X z
  rw [hc] at hcrv
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℝ _).1 fun l => ?_
  set c : ℝ → ℝ := fun t => l (h.AdU (h.expG (t • X)) z) with hcdef
  have hderiv : ∀ t, HasDerivAt c 0 t := by
    intro t
    have h1 := hcrv.deriv (l ∘ₗ (h.AdU (h.expG (t • X))).toLinearMap)
    simp only [map_zero] at h1
    have h2 : HasDerivAt (fun s : ℝ => l ((h.AdU (h.expG (t • X))).toLinearMap
        (h.AdU (h.expG ((s - t) • X)) z))) 0 t := by
      have h1' : HasDerivAt (fun s : ℝ => l ((h.AdU (h.expG (t • X))).toLinearMap
          (h.AdU (h.expG (s • X)) z))) 0 (t - t) := by
        rw [sub_self]; exact h1
      exact h1'.comp_sub_const t t
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show l (h.AdU (h.expG (s • X)) z) = l (h.AdU (h.expG (t • X)) (h.AdU (h.expG ((s - t) • X)) z))
    rw [← AlgHom.comp_apply, ← h.AdU_mul, ← h.expG_add_smul, add_sub_cancel]
  have hconst : c 1 = c 0 :=
    is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) 1 0
  simp only [hcdef, one_smul, zero_smul, h.expG_zero, h.AdU_one, AlgHom.id_apply] at hconst
  rw [map_sub, hconst, sub_self]

private theorem UpperTheory.ConvolutionTheory.Tf.AdU_closure {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra}
    (hz : z ∈ h.centerU) {k : G} (hk : k ∈ Subgroup.closure (Set.range h.expG)) :
    h.AdU k z = z := by
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    exact UpperTheory.ConvolutionTheory.Tf.AdU_expG h hz X
  | one => rw [h.AdU_one, AlgHom.id_apply]
  | mul x y _ _ hx hy => rw [h.AdU_mul, AlgHom.comp_apply, hy, hx]
  | inv x _ hx =>
    have := h.AdU_inv_apply x z
    rwa [hx] at this

end

theorem UpperTheory.ConvolutionTheory.Tf.centerTr :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (z : UEnv K n), z ∈ (isExpLieAlgebra K n).centerU → ∀ k ∈ Subgroup.closure (Set.range (isExpLieAlgebra K n).expG),
      ∀ (f : archGroup K n → ℂ) (hf : f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), ∃ hk : (fun g => f (g * k)) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ g,
        ((isExpLieAlgebra K n).rightUAction z ⟨_, hk⟩ : archGroup K n → ℂ) g = ((isExpLieAlgebra K n).rightUAction z ⟨f, hf⟩ : archGroup K n → ℂ) (g * k) := by
  intro K _ _ n z hz k hk f hf
  refine ⟨(isExpLieAlgebra K n).isSmoothFun_rightTranslate hf k, fun g => ?_⟩
  have hinv : (isExpLieAlgebra K n).AdU k⁻¹ z = z :=
    UpperTheory.ConvolutionTheory.Tf.AdU_closure _ hz (Subgroup.inv_mem _ hk)
  have e := LinearMap.congr_fun
    ((isExpLieAlgebra K n).rightUAction_comp_rightTranslate (F := ℂ) k z) ⟨f, hf⟩
  rw [hinv] at e
  exact congrFun (congrArg Subtype.val e) g
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped Manifold ContDiff Topology

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_inv {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun fun g => f g⁻¹ := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf (contMDiff_id.inv)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_cont {f : G → ℂ} (hf : h.IsSmoothFun f) : Continuous f := by
  letI := h.chartedSpace
  exact ContMDiff.continuous hf

private theorem UpperTheory.ConvolutionTheory.Tf.deriv_zero {f : G → ℂ} {U : Set G} (hU : IsOpen U) (h0 : ∀ g ∈ U, f g = 0)
    (X : 𝔤) : ∀ g ∈ U, h.rightDeriv X f g = 0 := by
  intro g hg
  have hc : Continuous fun Y : 𝔤 => g * h.expG Y := by
    letI := h.chartedSpace
    exact continuous_const.mul h.contMDiff_expG.continuous
  have he : (fun Y : 𝔤 => f (g * h.expG Y)) =ᶠ[𝓝 0] fun _ => 0 := by
    have : (fun Y : 𝔤 => g * h.expG Y) ⁻¹' U ∈ 𝓝 (0 : 𝔤) :=
      (hU.preimage hc).mem_nhds (by simpa using hg)
    filter_upwards [this] with Y hY using h0 _ hY
  simp [IsExpLieAlgebra.rightDeriv, he.fderiv_eq]

private theorem UpperTheory.ConvolutionTheory.Tf.act_zero {U : Set G} (hU : IsOpen U)
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    ∀ f : h.smoothFuns (F := ℂ), (∀ g ∈ U, (f : G → ℂ) g = 0) →
      ∀ g ∈ U, (h.rightUAction u f : G → ℂ) g = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro f hf g hg
    simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rw [Submodule.coe_smul_of_tower, Pi.smul_apply, hf g hg, smul_zero]
  | ι x =>
    intro f hf g hg
    show (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f : G → ℂ) g = 0
    rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
    exact UpperTheory.ConvolutionTheory.Tf.deriv_zero h hU hf _ g hg
  | mul a b iha ihb =>
    intro f hf
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact iha _ (ihb f hf)
  | add a b iha ihb =>
    intro f hf g hg
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, iha f hf g hg,
      ihb f hf g hg, add_zero]

end

theorem UpperTheory.ConvolutionTheory.Tf.invSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (f : archGroup K n → ℂ), f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) →
      (fun g => f g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ) ∧ Continuous f ∧ (HasCompactSupport f → (isExpLieAlgebra K n).IsTestFunction f) ∧
      ∀ (hf : f ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (u : UEnv K n), tsupport ((isExpLieAlgebra K n).rightUAction u ⟨f, hf⟩ : archGroup K n → ℂ) ⊆ tsupport f := by
  intro K _ _ n f hf
  refine ⟨UpperTheory.ConvolutionTheory.Tf.smooth_inv _ hf, UpperTheory.ConvolutionTheory.Tf.smooth_cont _ hf, fun hc => ⟨hf, hc⟩, fun hf u => ?_⟩
  refine closure_minimal (fun g hg => ?_) (isClosed_tsupport f)
  by_contra hn
  exact hg (UpperTheory.ConvolutionTheory.Tf.act_zero _ (isClosed_tsupport f).isOpen_compl u ⟨f, hf⟩
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) g hn)
end
