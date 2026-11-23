module

import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

@[expose] public section

section

noncomputable section

open Filter Topology MeasureTheory

namespace PositivityTheory.RL.Delta

open Complex
open scoped Real ContDiff

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x :=
  GlobalTheory.CompanionTheory.DiracComb.hadamard_lemma

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} :=
  fun _ => SchwartzMap.dense_hasCompactSupport

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t :=
  GlobalTheory.CompanionTheory.DiracComb.exists_quot

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x :=
  GlobalTheory.CompanionTheory.DiracComb.exists_div n f hf h0

theorem zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring

    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]

theorem eq_delta (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this

theorem eq_delta' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]

end PositivityTheory.RL.Delta

end
end

section

noncomputable section

open Complex Matrix Filter Topology
open scoped Real RealInnerProductSpace

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

theorem lie_of_exp_banach {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸]
    [StarModule ℝ 𝔸] (Z K : 𝔸) (h : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) * K * NormedSpace.exp (t • Z) = K) :
    star Z * K + K * Z = 0 := by
  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  have hP := (hE.star.mul (hasDerivAt_const (0 : ℝ) K)).mul hE
  have hf : ((fun u : ℝ => star (NormedSpace.exp (u • Z))) * (fun _ : ℝ => K)) *
      (fun u : ℝ => NormedSpace.exp (u • Z)) = fun _ => K := by
    funext u
    simp only [Pi.mul_apply]
    exact h u
  rw [hf] at hP
  have e := hP.unique (hasDerivAt_const (0 : ℝ) K)
  simpa [NormedSpace.exp_zero] using e

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem lie_of_exp {𝕜 ι : Type} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (Z K : Matrix ι ι 𝕜)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * K * NormedSpace.exp (t • Z) = K) : Zᴴ * K + K * Z = 0 := by
  exact @lie_of_exp_banach (Matrix ι ι 𝕜) _ _ _ _ ⟨continuous_id.matrix_conjTranspose⟩ _ Z K h

variable {l : Type} [Fintype l] [DecidableEq l]

theorem sympl_eq (w w' : l ⊕ l → ℝ) : sympl w w' = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ w') := by
  simp [sympl, pPart, qPart, dotProduct, Fintype.sum_sum_type, Matrix.J, Matrix.fromBlocks_mulVec,
    PiLp.inner_apply, Finset.sum_sub_distrib, Matrix.neg_mulVec, Matrix.one_mulVec, Finset.sum_neg_distrib]
  simp only [mul_comm]
  ring

theorem mem_sp_of (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ w w', sympl (A *ᵥ w) (A *ᵥ w') = sympl w w') :
    A ∈ Matrix.symplecticGroup l ℝ := by
  have key : ∀ v u : l ⊕ l → ℝ, (A *ᵥ v) ⬝ᵥ Matrix.J l ℝ *ᵥ (A *ᵥ u) = v ⬝ᵥ (Aᵀ * Matrix.J l ℝ * A) *ᵥ u := by
    intro v u
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [SymplecticGroup.mem_iff']
  ext i j
  have e := h (Pi.single i 1) (Pi.single j 1)
  rw [sympl_eq, sympl_eq, neg_inj, key] at e
  simpa [Matrix.mulVec_single_one, Pi.single_apply, dotProduct, Matrix.mulVec] using e

theorem mem_lie_of (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) :
    X ∈ LieAlgebra.Symplectic.sp l ℝ := by
  have := lie_of_exp X (Matrix.J l ℝ) fun t => by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact SymplecticGroup.mem_iff'.1 (h t)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  refine (mem_skewAdjointMatricesLieSubalgebra _ _).2 ((mem_skewAdjointMatricesSubmodule _ _).2 ?_)
  show Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X
  rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero, this]

variable {W β : Type} [Fintype W] [DecidableEq W] [Fintype β] [DecidableEq β]

def SG (K : W → Matrix β β ℂ) : Subgroup (W → Matrix β β ℂ)ˣ where
  carrier := {g | star g.1 * K * g.1 = K}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : star a.1 * K * a.1 = K := ha
    have hb' : star b.1 * K * b.1 = K := hb
    show star (a.1 * b.1) * K * (a.1 * b.1) = K
    calc _ = star b.1 * (star a.1 * K * a.1) * b.1 := by simp only [star_mul, mul_assoc]
      _ = K := by rw [ha', hb']
  inv_mem' := fun {a} ha => by
    have ha' : star a.1 * K * a.1 = K := ha
    show star a⁻¹.1 * K * a⁻¹.1 = K
    calc _ = star a⁻¹.1 * (star a.1 * K * a.1) * a⁻¹.1 := by rw [ha']
      _ = star (a.1 * a⁻¹.1) * K * (a.1 * a⁻¹.1) := by simp only [star_mul, mul_assoc]
      _ = K := by simp

def LG (K : W → Matrix β β ℂ) : Submodule ℝ (W → Matrix β β ℂ) where
  carrier := {Z | star Z * K + K * Z = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have ha' : star a * K + K * a = 0 := ha
    have hb' : star b * K + K * b = 0 := hb
    show star (a + b) * K + K * (a + b) = 0
    rw [star_add, add_mul, mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' := fun r a ha => by
    have ha' : star a * K + K * a = 0 := ha
    show star (r • a) * K + K * (r • a) = 0
    rw [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, ha', smul_zero]

end PositivityTheory.RL.Up

end
end

section

noncomputable section

open MvPolynomial FockH1Action

namespace PositivityTheory.KReal

section Abstract

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Ring E] [Algebra ℂ E]

def quadT (R L : ι → E) (A : Matrix ι ι ℂ) : E := ∑ i, ∑ j, A i j • (R i * L j)

def quartT (R L : ι → E) (A B : Matrix ι ι ℂ) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))

theorem quartT_comm (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a) (A B : Matrix ι ι ℂ) :
    quartT R L A B = quartT R L B A := by
  unfold quartT
  calc ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) • (R i * R k * (L j * L l))
      = ∑ x : ι × ι, ∑ y : ι × ι,
          (A x.1 x.2 * B y.1 y.2) • (R x.1 * R y.1 * (L x.2 * L y.2)) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ y : ι × ι, ∑ x : ι × ι,
          (B y.1 y.2 * A x.1 x.2) • (R y.1 * R x.1 * (L y.2 * L x.2)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        rw [mul_comm (A x.1 x.2), hR x.1, hL x.2]
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem quadT_mul (R L : ι → E)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ) :
    quadT R L A * quadT R L B = quartT R L A B + quadT R L (A * B) := by
  have key : ∀ i j k l, (A i j • (R i * L j)) * (B k l • (R k * L l)) =
      (A i j * B k l) • (R i * R k * (L j * L l)) +
        if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    intro i j k l
    have h1 : R i * L j * (R k * L l) = R i * (L j * R k) * L l := by simp only [mul_assoc]
    rw [smul_mul_smul_comm, h1, hLR]
    split_ifs with h
    · simp only [mul_add, add_mul, mul_one, smul_add, mul_assoc]
    · simp only [add_zero, mul_assoc]
  have h2 : quadT R L (A * B) =
      ∑ i, ∑ j, ∑ k, ∑ l, if j = k then (A i j * B k l) • (R i * L l) else 0 := by
    unfold quadT
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp
  rw [h2]
  unfold quadT quartT
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => key i j k l

theorem quadT_commute (R L : ι → E) (hR : ∀ a b, R a * R b = R b * R a)
    (hL : ∀ a b, L a * L b = L b * L a)
    (hLR : ∀ a b, L a * R b = R b * L a + if a = b then 1 else 0) (A B : Matrix ι ι ℂ)
    (h : A * B = B * A) : quadT R L A * quadT R L B = quadT R L B * quadT R L A := by
  rw [quadT_mul R L hLR, quadT_mul R L hLR, h, quartT_comm R L hR hL]

end Abstract

section Fock

variable {σ : Type*} [DecidableEq σ]

theorem pd_pd (a b : σ) :
    ((pderiv a).toLinearMap * (pderiv b).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) =
      (pderiv b).toLinearMap * (pderiv a).toLinearMap := by
  refine LinearMap.ext fun P => ?_
  change pderiv a (pderiv b P) = pderiv b (pderiv a P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hP, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem mx_mx (a b : σ) :
    (LinearMap.mulLeft ℂ (X a) * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * LinearMap.mulLeft ℂ (X a) := by
  refine LinearMap.ext fun P => ?_
  simp [mul_left_comm]

theorem pd_mx (a b : σ) :
    ((pderiv a).toLinearMap * LinearMap.mulLeft ℂ (X b) : Module.End ℂ (MvPolynomial σ ℂ)) =
      LinearMap.mulLeft ℂ (X b) * (pderiv a).toLinearMap + if a = b then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases h : a = b
  · subst h
    simp [Derivation.leibniz]
  · simp [Derivation.leibniz, h, pderiv_X_of_ne (Ne.symm h)]

end Fock

section Lines

variable {p q r s : ℕ}

theorem rai_rai (a b : Ln p q r s) : raiB a * raiB b = raiB b * raiB a := by
  unfold raiB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · simp only [ha, hb, if_true]; exact mx_mx a b
  · have hne : b ≠ a := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, mul_neg, neg_mul, pd_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, neg_mul_neg, neg_mul_neg, pd_pd]

theorem low_low (a b : Ln p q r s) : lowB a * lowB b = lowB b * lowB a := by
  unfold lowB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · rw [if_pos ha, if_pos hb, pd_pd]
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, pd_mx, if_neg hne, add_zero]
  · have hne : b ≠ a := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, pd_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, mx_mx]

theorem low_rai (a b : Ln p q r s) :
    lowB a * raiB b = raiB b * lowB a + if a = b then 1 else 0 := by
  unfold lowB raiB
  by_cases ha : linePos a = true <;> by_cases hb : linePos b = true
  · rw [if_pos ha, if_pos hb, pd_mx]
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [if_pos ha, if_neg hb, mul_neg, neg_mul, pd_pd, if_neg hne, add_zero]
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [if_neg ha, if_pos hb, mx_mx, if_neg hne, add_zero]
  · rw [if_neg ha, if_neg hb, mul_neg, neg_mul, pd_mx]
    by_cases h : a = b
    · rw [if_pos h, if_pos h.symm]; abel
    · rw [if_neg h, if_neg (Ne.symm h)]; abel

theorem omAct_eq (A : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s A = quadT raiB lowB A + (∑ l, A l l * (1 / 2 : ℂ)) • 1 := by
  unfold omAct quadT omE
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply,
    smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_smul, smul_smul]

theorem omAct_commute (A B : Matrix (Ln p q r s) (Ln p q r s) ℂ) (h : A * B = B * A) :
    omAct p q r s A * omAct p q r s B = omAct p q r s B * omAct p q r s A := by
  have hc := quadT_commute raiB lowB rai_rai low_low low_rai A B h
  rw [omAct_eq, omAct_eq]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hc, smul_add, smul_smul]
  rw [mul_comm (∑ l, A l l * (1 / 2 : ℂ))]
  abel

end Lines

theorem fockAct1_fockAct2_commute {p q r s : ℕ} (Z : Mat p q) (W : Mat r s) :
    fockAct1 p q r s Z * fockAct2 p q r s W = fockAct2 p q r s W * fockAct1 p q r s Z := by
  refine omAct_commute (Matrix.kroneckerMap (· * ·) Z 1) (Matrix.kroneckerMap (· * ·) 1 W) ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

end PositivityTheory.KReal

end
end
