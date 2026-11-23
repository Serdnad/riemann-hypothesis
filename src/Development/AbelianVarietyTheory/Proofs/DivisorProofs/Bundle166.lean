module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.SemistableReduction.Bundle002
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson.Dilation

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)

def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_apply_eq_toLp_dil (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE y w = WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)) := by
  ext i
  simp [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, _root_.GlobalTheory.HeckeTheta.dil]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_neg_apply_dilE_apply (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y w) = w := by
  ext i
  simp only [dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, WithLp.ofLp_toLp, Pi.neg_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma det_dilE_eq_exp_sum (y : I → ℝ) : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) = Real.exp (∑ i, y i) := by
  rw [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, LinearMap.det_conj, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, LinearMap.det_pi, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma inner_dilE_dilE_neg (y : I → ℝ) (v l : EuclideanSpace ℂ I) :
    ⟪_root_.GlobalTheory.HeckePoisson.Dilation.dilE y v, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫ = ⟪v, l⟫ := by
  simp [-Complex.ofReal_exp, dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, real_inner_eq_re_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Real.exp (y i / 2) * Real.exp (-y i / 2) = 1 := by
    rw [← Real.exp_add, show y i / 2 + -y i / 2 = 0 by ring, Real.exp_zero]
  linear_combination ((l.ofLp i).re * (v.ofLp i).re + (l.ofLp i).im * (v.ofLp i).im) * h


open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
theorem _root_.GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  let e : EuclideanSpace ℂ I ≃ₗ[ℝ] EuclideanSpace ℂ I :=
    LinearEquiv.ofLinear (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y))
      (LinearMap.ext fun w => by simpa using dilE_neg_apply_dilE_apply (-y) w)
      (LinearMap.ext fun w => dilE_neg_apply_dilE_apply y w)
  have hemb : MeasurableEmbedding (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) ≠ 0 := by
    rw [det_dilE_eq_exp_sum]
    exact (Real.exp_pos _).ne'
  have key := hemb.integral_map (μ := volume)
    (fun u => 𝐞 (-⟪u, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫) • f u)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, integral_smul_measure] at key
  simp only [inner_dilE_dilE_neg] at key
  simp only [dilE_apply_eq_toLp_dil] at key
  rw [Real.fourier_eq, Real.fourier_eq, ← key, det_dilE_eq_exp_sum, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg, Complex.real_smul]

end GlobalTheory.HeckePoisson.Dilation
end
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.GaussMarginal

open Real

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ,
      ← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
    refine lintegral_congr fun q => ?_
    simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e := (Fintype.equivFin ι).symm
  have h := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), ← e.prod_comp,
    ← lintegral_pi_fin _ μ (fun i => f (e i)) (fun i => hf _)]
  refine lintegral_congr fun q => ?_
  rw [← e.prod_comp]
  simp [MeasurableEquiv.coe_piCongrLeft]

theorem pi_withDensity_const {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _), ← lintegral_indicator (hs _)]
  rw [← lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i trivial) _).symm
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) :=
  GlobalTheory.isProbabilityMeasure_complexGaussian (by simp [Complex.finrank_real_complex])

theorem gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]

theorem map_ofLp_gaussProb (k : ℕ) :
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]

theorem measurePreserving_restrict_castLE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  intro N n h
  haveI := isProbabilityMeasure_complexGaussian_one
  have hofn : Measurable (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).measurable
  have hofN : Measurable (WithLp.ofLp (p := 2) (V := Fin N → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin N)).measurable
  have htoN : Measurable (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)) := by fun_prop
  have e1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) (gaussProb n)
      (Measure.pi fun _ : Fin n => GlobalTheory.complexGaussian ℂ 1) := ⟨hofn, map_ofLp_gaussProb n⟩
  have e3 : MeasurePreserving (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N))
      (Measure.pi fun _ : Fin N => GlobalTheory.complexGaussian ℂ 1) (gaussProb N) := by
    refine ⟨htoN, ?_⟩
    rw [← map_ofLp_gaussProb N, Measure.map_map htoN hofN]
    convert Measure.map_id
    funext x
    rfl
  exact e3.comp ((measurePreserving_restrict_castLE _ h).comp e1)

end GlobalTheory.GaussMarginal
end
end

section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

noncomputable section

namespace GlobalTheory.StdLoc

def blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin (a + b)) (Fin (a + b)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)

theorem det_blockMat {R : Type} [CommRing R] {a b : ℕ} (A : Matrix (Fin a) (Fin a) R) (B : Matrix (Fin a) (Fin b) R)
    (D : Matrix (Fin b) (Fin b) R) : (blockMat A B D).det = A.det * D.det := by
  rw [blockMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def blockParMk {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) : blockPar R a (a + b) :=
  ⟨Matrix.GeneralLinearGroup.mk'' (blockMat x.1.1 x.2.2 x.2.1.1) (by
      rw [det_blockMat]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 x.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 x.2.1.isUnit)), by
    rw [mem_blockPar]
    intro i j hj hi
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    show blockMat x.1.1 x.2.2 x.2.1.1 _ _ = 0
    rcases i with i | i
    · exact absurd hi (by simp)
    rcases j with j | j
    · simp only [blockMat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    · exact absurd hj (by simp)⟩

theorem blockParMk_val {R : Type} [CommRing R] {a b : ℕ}
    (x : GL (Fin a) R × GL (Fin b) R × Matrix (Fin a) (Fin b) R) :
    ((blockParMk x).1 : Matrix (Fin (a + b)) (Fin (a + b)) R) = blockMat x.1.1 x.2.2 x.2.1.1 := rfl

theorem blockParMk_bijective {R : Type} [CommRing R] {a b : ℕ} :
    Function.Bijective (blockParMk (R := R) (a := a) (b := b)) := by
  constructor
  · rintro ⟨A, D, B⟩ ⟨A', D', B'⟩ h
    have h1 : blockMat A.1 B D.1 = blockMat A'.1 B' D'.1 := by
      have := congrArg (fun g : blockPar R a (a + b) => (g.1 : Matrix (Fin (a + b)) (Fin (a + b)) R)) h
      simpa only [blockParMk_val] using this
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    obtain ⟨hA, hB, -, hD⟩ := Matrix.fromBlocks_inj.1 h2
    exact Prod.ext (Units.ext hA) (Prod.ext (Units.ext hD) hB)
  · rintro ⟨g, hg⟩
    set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
      (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm (g : Matrix (Fin (a + b)) (Fin (a + b)) R) with hM
    have h0 : M.toBlocks₂₁ = 0 := by
      ext i j
      exact (mem_blockPar g).1 hg (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) (by simp) (by simp)
    have hb : blockMat M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂ = g := by
      rw [blockMat, ← h0, Matrix.fromBlocks_toBlocks, hM, Equiv.apply_symm_apply]
    have hu : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
      rw [← det_blockMat _ M.toBlocks₁₂, hb]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    refine ⟨(Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left hu),
      Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right hu), M.toBlocks₁₂), ?_⟩
    exact Subtype.ext (Units.ext hb)

theorem card_blockPar (R : Type) [CommRing R] [Finite R] (a d : ℕ) (h : a ≤ d) :
    Nat.card (blockPar R a d) =
      Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ← Nat.card_eq_of_bijective _ blockParMk_bijective, Nat.card_prod, Nat.card_prod,
    mul_assoc]
  congr 2
  show Nat.card (Fin a → Fin b → R) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.StdLoc
end
end

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_eq_adj {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (y m : Fin n → K) :
    herm σ y (x *ᵥ m) = herm σ ((x.map σ)ᵀ *ᵥ y) m := by

  simp only [herm, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
  Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem matLat_adj_mul_eq_of_selfDual : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  intro O K _ _ _ σ _ n x hx M hM hxM

  have key : ∀ y, y ∈ matLat O x M ↔ (x.map σ)ᵀ *ᵥ y ∈ M := by
    intro y
    rw [hxM y, hM ((x.map σ)ᵀ *ᵥ y)]
    constructor
    · intro h m hm
      rw [← herm_mulVec_eq_adj]
      exact h _ ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
    · intro h w hw
      obtain ⟨m, hm, rfl⟩ := (mem_matLat x M w).1 hw
      rw [herm_mulVec_eq_adj]
      exact h m hm
  have hdet : IsUnit ((x.map σ)ᵀ * x).det := by
    have e : (x.map σ).det = σ x.det := (RingHom.map_det σ x).symm
    rw [Matrix.det_mul, Matrix.det_transpose, e]
    refine IsUnit.mul ?_ ((Matrix.isUnit_iff_isUnit_det x).1 hx)
    have h0 : x.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det x).1 hx).ne_zero
    exact isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 h0)
  ext u
  rw [mem_matLat]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← Matrix.mulVec_mulVec]
    exact (key _).1 ((mem_matLat x M _).2 ⟨m, hm, rfl⟩)
  · intro hu
    set A := (x.map σ)ᵀ * x with hA
    refine ⟨A⁻¹ *ᵥ u, ?_, ?_⟩
    · have h1 : (x.map σ)ᵀ *ᵥ (x *ᵥ (A⁻¹ *ᵥ u)) ∈ M := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hA,
          Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
        exact hu
      obtain ⟨m', hm', hxm'⟩ := (mem_matLat x M _).1 ((key _).2 h1)
      have : m' = A⁻¹ *ᵥ u := by
        have hx' : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hx
        have := congrArg (fun v => x⁻¹ *ᵥ v) hxm'
        simpa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul x hx'] using this
      exact this ▸ hm'
    · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]

end GlobalTheory.LatOrb
end

section

open Polynomial Matrix GlobalTheory.LatOrb

namespace GlobalTheory.LatOrb

theorem herm_mulVec_right {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (y u : Fin n → K) :
    herm σ y (g *ᵥ u) = herm σ ((g.map σ)ᵀ *ᵥ y) u := by

  simp only [herm, mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply,
  Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem selfDual_matLat_stdLat {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K)
    (_hinv : ∀ x, σ (σ x) = x) (hO : ∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b)
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : (g.map σ)ᵀ * g = 1) :
    SelfDual O σ (matLat O g (stdLat O n)) := by
  have hg' : g * (g.map σ)ᵀ = 1 := mul_eq_one_comm.mp hg
  have hσO : ∀ z ∈ (algebraMap O K).range, σ z ∈ (algebraMap O K).range := by
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hO a
    exact ⟨b, hb.symm⟩
  intro y
  rw [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩ x hx
    rw [mem_matLat] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [herm_mulVec_right, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
    unfold herm
    refine Subring.sum_mem _ (fun k _ => Subring.mul_mem _ ((mem_stdLat u).mp hu k) (hσO _ ((mem_stdLat v).mp hv k)))
  · intro h
    refine ⟨(g.map σ)ᵀ *ᵥ y, ?_, by rw [Matrix.mulVec_mulVec, hg', Matrix.one_mulVec]⟩
    rw [mem_stdLat]
    intro j
    have hx : g *ᵥ (Pi.single j 1 : Fin n → K) ∈ matLat O g (stdLat O n) := by
      rw [mem_matLat]
      refine ⟨Pi.single j 1, ?_, rfl⟩
      rw [mem_stdLat]
      intro i
      by_cases hij : i = j
      · subst hij; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
    have := h _ hx
    rw [herm_mulVec_right] at this
    simpa [herm, Pi.single_apply, map_one] using this

end GlobalTheory.LatOrb
end
