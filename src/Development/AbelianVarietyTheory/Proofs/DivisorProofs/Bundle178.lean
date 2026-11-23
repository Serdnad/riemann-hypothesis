module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

section

open scoped SchwartzMap Matrix

namespace GlobalTheory

open Matrix

theorem sympl_eq_neg_dotProduct_J {l : Type} [Fintype l] [DecidableEq l] (w w' : l ⊕ l → ℝ) :
    GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (J l ℝ *ᵥ w')) := by
  simp only [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, J, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, Matrix.one_apply, Finset.sum_neg_distrib, mul_comm, Matrix.neg_mulVec, Matrix.one_mulVec]
  ring

theorem exists_symplecticGroup_of_sympl (l : Type) [Fintype l] [DecidableEq l]
    (ψ : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (h : ∀ w w', GlobalTheory.RealWeil.sympl (ψ w) (ψ w') = GlobalTheory.RealWeil.sympl w w') :
    ∃ M : Matrix.symplecticGroup l ℝ, ∀ w, (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w = ψ w := by
  set M := LinearMap.toMatrix' ψ with hM
  have hMv : ∀ w, M *ᵥ w = ψ w := fun w => by rw [hM, LinearMap.toMatrix'_mulVec]
  have key : ∀ w w', w ⬝ᵥ ((Mᵀ * J l ℝ * M) *ᵥ w') = w ⬝ᵥ (J l ℝ *ᵥ w') := by
    intro w w'
    have := h w w'
    rw [sympl_eq_neg_dotProduct_J, sympl_eq_neg_dotProduct_J, ← hMv, ← hMv] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    linarith
  have hmem : M ∈ Matrix.symplecticGroup l ℝ := by
    rw [SymplecticGroup.mem_iff']
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, mulVec_single] using this
  exact ⟨⟨M, hmem⟩, hMv⟩

end GlobalTheory
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.EuclidTransport

variable (l : Type) [Fintype l]

theorem volume_preserving_ofLp' : MeasurePreserving (@WithLp.ofLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_ofLp l

theorem volume_preserving_toLp' : MeasurePreserving (@WithLp.toLp 2 (l → ℝ)) volume volume :=
  PiLp.volume_preserving_toLp l

def schwartzTransport : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l :=
  ContinuousLinearEquiv.equivOfInverse
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ))
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv l ℝ).symm)
    (fun φ => by ext x; rfl) (fun φ => by ext x; rfl)

variable {l}

theorem schwartzTransport_apply (φ : 𝓢(l → ℝ, ℂ)) (x : EuclideanSpace ℝ l) :
    schwartzTransport l φ x = φ x.ofLp := rfl

variable (l)

def l2TransportIsometry : Lp ℂ 2 (volume : Measure (l → ℝ)) →ₗᵢ[ℂ] L2 l :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 (l → ℝ)) (volume_preserving_ofLp' l)

theorem l2TransportIso_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2TransportIsometry l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2TransportIso_surjective : Function.Surjective (l2TransportIsometry l) := by
  intro h
  refine ⟨Lp.compMeasurePreserving (@WithLp.toLp 2 (l → ℝ)) (volume_preserving_toLp' l) h, ?_⟩
  rw [l2TransportIso_apply]
  ext1
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving h (volume_preserving_toLp' l))).trans ?_
  exact Filter.Eventually.of_forall fun x => rfl

def l2Transport : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l :=
  LinearIsometryEquiv.ofSurjective (l2TransportIsometry l) (l2TransportIso_surjective l)

variable {l}

theorem l2Transport_apply (f : Lp ℂ 2 (volume : Measure (l → ℝ))) :
    l2Transport l f = Lp.compMeasurePreserving _ (volume_preserving_ofLp' l) f := rfl

theorem l2Transport_toLp (φ : 𝓢(l → ℝ, ℂ)) : l2Transport l (φ.toLp 2) = (schwartzTransport l φ).toLp 2 := by
  rw [l2Transport_apply]
  have h4 : ((φ.toLp 2 : Lp ℂ 2 (volume : Measure (l → ℝ))) : (l → ℝ) → ℂ) =ᵐ[volume] (φ : (l → ℝ) → ℂ) :=
    φ.coeFn_toLp 2 volume
  have h5 : (((schwartzTransport l φ).toLp 2 : L2 l) : EuclideanSpace ℝ l → ℂ) =ᵐ[volume]
      (schwartzTransport l φ : EuclideanSpace ℝ l → ℂ) :=
    (schwartzTransport l φ).coeFn_toLp 2 volume
  refine Lp.ext (Filter.EventuallyEq.trans ?_ h5.symm)
  refine (Lp.coeFn_compMeasurePreserving _ (volume_preserving_ofLp' l)).trans ?_
  refine ((volume_preserving_ofLp' l).quasiMeasurePreserving.ae_eq_comp h4).trans ?_
  exact Filter.Eventually.of_forall fun x => (schwartzTransport_apply φ x).symm

theorem exists_schwartz_L2_transport (l : Type) [Fintype l] [DecidableEq l] :
    ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l),
      (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 :=
  ⟨schwartzTransport l, l2Transport l, schwartzTransport_apply, l2Transport_toLp⟩

end GlobalTheory.EuclidTransport
end
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.SchwartzIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) : E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x)
    ((continuous_norm.pow k).smul ((f.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k m f) (fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact f.le_seminorm ℂ k m x)

theorem weightedDeriv_apply (k m : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    weightedDeriv k m f x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ m f x := rfl

theorem norm_weightedDeriv_le (k m : ℕ) (f : 𝓢(E, ℂ)) :
    ‖weightedDeriv k m f‖ ≤ SchwartzMap.seminorm ℂ k m f :=
  (BoundedContinuousFunction.norm_le (apply_nonneg _ _)).mpr fun x => by
    rw [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact f.le_seminorm ℂ k m x

theorem seminorm_le_norm_weightedDeriv (k m : ℕ) (f : 𝓢(E, ℂ)) :
    SchwartzMap.seminorm ℂ k m f ≤ ‖weightedDeriv k m f‖ :=
  SchwartzMap.seminorm_le_bound ℂ k m f (norm_nonneg _) fun x => by
    have h := (weightedDeriv k m f).norm_coe_le_norm x
    rwa [weightedDeriv_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h

def weightedDerivCLM (k m : ℕ) :
    𝓢(E, ℂ) →L[ℂ] (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (weightedDeriv k m)
    (fun f g => by
      ext x : 1
      simp only [weightedDeriv_apply, add_apply, FunLike.coe_add]
      rw [iteratedFDeriv_add_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
        ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt, smul_add])
    (fun a f => by
      ext x : 1
      simp only [weightedDeriv_apply, FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [iteratedFDeriv_const_smul_apply ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt,
        smul_comm])
    ⟨{(k, m)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using norm_weightedDeriv_le k m f⟩

theorem weightedDerivCLM_apply (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl

section Param

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}

theorem continuous_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G) (m : ℕ) (y : E) :
    Continuous fun w => iteratedFDeriv ℝ m (G w) y := by
  have h := ((BoundedContinuousFunction.evalCLM ℂ y).comp (weightedDerivCLM (E := E) 0 m)).continuous.comp hG
  refine h.congr fun w => ?_
  simp [weightedDerivCLM_apply, weightedDeriv_apply]

theorem integrable_iteratedFDeriv_param {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) (m : ℕ) (y : E) :
    Integrable (fun w => iteratedFDeriv ℝ m (G w) y) ν :=
  (hint 0 m).mono' (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable
    (.of_forall fun w => (G w).norm_iteratedFDeriv_le_seminorm ℂ m y)

theorem iteratedFDeriv_eq_integral {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) (m : ℕ) :
    iteratedFDeriv ℝ m g = fun x => ∫ w, iteratedFDeriv ℝ m (G w) x ∂ν := by
  induction m with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hg x]
    exact ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry.integral_comp_comm _).symm
  | succ m ih =>
    funext x
    set Ψ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℂ
    have key : ∀ (f : E → ℂ) (y : E), iteratedFDeriv ℝ (m + 1) f y = Ψ.symm (fderiv ℝ (iteratedFDeriv ℝ m f) y) := by
      intro f y
      rw [iteratedFDeriv_succ_eq_comp_left]
      rfl
    have hdiff : ∀ w, Differentiable ℝ (iteratedFDeriv ℝ m (G w)) := fun w =>
      ((G w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top m)
    have hF' : ∀ w y, fderiv ℝ (iteratedFDeriv ℝ m (G w)) y = Ψ (iteratedFDeriv ℝ (m + 1) (G w) y) := by
      intro w y
      rw [key, LinearIsometryEquiv.apply_symm_apply]
    have hd : HasFDerivAt (fun y => ∫ w, iteratedFDeriv ℝ m (G w) y ∂ν)
        (∫ w, fderiv ℝ (iteratedFDeriv ℝ m (G w)) x ∂ν) x := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun w => SchwartzMap.seminorm ℂ 0 (m + 1) (G w))
        Filter.univ_mem (.of_forall fun y => (continuous_iteratedFDeriv_param hG m y).aestronglyMeasurable)
        (integrable_iteratedFDeriv_param hG hint m x) ?_ (.of_forall fun w y _ => ?_) (hint 0 (m + 1))
        (.of_forall fun w y _ => (hdiff w y).hasFDerivAt)
      · simp_rw [hF']
        exact (Ψ.continuous.comp (continuous_iteratedFDeriv_param hG (m + 1) x)).aestronglyMeasurable
      · rw [norm_fderiv_iteratedFDeriv]
        exact (G w).norm_iteratedFDeriv_le_seminorm ℂ (m + 1) y
    rw [key, ih, hd.fderiv]
    have := Ψ.symm.toLinearIsometry.integral_comp_comm (μ := ν) (fun w => fderiv ℝ (iteratedFDeriv ℝ m (G w)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
    rw [← this]
    simp_rw [hF', LinearIsometryEquiv.symm_apply_apply]

abbrev Target (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset (ℕ × ℕ)) : Type :=
  (i : s) → (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ)

def embed (s : Finset (ℕ × ℕ)) : 𝓢(E, ℂ) →L[ℂ] Target E s :=
  ContinuousLinearMap.pi fun i => weightedDerivCLM i.1.1 i.1.2

theorem embed_apply (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) (i : s) : embed s f i = weightedDeriv i.1.1 i.1.2 f := rfl

theorem norm_embed_le (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) :
    ‖embed s f‖ ≤ ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 f :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => apply_nonneg _ _)).mpr fun i =>
    (norm_weightedDeriv_le _ _ f).trans
      (Finset.single_le_sum (f := fun j : ℕ × ℕ => SchwartzMap.seminorm ℂ j.1 j.2 f)
        (fun j _ => apply_nonneg _ _) i.2)

theorem seminorm_le_norm_embed (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)

theorem clm_apply_eq_integral (L : 𝓢(E, ℂ) →L[ℂ] ℂ) {G : W → 𝓢(E, ℂ)} (hG : Continuous G)
    (hint : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (G w)) ν) {g : 𝓢(E, ℂ)}
    (hg : ∀ x, g x = ∫ w, G w x ∂ν) : L g = ∫ w, L (G w) ∂ν := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (continuous_norm.comp L.continuous)
  have hL : ∀ f, ‖L f‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ E ℂ)) f := fun f => hC f
  set t := insert ((0 : ℕ), (0 : ℕ)) s
  have hLt : ∀ f, ‖L f‖ ≤ C * ‖embed t f‖ := fun f => (hL f).trans (mul_le_mul_of_nonneg_left
    (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi =>
      seminorm_le_norm_embed t f (Finset.mem_insert_of_mem hi)) C.2)
  have hinj : Function.Injective (embed (E := E) t) := by
    refine (injective_iff_map_eq_zero (embed (E := E) t)).mpr fun f hf => ?_
    ext x
    have h1 := seminorm_le_norm_embed t f (Finset.mem_insert_self _ _)
    rw [hf, norm_zero] at h1
    have h2 := (f.norm_le_seminorm ℂ x).trans h1
    simpa using h2
  let Φ : 𝓢(E, ℂ) →ₗ[ℂ] Target E t := (embed (E := E) t : 𝓢(E, ℂ) →ₗ[ℂ] Target E t)
  let e := LinearEquiv.ofInjective Φ hinj
  have he : ∀ y : LinearMap.range Φ, embed t (e.symm y) = y := fun y => by
    have := congrArg Subtype.val (e.apply_symm_apply y)
    exact (LinearEquiv.ofInjective_apply Φ (e.symm y)).symm.trans this
  let f0 : LinearMap.range Φ →ₗ[ℂ] ℂ := (L : 𝓢(E, ℂ) →ₗ[ℂ] ℂ).comp e.symm.toLinearMap
  let f1 : StrongDual ℂ (LinearMap.range Φ) := f0.mkContinuous C fun y => by
    show ‖L (e.symm y)‖ ≤ C * ‖(y : Target E t)‖
    rw [← he]
    exact hLt _
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) f1
  have hLℓ : ∀ f, L f = ℓ (embed t f) := by
    intro f
    have h1 := hℓ ⟨embed t f, LinearMap.mem_range_self Φ f⟩
    have h2 : e.symm ⟨embed t f, LinearMap.mem_range_self Φ f⟩ = f := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have h3 : ℓ (embed t f) = f1 ⟨embed t f, LinearMap.mem_range_self Φ f⟩ := h1
    rw [h3, LinearMap.mkContinuous_apply]
    show L f = L (e.symm _)
    rw [h2]
  have hcont : Continuous fun w => embed t (G w) := (embed t).continuous.comp hG
  haveI : SecondCountableTopology W := inferInstance
  haveI : SecondCountableTopologyEither W (Target E t) := secondCountableTopologyEither_of_left _ _
  have hInt : Integrable (fun w => embed t (G w)) ν :=
    (MeasureTheory.integrable_finsetSum t fun i _ => hint i.1 i.2).mono' hcont.aestronglyMeasurable
      (.of_forall fun w => norm_embed_le t (G w))
  have hemb : embed t g = ∫ w, embed t (G w) ∂ν := by
    funext i
    refine BoundedContinuousFunction.ext fun x => ?_
    have h1 := ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i : t => E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin i.1.2 => E) ℂ) i)).integral_comp_comm hInt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      BoundedContinuousFunction.evalCLM_apply] at h1
    rw [← h1]
    simp only [embed_apply, weightedDeriv_apply]
    rw [integral_smul, iteratedFDeriv_eq_integral hG hint hg]
  rw [hLℓ g, hemb, ← ℓ.integral_comp_comm hInt]
  simp_rw [← hLℓ]

end Param

theorem clm_integral_interchange : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (ν : Measure W) [SigmaFinite ν] (n : ℕ) (L : Sch (Fin n) →L[ℂ] ℂ)
    (G : W → Sch (Fin n)) (c : W → ℂ) (g : Sch (Fin n)), Continuous G → Continuous c →
    (∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) ν) →
    (∀ x, g x = ∫ w, c w * G w x ∂ν) → L g = ∫ w, c w * L (G w) ∂ν := by
  intro W _ _ _ _ _ ν _ n L G c g hG hc hint hg
  have hG' : Continuous fun w => c w • G w := hc.smul hG
  have hint' : ∀ k m : ℕ, Integrable (fun w => SchwartzMap.seminorm ℂ k m (c w • G w)) ν := by
    intro k m
    simpa only [map_smul_eq_mul] using hint k m
  have hg' : ∀ x, g x = ∫ w, (c w • G w) x ∂ν := by
    intro x
    rw [hg x]
    rfl
  rw [clm_apply_eq_integral L hG' hint' hg']
  simp only [map_smul, smul_eq_mul]

end GlobalTheory.SchwartzIntegral
end
end

section

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem gaussian_selfPairing_pos (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ (∫ x, GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x *
      starRingEnd ℂ (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) x)) = (r : ℂ) := by
  refine ⟨∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(2 * Real.pi) * ‖x‖ ^ 2), ?_, ?_⟩
  · rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
    have : 0 < Real.pi / (2 * Real.pi) := by positivity
    positivity
  · rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem hermitian_form_eq_smul_l2 : ∀ (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ), (∀ h h', B h' h = starRingEnd ℂ (B h h')) →
    (∀ h, 0 ≤ (B h h).re) →
    (∀ f f' g g' : Sch (Fin n), (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' = (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hherm hpos hid
  set h₀ : Sch (Fin n) := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin n)) with hh₀
  obtain ⟨r, hr, hs⟩ := gaussian_selfPairing_pos n
  have hb : B h₀ h₀ = ((B h₀ h₀).re : ℂ) := by
    have := hherm h₀ h₀
    apply Complex.ext
    · simp
    · have h2 : (B h₀ h₀).im = -(B h₀ h₀).im := by
        conv_lhs => rw [this]
        simp
      simp; linarith
  refine ⟨(B h₀ h₀).re / r, div_nonneg (hpos h₀) hr.le, fun h h' => ?_⟩
  have key := hid h₀ h' h₀ h
  rw [hs, hb] at key
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linear_combination key

end GlobalTheory
end

section

namespace GlobalTheory.CovNum

open Formalism.NormVectorIdentities.Items

theorem hsLogRho_bounds (D : ℕ) (n Λ δ h l₀ : ℝ) (hD : 1 ≤ D) (hn : 1 ≤ n) (hΛ : 1 ≤ Λ)
    (hδ : 1 ≤ δ)
    (hl : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀) :
    0 ≤ hsLogRho 26 n D 1 Λ δ h ∧
      hsLogRho 26 n D 1 Λ δ h ≤ l₀ + 26 * Real.log (2 + |h|) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hh : 0 ≤ |h| := abs_nonneg h
  have h1 : 1 ≤ n * D * δ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn hD') hδ
  have h2 : 1 ≤ n * D * δ * (2 + |h| + Real.log Λ) :=
    one_le_mul_of_one_le_of_one_le h1 (by linarith)
  have h3 : n * D * δ * (2 + |h| + Real.log Λ)
      ≤ (n * D * δ * (1 + Real.log Λ)) * (2 + |h|) := by
    rw [mul_assoc (n * D * δ)]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    nlinarith [mul_nonneg hL hh]
  have h4 : Real.log (n * D * δ * (2 + |h| + Real.log Λ))
      ≤ Real.log (n * D * δ * (1 + Real.log Λ)) + Real.log (2 + |h|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by linarith) h3
  have h5 := Real.log_nonneg h2
  unfold hsLogRho
  rw [mul_one]
  constructor <;> linarith

theorem deg_lower_of_claim : ∀ (T D : ℕ) (n Λ β ΛD ΛT J δ h d deg z l₀ : ℝ), 1 ≤ T → 1 ≤ D → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → 0 ≤ z → z ≤ 1 / 2 → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤ l₀ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → ((T - 1).choose D : ℕ) * δ * (T * h - 3 * (D + 1) * |h| - 26 * (26 * D ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (J + 26 * D ^ 2 * (l₀ + Real.log T) + (T + D + 1) * Real.log β + (T + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * (T * (Real.log 2 + l₀ + Real.log β / 2) + Real.log ΛD + Real.log ΛT))) ≤ deg := by
  intro T D n Λ β ΛD ΛT J δ h d deg z l₀ hT hD hn hΛ hβ hΛD hΛT hδ hd hz hz2 hP hl hc
  obtain ⟨hρ0, hρ⟩ := hsLogRho_bounds D n Λ δ h l₀ hD hn hΛ hδ hl
  obtain ⟨-, -, hc⟩ := hc
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hβ0 : 0 < β := by linarith
  have e1 : Real.log (Real.exp (hsLogRho 26 n D 1 Λ δ h) * T)
      = hsLogRho 26 n D 1 Λ δ h + Real.log T := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have e2 : Real.log (2 * Real.exp (hsLogRho 26 n D 1 Λ δ h) * Real.sqrt β)
      = Real.log 2 + hsLogRho 26 n D 1 Λ δ h + Real.log β / 2 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_sqrt hβ0.le]
  rw [e1, e2, le_div_iff₀ hd] at hc
  unfold hsZ hsR at hc
  generalize hsLogRho 26 n D 1 Λ δ h = ρ at hρ0 hρ hc
  generalize ((Nat.choose (T - 1) D : ℕ) : ℝ) * δ = P at hP hc ⊢
  generalize hsG D n = g at hc ⊢
  have hb := Real.log_nonneg hβ
  have hLD := Real.log_nonneg hΛD
  have hLT := Real.log_nonneg hΛT
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  generalize Real.log (2 + |h|) = L at hρ ⊢
  have hdP : d ≤ 2 * P := by nlinarith
  have hP0 : 0 ≤ P := by linarith
  have hdef : d - P ≤ 2 * z * P := by nlinarith
  set A := (T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 26 * (D : ℝ) ^ 2 * (ρ + Real.log T)
    - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) with hA
  set B := (T : ℝ) * (Real.log 2 + ρ + Real.log β / 2) + Real.log ΛD + Real.log ΛT with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have e3 : ((1 - (1 - P / d)) * A - (1 - P / d) * B) * d = P * A - (d - P) * B := by
    field_simp
    ring
  rw [e3] at hc
  have h6 : (d - P) * B ≤ 2 * z * P * B := mul_le_mul_of_nonneg_right hdef hB0
  have h7 : 0 ≤ (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ) :=
    mul_nonneg (by positivity) (by linarith)
  have h8 : P * (A - 2 * z * B - (26 * (D : ℝ) ^ 2 + 2 * z * T) * (l₀ + 26 * L - ρ))
      ≤ P * (A - 2 * z * B) := mul_le_mul_of_nonneg_left (by linarith) hP0
  refine le_trans (le_of_eq ?_) (h8.trans (by linarith))
  rw [hA, hB]
  ring

end GlobalTheory.CovNum
end
