module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

namespace GlobalTheory.GaugeEx.GramPair

section Ring

variable {A : Type} [CommRing A] (s : A →+* A) {M N : ℕ} (G : Matrix (Fin M) (Fin M) A)

theorem hform_eq_dot (x y : Fin M → A) :
    Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (P : Matrix (Fin M) (Fin N) A) (x y : Fin N → A) :
    Formalism.UG.hform s G (P *ᵥ x) (P *ᵥ y) = Formalism.UG.hform s (Formalism.UG.cT s P * G * P) x y := by
  have e : (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s P := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq_dot, hform_eq_dot, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem hform_mulVec_right (P : Matrix (Fin M) (Fin N) A) (x : Fin M → A) (w : Fin N → A) :
    Formalism.UG.hform s G x (P *ᵥ w) = ∑ j, Formalism.UG.hform s G x (fun i => P i j) * w j := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem hform_symm (hs : ∀ a, s (s a) = a) (hG : ∀ i j, s (G j i) = G i j) (x y : Fin M → A) :
    Formalism.UG.hform s G y x = s (Formalism.UG.hform s G x y) := by

  simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hG]
  ring

theorem hform_lin (a b c d : A) (x y : Fin M → A) :
    Formalism.UG.hform s G (a • x + b • y) (c • x + d • y) =
      s a * c * Formalism.UG.hform s G x x + s a * d * Formalism.UG.hform s G x y +
        s b * c * Formalism.UG.hform s G y x + s b * d * Formalism.UG.hform s G y y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Ring

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj σ h]

omit [NumberField F] [NumberField E] in
theorem sigR_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show r ⊗ₜ[F] σ 1 = r ⊗ₜ[F] 1
  rw [map_one]

omit [NumberField F] [NumberField E] in
theorem hR_rat {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = inclR R (hE σ J x z) := by
  simp [hR, hE, Formalism.UG.hform, sigR, JR, inclR, TensorProduct.tmul_sum]

theorem half_trace (h : IsCMExt F E σ) (k : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) k) = k := by
  have h2 : Algebra.trace F E 1 = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) 1
    rw [map_one, h.2.2.1] at this
    rw [this]; norm_num
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (1 : E)) = algebraMap F R 2 := by
    rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
      ← Algebra.trace_apply, h2]
  rw [Algebra.algebraMap_eq_smul_one k, map_smul, Algebra.TensorProduct.one_def, h1, smul_eq_mul,
    mul_left_comm, ← map_mul, show (1 / 2 * 2 : F) = 1 by norm_num, map_one, mul_one]

omit [NumberField F] [NumberField E] in
theorem JR_cT {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E) :
    Formalism.UG.cT (sigR R σ) (B.map (inclR (F := F) R)) * JR (F := F) R J * B.map (inclR (F := F) R) =
      JR (F := F) R (Formalism.UG.cT (σ : E →+* E) B * J * B) := by
  rw [JR, JR, Matrix.map_mul, Matrix.map_mul]
  rfl

end Tens

theorem gram_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → Continuous (gram3 R σ J) ∧ ∃ n : R ⊗[F] E → R, Continuous n ∧ n 0 = 0 ∧ ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) (r r' : R) (t : R ⊗[F] E), g • ratTup (F := F) R x = y → gram3 R σ J ![algebraMap R (R ⊗[F] E) r • y 0, t • y 0 + algebraMap R (R ⊗[F] E) r' • pairOf R σ J B y g y' 1] = (r * r * algebraMap F R a, algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t, n t + r' * r' * qR R σ J' (y' 0)) := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ M J x a B J' hS
  obtain ⟨hJ, -, hx, hB, hJ', -⟩ := hS
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  have hc : ∀ i j : Fin 2, Continuous fun X : Fin 2 → Fin (M + 1) → R ⊗[F] E =>
      hR R σ J (X i) (X j) := by
    intro i j
    unfold hR Formalism.UG.hform
    fun_prop
  refine ⟨(continuous_const.mul (h1.comp (hc 0 0))).prodMk
    ((hc 0 1).prodMk (continuous_const.mul (h1.comp (hc 1 1)))),
    fun t => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)),
    continuous_const.mul (h1.comp ((h2.mul continuous_id).mul continuous_const)), by simp, ?_⟩
  intro g y y' r r' t hy
  set G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) := (HA.mat R σ J g).1 with hG
  have hk : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := (show HR R σ J from g).2
  have hact : ∀ u v, hR R σ J (G *ᵥ u) (G *ᵥ v) = hR R σ J u v := fun u v => by
    rw [hR, hform_mulVec, hk, hR]
  have hy0 : y 0 = G *ᵥ (fun i => inclR R (x 0 i)) := by rw [← hy]; rfl
  set z := pairOf R σ J B y g y' 1 with hz
  have hz0 : z = G *ᵥ (B.map (inclR (F := F) R) *ᵥ y' 0) := rfl
  have e00 : hR R σ J (y 0) (y 0) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [hy0, hact, hR_rat, hx, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have e01 : hR R σ J (y 0) z = 0 := by
    rw [hy0, hz0, hact, hR, hform_mulVec_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hR_rat σ R J (x 0) (fun i => B i j)
    rw [hB, map_zero] at this
    exact mul_eq_zero_of_left this _
  have hJs : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have e10 : hR R σ J z (y 0) = 0 := by
    rw [hR, hform_symm _ _ (sigR_sigR σ R h) hJs, ← hR, e01, map_zero]
  have e11 : hR R σ J z z = hR R σ J' (y' 0) (y' 0) := by
    rw [hz0, hact, hR, hform_mulVec, JR_cT, ← hJ', hR]
  have lin : ∀ p q u v : R ⊗[F] E, hR R σ J (p • y 0 + q • z) (u • y 0 + v • z) =
      sigR R σ p * u * algebraMap R (R ⊗[F] E) (algebraMap F R a) +
        sigR R σ q * v * hR R σ J' (y' 0) (y' 0) := by
    intro p q u v
    rw [hR, hform_lin, ← hR, ← hR, ← hR, ← hR, e00, e01, e10, e11]
    ring
  have f0 : algebraMap R (R ⊗[F] E) r • y 0 =
      algebraMap R (R ⊗[F] E) r • y 0 + (0 : R ⊗[F] E) • z := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show qR R σ J (algebraMap R (R ⊗[F] E) r • y 0) = r * r * algebraMap F R a
    rw [qR, f0, lin, sigR_alg, mul_zero, zero_mul, add_zero, ← map_mul, ← map_mul, half_trace σ R h]
  · show hR R σ J (algebraMap R (R ⊗[F] E) r • y 0) (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t
    rw [f0, lin, sigR_alg, map_zero, map_mul]
    ring
  · show qR R σ J (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)) + r' * r' * qR R σ J' (y' 0)
    rw [qR, lin, sigR_alg, ← map_mul, ← Algebra.smul_def (r' * r'), map_add (f := _), map_smul, qR, smul_eq_mul]
    ring

end GlobalTheory.GaugeEx.GramPair
end

section

noncomputable section

namespace GlobalTheory.GaugeEx.StdExist

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

def coordHomeo {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (R ⊗[F] E) ≃ₜ (Fin d → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact isCompact_iff_compactSpace.2 this

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem intV_eq {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    intV b v = coordHomeo b (Fv F v) ⁻¹'
      (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext y
  simp only [intV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

theorem isCompact_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (intV b v) := by
  rw [intV_eq, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_integers v

theorem isOpen_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (intV b v) := by
  rw [intV_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers v).preimage
    (coordHomeo b (Fv F v)).continuous

def intK (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (Fv F v) where
  carrier := v.adicCompletionIntegers F
  isCompact' := isCompact_integers v
  interior_nonempty' := by
    rw [(isOpen_integers v).interior_eq]
    exact ⟨0, zero_mem _⟩

def intVK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    TopologicalSpace.PositiveCompacts (Fv F v ⊗[F] E) where
  carrier := intV b v
  isCompact' := isCompact_intV b v
  interior_nonempty' := by
    rw [(isOpen_intV b v).interior_eq]
    exact ⟨0, fun k => by simp⟩

theorem nonempty_stdMeas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) : Nonempty (StdMeas b) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  exact ⟨{
    lamI := Measure.addHaar
    lamV := fun v => Measure.addHaarMeasure (intVK b v)
    nuI := Measure.addHaar
    nuV := fun v => Measure.addHaarMeasure (intK v)
    haar_lamI := inferInstance
    haar_lamV := fun v => inferInstance
    haar_nuI := inferInstance
    haar_nuV := fun v => inferInstance
    lamV_int := fun v => Measure.addHaarMeasure_self (K₀ := intVK b v)
    nuV_int := fun v => Measure.addHaarMeasure_self (K₀ := intK v) }⟩

end GlobalTheory.GaugeEx.StdExist
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibBasic

section General

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {f : V → X} {ν : Measure X} {B : Set X}

theorem lintegral_preimage {fib : X → Measure V} (hf : Measurable f)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ Set.univ := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [Set.indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_mem (by simpa [hv] using hbS) _
  · rw [Set.indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_notMem (by simpa [hv] using hbS) _

theorem finite_on_compacts [T2Space V] [LocallyCompactSpace V] [BorelSpace V]
    {fib : X → Measure V} (h : IsFibreFamily μ f id Set.univ ν B fib) {β : X} (hβ : β ∈ B) :
    IsFiniteMeasureOnCompacts (fib β) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨φ, h1, -, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)
  have hi := (h.2.2 φ φ.continuous hc (Set.subset_univ _)).1 β hβ
  refine lt_of_le_of_lt (measure_mono ?_) (hi.measure_ge_lt_top (ε := 1) one_pos)
  intro v hv
  exact (h1 hv).ge

theorem eq_at [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [BorelSpace V]
    [BorelSpace X] [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {fib fib' : X → Measure V} (hf : Measurable f) (hB : IsOpen B)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (h' : IsFibreFamily μ f id Set.univ ν B fib')
    {β : X} (hβ : β ∈ B) : fib β = fib' β := by
  haveI := finite_on_compacts h hβ
  haveI := finite_on_compacts h' hβ
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun g => ?_
  set φ : V → ℝ := fun v => (g v : ℝ) with hφdef
  have hφ : Continuous φ := NNReal.continuous_coe.comp g.continuous
  have hc : HasCompactSupport φ := HasCompactSupport.comp_left g.hasCompactSupport rfl
  have h0 : ∀ v, 0 ≤ φ v := fun v => (g v).2
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (Set.subset_univ _)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (Set.subset_univ _)
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[ν.restrict B]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable hB.measurableSet)
      (c'.aemeasurable hB.measurableSet) fun S hS _ => ?_
    rw [Measure.restrict_restrict hS,
      ← lintegral_preimage hf h _ hφm _ (hS.inter hB.measurableSet),
      ← lintegral_preimage hf h' _ hφm _ (hS.inter hB.measurableSet)]
  have e := Measure.eqOn_open_of_ae_eq hae hB c c' hβ
  simp only at e
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβ) (Filter.Eventually.of_forall h0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβ) (Filter.Eventually.of_forall h0)] at e
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) (integral_nonneg h0)).1 e

end General

theorem continuous_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem fibAt_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J μ ν β m hν hβ hm
  obtain ⟨fib, h, rfl⟩ := hm
  haveI := hN.2.2.1
  have hB : IsOpen {c : R | IsUnit c} :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
  refine ⟨?_, finite_on_compacts h hβ, ?_⟩
  · refine measure_mono_null ?_ (h.1 β)
    intro X hX hX'
    exact hX hX'.1
  · rintro m' ⟨fib', h', rfl⟩
    exact eq_at (continuous_qR σ R J).measurable hB h' h hβ

end GlobalTheory.GaugeEx.FibBasic
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Filter
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeEx

theorem continuous_distribHaarChar_units (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] :
    Continuous (fun u : Rˣ => distribHaarChar R u) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hup : ∀ c : ℝ≥0, 1 < c → ∃ V ∈ 𝓝 (1 : R), ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u < c := by
    intro c hc
    have hlt : μ K < (c : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < _ := (ENNReal.mul_lt_mul_iff_left h0 ht).2 (by exact_mod_cast hc)
    obtain ⟨U, hKU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hKc hUo hKU
    refine ⟨V, hV, fun u hu => ?_⟩
    have h1 : μ (u • K) ≤ μ U := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u K] at h1
    have h3 := (ENNReal.mul_lt_mul_iff_left h0 ht).1 (h1.trans_lt hU)
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  rw [ContinuousAt, map_one, tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      exact Eventually.of_forall fun u => distribHaarChar_pos
    have hap : 0 < a := pos_iff_ne_zero.2 ha0
    obtain ⟨V, hV, h⟩ := hup a⁻¹ ((one_lt_inv₀ hap).2 ha)
    have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
      Units.continuous_coe_inv.continuousAt.eventually
        (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
    filter_upwards [e2] with u hu
    have := h _ hu
    rw [map_inv] at this
    exact (inv_lt_inv₀ distribHaarChar_pos hap).1 this
  · intro c hc
    obtain ⟨V, hV, h⟩ := hup c hc
    have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
      Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
    filter_upwards [e1] with u hu using h u hu

theorem modu_units (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [LocallyCompactSpace S] (u : Sˣ) : modu S (u : S) = distribHaarChar S u := by
  simp [modu]

theorem modu_basic : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], (∀ u : S, IsUnit u → 0 < modu S u ∧ ∀ ν : Measure S, ν.IsAddHaarMeasure → ν = modu S u • ν.map (fun z => u * z)) ∧ (∀ u w : S, IsUnit u → IsUnit w → modu S (u * w) = modu S u * modu S w) ∧ modu S 1 = 1 ∧ (IsOpenUnits S → ContinuousOn (modu S) {u | IsUnit u}) := by
  intro S _ _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [modu_units]
    refine ⟨distribHaarChar_pos, fun ν hν => ?_⟩
    ext s hs
    have e : (fun z : S => (u : S) * z) ⁻¹' s = u⁻¹ • s := by
      ext z
      rw [Set.mem_inv_smul_set_iff]; rfl
    rw [Measure.smul_apply, Measure.map_apply (measurable_const_mul _) hs, e, ENNReal.smul_def,
      smul_eq_mul, distribHaarChar_mul, smul_inv_smul]
  · rintro _ _ ⟨u, rfl⟩ ⟨w, rfl⟩
    rw [← Units.val_mul, modu_units, modu_units, modu_units, map_mul]
  · rw [← Units.val_one, modu_units, map_one]
  · intro hS
    rintro _ ⟨u, rfl⟩
    have hoe : IsOpenEmbedding (Units.val : Sˣ → S) := IsOpenUnits.isOpenEmbedding_unitsVal
    refine ContinuousAt.continuousWithinAt ?_
    rw [← hoe.continuousAt_iff]
    have : modu S ∘ Units.val = fun u : Sˣ => distribHaarChar S u := funext (modu_units S)
    rw [this]
    exact (continuous_distribHaarChar_units S).continuousAt

end GlobalTheory.GaugeEx
end
