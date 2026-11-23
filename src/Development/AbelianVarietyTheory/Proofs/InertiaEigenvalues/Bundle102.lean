module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle068
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem eventually_isUnit_and_tendsto_inverse_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [NormedCommRing R] [NormedAlgebra F R] [Module.Finite F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  have : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩
  have h := (NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto
  simpa using h

theorem eventually_isUnit_and_tendsto_inverse (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  classical
  have hτ : τ = moduleTopology F R := eq_moduleTopology F R
  let b := Module.finBasis F R
  let : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing R := NormedCommRing.induced R _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := @eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›
  have hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R :=
    @finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›
  rw [hτ, ← hN]
  exact key

theorem eventually_testFn_mul_inverse_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  intro F E _ _ _ _ hU A φ' hφ a ha
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : CompleteSpace F := inferInstance
  obtain ⟨hunit, hinv⟩ := eventually_isUnit_and_tendsto_inverse F A.K
  have hC : IsCompact (tsupport φ') := hφ.2
  have H1 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q ∈ tsupport φ', φ' (q.1 * w, q.2) = φ' q := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    have hc : Tendsto (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) (𝓝 (1, p)) (𝓝 p) := by
      have : Continuous (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) := by fun_prop
      simpa using this.tendsto (1, p)
    have hl : ∀ᶠ q in 𝓝 p, φ' q = φ' p := hφ.1.eventually_eq p
    have h2 : Tendsto (fun z : A.K × (A.K × A.K) => z.2) (𝓝 (1, p)) (𝓝 p) := continuous_snd.tendsto _
    filter_upwards [hc.eventually hl, h2.eventually hl] with z hz1 hz2
    exact hz1.trans hz2.symm
  have H2 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q : A.K × A.K, φ' (q.1 * w, q.2) = φ' q := by
    filter_upwards [hunit, hinv.eventually H1, H1] with w hw hw' h1 q
    by_cases hq : q ∈ tsupport φ'
    · exact h1 q hq
    by_cases hq' : (q.1 * w, q.2) ∈ tsupport φ'
    · have := hw' _ hq'
      simp only [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hq, image_eq_zero_of_notMem_tsupport hq']
  have hT : Tendsto (fun s : A.K => Ring.inverse a * s) (𝓝 a) (𝓝 1) := by
    have : Continuous (fun s : A.K => Ring.inverse a * s) := by fun_prop
    simpa [Ring.inverse_mul_cancel a ha] using this.tendsto a
  filter_upwards [hT.eventually H2] with s hs t _
  have := hs (a * Ring.inverse t, t)
  have e : a * Ring.inverse t * (Ring.inverse a * s) = s * Ring.inverse t := by
    calc a * Ring.inverse t * (Ring.inverse a * s) = (a * Ring.inverse a) * s * Ring.inverse t := by ring
      _ = s * Ring.inverse t := by rw [Ring.mul_inverse_cancel a ha, one_mul]
  simpa [e] using this

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKFub

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem secondCountableK [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem stdChar_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem psiK_continuous (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) :=
  (stdChar_continuous ψ hψ).comp (IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K))

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (x y : A.K) : A.psiK ψ (x + y) = A.psiK ψ x * A.psiK ψ y := by
  simp only [Et.psiK, map_add (f := _), AddChar.map_add_eq_mul]

theorem fourK_eq_fourB_tilde : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → ∀ b c : A.K, A.fourK μK ψ φ' (b, c) = fourB μK (A.kerK ψ) (fun c' => A.tilde μK ψ φ' c' c) b := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ b c
  haveI := secondCountableK A
  have hc := psiK_continuous A ψ hψ
  let f : A.K × A.K → ℂ := fun p => φ' p * A.psiK ψ (b * p.2 + p.1 * c)
  have hf : Integrable f (μK.prod μK) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hφ.1.continuous.mul (hc.comp (by fun_prop))
    · exact hφ.2.mul_right
  simp only [Et.fourK, fourB, Et.tilde, Et.kerK]
  rw [integral_integral_swap (f := fun b' c' => φ' (b', c') * A.psiK ψ (b * c' + b' * c)) hf]
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
  simp only
  rw [psiK_add, mul_comm b c', mul_comm b' c]
  ring

end GlobalTheory.FourKFub
end
end

section

open GlobalTheory.JR MeasureTheory

theorem GlobalTheory.JR.fourB_prod_iterated : ∀ {V V₁ V₂ : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V₁] [TopologicalSpace V₁] [IsTopologicalAddGroup V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [AddCommGroup V₂] [TopologicalSpace V₂] [IsTopologicalAddGroup V₂] [T2Space V₂] [LocallyCompactSpace V₂] [SecondCountableTopology V₂] [MeasurableSpace V₂] [BorelSpace V₂] (e : V ≃+ V₁ × V₂), Continuous e → Continuous e.symm → ∀ (B : V → V → ℂ) (B₁ : V₁ → V₁ → ℂ) (B₂ : V₂ → V₂ → ℂ), Continuous (fun p : V₁ × V₁ => B₁ p.1 p.2) → Continuous (fun p : V₂ × V₂ => B₂ p.1 p.2) → (∀ y' y, B y' y = B₁ (e y').1 (e y).1 * B₂ (e y').2 (e y).2) → ∀ (μ : Measure V) (μ₁ : Measure V₁) (μ₂ : Measure V₂), μ.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : V → ℂ, IsTest φ → ∀ y, fourB μ B φ y = c * ∫ u, (∫ v, φ (e.symm (u, v)) * B₂ v (e y).2 ∂μ₂) * B₁ u (e y).1 ∂μ₁ := by
  intro V V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e he hes B B₁ B₂ hB₁ hB₂ hB μ μ₁ μ₂ hμ hμ₁ hμ₂
  let h : V ≃ₜ V₁ × V₂ := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let hm : V ≃ᵐ V₁ × V₂ := h.toMeasurableEquiv
  haveI : (Measure.map e μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e he hes
  haveI : (μ₁.prod μ₂).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ₁ μ₂
  set k := Measure.addHaarScalarFactor (Measure.map e μ) (μ₁.prod μ₂) with hk
  have hkeq : Measure.map e μ = k • (μ₁.prod μ₂) := Measure.isAddLeftInvariant_eq_smul _ _
  have hkpos : 0 < k := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨((k : ℝ) : ℂ), by exact_mod_cast hkpos.ne', fun φ hφ y => ?_⟩
  have hmap : Measure.map hm μ = Measure.map e μ := rfl
  have step1 : fourB μ B φ y = ∫ q, φ (e.symm q) * B (e.symm q) y ∂(Measure.map e μ) := by
    rw [← hmap, hm.measurableEmbedding.integral_map]
    simp [fourB, hm, h]
  rw [step1, hkeq, integral_smul_nnreal_measure]
  have hcont : Continuous fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) :=
    (hφ.1.continuous.comp hes).mul ((hB₁.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.1, (e y).1))).mul
      (hB₂.comp (by fun_prop : Continuous fun q : V₁ × V₂ => (q.2, (e y).2))))
  have hsupp : HasCompactSupport fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    have : HasCompactSupport (φ ∘ h.symm) := hφ.2.comp_homeomorph h.symm
    exact this.mul_right
  have hint := hcont.integrable_of_hasCompactSupport hsupp (μ := μ₁.prod μ₂)
  have e2 : (fun q : V₁ × V₂ => φ (e.symm q) * B (e.symm q) y) =
      fun q : V₁ × V₂ => φ (e.symm q) * (B₁ q.1 (e y).1 * B₂ q.2 (e y).2) := by
    ext q; rw [hB]; simp
  rw [e2, integral_prod _ hint]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1; ext v; ring
end

section

open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.LagIdem

variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]

noncomputable def lagPoly (a : ι → R) (i : ι) : R[X] :=
  C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) *
    ∏ j ∈ Finset.univ.erase i, (X - C (a j))

end GlobalTheory.LagIdem

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_eq_zero_of_dvd_of_aeval_eq_zero {M : E} {p q : R[X]} (hp : aeval M p = 0) (h : p ∣ q) :
    aeval M q = 0 := by
  obtain ⟨r, rfl⟩ := h
  simp [hp]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
private lemma prod_X_sub_C_dvd_sum_lagPoly_sub_one :
    ∏ j, (X - C (a j)) ∣ ∑ i, _root_.GlobalTheory.LagIdem.lagPoly a i - 1 := by
  refine Fintype.prod_dvd_of_coprime
    (fun i j hij => isCoprime_X_sub_C_of_isUnit_sub (hu i j hij)) fun k => ?_
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_one, eval_finsetSum, sub_eq_zero,
    Finset.sum_eq_single k]
  · simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact Ring.inverse_mul_cancel _
      (IsUnit.prod_iff.mpr fun j hj => hu k j (Finset.ne_of_mem_erase hj).symm)
  · intro i _ hik
    simp only [_root_.GlobalTheory.LagIdem.lagPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩) (sub_self _))
  · intro h
    exact absurd (Finset.mem_univ k) h

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma aeval_lagPoly_eq_lagIdem (M : E) (a : ι → R) (i : ι) :
    aeval M (_root_.GlobalTheory.LagIdem.lagPoly a i) = _root_.GlobalTheory.Pat.lagIdem M a i := by
  simp [_root_.GlobalTheory.LagIdem.lagPoly, _root_.GlobalTheory.Pat.lagIdem, Algebra.smul_def]

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma prod_X_sub_C_eq_mul_prod_erase (a : ι → R) (i : ι) :
    ∏ j, (X - C (a j)) = (X - C (a i)) * ∏ j ∈ Finset.univ.erase i, (X - C (a j)) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
variable (a : ι → R) (hu : ∀ i j, i ≠ j → IsUnit (a i - a j)) in
include hu in
omit hu in
private lemma prod_X_sub_C_dvd_lagPoly_mul_of_ne {i j : ι} (hij : i ≠ j) :
    ∏ l, (X - C (a l)) ∣ _root_.GlobalTheory.LagIdem.lagPoly a i * _root_.GlobalTheory.LagIdem.lagPoly a j := by
  rw [prod_X_sub_C_eq_mul_prod_erase a i]
  have h : X - C (a i) ∣ ∏ l ∈ Finset.univ.erase j, (X - C (a l)) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  obtain ⟨q, hq⟩ := h
  refine ⟨C (Ring.inverse (∏ l ∈ Finset.univ.erase i, (a i - a l))) *
    C (Ring.inverse (∏ l ∈ Finset.univ.erase j, (a j - a l))) * q, ?_⟩
  simp only [_root_.GlobalTheory.LagIdem.lagPoly, hq]
  ring

open TensorProduct Polynomial IsLocalRing in
variable {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] in
private lemma commute_aeval_of_commute' {T M : E} (h : Commute T M) (p : R[X]) :
    Commute T (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact Commute.mul_right (show Commute T (algebraMap R E c) from (Algebra.commutes c T).symm)
      (h.pow_right n)

open TensorProduct Polynomial IsLocalRing in
theorem _root_.GlobalTheory.lagIdem_spec : ∀ (R E ι : Type) [CommRing R]
    [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : E) (a : ι → R),
    (∀ i j, i ≠ j → IsUnit (a i - a j)) → Polynomial.aeval M (∏ j, (X - C (a j))) = 0 →
    CompleteOrthogonalIdempotents (_root_.GlobalTheory.Pat.lagIdem M a) ∧
      (∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i = a i • _root_.GlobalTheory.Pat.lagIdem M a i) ∧
      M = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i ∧
      ∀ (T : E) i, Commute T M → Commute T (_root_.GlobalTheory.Pat.lagIdem M a i) := by
  intro R E ι _ _ _ _ _ _ M a hu hM
  have hsum : ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i = 1 := by
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_sum_lagPoly_sub_one a hu)

    simpa [map_sum, aeval_lagPoly_eq_lagIdem, sub_eq_zero] using h
  have hortho : ∀ i j, i ≠ j →
      _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a j = 0 := by
    intro i j hij
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM (prod_X_sub_C_dvd_lagPoly_mul_of_ne a hij)
    simpa [aeval_lagPoly_eq_lagIdem] using h
  have hidem : ∀ i, IsIdempotentElem (_root_.GlobalTheory.Pat.lagIdem M a i) := by
    intro i
    have h : _root_.GlobalTheory.Pat.lagIdem M a i * ∑ j, _root_.GlobalTheory.Pat.lagIdem M a j =
        _root_.GlobalTheory.Pat.lagIdem M a i * _root_.GlobalTheory.Pat.lagIdem M a i := by
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hji => hortho i j (Ne.symm hji))
        (fun h => absurd (Finset.mem_univ i) h)]
    rw [hsum, mul_one] at h
    exact h.symm
  have heigen : ∀ i, M * _root_.GlobalTheory.Pat.lagIdem M a i =
      a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
    intro i
    have hdvd : ∏ j, (X - C (a j)) ∣ (X - C (a i)) * _root_.GlobalTheory.LagIdem.lagPoly a i := by
      refine ⟨C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))), ?_⟩
      rw [prod_X_sub_C_eq_mul_prod_erase a i, _root_.GlobalTheory.LagIdem.lagPoly]
      ring
    have h := aeval_eq_zero_of_dvd_of_aeval_eq_zero hM hdvd
    rw [map_mul, aeval_lagPoly_eq_lagIdem, map_sub, aeval_X, aeval_C, sub_mul,
      sub_eq_zero, ← Algebra.smul_def] at h
    exact h
  refine ⟨⟨⟨hidem, fun i j hij => hortho i j hij⟩, hsum⟩, heigen, ?_, ?_⟩
  · calc M = M * ∑ i, _root_.GlobalTheory.Pat.lagIdem M a i := by rw [hsum, mul_one]
      _ = ∑ i, a i • _root_.GlobalTheory.Pat.lagIdem M a i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => heigen i
  · intro T i hT
    rw [← aeval_lagPoly_eq_lagIdem]
    exact commute_aeval_of_commute' hT _
end

section

open Polynomial TensorProduct

noncomputable section

namespace GlobalTheory.JR.EtExist

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def conjAlg [h : Unram F E] : E →ₐ[F] E :=
  { starRingEnd E with commutes' := fun x => h.star_fix x }

theorem conjAlg_apply [Unram F E] (y : E) : conjAlg F E y = star y := rfl

variable (K : Type) [CommRing K] [Algebra F K]

def conjT [Unram F E] : E ⊗[F] K →ₐ[F] E ⊗[F] K := Algebra.TensorProduct.map (conjAlg F E) (AlgHom.id F K)

theorem conjT_conjT [Unram F E] (z : E ⊗[F] K) : conjT F E K (conjT F E K z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjT, conjAlg_apply]
  | add a b ha hb => simp [ha, hb]

@[reducible] def starT [Unram F E] : StarRing (E ⊗[F] K) where
  star := conjT F E K
  star_involutive := conjT_conjT F E K
  star_mul a b := by
    change conjT F E K (a * b) = conjT F E K b * conjT F E K a
    rw [map_mul, mul_comm]
  star_add a b := map_add (conjT F E K) a b

theorem locallyCompact_moduleTopology [LocallyCompactSpace F] [Module.Finite F K] :
    @LocallyCompactSpace K (moduleTopology F K) := by
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  let b := (Module.finBasis F K).equivFun
  have h1 : Continuous b := IsModuleTopology.continuous_of_linearMap b.toLinearMap
  haveI : ContinuousAdd K := IsModuleTopology.toContinuousAdd F K
  have h2 : Continuous b.symm := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  let e : K ≃ₜ (Fin (Module.finrank F K) → F) := { b.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  exact e.isClosedEmbedding.locallyCompactSpace

def ofAlgebra [h : Unram F E] [Module.Finite F K] [IsReduced K] : Et F E :=
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[F] K) := moduleTopology F (E ⊗[F] K)
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  { K := K
    L := E ⊗[F] K
    trK := IsModuleTopology.isTopologicalRing F K
    lcK := haveI := h.lcF; locallyCompact_moduleTopology F K
    mK := borel K
    bK := @BorelSpace.mk _ _ (borel K) rfl
    stL := starT F E K
    mtL := ⟨rfl⟩
    mL := borel (E ⊗[F] K)
    bL := @BorelSpace.mk _ _ (borel (E ⊗[F] K)) rfl
    push := inferInstance
    star_K := fun x => by
      change conjT F E K (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [conjT]
    star_E := fun y => by
      change conjT F E K (y ⊗ₜ 1) = star y ⊗ₜ 1
      simp [conjT, conjAlg_apply] }

theorem exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  set P : F[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : F[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite F (AdjoinRoot P) := pb.finite
  haveI : IsReduced (AdjoinRoot P) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      ((isRadical_iff_span_singleton).1 hs.squarefree.isRadical)
  refine ⟨ofAlgebra F E (AdjoinRoot P), AdjoinRoot.root P, ?_, ?_, ?_⟩
  · change LinearIndependent F (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ))
    have := pb.basis.linearIndependent.comp (Fin.cast (show r = pb.dim from hd.symm)) (Fin.cast_injective _)
    have e : (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ)) = pb.basis ∘ Fin.cast (show r = pb.dim from hd.symm) := by
      funext i
      rw [Function.comp_apply, pb.basis_eq_pow]
      rfl
    rw [e]; exact this
  · change Module.finrank F (AdjoinRoot P) = r
    rw [pb.finrank]; exact hd
  · change AdjoinRoot.root P ^ r + ∑ i, p i • AdjoinRoot.root P ^ (i : ℕ) = 0
    have := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at this
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]) = 0 := this

    simp only [map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    simpa only [Algebra.smul_def] using h2

end GlobalTheory.JR.EtExist
end
end

section

open PowerSeries GlobalTheory.BK Filter Topology

theorem _root_.GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  first | exact @GlobalTheory.BK.frob_recursion_decay | exact GlobalTheory.BK.frob_recursion_decay | (intros; apply GlobalTheory.BK.frob_recursion_decay <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Filter Topology

theorem _root_.GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := by
  first | exact @GlobalTheory.mem_R_of_adic_limit | exact GlobalTheory.mem_R_of_adic_limit | (intros; apply GlobalTheory.mem_R_of_adic_limit <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  first | exact @GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | exact GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall | (intros; apply GlobalTheory.CoeffComplete.completeSpace_of_finite_unitBall <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_prime_pow_kills_finiteLength_integralPowerSeries : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (Mo : Type) [AddCommGroup Mo] [Module (A O K) Mo], IsFiniteLength (A O K) Mo → ∃ m : ℕ, ∀ q : Mo, ((l : A O K) ^ m) • q = 0 := by
  first | exact @GlobalTheory.PowKill.main | exact GlobalTheory.PowKill.main | (intros; apply GlobalTheory.PowKill.main <;> assumption)
end
