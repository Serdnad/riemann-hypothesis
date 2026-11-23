module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle061
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle170
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JHypEquiv

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem secondCountable_K [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem t2Space_K (A : Et F E) : T2Space A.K := by
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).symm.t2Space

theorem row_one (A : Et F E) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K) (j : Fin 2) :
    (nS z * mS s * g) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g 1 j := by
  show ((nS z).1 * (mS s).1 * g.1) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g.1 1 j
  simp [nS, mS, Matrix.mul_apply, Fin.sum_univ_two]

theorem absK_unit (A : Et F E) (s : A.Kˣ) : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
  unfold Et.absK
  rw [dite_eq_left s.isUnit]
  congr 2
  exact Units.ext (IsUnit.unit_spec _)

theorem integral_inv_mul [Unram F E] (A : Et F E) (μK : Measure A.K) [μK.IsAddHaarMeasure] (s : A.Kˣ)
    (H : A.K → ℂ) :
    ∫ t, H (((s⁻¹ : A.Kˣ) : A.K) * t) ∂μK = (distribHaarChar A.K s : ℝ) * ∫ u, H u ∂μK := by
  haveI := secondCountable_K A
  haveI := t2Space_K A
  have hmap : μK.map (fun x => (s⁻¹ : A.Kˣ) • x) = (distribHaarChar A.K s : ENNReal) • μK := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul _) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul, inv_inv]
  have e := integral_map_equiv (MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K) (μ := μK) H
  rw [show (⇑(MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K)) = fun x => (s⁻¹ : A.Kˣ) • x from rfl, hmap,
    integral_smul_measure] at e
  rw [show (fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t)) = fun t => H ((s⁻¹ : A.Kˣ) • t) from rfl, ← e]
  simp [Complex.real_smul]

theorem etaK_mul [Unram F E] (A : Et F E) (s : A.Kˣ) (u : A.K) (hu : IsUnit u) :
    A.etaK ((s : A.K) * u) = A.etaK s * A.etaK u := by
  unfold Et.etaK
  rw [map_mul]
  exact (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ (s.isUnit.map (Algebra.norm F)).ne_zero (hu.map (Algebra.norm F)).ne_zero

theorem jHyp_nm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ)
    (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K),
    A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  intro F E _ _ _ _ _ A μK hμ ψ φ' z s g
  haveI := hμ
  unfold Et.jHyp
  simp only [row_one]
  set H : A.K → ℂ := fun u => A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK ((s : A.K) * u) with hH
  have h1 : (fun t => A.tilde μK ψ φ' (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 0)) (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 1)) *
      A.etaK t) = fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t) := by
    funext t
    simp only [hH]
    rw [Units.mul_inv_cancel_left]
    congr 2 <;> ring
  rw [h1, integral_inv_mul A μK s H]
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ u ∂μK, IsUnit u := ae_iff.mpr hnull
  have h2 : ∫ u, H u ∂μK = ∫ u, A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK u * A.etaK s ∂μK := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hH]
    rw [etaK_mul A s u hu]
    ring
  rw [h2, integral_mul_const, absK_unit]
  ring

end GlobalTheory.JHypEquiv
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (u v : A.K) :
    A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
  unfold psiK
  rw [map_add (f := _), AddChar.map_add_eq_mul]

theorem psiK_continuous (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) := by
  have h1 : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact (DualLattice.stdChar_continuous hψ).comp h1

theorem NL_continuous [Unram F E] (A : Et F E) : Continuous A.NL := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [this]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hlin : Continuous (((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F) :=
    IsModuleTopology.continuous_of_linearMap _
  convert hlin using 1
  funext y
  simp [Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.Et

namespace GlobalTheory.JR.Et

theorem whittaker_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  intro F E _ _ _ _ _ A ψ hψ μK _ μ _ φ hφ x a c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  set M : Set A.K := {z : A.K | c • z ∈ A.OK} with hMdef
  have hOKclosed : IsClosed A.OK := by
    have : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by
      change IsOpen (R : Set A.K); rw [hR]; exact hOpen
    have h2 := AddSubgroup.isClosed_of_isOpen _ this
    change IsClosed (R : Set A.K) at h2
    rwa [hR] at h2
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMopen : IsOpen M := hOpen.preimage hsm
  have hMclosed : IsClosed M := hOKclosed.preimage hsm
  have hMcpt : IsCompact M := by
    have : M = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        change c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]
    exact hCpt.image (continuous_const_smul _)
  have hMmeas : MeasurableSet M := hMopen.measurableSet
  let g : A.K → A.L → ℂ := fun z y => φ y * A.psiK ψ (z * (x * A.NL y - a))
  let f : A.K → A.L → ℂ := fun z y => M.indicator (fun _ => (1 : ℂ)) z * g z y
  have hpt : ∀ z y, φ y * A.psiK ψ (z * x * A.NL y) * A.psiK ψ (-(a * z)) = g z y := by
    intro z y
    simp only [g]
    rw [mul_assoc, ← psiK_add]
    congr 2
    ring
  have hL : ∀ z, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) = ∫ y, g z y ∂μ := by
    intro z
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => hpt z y)
  have hind : ∀ (h : A.K → ℂ) z, M.indicator (fun _ => (1 : ℂ)) z * h z = M.indicator h z := by
    intro h z
    by_cases hz : z ∈ M <;> simp [hz]
  have hcontI : Continuous (M.indicator (fun _ : A.K => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hMclosed, hMopen⟩ continuous_const
  have hφc : Continuous φ := hφ.1.continuous
  have hcont : Continuous (Function.uncurry f) := by
    have hN := A.NL_continuous
    have hP := A.psiK_continuous hψ
    refine (hcontI.comp continuous_fst).mul ((hφc.comp continuous_snd).mul (hP.comp ?_))
    exact continuous_fst.mul (((continuous_const.mul (hN.comp continuous_snd))).sub continuous_const)
  have hsupp : HasCompactSupport (Function.uncurry f) := by
    have hsub : Function.support (Function.uncurry f) ⊆ M ×ˢ tsupport φ := by
      rintro ⟨z, y⟩ hzy
      simp only [Function.mem_support, Function.uncurry_apply_pair, f, g] at hzy
      refine ⟨?_, subset_tsupport _ ?_⟩
      · by_contra hz
        exact hzy (by simp [hz])
      · intro h0
        exact hzy (by simp [h0])
    exact IsCompact.of_isClosed_subset (hMcpt.prod hφ.2) (isClosed_tsupport _)
      (closure_minimal hsub (hMclosed.prod (isClosed_tsupport _)))
  have hswap := integral_integral_swap_of_hasCompactSupport hcont hsupp (μ := μK) (ν := μ)
  calc ∫ z in M, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK
      = ∫ z in M, (∫ y, g z y ∂μ) ∂μK := setIntegral_congr_fun hMmeas (fun z _ => hL z)
    _ = ∫ z, M.indicator (fun z => ∫ y, g z y ∂μ) z ∂μK := (integral_indicator hMmeas).symm
    _ = ∫ z, ∫ y, f z y ∂μ ∂μK := by
      congr 1 with z
      rw [← hind, ← integral_const_mul]
    _ = ∫ y, ∫ z, f z y ∂μK ∂μ := hswap
    _ = ∫ y, φ y * ∫ z in M, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
      congr 1 with y
      rw [← integral_const_mul, ← integral_indicator hMmeas]
      congr 1 with z
      rw [← hind]

end GlobalTheory.JR.Et
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def betaK (A : Et F E) : LinearMap.BilinForm F (A.K × A.K) :=
  (Algebra.traceForm F A.K).compl₁₂ (LinearMap.fst F A.K A.K) (LinearMap.snd F A.K A.K) +
    (Algebra.traceForm F A.K).compl₁₂ (LinearMap.snd F A.K A.K) (LinearMap.fst F A.K A.K)

theorem betaK_apply (A : Et F E) (x y : A.K × A.K) :
    betaK A x y = Algebra.trace F A.K (x.1 * y.2) + Algebra.trace F A.K (x.2 * y.1) := by
  simp [betaK, Algebra.traceForm_apply]

theorem betaK_isSymm (A : Et F E) : (betaK A).IsSymm :=
  ⟨fun x y => by rw [betaK_apply, betaK_apply, mul_comm x.1, mul_comm x.2, add_comm]⟩

theorem betaK_nondeg (A : Et F E) (h : (Algebra.traceForm F A.K).Nondegenerate) : (betaK A).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (betaK A) := by
    intro x hx
    have h1 : x.1 = 0 := h.1 x.1 fun z => by
      have := hx (0, z); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    have h2 : x.2 = 0 := h.1 x.2 fun z => by
      have := hx (z, 0); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    exact Prod.ext h1 h2
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [(betaK_isSymm A).eq]; exact hy x

theorem secondCountable [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem psi_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem fourK_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  haveI := secondCountable A
  haveI : μK.IsAddHaarMeasure := hsd.1
  haveI : (μK.prod μK).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hnd := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have key := (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ (A.K × A.K) (betaK A) (betaK_isSymm A) (betaK_nondeg A hnd)).2
    (μK.prod μK) inferInstance φ' hφ
  have hψc := psi_continuous ψ hψ
  have heq : A.fourK μK ψ φ' = fourB (μK.prod μK) (fun x y => ψ (betaK A x y)) φ' := by
    funext p
    simp only [fourB, Et.fourK]
    rw [integral_prod]
    · refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
      refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
      simp only [Et.psiK, betaK_apply, map_add (f := _)]
      congr 1
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_comm p.1, mul_comm c' p.1]
      ring
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hφ.1.continuous.mul (hψc.comp (IsModuleTopology.continuous_of_linearMap ((betaK A).flip p)))
      · exact hφ.2.mul_right
  rw [heq]; exact key

end GlobalTheory.FourKTest
end
end

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat, Nat.padicValNat_def]

theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

open GlobalTheory.BK in
theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.charpoly_overExt_integral_reduction_pow : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  first | exact @GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | exact GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction | (intros; apply GlobalTheory.UnitLemma.Unr.charpoly_overExt_integral_reduction <;> assumption)
end
