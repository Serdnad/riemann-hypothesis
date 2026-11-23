module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle120
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle132
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle133
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle139
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem mulMat_comm (A : Et F E) {r : ℕ} (τ : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : Matrix (Fin r) (Fin r) E)
    (hA : ∀ z, j (algebraMap A.K A.L τ * z) = Ax *ᵥ j z) (t : A.L) :
    Ax * A.mulMat j t = A.mulMat j t * Ax := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Et.mulMat_mulVec_apply, ← hA]
  congr 1; ring

theorem actU_actU {r : ℕ} (g h : unitaryGroup (Fin r) E) (X : Hn r F E) :
    actU g (actU h X) = actU (g * h) X := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show g.1 * (h.1 * X.1.1 * star h.1) * star g.1 = (g.1 * h.1) * X.1.1 * star (g.1 * h.1)
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show g.1 *ᵥ (h.1 *ᵥ X.2.1) = (g.1 * h.1) *ᵥ X.2.1
    rw [Matrix.mulVec_mulVec]

end GlobalTheory.JR.DescOrb

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_mulMat [hU : Unram F E] (A : Et F E) {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous fun t : A.L => A.mulMat j t := by
  haveI := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hj : Continuous (j : A.L → Fin r → E) :=
    IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  refine continuous_matrix fun i k => ?_
  simp only [Et.mulMat, LinearMap.toMatrix'_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe]
  exact (continuous_apply i).comp (hj.comp (continuous_id.mul continuous_const))

theorem orbL_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  intro F E _ _ _ _ hU A r M τ x j hx Ax hA lam ν hν α hα hα0 Z hZ f₀ hf₀ hf₀Z y hint
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE; haveI := hU.lcE; haveI := hU.ultraF; haveI := hU.lcF
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  haveI : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  haveI : LocallyCompactSpace (unitary A.L) := (isClosed_unitary (R := A.L)).locallyCompactSpace
  haveI : SecondCountableTopology (unitary A.L) :=
    (isClosed_unitary (R := A.L)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite M.μU := inferInstance
  haveI : M.μU.IsMulRightInvariant := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  have huc : Continuous (A.uHom hx) := continuous_induced_rng.2 ((continuous_mulMat A j).comp continuous_subtype_val)
  have hinvc : Continuous fun g : unitaryGroup (Fin r) E => g⁻¹ := continuous_inv

  set X : Hn r F E := (Ax, j y, lam) with hXdef
  have hcomm : ∀ t : unitary A.L, ((A.uHom hx t : Matrix (Fin r) (Fin r) E)) * Ax.1 = Ax.1 * A.uHom hx t := fun t =>
    (mulMat_comm A τ j Ax.1 hA t).symm
  have hshift : ∀ t : unitary A.L, ((Ax, j (t.1 * y), lam) : Hn r F E) = actU (A.uHom hx t) X := by
    intro t
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
    · show Ax.1 = (A.uHom hx t : Matrix (Fin r) (Fin r) E) * Ax.1 * star (A.uHom hx t : Matrix (Fin r) (Fin r) E)
      rw [hcomm, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (A.uHom hx t).2, Matrix.mul_one]
    · show j (t.1 * y) = (A.uHom hx t : Matrix (Fin r) (Fin r) E) *ᵥ j y
      rw [Et.uHom_apply, Et.mulMat_mulVec_apply]
  have step1 : ∀ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) =
      ∫ g, f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ) ∂M.μU := by
    intro t
    have h := integral_mul_right_eq_self (μ := M.μU)
      (fun g => f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (A.uHom hx t)
    simp only [mul_inv_cancel_right] at h
    rw [← h]
    show (∫ g, f₀ (actU g ((Ax, j (t.1 * y), lam) : Hn r F E)) * (α g : ℂ) ∂M.μU) = _
    simp only [hshift t, actU_actU]
  have hact : Continuous fun g : unitaryGroup (Fin r) E => actU g X := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact (((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        (continuous_subtype_val.star))).subtype_mk _
    · exact continuous_subtype_val.matrix_mulVec continuous_const
  have hcont : Continuous (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) :=
    (hf₀.comp (hact.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
      (hα.continuous.comp (continuous_snd.mul (hinvc.comp (huc.comp continuous_fst)))))
  have hαint : ∀ g : unitaryGroup (Fin r) E, f₀ (actU g X) ≠ 0 →
      Integrable (fun t => α (g * (A.uHom hx t)⁻¹)) ν := by
    intro g hg
    by_contra hn
    have h1 := integral_undef hn
    rw [hZ g (hf₀Z _ hg)] at h1
    exact one_ne_zero h1
  have hInt : Integrable (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (ν.prod M.μU) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : f₀ (actU g X) = 0
      · simp [Function.uncurry, hg]
      · exact ((hαint g hg).ofReal).const_mul (f₀ (actU g X))
    · refine hint.norm.congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul]
      by_cases hg : f₀ (actU g X) = 0
      · simp [hg]
      · rw [integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hα0 _)), hZ g (hf₀Z _ hg), mul_one]
  show ∫ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) ∂ν = ∫ g, f₀ (actU g X) ∂M.μU
  simp_rw [step1]
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hg : f₀ (actU g X) = 0
  · simp [hg]
  · rw [hZ g (hf₀Z _ hg)]; simp

end GlobalTheory.JR.DescOrb
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  first | exact @GlobalTheory.JR.Hyp.pt_pt_eq_reflect | exact GlobalTheory.JR.Hyp.pt_pt_eq_reflect | (intros; apply GlobalTheory.JR.Hyp.pt_pt_eq_reflect <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  first | exact @GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | exact GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | (intros; apply GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  first | exact @GlobalTheory.JR.Hyp.isTest_coord | exact GlobalTheory.JR.Hyp.isTest_coord | (intros; apply GlobalTheory.JR.Hyp.isTest_coord <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.quadraticWeilTorus_mul_unipotent_commute : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ), mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  first | exact @GlobalTheory.JR.WeilQuad.mOp_nOp | exact GlobalTheory.JR.WeilQuad.mOp_nOp | (intros; apply GlobalTheory.JR.WeilQuad.mOp_nOp <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.idempotentCoordinates_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  first | exact @GlobalTheory.JR.Hyp.coord_structure | exact GlobalTheory.JR.Hyp.coord_structure | (intros; apply GlobalTheory.JR.Hyp.coord_structure <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  first | exact @GlobalTheory.JR.Hyp.isTest_ops | exact GlobalTheory.JR.Hyp.isTest_ops | (intros; apply GlobalTheory.JR.Hyp.isTest_ops <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual | exact GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_stable_of_dual <;> assumption)
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem isLocallyConstant_of_stdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : IsLocallyConstant ψ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  filter_upwards [Metric.closedBall_mem_nhds a one_pos] with b hb
  have h1 : ψ (b - a) = 1 := hψ.1 _ (by simpa [Metric.mem_closedBall, dist_eq_norm] using hb)
  calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
    _ = ψ a := by rw [AddChar.map_add_eq_mul, h1, mul_one]

theorem continuous_mulLeft (A : Et F E) (c : A.L) : Continuous fun y : A.L => c * y := by
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  exact IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft F c)

def smulHomeo (A : Et F E) (s : A.Kˣ) : A.L ≃ₜ A.L where
  toFun y := (s : A.K) • y
  invFun y := ((s⁻¹ : A.Kˣ) : A.K) • y
  left_inv y := by simp [smul_smul]
  right_inv y := by simp [smul_smul]
  continuous_toFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _
  continuous_invFun := by
    simp only [Algebra.smul_def]; exact continuous_mulLeft A _

theorem isTest_nOp [Unram F E] (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (x z : A.K) {φ : A.L → ℂ}
    (hφ : IsTest φ) : IsTest (nOp A ψ x z φ) := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun y : A.L => Algebra.trace F A.K (z * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hl : IsLocallyConstant fun y : A.L => A.psiK ψ (z * x * A.NL y) :=
    (isLocallyConstant_of_stdChar hψ).comp_continuous hc
  exact ⟨hl.mul hφ.1, hφ.2.mul_left⟩

theorem isTest_mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) {φ : A.L → ℂ} (hφ : IsTest φ) :
    IsTest (mOp A ω s φ) := by
  have h1 : IsTest (φ ∘ smulHomeo A s) :=
    ⟨hφ.1.comp_continuous (smulHomeo A s).continuous, hφ.2.comp_homeomorph _⟩
  exact ⟨(IsLocallyConstant.const (ω s * (A.absK s : ℂ))).mul h1.1, h1.2.mul_left⟩

theorem isTest_nOp_mOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → (∀ z, IsTest (nOp A ψ x z φ)) ∧ ∀ s, IsTest (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  exact ⟨fun z => isTest_nOp A h.2.2.1 x z hφ, fun s => isTest_mOp A ω s hφ⟩

end GlobalTheory.JR.WeilQuad
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem _root_.GlobalTheory.T.alternatingDifference_term_window : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ I I' : Finset ι, I ⊆ S → I' ⊆ S → (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N : ℕ) (x s : B.A), IsUnit x → IsUnit s → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ k : ℕ, L ≤ k → ∀ (M : Submodule K.O B.A) (p : ι → ℤ), Pos B a e N M p → (term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M ≠ 0 → Win I I' L k p) ∧ (Win I I' L k p → Mid S L k p → term B π I I' (x * algebraMap K.O B.A a ^ (2 * k)) s M = term B π I I' (eS B e I * (x * algebraMap K.O B.A a ^ (2 * k))) (eS B e I' * s) M) := by
  first | exact @GlobalTheory.UnitLemma.Desc.term_window | exact GlobalTheory.UnitLemma.Desc.term_window | (intros; apply GlobalTheory.UnitLemma.Desc.term_window <;> assumption)
end

section

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc.PosCount

section Idem

variable {ι : Type} [Fintype ι] {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem sum_smul_mul_idem {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (i : ι) (x : A) :
    (∑ j, c j • e j) * (e i * x) = c i • (e i * x) := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, ← mul_assoc, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_assoc, ← mul_assoc, he.ortho hj, zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_smul_mul {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (x : A) :
    (∑ j, c j • e j) * x = ∑ i, c i • (e i * x) := by
  calc (∑ j, c j • e j) * x = (∑ j, c j • e j) * (∑ i, e i * x) := by
        rw [← Finset.sum_mul, he.complete, one_mul]
    _ = ∑ i, (∑ j, c j • e j) * (e i * x) := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun i _ => sum_smul_mul_idem he c i x

theorem sum_smul_mul_cancel {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c c' : ι → R)
    (h : ∀ i, c' i * c i = 1) (x : A) : (∑ j, c' j • e j) * ((∑ j, c j • e j) * x) = x := by
  rw [sum_smul_mul he c x, Finset.mul_sum]
  calc ∑ i, (∑ j, c' j • e j) * (c i • (e i * x)) = ∑ i, e i * x :=
        Finset.sum_congr rfl fun i _ => by
          rw [mul_smul_comm, sum_smul_mul_idem he, smul_smul, mul_comm, h, one_smul]
    _ = x := by rw [← Finset.sum_mul, he.complete, one_mul]

end Idem

variable (K : UQ) (B : InvAlg K)

def Sandwich (a : K.O) (N : ℕ) : Set (Submodule K.O B.A) :=
  {M | (∀ r : B.A, IsIntegral K.O r → a ^ N • r ∈ M) ∧ ∀ m ∈ M, IsIntegral K.O m}

theorem finite_quotient_span_pow {a : K.O} (ha : a ≠ 0) (N : ℕ) :
    Finite (K.O ⧸ Ideal.span {a ^ N}) := by
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k * N, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton, mul_pow,
    ← Units.val_pow_eq_pow_val, Units.mul_left_dvd, ← pow_mul]

theorem sandwich_finite (hR : (Subalgebra.toSubmodule (integralClosure K.O B.A)).FG) {a : K.O} (ha : a ≠ 0)
    (N : ℕ) : (Sandwich K B a N).Finite := by
  set R := Subalgebra.toSubmodule (integralClosure K.O B.A) with hRdef
  haveI : Module.Finite K.O R := Module.Finite.iff_fg.mpr hR
  set I : Ideal K.O := Ideal.span {a ^ N}
  haveI := finite_quotient_span_pow K ha N
  set P : Submodule K.O R := I • (⊤ : Submodule K.O R)
  haveI : Module.Finite (K.O ⧸ I) (R ⧸ P) := Module.Finite.of_restrictScalars_finite K.O _ _
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (K.O ⧸ I)
  haveI : Finite (Submodule K.O (R ⧸ P)) :=
    Finite.of_injective (fun Q : Submodule K.O (R ⧸ P) => (Q : Set (R ⧸ P))) SetLike.coe_injective
  let Φ : Submodule K.O B.A → Submodule K.O (R ⧸ P) := fun M => (M.comap R.subtype).map P.mkQ
  have key : ∀ M ∈ Sandwich K B a N, M = ((Φ M).comap P.mkQ).map R.subtype := by
    intro M hM
    have hP : P ≤ M.comap R.subtype := by
      refine Submodule.smul_le.2 fun r hr n _ => ?_
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul]
      exact M.smul_mem b (hM.1 _ n.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 hP, Submodule.map_comap_subtype,
      inf_eq_right.2 fun m hm => hM.2 m hm]
  have hinj : Set.InjOn Φ (Sandwich K B a N) := by
    intro M₁ h₁ M₂ h₂ h
    rw [key M₁ h₁, key M₂ h₂, h]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

theorem card_pos_le : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O),
    B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ,
    {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  intro K B ι _ e π S a hP ha hF N
  have he : CompleteOrthogonalIdempotents e := hF.1.1
  haveI : Algebra.Etale K.E B.A := GlobalTheory.etale_of_separable_charpoly_mulLeft K.E B.A B.g hP
  have hR := GlobalTheory.IntegralClosureFG.integralClosure_fg K.O K.E B.A
  have hfin := sandwich_finite K B hR ha.1 N
  refine ⟨(Sandwich K B a N).ncard, fun p => ?_⟩
  have hal : al K a ≠ 0 := by
    simpa using (IsFractionRing.injective K.O K.E).ne ha.1
  set t : B.A := ∑ j, (al K a ^ (-p j)) • e j with ht
  set t' : B.A := ∑ j, (al K a ^ (p j)) • e j with ht'
  have hcancel : ∀ x : B.A, t' * (t * x) = x := fun x =>
    sum_smul_mul_cancel he (fun j => al K a ^ (-p j)) (fun j => al K a ^ (p j))
      (fun i => by rw [← zpow_add₀ hal, add_neg_cancel, zpow_zero]) x
  have hmaps : ∀ M ∈ {M : Submodule K.O B.A | Pos B a e N M p}, mulLat K.O t M ∈ Sandwich K B a N := by
    intro M hM
    refine ⟨fun r hr => ?_, fun m hm => ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, (al K a ^ (p i + N)) • (e i * r),
        Submodule.sum_mem _ fun i _ => (hM i).1 r hr, ?_⟩
      rw [LinearMap.mulLeft_apply, Finset.mul_sum]
      calc ∑ i, t * (al K a ^ (p i + N) • (e i * r)) = ∑ i, (al K a ^ N) • (e i * r) :=
            Finset.sum_congr rfl fun i _ => by
              rw [mul_smul_comm, ht, sum_smul_mul_idem he, smul_smul, ← zpow_add₀ hal,
                show p i + N + -p i = (N : ℤ) by ring, zpow_natCast]
        _ = a ^ N • r := by
            rw [← Finset.smul_sum, ← Finset.sum_mul, he.complete, one_mul, ← map_pow, algebraMap_smul]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hm
      rw [LinearMap.mulLeft_apply, ht, sum_smul_mul he]
      exact IsIntegral.sum _ fun i _ => (hM i).2 y hy
  have hinj : Set.InjOn (mulLat K.O t) {M : Submodule K.O B.A | Pos B a e N M p} := by
    intro M₁ _ M₂ _ h
    have hid : (LinearMap.mulLeft K.O t').comp (LinearMap.mulLeft K.O t) = LinearMap.id :=
      LinearMap.ext fun x => hcancel x
    have h' := congrArg (Submodule.map (LinearMap.mulLeft K.O t')) h
    simp only [mulLat, ← Submodule.map_comp, hid, Submodule.map_id] at h'
    exact h'
  exact ⟨Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 hmaps)) hinj,
    Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin⟩

end GlobalTheory.UnitLemma.Desc.PosCount
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

theorem _root_.GlobalTheory.T.exists_isIntegral_smallElement_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A, ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  first | exact @GlobalTheory.UnitLemma.Desc.smul_pow_integral | exact GlobalTheory.UnitLemma.Desc.smul_pow_integral | (intros; apply GlobalTheory.UnitLemma.Desc.smul_pow_integral <;> assumption)
end
